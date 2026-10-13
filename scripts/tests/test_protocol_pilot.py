import importlib.util
import tempfile
import unittest
import os
import sys
import time
from unittest.mock import patch
from pathlib import Path

spec = importlib.util.spec_from_file_location("pilot", Path(__file__).parents[1] / "protocol_pilot.py")
pilot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pilot)

LIMITS = dict(calls=6, input_bytes=12000, output_tokens=1536, seconds=60,
              retries=1, depth=2, children=3, usd=1,
              input_usd_per_million=1, output_usd_per_million=1)
ROOT = dict(id="fixture", prefix="", positive="True", negative="False", leakage="synthetic test", validation={"fixture": True})
JOB = dict(id="fixture", root="fixture", arm="decomposition", polarity="positive", repetition=0)


class PilotTests(unittest.TestCase):
    def run_fixture(self, responses, checker, **limits):
        with tempfile.TemporaryDirectory() as directory:
            return pilot.run_session(ROOT, JOB, dict(LIMITS, **limits), pilot.Replay(responses), checker, Path(directory))

    def test_late_provider_cannot_close_root(self):
        clock = [0.0]
        def late(prompt, timeout):
            clock[0] = 61.0
            return '{"proof":"by trivial"}', {}
        with patch.object(pilot.time, "monotonic", side_effect=lambda: clock[0]), tempfile.TemporaryDirectory() as directory:
            result = pilot.run_session(ROOT, JOB, LIMITS, late, lambda *args, **kwargs: (True, ""), Path(directory))
        self.assertEqual(result["outcome"], "budget_exhausted")
        self.assertFalse(result["root_closed"])

    def test_late_checker_cannot_close_root(self):
        clock = [0.0]
        def late(*args, **kwargs):
            clock[0] = 61.0
            return True, ""
        with patch.object(pilot.time, "monotonic", side_effect=lambda: clock[0]):
            result = self.run_fixture([{"proof": "by trivial"}], late)
        self.assertEqual(result["outcome"], "budget_exhausted")
        self.assertFalse(result["root_closed"])

    def test_hung_worker_is_killed_by_aggregate_deadline(self):
        started = time.monotonic()
        with self.assertRaises(pilot.BudgetExceeded):
            pilot.run_process([sys.executable, "-c", "import time; time.sleep(10)"], 0.2)
        self.assertLess(time.monotonic() - started, 3)

    def test_provider_worker_deadline_covers_blocked_io(self):
        # A FIFO blocks urllib's file handler without any network or paid call.
        with tempfile.TemporaryDirectory() as directory:
            fifo = Path(directory) / "blocked-response"
            os.mkfifo(fifo)
            provider = pilot.OpenAIChat("fixture", "not-a-real-key", fifo.as_uri(), LIMITS)
            with self.assertRaises(pilot.BudgetExceeded):
                provider("fixture", 0.2)

    def test_untrusted_host_checker_fails_closed(self):
        with self.assertRaises(pilot.IsolationUnavailable):
            pilot.lean_checker("lean", Path("."))

    def test_worker_output_is_bounded(self):
        with self.assertRaisesRegex(pilot.BudgetExceeded, "output byte cap"):
            pilot.run_process([sys.executable, "-c", "print('x' * 100000)"], 3, output_limit=1024)

    @unittest.skipUnless(os.environ.get("SCRIBE_PILOT_DOCKER_TESTS"), "requires explicit Docker integration run")
    def test_isolated_kernel_verifier_rejects_real_exit_zero_bypass(self):
        image = pilot.docker_image_id(os.environ.get("SCRIBE_PILOT_IMAGE", "scribe:pilot-isolated"))
        with tempfile.TemporaryDirectory() as directory:
            check = pilot.docker_checker(image, Path(directory))
            passed, _ = check("", "False", "by\n  run_tac do\n    let _ ← (IO.Process.exit 0 : IO Unit)\n    pure ()", False, 120)
            self.assertFalse(passed)
            passed, feedback = check("", "True", "by trivial", False, 120)
            self.assertTrue(passed, feedback)
            # A child compiler fabricates an artifact while the original false
            # candidate exits zero. Independent type and axiom checks must win.
            for forged in ("theorem pilot_root : True := by trivial",
                           "axiom invented : False\ntheorem pilot_root : False := invented"):
                import json
                text = "import ZkGadgets.Audit\n" + forged + "\n"
                proof = ("by\n  run_tac do\n    IO.FS.writeFile \"/work/Forged.lean\" " + json.dumps(text) +
                         "\n    let _ ← IO.Process.output {cmd := \"lake\", args := #[\"env\", \"lean\", "
                         "\"--root=/work\", \"-o\", \"/work/Candidate.olean\", \"/work/Forged.lean\"]}" +
                         "\n    let _ ← (IO.Process.exit 0 : IO Unit)\n    pure ()")
                passed, feedback = check("", "False", proof, False, 120)
                self.assertFalse(passed, feedback)
                expected = "frozen proposition" if "True" in forged else "untrusted axiom"
                self.assertIn(expected, feedback)

    @unittest.skipUnless(os.environ.get("SCRIBE_PILOT_DOCKER_TESTS"), "requires explicit Docker integration run")
    def test_universe_polymorphic_target_is_explicitly_rejected(self):
        image = pilot.docker_image_id(os.environ.get("SCRIBE_PILOT_IMAGE", "scribe:pilot-isolated"))
        with tempfile.TemporaryDirectory() as directory:
            check = pilot.docker_checker(image, Path(directory))
            passed, feedback = check("universe u", "∀ (α : Type u) (x : α), x = x",
                                     "by intro α x; rfl", False, 120)
            self.assertFalse(passed, feedback)
            self.assertIn("universe-polymorphic targets are unsupported", feedback)

    def test_schedule_is_balanced_reproducible_and_shuffled(self):
        manifest = {"roots": [dict(ROOT, id=f"root-{i}") for i in range(6)]}
        jobs = pilot.schedule(manifest, 42)
        self.assertEqual(jobs, pilot.schedule(manifest, 42))
        self.assertNotEqual(jobs, pilot.schedule(manifest, 43))
        self.assertEqual(len(jobs), 48)
        self.assertEqual(sum(j["polarity"] == "positive" for j in jobs), 36)
        self.assertEqual(sum(j["polarity"] == "negative" for j in jobs), 12)

    def test_closed_leaves_do_not_count_as_root_closure(self):
        def checker(prefix, statement, proof, refutation, timeout, **kwargs):
            return (statement == "1 = 1", "root recomposition fails")
        responses = [{"children": [{"statement": "1 = 1"}], "proof": "by exact False.elim"}, {"proof": "by rfl"}]
        result = self.run_fixture(responses, checker, retries=0)
        self.assertEqual(result["outcome"], "stalled")
        self.assertFalse(result["root_closed"])
        self.assertEqual(result["calls"], 2)

    def test_decomposition_and_recomposition_share_call_budget(self):
        responses = [{"children": [{"statement": "True"}], "proof": "by exact leaf_0"}, {"proof": "by trivial"}]
        result = self.run_fixture(responses, lambda *args, **kwargs: (True, ""), calls=1)
        self.assertEqual(result["outcome"], "budget_exhausted")
        self.assertEqual(result["calls"], 1)
        self.assertFalse(result["root_closed"])

    def test_failed_provider_is_charged_and_classified(self):
        result = self.run_fixture([], lambda *args, **kwargs: (True, ""))
        self.assertEqual(result["outcome"], "tool_failure")
        self.assertGreater(result["reserved_usd"], 0)

    def test_recomposed_root_checked(self):
        observed = []
        def checker(prefix, statement, proof, refutation, timeout, **kwargs):
            observed.append((statement, proof, kwargs["trusted_statement"]))
            return True, ""
        result = self.run_fixture([{"children": [{"statement": "1 = 1"}], "proof": "by trivial"}, {"proof": "by rfl"}], checker)
        self.assertEqual(result["outcome"], "root_closed")
        self.assertEqual(observed[-1][0], ROOT["positive"])
        self.assertIn("have leaf_0", observed[-1][1])
        self.assertEqual([row[2] for row in observed], [False, True])

    def test_axiom_audit_is_in_generated_source(self):
        text = pilot.source("", "True", "by sorry")
        self.assertIn("#audit_axioms pilot_root", text)
        self.assertIn("theorem pilot_root :\n  True :=", text)

    def test_dollar_cap_prevents_dispatch(self):
        result = self.run_fixture([{"proof": "by trivial"}], lambda *args, **kwargs: (True, ""), usd=0.001)
        self.assertEqual(result["outcome"], "budget_exhausted")
        self.assertEqual(result["calls"], 0)

    def test_uncertainty_is_not_reported_for_incomplete_roots(self):
        result = self.run_fixture([{"proof": "by trivial"}], lambda *args, **kwargs: (True, ""))
        self.assertIsNone(pilot.report([result])["paired_root_uncertainty"])

    def test_compact_replay_keeps_direct_and_split_sessions_separate(self):
        fixtures = {"fixtures": {"fixture": {"proof": "by trivial", "refutation": "by simp"}}}
        split = pilot.replay_responses(fixtures, JOB, ROOT)
        direct = pilot.replay_responses(fixtures, dict(JOB, arm="direct"), ROOT)
        self.assertEqual(len(split), 2)
        self.assertEqual(len(direct), 1)
        self.assertEqual(split[0]["children"][0]["statement"], ROOT["positive"])
        self.assertEqual(pilot.replay_responses({"fixtures": {}}, JOB, ROOT), [])

    def test_refutation_is_not_proof_success(self):
        result = self.run_fixture([{"refutation": "by intro h; contradiction"}], lambda *args, **kwargs: (True, ""))
        self.assertEqual(result["outcome"], "checked_refutation")
        self.assertFalse(result["root_closed"])


if __name__ == "__main__":
    unittest.main()
