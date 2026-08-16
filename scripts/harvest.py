#!/usr/bin/env python3
"""Harvest verified public zkGolf submissions into corpus/submissions/.

For every challenge (or the slugs given on the command line) this downloads:
  - challenge.json     — challenge metadata (spec, baseline, comparison points)
  - state.json         — current leader + solver counts
  - leaderboard.json   — ranked record-setting submissions
  - per submission <rank>-<id8>/:
      metadata.json    — score, allocations/constraints, description (technique
                         write-ups — solvers document their own tricks here)
      solution.diff    — what this record changed. Leaderboard ranks are
                         CHRONOLOGICAL (rank 1 = first record, rank N = current
                         best) and the API's default diff base is the previous
                         record — the baseline reference solution
                         (corpus/zk-golf-challenges/Solution/<Instance>/) for
                         rank 1.
      files/           — the full reconstructed solution, built by chaining:
                         baseline + diff(1) + … + diff(rank) via patch(1)

Uses only the Python standard library. Idempotent: already-harvested
submissions are skipped unless --force is given.

API: https://zk.golf/llms.txt  (public endpoints, no auth required)
"""

import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import time

BASE = "https://zk.golf/api/agent/v1"
REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT_ROOT = REPO_ROOT / "corpus" / "submissions"
SLEEP = 0.5  # politeness delay between requests


class HTTPError(Exception):
    def __init__(self, code, url):
        super().__init__(f"HTTP {code} on {url}")
        self.code = code


def get(path, raw=False):
    # curl instead of urllib: the framework Python on macOS often has no CA
    # bundle, and curl uses the system trust store.
    url = f"{BASE}{path}"
    for attempt in range(3):
        proc = subprocess.run(
            ["curl", "-sS", "-w", "\n%{http_code}", "-A", "scribe-harvest/0.1",
             "--max-time", "60", url],
            capture_output=True, check=True,
        )
        body, _, code = proc.stdout.rpartition(b"\n")
        code = int(code)
        if code == 429 or code >= 500:
            wait = 5 * (attempt + 1)
            print(f"  HTTP {code} on {path}, retrying in {wait}s", file=sys.stderr)
            time.sleep(wait)
            continue
        if code != 200:
            raise HTTPError(code, url)
        time.sleep(SLEEP)
        return body if raw else json.loads(body)
    raise RuntimeError(f"giving up on {url}")


GOLF_REPO = REPO_ROOT / "corpus" / "zk-golf-challenges"


def baseline_dir_for(slug):
    """Extract the baseline Solution/<Instance> as of the FIRST record's
    submission date (the server diffs rank 1 against the baseline it shipped
    with, which may predate the current repo HEAD). Cached under
    <slug>/baseline/. Requires a full (unshallowed) clone at GOLF_REPO."""
    cache = OUT_ROOT / slug / "baseline"
    if cache.is_dir():
        return cache
    ch = json.loads((OUT_ROOT / slug / "challenge.json").read_text())
    instance = ch.get("instance_name")
    board = json.loads((OUT_ROOT / slug / "leaderboard.json").read_text())
    if not instance:
        return None
    live = GOLF_REPO / "Solution" / instance
    if not board:
        return live if live.is_dir() else None
    first = min(e["submitted_at"] for e in board)
    rev = subprocess.run(
        ["git", "-C", str(GOLF_REPO), "rev-list", "-1", f"--before={first}", "HEAD"],
        capture_output=True, text=True, check=True).stdout.strip()
    if not rev:
        return live if live.is_dir() else None
    cache.mkdir(parents=True)
    tar = subprocess.Popen(
        ["git", "-C", str(GOLF_REPO), "archive", rev, f"Solution/{instance}"],
        stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "--strip-components", "2", "-C", str(cache)],
                   stdin=tar.stdout, check=True)
    tar.wait()
    return cache


def reconstruct_files(diff_path, out_dir, baseline):
    """The API's no-base diff is `diff -ruN -- base/ target/` where base/ is the
    BASELINE reference solution. Rebuild the full solution by copying the
    baseline and applying the diff with patch(1) (-p1 strips base//target/)."""
    if out_dir.exists():
        shutil.rmtree(out_dir)
    if baseline:
        shutil.copytree(baseline, out_dir,
                        ignore=shutil.ignore_patterns("*.rej", "*.orig"))
    else:
        out_dir.mkdir(parents=True)
    proc = subprocess.run(
        ["patch", "-p1", "-s", "-f", "-E", "--no-backup-if-mismatch",
         "-d", str(out_dir), "-i", str(diff_path.resolve())],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        print(f"    patch failed for {out_dir.parent.name}: "
              f"{proc.stderr.strip() or proc.stdout.strip()}", file=sys.stderr)


def harvest_challenge(slug, force):
    out = OUT_ROOT / slug
    out.mkdir(parents=True, exist_ok=True)
    print(f"== {slug}")

    (out / "challenge.json").write_text(json.dumps(get(f"/challenges/{slug}"), indent=2))
    (out / "state.json").write_text(json.dumps(get(f"/challenges/{slug}/state"), indent=2))
    board = get(f"/challenges/{slug}/leaderboard")
    (out / "leaderboard.json").write_text(json.dumps(board, indent=2))

    prev_files, prev_sid = baseline_dir_for(slug), None
    for entry in board:  # ranks are chronological: 1 = first record
        sid = entry["submission_id"]
        sdir = out / f"{entry['rank']:02d}-{sid[:8]}"
        if not (sdir / "solution.diff").exists() or force:
            sdir.mkdir(parents=True, exist_ok=True)
            print(f"  #{entry['rank']} {sid[:8]} score={entry['score']} by {entry.get('github_login')}")
            meta = get(f"/submissions/{sid}")
            (sdir / "metadata.json").write_text(json.dumps(meta, indent=2))
            # rank 1: default base (= baseline at challenge launch); later
            # ranks: explicit base so the chain is exact regardless of drift
            path = f"/submissions/{sid}/diff" + (f"?base={prev_sid}" if prev_sid else "")
            (sdir / "solution.diff").write_text(get(path, raw=True).decode())
        # always re-chain files/ so every rank builds on the previous record
        reconstruct_files(sdir / "solution.diff", sdir / "files", prev_files)
        prev_files, prev_sid = sdir / "files", sid

    return board


def write_index(harvested):
    """corpus/submissions/INDEX.md — scores + technique descriptions at a glance."""
    lines = ["# Harvested zkGolf submissions\n"]
    for slug, board in sorted(harvested.items()):
        ch = json.loads((OUT_ROOT / slug / "challenge.json").read_text())
        lines.append(f"\n## {slug} (baseline {ch.get('baseline_score')}, best {ch.get('best_score')})\n")
        for entry in board:
            sid = entry["submission_id"]
            meta_path = OUT_ROOT / slug / f"{entry['rank']:02d}-{sid[:8]}" / "metadata.json"
            desc = ""
            if meta_path.exists():
                meta = json.loads(meta_path.read_text())
                desc = (meta.get("description") or "").strip()
                assisted = meta.get("assisted_by")
                if assisted:
                    desc = f"*(assisted by {assisted})* {desc}"
            lines.append(
                f"### #{entry['rank']} — {entry['score']} "
                f"({entry['allocations']}a + {entry['constraints']}c) "
                f"by {entry.get('github_login')} — `{sid[:8]}`\n\n{desc}\n"
            )
    (OUT_ROOT / "INDEX.md").write_text("\n".join(lines))
    print(f"wrote {OUT_ROOT / 'INDEX.md'}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("slugs", nargs="*", help="challenge slugs (default: all)")
    ap.add_argument("--force", action="store_true", help="re-download existing submissions")
    ap.add_argument("--rebuild", action="store_true",
                    help="re-apply stored solution.diff files locally, no network")
    args = ap.parse_args()

    if args.rebuild:
        for slug_dir in sorted(d for d in OUT_ROOT.iterdir() if d.is_dir()):
            if args.slugs and slug_dir.name not in args.slugs:
                continue
            prev_files = baseline_dir_for(slug_dir.name)
            for sdir in sorted(d for d in slug_dir.iterdir() if d.is_dir()):
                diff_path = sdir / "solution.diff"
                if diff_path.exists():
                    reconstruct_files(diff_path, sdir / "files", prev_files)
                    prev_files = sdir / "files"
            print(f"rebuilt {slug_dir.name}")
        return

    challenges = get("/challenges")
    slugs = args.slugs or [c["slug"] for c in challenges]
    unknown = set(slugs) - {c["slug"] for c in challenges}
    if unknown:
        sys.exit(f"unknown slugs: {', '.join(sorted(unknown))}")

    harvested = {}
    for slug in slugs:
        try:
            harvested[slug] = harvest_challenge(slug, args.force)
        except Exception as e:  # keep going; one bad challenge shouldn't kill the run
            print(f"  FAILED {slug}: {e}", file=sys.stderr)
    write_index(harvested)


if __name__ == "__main__":
    main()
