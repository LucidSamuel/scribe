#!/usr/bin/env python3
"""Long-running LSP feedback server for proof-pilot.

Communicates via newline-delimited JSON on stdin/stdout.

Commands:
  {"cmd": "feedback", "file": "ZkGadgets/Foo.lean"}
    → Get diagnostics + goal states (opens file if needed).

  {"cmd": "update", "file": "ZkGadgets/Foo.lean"}
    → Close & reopen file to pick up disk changes, then get feedback.

  {"cmd": "search", "query": "sub_eq_zero", "num_results": 5}
    → Search Mathlib via loogle for relevant lemmas.

  {"cmd": "probe", "file": "ZkGadgets/Foo.lean", "line": 12, "col": 2,
   "tactics": ["ring", "simp", "linear_combination h"]}
    → Try each tactic at a position and report which ones make progress.

  {"cmd": "quit"}
    → Shut down cleanly.

File paths are relative to the Lean project root.
"""
import sys
import json
import re
from leanclient import LeanLSPClient


def gather_feedback(client, file_path):
    """Get diagnostics and goal states for a Lean file."""
    result = client.get_diagnostics(file_path)

    diagnostics = []
    for d in result.diagnostics:
        rng = d.get("range", {})
        start = rng.get("start", {})
        diagnostics.append({
            "line": start.get("line", 0),
            "col": start.get("character", 0),
            "severity": d.get("severity", 1),
            "message": d.get("message", ""),
        })

    # Collect positions to query for goal state:
    # 1. Error diagnostic positions
    # 2. Actual `sorry` token positions in the file content
    query_positions = set()
    for d in diagnostics:
        if d["severity"] == 1:  # errors
            query_positions.add((d["line"], d["col"]))

    # Find sorry tokens in the file to get their tactic state
    try:
        content = client.get_file_content(file_path)
        for i, line_text in enumerate(content.splitlines()):
            col = line_text.find("sorry")
            if col >= 0:
                query_positions.add((i, col))
    except Exception:
        pass

    goals = []
    for (line, col) in sorted(query_positions):
        try:
            goal = client.get_goal(file_path, line, col)
            if goal and isinstance(goal, dict):
                goal_list = goal.get("goals", [])
                if goal_list:
                    goals.append({
                        "line": line,
                        "col": col,
                        "goals": goal_list,
                    })
        except Exception:
            pass

    # Also check for forbidden tactic warnings (sorry, axiom, native_decide)
    has_forbidden = any(
        "sorry" in d["message"].lower() or
        "axiom" in d["message"].lower() or
        "native_decide" in d["message"].lower()
        for d in diagnostics
        if d["severity"] == 2  # warnings
    )

    return {
        "success": result.success and not has_forbidden,
        "diagnostics": diagnostics,
        "goals": goals,
    }


def search_loogle(query, num_results=5):
    """Search Mathlib via loogle for relevant lemmas."""
    try:
        from lean_lsp_mcp.loogle import loogle_remote
        results = loogle_remote(query, num_results)
        if isinstance(results, str):
            # Error message
            return {"results": [], "error": results}
        return {
            "results": [
                {"name": r.name, "type": str(r.type), "module": str(r.module)}
                for r in results
            ]
        }
    except Exception as e:
        return {"results": [], "error": str(e)}


def probe_tactics(client, file_path, line, col, tactics):
    """Try each tactic at a position and report goal state / success."""
    try:
        content = client.get_file_content(file_path)
    except Exception:
        # File might not be open yet
        client.get_diagnostics(file_path)
        content = client.get_file_content(file_path)

    lines = content.splitlines()

    # Find the tactic at (line, col) — typically a sorry or failed tactic.
    # We'll replace the entire line's tactic content with each candidate.
    if line >= len(lines):
        return {"error": f"line {line} out of range (file has {len(lines)} lines)"}

    # Find the indentation of the target line
    target_line = lines[line]
    indent = len(target_line) - len(target_line.lstrip())
    indent_str = target_line[:indent]

    results = []
    for tactic in tactics:
        # Build modified content: replace the line at (line) with the candidate tactic
        modified_lines = lines[:line] + [indent_str + tactic] + lines[line + 1:]
        modified_content = "\n".join(modified_lines)
        if content.endswith("\n"):
            modified_content += "\n"

        try:
            client.update_file_content(file_path, modified_content)
            diags = client.get_diagnostics(file_path)

            # Check for errors on this specific line
            line_errors = [
                d for d in diags.diagnostics
                if d.get("range", {}).get("start", {}).get("line", -1) == line
                and d.get("severity", 1) == 1
            ]

            # Get goal state after this tactic
            goal = None
            # Query goal at the line AFTER, to see remaining goals
            if line + 1 < len(modified_lines):
                try:
                    goal_resp = client.get_goal(file_path, line + 1, 0)
                    if goal_resp and isinstance(goal_resp, dict):
                        goal = goal_resp.get("goals", [])
                except Exception:
                    pass

            if not line_errors and diags.success:
                results.append({
                    "tactic": tactic,
                    "status": "solved",
                    "remaining_goals": goal or [],
                })
            elif not line_errors:
                results.append({
                    "tactic": tactic,
                    "status": "progress",
                    "remaining_goals": goal or [],
                })
            else:
                err_msg = line_errors[0].get("message", "error")
                results.append({
                    "tactic": tactic,
                    "status": "failed",
                    "error": err_msg.split("\n")[0],
                })
        except Exception as e:
            results.append({
                "tactic": tactic,
                "status": "error",
                "error": str(e),
            })

    # Restore original content
    try:
        client.update_file_content(file_path, content)
    except Exception:
        pass

    return {"results": results}


def main():
    if len(sys.argv) < 2:
        print(json.dumps({"error": "usage: lsp-server.py <lean-project-path>"}),
              flush=True)
        sys.exit(1)

    project_path = sys.argv[1]
    print(json.dumps({"status": "ready"}), flush=True)

    client = None
    try:
        client = LeanLSPClient(project_path, initial_build=False)
        print(json.dumps({"status": "initialized"}), flush=True)

        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue

            try:
                cmd = json.loads(line)
            except json.JSONDecodeError as e:
                print(json.dumps({"error": f"invalid JSON: {e}"}), flush=True)
                continue

            action = cmd.get("cmd", "")

            if action == "quit":
                print(json.dumps({"status": "quit"}), flush=True)
                break

            elif action == "feedback":
                file_path = cmd.get("file", "")
                try:
                    fb = gather_feedback(client, file_path)
                    print(json.dumps(fb), flush=True)
                except Exception as e:
                    print(json.dumps({"error": str(e)}), flush=True)

            elif action == "update":
                file_path = cmd.get("file", "")
                try:
                    # Close file so LSP re-reads from disk
                    try:
                        client.close_files([file_path])
                    except Exception:
                        pass
                    fb = gather_feedback(client, file_path)
                    print(json.dumps(fb), flush=True)
                except Exception as e:
                    print(json.dumps({"error": str(e)}), flush=True)

            elif action == "search":
                query = cmd.get("query", "")
                num = cmd.get("num_results", 5)
                try:
                    result = search_loogle(query, num)
                    print(json.dumps(result), flush=True)
                except Exception as e:
                    print(json.dumps({"results": [], "error": str(e)}),
                          flush=True)

            elif action == "probe":
                file_path = cmd.get("file", "")
                line = cmd.get("line", 0)
                col = cmd.get("col", 0)
                tactics = cmd.get("tactics", [])
                try:
                    result = probe_tactics(client, file_path, line, col, tactics)
                    print(json.dumps(result), flush=True)
                except Exception as e:
                    print(json.dumps({"error": str(e)}), flush=True)

            else:
                print(json.dumps({"error": f"unknown command: {action}"}),
                      flush=True)

    except Exception as e:
        print(json.dumps({"error": f"init failed: {e}"}), flush=True)
        sys.exit(1)

    finally:
        if client:
            try:
                client.close()
            except Exception:
                pass


if __name__ == "__main__":
    main()
