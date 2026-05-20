#!/usr/bin/env python3
"""Long-running LSP feedback server for proof-pilot.

Communicates via newline-delimited JSON on stdin/stdout.

Commands:
  {"cmd": "feedback", "file": "ZkGadgets/Foo.lean"}
    → Get diagnostics + goal states (opens file if needed).

  {"cmd": "update", "file": "ZkGadgets/Foo.lean"}
    → Close & reopen file to pick up disk changes, then get feedback.

  {"cmd": "quit"}
    → Shut down cleanly.

File paths are relative to the Lean project root.
"""
import sys
import json
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
