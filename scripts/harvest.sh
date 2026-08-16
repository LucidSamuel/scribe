#!/usr/bin/env bash
# Harvest verified public zkGolf submissions into corpus/submissions/.
# Usage: scripts/harvest.sh [slug ...] [--force]
set -euo pipefail
exec python3 "$(dirname "$0")/harvest.py" "$@"
