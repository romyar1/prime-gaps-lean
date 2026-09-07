#!/usr/bin/env bash
# Linux runner wrapper: preserve the verifier's exit status and resource evidence.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
mkdir -p verification

resource_snapshot() {
  date -u '+%Y-%m-%dT%H:%M:%SZ'
  free -m
  df -h .
  # Include arguments so a stalled module can be identified while Lake is
  # still buffering its compiler's output. ps contains no environment values.
  ps -eo pid,ppid,pcpu,rss,etime,args --sort=-rss | head -n 12 || true
}

resource_snapshot | tee verification/resources.log
(
  while sleep 30; do
    resource_snapshot | tee -a verification/resources.log
  done
) &
monitor_pid=$!
trap 'kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true' EXIT

# A whole-verification deadline leaves time within the 180-minute job for
# cleanup and upload. SIGINT lets verify.py record FAIL and stop its children.
# --fresh cleans this package only; the pinned Mathlib cache remains usable.
timeout --signal=INT --kill-after=30s 150m \
  /usr/bin/time -v -o verification/time.txt \
  ./verify.sh --fresh --timeout 8400
