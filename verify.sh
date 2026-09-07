#!/bin/sh
set -eu
prime_gaps_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$prime_gaps_root"
exec "${PRIME_GAPS_PYTHON:-python3}" -B scripts/verify.py "$@"
