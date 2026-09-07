#!/usr/bin/env bash
# Additional swap only, on GitHub's disposable Linux virtual machine.
set -euo pipefail
if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_OS:-}" != Linux ||
      "${RUNNER_ENVIRONMENT:-}" != github-hosted ]]; then
  echo 'Memory preparation is restricted to a GitHub-hosted Linux runner.' >&2
  exit 1
fi

: "${RUNNER_TEMP:?GitHub runner temporary directory is required}"
swap_file="$RUNNER_TEMP/prime-gaps-verification.swap"
if [[ -e "$swap_file" || -L "$swap_file" ]]; then
  echo "Refusing to overwrite an existing swap file: $swap_file" >&2
  exit 1
fi

# The dependency cache is already present. Reserve 6 GiB for build outputs.
# Never remove installed software or existing files to make room.
required_mib=$(( (24 + 6) * 1024 ))
available_mib=$(df -Pm "$RUNNER_TEMP" | awk 'NR == 2 {print $4}')
# Some hosted VMs expose an additional temporary disk at /mnt. Use it when
# the workspace still has its 6 GiB reserve but lacks room for the swap file.
if (( available_mib >= 6 * 1024 && available_mib < required_mib )) && [[ -d /mnt ]]; then
  scratch_mib=$(df -Pm /mnt | awk 'NR == 2 {print $4}')
  if (( scratch_mib >= required_mib )); then
    swap_file=/mnt/prime-gaps-verification.swap
    available_mib=$scratch_mib
    if [[ -e "$swap_file" || -L "$swap_file" ]]; then
      echo "Refusing to overwrite an existing swap file: $swap_file" >&2
      exit 1
    fi
  fi
fi
if (( available_mib < required_mib )); then
  echo 'Insufficient disk space for 24 GiB swap plus 6 GiB build headroom.' >&2
  echo 'Use a runner with more capacity; no existing files were removed.' >&2
  df -h "$RUNNER_TEMP"
  exit 1
fi

sudo install -m 600 /dev/null "$swap_file"
sudo fallocate -l 24G "$swap_file"
sudo mkswap "$swap_file"
sudo swapon "$swap_file"
free -m
df -h "$RUNNER_TEMP" "$(dirname -- "$swap_file")"
# GitHub discards this VM and the additional swap file after the job.
