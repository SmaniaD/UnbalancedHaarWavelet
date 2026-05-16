#!/usr/bin/env bash
set -euo pipefail

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "Error: run this script from the root of a Lake project."
  exit 1
fi

if ! command -v rg >/dev/null 2>&1; then
  echo "Error: ripgrep (rg) is required but was not found in PATH."
  exit 1
fi

repo_root="$PWD"
if git rev-parse --show-toplevel >/dev/null 2>&1; then
  repo_root="$(git rev-parse --show-toplevel)"
fi
cd "$repo_root"

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  mapfile -t lean_files < <(git ls-files '*.lean')
else
  mapfile -t lean_files < <(find . -type f -name '*.lean' -not -path './.lake/*' -not -path './build/*' | sed 's#^\./##')
fi

if [ "${#lean_files[@]}" -eq 0 ]; then
  echo "No Lean files found to scan."
  exit 1
fi

critical_count=0
warning_count=0

scan_pattern() {
  local title="$1"
  local severity="$2"
  local regex="$3"

  local tmp
  tmp="$(mktemp)"

  if rg -n --color never -e "$regex" "${lean_files[@]}" >"$tmp"; then
    echo "[${severity}] ${title}"
    cat "$tmp"
    echo
    if [ "$severity" = "CRITICAL" ]; then
      critical_count=$((critical_count + 1))
    else
      warning_count=$((warning_count + 1))
    fi
  fi

  rm -f "$tmp"
}

echo "Scanning ${#lean_files[@]} Lean files for common proof-soundness risks..."
echo


scan_pattern "Found sorry" "CRITICAL" '\bsorry\b'
scan_pattern "Found admit" "CRITICAL" '\badmit\b'
scan_pattern "Found sorryAx" "CRITICAL" '\bsorryAx\b'
scan_pattern "Found explicit axiom/constant declaration" "CRITICAL" '^[[:space:]]*(axiom|constant)[[:space:]]+'
scan_pattern "Found set_option sorryElab true" "CRITICAL" '\bset_option[[:space:]]+sorryElab[[:space:]]+true\b'
scan_pattern "Found set_option debug.skipKernelTC" "CRITICAL" '\bset_option[[:space:]]+debug.skipKernelTC[[:space:]]+true\b'
scan_pattern "Found unsafe declaration (review manually)" "WARNING" '^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|example|abbrev|axiom)\b'

if [ "$critical_count" -gt 0 ]; then
  echo "Result: FAILED (${critical_count} critical pattern group(s), ${warning_count} warning pattern group(s))."
  echo "Your repository likely contains proof-soundness risks."
  exit 2
fi

if [ "$warning_count" -gt 0 ]; then
  echo "Result: PASS WITH WARNINGS (${warning_count} warning pattern group(s))."
  echo "No critical patterns found, but review warnings above."
  exit 0
fi

echo "Result: PASS."
echo "No known critical proof-soundness patterns were found."
