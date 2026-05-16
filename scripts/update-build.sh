#!/usr/bin/env bash
set -euo pipefail

# Deve ser rodado na raiz do projeto Lake.

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "Error: run this script from the root of a Lake project."
  exit 1
fi

repo_root="$PWD"
if git rev-parse --show-toplevel >/dev/null 2>&1; then
  repo_root="$(git rev-parse --show-toplevel)"
fi
repo_name="$(basename "$repo_root")"

# Fallback para o nome do repositório quando não for possível detectar o pacote.
pkg_name="$repo_name"
if [ -f lakefile.toml ]; then
  detected_pkg="$(sed -n 's/^name = "\(.*\)"/\1/p' lakefile.toml | head -n1)"
  if [ -n "$detected_pkg" ]; then
    pkg_name="$detected_pkg"
  fi
fi

echo "==> Repository: $repo_name"
echo "==> Lean package: $pkg_name"

echo "==> Running lake update..."
lake update

echo "==> Downloading Mathlib cache..."
lake exe cache get

echo "==> Building..."
lake build

echo "==> Running leanchecker..."
lake env leanchecker "$pkg_name"

echo "==> Running proof sanity check..."
bash scripts/check-proof-sanity.sh

echo "==> Done."
