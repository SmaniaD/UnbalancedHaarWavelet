#!/usr/bin/env bash
set -euo pipefail

# Deve ser rodado na raiz do projeto Lake.

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "Erro: rode este script na raiz do projeto Lake."
  exit 1
fi

echo "==> Rodando lake update..."
lake update

echo "==> Baixando cache da mathlib..."
lake exe cache get

echo "==> Compilando..."
lake build

echo "==> Pronto."
