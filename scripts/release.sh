#!/usr/bin/env bash
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "Uso: $0 v0.1.0"
  exit 1
fi

TAG="$1"

# Conferências básicas
command -v git >/dev/null || { echo "Erro: git não encontrado"; exit 1; }
command -v gh >/dev/null || { echo "Erro: GitHub CLI 'gh' não encontrado"; exit 1; }
command -v lake >/dev/null || { echo "Erro: lake não encontrado"; exit 1; }

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "Erro: rode este script na raiz do projeto Lake."
  exit 1
fi

if [ -n "$(git status --porcelain)" ]; then
  echo "Erro: há mudanças não commitadas."
  echo "Faça commit antes de criar a release."
  git status --short
  exit 1
fi

if git rev-parse "$TAG" >/dev/null 2>&1; then
  echo "Erro: a tag $TAG já existe localmente."
  exit 1
fi

if git ls-remote --tags origin "$TAG" | grep -q "$TAG"; then
  echo "Erro: a tag $TAG já existe no GitHub."
  exit 1
fi

echo "==> Baixando cache da mathlib, se disponível..."
lake exe cache get || true

echo "==> Compilando projeto..."
lake build

echo "==> Criando tag $TAG..."
git tag -a "$TAG" -m "Release $TAG"

echo "==> Enviando branch atual e tag para o GitHub..."
CURRENT_BRANCH="$(git branch --show-current)"
git push origin "$CURRENT_BRANCH"
git push origin "$TAG"

echo "==> Criando GitHub release..."
gh release create "$TAG" \
  --title "$TAG" \
  --notes "Release $TAG with precompiled Lake build artifacts."

echo "==> Enviando artefatos pré-compilados com lake upload..."
lake upload "$TAG"

echo "==> Pronto."
echo "Release criada: $TAG"
