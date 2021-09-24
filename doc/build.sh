#!/usr/bin/env bash

set -euo pipefail

[[ -d doc ]] && cd doc

LANGS=(Es En)

# Create latex target files
mkdir -p latex
cp ./llncs.cls latex

poetry run python render.py "${LANGS[@]/%/.lagda}"

for L in "${LANGS[@]}"; do
  agda --latex "$L.lagda"

  (
  cd latex
  xelatex -shell-escape -interaction=nonstopmode "$L.tex"
  )
done

