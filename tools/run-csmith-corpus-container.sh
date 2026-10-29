#!/bin/sh
set -eu

workspace=/campaign/CLight-Lean
csmith=/opt/csmith/bin/csmith
runtime_include=/opt/csmith/include

if [ ! -x "$csmith" ] || [ ! -f "$runtime_include/csmith.h" ] || [ ! -f "$runtime_include/safe_math.h" ]; then
  echo "container CSmith installation is incomplete" >&2
  exit 2
fi

exec python3 "$workspace/tools/csmith_corpus.py" \
  --csmith-bin "$csmith" \
  --csmith-runtime-include "$runtime_include" \
  --compcert-root /campaign/CompCert \
  --csmith-root /campaign/csmith \
  "$@"
