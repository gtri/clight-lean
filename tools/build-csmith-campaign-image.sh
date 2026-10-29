#!/bin/sh
set -eu

# Build a minimal, source-only Docker context from the pinned CLight-Lean
# commit. The Dockerfile fetches public CompCert and CSmith commits itself, so
# local sibling checkouts are not required. This avoids sending local Lake
# caches, generated case trees, artifacts, or unrelated untracked workspace
# material to the Docker daemon.

# The single source of truth for the campaign pin. The default image tag is
# derived from this revision below, so bumping the pin is a one-line change.
CLIGHT_LEAN_REV=cd99b5b2bfd0d494ce0296858d58a9ed74181b6e
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
clight_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
tag=${1:-clight-csmith:$(git -C "$clight_root" rev-parse --short "$CLIGHT_LEAN_REV")}

require_revision() {
  directory=$1
  revision=$2
  label=$3
  test -d "$directory/.git" || {
    echo "$label checkout has no .git directory: $directory" >&2
    exit 2
  }
  git -C "$directory" cat-file -e "$revision^{commit}" 2>/dev/null || {
    echo "$label does not contain required commit: $revision" >&2
    exit 2
  }
}

require_revision "$clight_root" "$CLIGHT_LEAN_REV" CLight-Lean

context=$(mktemp -d "${TMPDIR:-/tmp}/clight-csmith-context.XXXXXX")
cleanup() { rm -rf "$context"; }
trap cleanup EXIT HUP INT TERM

mkdir "$context/CLight-Lean"
git -C "$clight_root" archive "$CLIGHT_LEAN_REV" | tar -x -C "$context/CLight-Lean"
printf '%s\n' "$CLIGHT_LEAN_REV" > "$context/CLight-Lean/.campaign-source-rev"

# Copy the container inputs after exporting the pinned source archive. This
# permits a WIP checkout to validate its container layout without admitting any
# other untracked workspace material into the Docker context.
cp "$clight_root/Dockerfile.csmith-campaign" "$context/CLight-Lean/"
mkdir -p "$context/CLight-Lean/tools"
cp "$clight_root/tools/run-csmith-corpus-container.sh" \
  "$context/CLight-Lean/tools/"
mkdir -p "$context/CLight-Lean/patches"
cp "$clight_root/patches/compcert-lean-clightgen.patch" \
  "$context/CLight-Lean/patches/"

if [ "${CSMITH_CAMPAIGN_DRY_RUN:-0}" = 1 ]; then
  test -f "$context/CLight-Lean/.campaign-source-rev"
  test -f "$context/CLight-Lean/Dockerfile.csmith-campaign"
  test -f "$context/CLight-Lean/patches/compcert-lean-clightgen.patch"
  test -x "$context/CLight-Lean/tools/run-csmith-corpus-container.sh"
  printf '%s\n' "campaign Docker context: PASS ($context/CLight-Lean)"
  exit 0
fi

docker build \
  -f "$context/CLight-Lean/Dockerfile.csmith-campaign" \
  --build-arg CLIGHT_LEAN_REV="$CLIGHT_LEAN_REV" \
  -t "$tag" \
  "$context/CLight-Lean"
