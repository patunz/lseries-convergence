#!/bin/sh
# Build LSeriesConv inside a clone of Tau Ceti at the pinned commit.
# Needs: git, elan (https://github.com/leanprover/elan), uv (https://docs.astral.sh/uv/).
# Usage: scripts/build.sh [workdir]     (default: ./_tc)
set -eu
TC_COMMIT=b608709b45f23ccda55703d572b0adb1fdec30fd
HERE="$(cd "$(dirname "$0")/.." && pwd)"
WORK="${1:-$HERE/_tc}"

if [ ! -d "$WORK/.git" ]; then
  git clone https://github.com/TauCetiProject/TauCeti.git "$WORK"
fi
cd "$WORK"
git fetch --depth 1 origin "$TC_COMMIT"
git checkout --detach "$TC_COMMIT"
grep -q 'name = "LSeriesConv"' lakefile.toml ||
  printf '\n[[lean_lib]]\nname = "LSeriesConv"\n' >> lakefile.toml
rm -rf LSeriesConv LSeriesConv.lean
cp -r "$HERE/LSeriesConv" "$HERE/LSeriesConv.lean" .

lake exe cache get                 # Mathlib's oleans
bash scripts/lake-cache-get.sh .   # Tau Ceti's oleans
lake build LSeriesConv

cat > LSeriesConv/Axioms.lean <<'EOF'
import LSeriesConv
#print axioms LSeriesConv.lseriesSummable_LFunction
#print axioms LSeriesConv.abscissaOfAbsConv_LFunction_le
#print axioms LSeriesConv.norm_LFunction_prime_pow_le
EOF
lake env lean LSeriesConv/Axioms.lean
rm LSeriesConv/Axioms.lean
