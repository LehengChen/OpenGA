#!/usr/bin/env bash
# Lift one DifferentialGeometry.Analysis.* module into OpenGALib/Analysis/*,
# rehoming namespace DifferentialGeometry.Analysis.* -> Analysis.* (drop DiffGeo
# root) and import paths -> OpenGALib.Analysis.*. Version-drift fixes are manual.
# Usage: scripts/lift-analysis.sh DifferentialGeometry.Analysis.Sub.Module
set -euo pipefail
mod="$1"
src="external/differential-geometry/${mod//.//}.lean"
rel="${mod#DifferentialGeometry.}"
dst="OpenGALib/${rel//.//}.lean"
[ -f "$src" ] || { echo "missing source: $src"; exit 1; }
mkdir -p "$(dirname "$dst")"
sed -e 's|import DifferentialGeometry\.Analysis|import OpenGALib.Analysis|g' \
    -e '/^namespace DifferentialGeometry$/d' \
    -e '/^end DifferentialGeometry$/d' \
    -e 's|DifferentialGeometry\.Analysis|Analysis|g' \
    "$src" > "$dst"
echo "lifted: $dst ($(wc -l < "$dst") lines)"
