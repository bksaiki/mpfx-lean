#!/usr/bin/env bash
# Packages the sources needed to build Myna into myna-lean.tar.gz.
set -euo pipefail
cd "$(dirname "$0")"

out=myna-lean.tar.gz
files=(
  README.md LICENSE NOTICE docs/DESIGN.md
  lakefile.toml lake-manifest.json lean-toolchain
  Myna.lean Myna MynaTest
)

# Strip owner names and timestamps so the archive carries no identifying metadata.
tar --create --sort=name --transform 's,^,myna-lean/,' \
    --owner=0 --group=0 --numeric-owner --mtime='2000-01-01' \
    "${files[@]}" | gzip -n > "$out"
echo "wrote $out"
