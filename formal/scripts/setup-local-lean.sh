#!/usr/bin/env bash
# Reproducible Linux x86_64 Lean installation, without elan/global configuration.
set -euo pipefail
project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
install_root="${LEAN_INSTALL_ROOT:-$project_dir/.toolchain}"
version=4.35.0
sha256=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
archive="lean-$version-linux.tar.zst"
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'This pinned installer supports Linux x86_64 only. Use the version in lean-toolchain on other systems.' >&2
  exit 1
fi
for command in curl sha256sum tar zstd; do
  command -v "$command" >/dev/null || { echo "Required program missing: $command" >&2; exit 1; }
done
mkdir -p "$install_root"
if [[ ! -x "$install_root/lean-$version-linux/bin/lean" ]]; then
  curl --fail --location --show-error \
    "https://github.com/leanprover/lean4/releases/download/v$version/$archive" \
    --output "$install_root/$archive"
  printf '%s  %s\n' "$sha256" "$install_root/$archive" | sha256sum --check -
  tar --zstd --extract --file "$install_root/$archive" --directory "$install_root"
fi
export PATH="$install_root/lean-$version-linux/bin:$PATH"
export MATHLIB_CACHE_DIR="$install_root/mathlib-cache"
export XDG_CACHE_HOME="$install_root/cache"
lean --version
lake --version
printf '\nFor this shell, run:\nexport PATH=%q:$PATH\n' "$install_root/lean-$version-linux/bin"
printf 'export MATHLIB_CACHE_DIR=%q\nexport XDG_CACHE_HOME=%q\n' "$MATHLIB_CACHE_DIR" "$XDG_CACHE_HOME"
