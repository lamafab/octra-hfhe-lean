#!/bin/bash
# This script runs after the container is created.

set -e

echo "=== DevContainer Setup ==="

# 1. Install the toolchain specified in lean-toolchain
TOOLCHAIN=$(cat lean-toolchain | tr -d '[:space:]')
echo "Installing toolchain: $TOOLCHAIN"
elan default "$TOOLCHAIN"

# 2. Update lake dependencies
echo "Updating lake dependencies..."
lake update

# 3. If Mathlib is a dependency, fetch precompiled cache
if grep -q "mathlib" lakefile.lean 2>/dev/null || grep -q "mathlib" lakefile.toml 2>/dev/null; then
    echo "Mathlib detected as dependency. Fetching precompiled cache..."
    echo "This may take a few minutes on first run."
    lake exe cache get || echo "WARNING: cache get failed. You may need to build Mathlib from source."
fi

echo ""
echo "=== Setup Complete ==="
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"