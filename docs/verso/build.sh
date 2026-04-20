#!/bin/bash
# Build Verso document with Halcyonic theme
set -e

lake exe proposal

OUT="_out/html-multi"
[ -d "$OUT" ] || OUT="_out/html-single"

# Copy theme CSS
cp halcyonic-theme.css "$OUT/"

# Inject theme link into all HTML files
find "$OUT" -name "index.html" -exec sed -i '' 's|</head>|<link rel="stylesheet" href="/halcyonic-theme.css"></head>|' {} \;

echo "Built with Halcyonic theme → $OUT"
