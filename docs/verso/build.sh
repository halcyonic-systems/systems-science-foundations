#!/bin/bash
# Build Verso documents with Halcyonic theme
set -e

apply_theme() {
  local out="$1"
  cp halcyonic-theme.css "$out/"
  find "$out" -name "index.html" -exec sed -i '' 's|</head>|<link rel="stylesheet" href="/halcyonic-theme.css"></head>|' {} \;
}

echo "Building: A Formal Systems Ontology..."
lake exe proposal
PROPOSAL_OUT="_out/html-multi"
[ -d "$PROPOSAL_OUT" ] || PROPOSAL_OUT="_out/html-single"
apply_theme "$PROPOSAL_OUT"
echo "  → $PROPOSAL_OUT"

echo "Building: Building Story..."
lake exe building-story
STORY_OUT="_out/building-story/html-multi"
[ -d "$STORY_OUT" ] || STORY_OUT="_out/building-story/html-single"
if [ -d "$STORY_OUT" ]; then
  apply_theme "$STORY_OUT"
  echo "  → $STORY_OUT"
else
  echo "  (Building Story output not found — check Verso output path)"
fi

echo "Done."
