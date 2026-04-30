#!/bin/bash
# Build Verso documents with Halcyonic theme
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

apply_theme() {
  local out="$1"
  cp halcyonic-theme.css "$out/"
  # Inject theme at END of </body> as <style> block to guarantee cascade priority
  # This ensures our overrides beat Verso's inline <style> blocks
  find "$out" -name "index.html" -exec sed -i '' "s|</body>|<link rel=\"stylesheet\" href=\"/halcyonic-theme.css\"></body>|" {} \;
  # Add "Introduction" entry before chapter 1 in the TOC (handles both "numbered" and "current numbered")
  find "$out" -name "index.html" -exec sed -i '' 's|<tr class="\(.*\)numbered"><td class="num">1\.</td>|<tr class="numbered"><td class="num">0.</td><td><a href="/">Introduction</a></td></tr><tr class="\1numbered"><td class="num">1.</td>|' {} \;
}

echo "Building: Foundations for Mathematical Systems Science..."
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
