#!/usr/bin/env bash
set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
REMOTE="$(cd "$REPO_DIR" && git remote get-url origin)"

echo "=== Building Verso ==="
cd "$REPO_DIR/docs/verso"
lake build
.lake/build/bin/proposal

echo "=== Assembling site ==="
tmp=$(mktemp -d)
cp "$REPO_DIR/site/index.html" "$tmp/"
touch "$tmp/.nojekyll"
cp -r "$REPO_DIR/site/handout" "$tmp/handout"
cp -r "$REPO_DIR/docs/verso/_out/html-multi" "$tmp/verso"

echo "=== Applying theme ==="
find "$tmp/verso" -name "index.html" -exec sh -c 'cp "$1" "$(dirname "$2")/"' _ "$REPO_DIR/docs/verso/halcyonic-theme.css" {} \;
find "$tmp/verso" -name "index.html" -exec sed -i '' 's|</body>|<link rel="stylesheet" href="halcyonic-theme.css"></body>|' {} \;
find "$tmp/verso" -name "index.html" -exec sed -i '' 's|Foundations for Mathematical Systems Science: Seven Traditions, One Theorem</h1>|Foundations for Mathematical Systems Science</h1>|' {} \;

echo "=== Deploying to gh-pages ==="
deploy=$(mktemp -d)
cd "$deploy"
git init -q
git remote add origin "$REMOTE"
git checkout --orphan gh-pages

cp -r "$tmp"/* .
cp "$tmp/.nojekyll" .
rm -rf "$tmp"

git add -A
git commit -m "deploy: update site $(date +%Y-%m-%d)" -q
git push origin gh-pages --force -q

rm -rf "$deploy"
cd "$REPO_DIR"

echo "=== Done. Site will be live at https://halcyonic.systems/systems-ontology/ ==="
