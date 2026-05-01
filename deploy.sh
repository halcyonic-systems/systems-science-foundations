#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

echo "=== Building Verso ==="
cd docs/verso
lake build
.lake/build/bin/proposal
cd ../..

echo "=== Assembling site ==="
tmp=$(mktemp -d)
cp site/index.html "$tmp/"
cp site/.nojekyll "$tmp/" 2>/dev/null || touch "$tmp/.nojekyll"
cp -r site/handout "$tmp/handout"
cp -r docs/verso/_out/html-multi "$tmp/verso"

echo "=== Deploying to gh-pages ==="
git stash --include-untracked -q 2>/dev/null || true
git checkout gh-pages 2>/dev/null || git checkout --orphan gh-pages

git rm -rf . -q 2>/dev/null || true
cp -r "$tmp"/* .
cp "$tmp/.nojekyll" .
rm -rf "$tmp"

git add -A
git commit -m "deploy: update site $(date +%Y-%m-%d)" --allow-empty
git push origin gh-pages --force-with-lease

git checkout main -q
git stash pop -q 2>/dev/null || true

echo "=== Done. Site will be live at https://halcyonic.systems/systems-ontology/ ==="
