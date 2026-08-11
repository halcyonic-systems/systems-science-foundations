#!/usr/bin/env bash
# Cold verification of the K ≅ 2 headline claims (comparator pattern, own stack).
#
# Elaborates Systems/Challenge.lean — the trusted statement file — and verifies:
#   1. every restated theorem elaborates against the library proof
#      (statement equality, kernel-checked), and
#   2. no theorem depends on any axiom beyond Lean's standard three
#      (propext, Classical.choice, Quot.sound) — no sorryAx, no custom axioms.
#
# A cold reader needs only Systems/Challenge.lean + the definitions it names.
set -euo pipefail
cd "$(dirname "$0")/.."

EXPECTED=20   # theorems audited at the bottom of Challenge.lean

out=$(lake env lean Systems/Challenge.lean 2>&1) || {
  echo "$out"
  echo "FAIL: Challenge.lean did not elaborate (statement mismatch or build error)"
  exit 1
}

audited=$(grep -c "^'Challenge\." <<<"$out" || true)
if [ "$audited" -ne "$EXPECTED" ]; then
  echo "$out"
  echo "FAIL: expected $EXPECTED axiom-audit lines, saw $audited"
  exit 1
fi

bad=$(grep "^'Challenge\." <<<"$out" \
  | grep -v "does not depend on any axioms" \
  | sed "s/.*depends on axioms: \[//; s/\]//" \
  | tr ', ' '\n' | sed '/^$/d' | sort -u \
  | grep -v -E "^(propext|Classical\.choice|Quot\.sound)$" || true)
if [ -n "$bad" ]; then
  echo "$out"
  echo "FAIL: non-standard axioms detected: $bad"
  exit 1
fi

echo "$out"
echo "OK: $audited theorems, statements match, standard axioms only"
