#!/usr/bin/env bash
# axiom-profile.sh — foundational-purity profile for SSF headline theorems.
#
# Runs Lean's `#print axioms` on one showcase theorem per Mobus principle and
# emits a markdown table classifying each as:
#   constructive  — depends on no axioms
#   choice-free   — propext / Quot.sound only (still no Classical.choice)
#   classical     — pulls in Classical.choice
#   UNSOUND       — pulls in sorryAx  (should never happen; zero-sorry invariant)
#
# This is the rigorous, machine-checked version of the "proof vector" idea in
# arXiv:2504.00063 — the difference being these dependencies are *computed by
# the kernel*, not hand-asserted. Note: SSF's 8 systems "axioms" are structures/
# defs, not Lean `axiom`s, so they do NOT appear here. The systems-level
# dependency vector lives in docs/paper/dependency-dag.mmd instead.
#
# Usage:  scripts/axiom-profile.sh            # print markdown table
#         scripts/axiom-profile.sh --raw      # raw `#print axioms` output
set -euo pipefail
cd "$(dirname "$0")/.."

# principle# | label | fully-qualified headline theorem (one showcase result per principle)
THEOREMS=(
  "1|Systemness|Systems.ConcreteSystem.composition_organized"
  "2|Hierarchy|Systems.ancestor_trans"
  "3|Networks|Systems.FlowNetwork.toRelation_irrefl"
  "4|Dynamics|Systems.coupled_equilibrium_iff_fixed"
  "5|Complexity|Systems.sameKind_equivalence"
  "6|Evolution|Systems.evolvable_but_not_improvable"
  "7|Information|Systems.entropy_le_log_card"
  "8|Governance|Systems.Homeostat.target_is_equilibrium"
  "9|Internal Models|Systems.AnticipatoryModel.tracks"
  "10|Self-Models|Systems.FastSelfModel.accurate_forces_periodic"
  "11|Understandability|Systems.no_trivial_understanding"
  "12|Improvability|Systems.goal_is_external"
)

SCRATCH="$(mktemp -t axiomsweep.XXXXXX).lean"
trap 'rm -f "$SCRATCH" "${SCRATCH%.lean}.olean" 2>/dev/null || true' EXIT
{
  echo "import Systems"
  for entry in "${THEOREMS[@]}"; do
    echo "#print axioms ${entry##*|}"
  done
} > "$SCRATCH"

RAW="$(lake env lean "$SCRATCH" 2>&1)"

if [[ "${1:-}" == "--raw" ]]; then
  echo "$RAW"; exit 0
fi

classify() {  # $1 = axiom list line for a theorem
  if   grep -q "sorryAx"          <<<"$1"; then echo "🔴 UNSOUND (sorryAx)";
  elif grep -q "Classical.choice" <<<"$1"; then echo "classical";
  elif grep -q "does not depend"  <<<"$1"; then echo "constructive";
  else echo "choice-free"; fi
}

echo "| # | Principle | Headline theorem | Foundational profile |"
echo "|---|-----------|------------------|----------------------|"
for entry in "${THEOREMS[@]}"; do
  IFS='|' read -r num label thm <<<"$entry"
  line="$(grep -F "'$thm'" <<<"$RAW" || echo "$thm MISSING")"
  echo "| $num | $label | \`${thm#Systems.}\` | $(classify "$line") |"
done
