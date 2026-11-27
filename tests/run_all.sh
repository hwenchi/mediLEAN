#!/usr/bin/env bash
# Full mediLEAN check:
#   1. layering: Core imports only Core; Theory imports only Core/Theory;
#      no `axiom` anywhere, so Theory/Premises.lean is the only source of
#      assumptions.
#   2. build: verdicts, test models (each checked against every premise),
#      witnesses, rejected claims, checklist minimality.
#   3. axiom audit: no result depends on `sorry` or classical choice.
#      Lean's standard `propext` / `Quot.sound` are allowed.
set -eu
cd "$(dirname "$0")/.."

echo "== layering"
bad=0
if grep -n "^import MediLean\.\(Theory\|Claims\)" MediLean/Core/*.lean; then
  echo "FAIL: Core must not import Theory or Claims"; bad=1; fi
if grep -n "^import MediLean\.Claims" MediLean/Theory/*.lean; then
  echo "FAIL: Theory must not import Claims"; bad=1; fi
if grep -rnE "^\s*axiom\b" MediLean; then
  echo "FAIL: no axioms allowed; premises belong in Theory/Premises.lean"; bad=1; fi
if [ "$(grep -rl "^structure TriageModel" MediLean)" != "MediLean/Theory/Premises.lean" ]; then
  echo "FAIL: TriageModel (the premises) must live only in Theory/Premises.lean"; bad=1; fi
[ $bad -eq 0 ] || exit 1
echo "OK: Core <- Theory <- Claims; premises only in Theory/Premises.lean"

echo "== build"
lake build 2>&1 | tail -1

echo "== axiom audit"
NAMES=$(grep -rhoE '^(def|theorem) (c[0-9]+[a-z_0-9]*|caution_under_doubt)' MediLean | awk '{print $2}')
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
{ echo "import MediLean"; echo "open MediLean"; for n in $NAMES; do echo "#print axioms $n"; done; } > "$TMP/Axioms.lean"
OUT="$(lake env lean "$TMP/Axioms.lean")"
echo "$OUT" | sed 's/^/  /'
if echo "$OUT" | grep -qE 'sorryAx|Classical.choice'; then
  echo "FAIL: forbidden axiom found"; exit 1
fi
echo "OK: $(echo "$NAMES" | wc -l | tr -d ' ') results audited, no sorry, no choice"
