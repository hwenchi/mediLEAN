#!/usr/bin/env bash
# Mutation testing for mediLEAN.
#
# Each mutation corrupts one premise in Theory/Premises.lean (in a scratch
# copy of the project), then runs `lake build`.
#   CAUGHT   = build failed: a verdict, test model, or test noticed.
#   SURVIVED = build passed: nothing in the suite depends on that premise.
#
# kind: unsafe    = makes the system refer LESS (the dangerous direction)
#       cautious  = makes the system refer MORE
#       benign    = expected to change nothing a claim depends on
#
# Usage: tests/mutation_test.sh   (from anywhere)
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp -R "$ROOT/." "$WORK/"
PREM="MediLean/Theory/Premises.lean"
cp "$WORK/$PREM" "$WORK/Premises.orig"

# name @@ kind @@ perl substitution (applied once, whole file as one string)
MUTATIONS=(
  'caution: cardiac only needs urgent care      @@unsafe  @@s/(caution_cardiac : .*?SeeksAtLeast seeks )\.emergency/${1}.urgentCare/'
  'caution: meningitis only needs urgent care   @@unsafe  @@s/(caution_meningitis : .*?SeeksAtLeast seeks )\.emergency/${1}.urgentCare/'
  'caution: pneumonia only needs a doctor       @@unsafe  @@s/(caution_pneumonia : .*?SeeksAtLeast seeks )\.urgentCare/${1}.seeDoctor/'
  'caution: pneumonia needs emergency           @@cautious@@s/(caution_pneumonia : .*?SeeksAtLeast seeks )\.urgentCare/${1}.emergency/'
  'red flag: cardiac also needs headache        @@unsafe  @@s/(redflag_cardiac : ∀ w, has \.chestPain w → has \.armPain w → )/${1}has .headache w → /'
  'red flag: meningitis also needs headache     @@unsafe  @@s/(redflag_meningitis : ∀ w, has \.fever w → has \.stiffNeck w → )/${1}has .headache w → /'
  'red flag: pneumonia also needs chest pain    @@unsafe  @@s/(redflag_pneumonia : ∀ w, has \.fever w → has \.cough w → has \.breathless w → )/${1}has .chestPain w → /'
  'red flag: viral ignores sore throat          @@benign  @@s/ ∨ has \.soreThroat w → Diamond compat \(cond \.viral\)/ → Diamond compat (cond .viral)/'
  'needs: cardiac without arm pain              @@unsafe  @@s/(cardiac_needs : ∀ w, cond \.cardiac w → has \.chestPain w) ∨ has \.armPain w/${1}/'
  'needs: meningitis without headache           @@unsafe  @@s/(meningitis_needs : ∀ w, cond \.meningitis w → has \.stiffNeck w) ∨ has \.headache w/${1}/'
  'needs: pneumonia also needs headache         @@unsafe  @@s/(pneumonia_needs : ∀ w, cond \.pneumonia w → has \.fever w ∧ )/${1}has .headache w ∧ /'
  'needs: pneumonia without fever               @@cautious@@s/(pneumonia_needs : ∀ w, cond \.pneumonia w → )has \.fever w ∧ /${1}/'
  'needs: viral without headache                @@benign  @@s/(viral_needs : .*?has \.soreThroat w) ∨ has \.headache w/${1}/'
  'permit: urgent care skips meningitis check   @@unsafe  @@s/(permit_urgentCare : ∀ w, BoxNot compat \(cond \.cardiac\) w → )BoxNot compat \(cond \.meningitis\) w → /${1}/'
  'permit: self-care skips pneumonia check      @@unsafe  @@s/(permit_selfCare : .*?BoxNot compat \(cond \.meningitis\) w → )BoxNot compat \(cond \.pneumonia\) w → /${1}/'
  'permit: self-care also needs viral ruled out @@cautious@@s/(permit_selfCare : ∀ w, )/${1}BoxNot compat (cond .viral) w → /'
)

cd "$WORK" || exit 1
echo "Baseline build..."
if ! lake build >/dev/null 2>&1; then echo "Baseline build FAILS; aborting."; exit 1; fi

caught=0; survived=0; bad=0
printf '\n%-46s %-9s %s\n' "MUTATION" "KIND" "RESULT"
for m in "${MUTATIONS[@]}"; do
  name="$(echo "${m%%@@*}" | sed 's/ *$//')"
  rest="${m#*@@}"; kind="$(echo "${rest%%@@*}" | sed 's/ *$//')"; expr="${rest#*@@}"
  cp Premises.orig "$PREM"
  perl -0777 -i -pe "$expr" "$PREM"
  if cmp -s Premises.orig "$PREM"; then
    printf '%-46s %-9s %s\n' "$name" "$kind" "NOT APPLIED (pattern missing)"; bad=$((bad+1)); continue
  fi
  out="$(lake build 2>&1)"
  if [ $? -ne 0 ]; then
    where="$(echo "$out" | grep -o 'error: MediLean/[A-Za-z/]*\.lean:[0-9]*' | head -1 | sed 's/error: MediLean\///')"
    printf '%-46s %-9s %s\n' "$name" "$kind" "CAUGHT  ($where)"; caught=$((caught+1))
  else
    printf '%-46s %-9s %s\n' "$name" "$kind" "SURVIVED"; survived=$((survived+1))
  fi
done
cp Premises.orig "$PREM"
echo
echo "caught: $caught   survived: $survived   not applied: $bad"
