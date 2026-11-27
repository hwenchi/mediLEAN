#!/usr/bin/env bash
# Mutation testing for mediLEAN.
#
# Each mutation corrupts one premise in Theory/Premises.lean (in a scratch
# copy of the project), then runs `lake build`.
#   CAUGHT   = some layer failed to build; every failing layer is listed:
#              rules      a derived rule in Theory/Rules.lean became false
#              verdicts   a certified verdict no longer follows
#              models     a test model now violates the premise, or a
#                         rejected claim's countermodel stopped working
#              checklists a minimality test model violates the premise
#   SURVIVED = everything built: nothing in the suite depends on that premise.
#
# Test models are built independently of the verdicts, so a mutation that
# only breaks a verdict's proof is distinguishable from one a model catches.
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
  'needs: meningitis without headache           @@unsafe  @@s/(meningitis_needs : ∀ w, 12 ≤ ageMonths w → cond \.meningitis w → has \.stiffNeck w) ∨ has \.headache w/${1}/'
  'needs: meningitis age gate removed           @@unsafe  @@s/meningitis_needs : ∀ w, 12 ≤ ageMonths w → /meningitis_needs : ∀ w, /'
  'needs: meningitis age gate lowered to 3 mo   @@unsafe  @@s/meningitis_needs : ∀ w, 12 ≤ ageMonths w/meningitis_needs : ∀ w, 3 ≤ ageMonths w/'
  'red flag: infant fever only under 2 months   @@unsafe  @@s/(redflag_infant_fever : ∀ w, ageMonths w < )3/${1}2/'
  'red flag: infant fever under 4 months        @@cautious@@s/(redflag_infant_fever : ∀ w, ageMonths w < )3/${1}4/'
  'red flag: neck + headache also needs fever   @@unsafe  @@s/(redflag_meningitis_headache : ∀ w, )/${1}has .fever w → /'
  'threshold: fever from 39.0 not 38.0          @@unsafe  @@s/fever_of_temp : ∀ w, 380 ≤/fever_of_temp : ∀ w, 390 ≤/'
  'threshold: high fever from 41.0 not 40.0     @@unsafe  @@s/caution_highFever : ∀ w, 400 ≤/caution_highFever : ∀ w, 410 ≤/'
  'permit: self-care skips infant-infection check @@unsafe@@s/BoxNot compat \(cond \.seriousInfection\) w → Box compat/Box compat/'
  'permit: self-care skips high-fever check     @@unsafe  @@s/ Box compat \(fun v => tempTenths v < 400\) w →//'
  'needs: pneumonia also needs headache         @@unsafe  @@s/(pneumonia_needs : ∀ w, cond \.pneumonia w → )/${1}has .headache w ∧ /'
  'needs: pneumonia without fever at any age    @@cautious@@s/(pneumonia_needs : ∀ w, cond \.pneumonia w → )\(ageMonths w < 780 → has \.fever w\) ∧ /${1}/'
  'needs: pneumonia always needs fever          @@unsafe  @@s/\(ageMonths w < 780 → has \.fever w\)/has .fever w/'
  'needs: afebrile pneumonia only from 70       @@unsafe  @@s/\(ageMonths w < 780 → has \.fever w\)/(ageMonths w < 840 → has .fever w)/'
  'needs: cardiac never breathlessness alone    @@unsafe  @@s/ ∨ \(780 ≤ ageMonths w ∧ has \.breathless w\)//'
  'needs: atypical cardiac only from 70         @@unsafe  @@s/\(780 ≤ ageMonths w ∧ has \.breathless w\)/(840 ≤ ageMonths w ∧ has .breathless w)/'
  'red flag: older pneumonia also needs fever   @@unsafe  @@s/(redflag_pneumonia_older : ∀ w, 780 ≤ ageMonths w → )/${1}has .fever w → /'
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
  layers=""
  if ! lake build MediLean.Theory.Rules >/dev/null 2>&1; then
    layers="rules"
  else
    lake build MediLean.Claims.Verdicts   >/dev/null 2>&1 || layers="$layers verdicts"
    lake build MediLean.Claims.Models     >/dev/null 2>&1 || layers="$layers models"
    lake build MediLean.Claims.Checklists >/dev/null 2>&1 || layers="$layers checklists"
  fi
  layers="$(echo "$layers" | sed 's/^ *//')"
  if [ -n "$layers" ]; then
    printf '%-46s %-9s %s\n' "$name" "$kind" "CAUGHT  ($layers)"; caught=$((caught+1))
  else
    printf '%-46s %-9s %s\n' "$name" "$kind" "SURVIVED"; survived=$((survived+1))
  fi
done
cp Premises.orig "$PREM"
echo
echo "caught: $caught   survived: $survived   not applied: $bad"
