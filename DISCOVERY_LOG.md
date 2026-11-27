# mediLEAN discovery log

Premise source for this phase is the LLM's own knowledge, which nobody has
reviewed. Use it for exploration only.

## Layout

```
MediLean/
  Core/                FIXED: never changes as the medical knowledge grows
    Modal.lean           Box, Diamond, BoxNot, K, monotonicity, duality
    Frame.lean           frames, modal vocabulary, the laws T, 4 and D
    Urgency.lean         the four-level care scale
  Theory/              THE PREMISES we are distilling
    Vocabulary.lean      symptoms and conditions
    Premises.lean        ★ every assumption, as a named field of TriageModel
    Rules.lean           consequences of the premises (assumes nothing new)
  Claims/              TESTS of the theory
    Verdicts.lean        certified claims C1–C16, each proved from named premises
    Finite.lean          infrastructure: finite test models checked by `decide`
    Models.lean          test models and rejected claims (built without the verdicts)
    Witnesses.lean       every verdict's hypothesis holds in some test model
    Checklists.lean      checklist-minimality tests
```

**To review the theory, read `Theory/Premises.lean`.** It is the only place
anything is assumed, and `tests/run_all.sh` enforces that:
- Core imports only Core.
- Theory never imports Claims.
- No `axiom` declaration exists anywhere.
- `TriageModel` is defined only in `Premises.lean`.

```bash
tests/run_all.sh        # layering + build + axiom audit
tests/mutation_test.sh  # corrupt premises 25 ways; report every layer that notices
```

## Premises (in `Theory/Premises.lean`)

| Group | Premise | Says |
|-------|---------|------|
| Patient facts | `ageMonths`, `tempTenths`, `diabetic`, `female`, `coughDays` | age in months; highest measured temperature (tenths of °C); diabetes; sex; days of cough (step 11) |
| Measurements | `fever_of_temp` | a reading of 38.0 °C or more is a fever |
| | `cough_of_days` | a cough lasting a day or more is a cough (step 11) |
| Red flags | `redflag_cardiac` | chest pain + arm pain ⇒ cardiac can't be ruled out |
| | `redflag_meningitis` | fever + stiff neck ⇒ meningitis can't be ruled out |
| | `redflag_meningitis_headache` | stiff neck + headache ⇒ meningitis can't be ruled out, even with no fever (step 8) |
| | `redflag_meningitis_confusion` | fever + new confusion ⇒ meningitis can't be ruled out (step 10) |
| | `redflag_meningitis_rash` | non-blanching rash ⇒ meningitis (incl. meningococcal septicaemia) can't be ruled out, no fever needed (step 12) |
| | `redflag_pneumonia` | fever + cough + breathlessness ⇒ pneumonia can't be ruled out |
| | `redflag_pneumonia_older` | **from 65:** cough + breathlessness ⇒ pneumonia can't be ruled out, no fever needed (step 9) |
| | `redflag_viral` | fever, cough or sore throat ⇒ viral can't be ruled out |
| | `redflag_infant_fever` | infant under 3 months + fever ⇒ serious infection can't be ruled out (step 8) |
| Necessary symptoms | `cardiac_needs` | cardiac ⇒ chest pain ∨ arm pain ∨ (**65+, diabetic or female:** breathlessness) (steps 9, 10) |
| | `meningitis_needs` | **from age 1:** meningitis ⇒ stiff neck ∨ headache ∨ confusion ∨ non-blanching rash (step 8: age-gated; step 10: confusion; step 12: rash) |
| | `pneumonia_needs` | pneumonia ⇒ (**under 65:** fever) ∧ (cough ∨ breathlessness ∨ **65+:** confusion) (steps 9, 10) |
| | `viral_needs` | viral ⇒ fever ∨ cough ∨ sore throat ∨ headache |
| | `seriousInfection_needs` | serious infection ⇒ under 3 months ∧ fever (step 8) |
| Caution | `caution_cardiac` | cardiac possible ⇒ emergency care obligatory |
| | `caution_meningitis` | meningitis possible ⇒ emergency care obligatory |
| | `caution_pneumonia` | pneumonia possible ⇒ at least urgent care obligatory |
| | `caution_seriousInfection` | serious infection possible ⇒ emergency care obligatory (step 8) |
| | `caution_highFever` | reading of 40.0 °C or more ⇒ at least urgent care obligatory (step 8) |
| | `caution_persistentCough` | cough of 21 days or more ⇒ at least see a doctor (step 11) |
| | `caution_newConfusion` | new confusion possible ⇒ emergency care obligatory, whatever the cause (step 12) |
| Proportionality | `permit_selfCare` | cardiac, meningitis, pneumonia, serious infection ruled out, no reading ≥ 40.0 °C possible, no cough of 21+ days possible, and no new confusion possible ⇒ self-care permitted |
| | `permit_seeDoctor` | same, but a persistent cough is fine ⇒ seeing a doctor permitted (step 11) |
| | `permit_urgentCare` | cardiac, meningitis, serious infection ruled out, no new confusion possible ⇒ urgent care permitted |
| Pathways | `one_pathway` | one care pathway at a time |

Frame laws (in Core): T for knowledge, **4 for knowledge (`compat_trans`)**,
T and 4 for time, and D for obligation.

## Claims

| # | Claim | Status | Premises used |
|---|-------|--------|---------------|
| C1 | chest + arm ⇒ emergency care obligatory | proved | redflag_cardiac, caution_cardiac |
| C2 | chest + arm ⇒ emergency care permitted | proved | C1 + law D |
| C3 | fever + stiff neck ⇒ emergency care obligatory | proved | redflag_meningitis, caution_meningitis |
| C4 | chest + arm ⇒ cardiac not ruled out | proved | redflag_cardiac |
| C6 | **age 1–64**; no chest, arm, stiff neck, headache, **confusion**, fever or **breathlessness** ⇒ self-care permitted | proved (7 questions since step 10) | the *_needs premises, fever_of_temp, permit_selfCare |
| C6c | **low-risk shortcut**: man aged 1–64 without diabetes; C6 minus the breathlessness question ⇒ self-care permitted | proved (step 10) | cardiac_needs, low-risk form |
| C6b | age ≥ 1 year (any adult age, any sex), no reading ≥ 40.0 °C; fever, but no chest, arm, stiff neck, headache, confusion, cough or breathlessness ⇒ self-care permitted | proved | same, ruling out pneumonia the other way |
| C8 | chest + arm ⇒ self-care forbidden | proved | C1's premises + one_pathway |
| C9 | red flags eventually ⇒ emergency care eventually obligatory | proved | C1 lifted through `Eventually` |
| C10 | self-care now, emergency care if chest + arm pain later | proved | C6 ∧ C9 |
| C11 | **man aged 1–64 without diabetes**; fever + cough + breathless, with cardiac and meningitis flags absent ⇒ urgent care | proved | 7 premises |
| C14 | chest pain confirmed, **unsure** about arm pain ⇒ emergency care obligatory | proved | redflag_cardiac, caution_cardiac, **law 4** |
| C16 | fever and stiff neck might be present **together** ⇒ emergency care obligatory | proved | redflag_meningitis, caution_meningitis, law 4 |
| C5 | fever alone ⇒ emergency care obligatory | rejected, correctly | — |
| C5′ | fever alone ⇒ self-care permitted | rejected, correctly ("ask more") | — |
| C7 | cough alone ⇒ self-care permitted | rejected, correctly | — |
| C12 | pneumonia pattern ⇒ emergency care obligatory | rejected, correctly (no over-referral) | — |
| C13 | C11's checklist without "no stiff neck" ⇒ urgent care permitted | rejected, correctly | — |
| C15 | fever *might* be present, stiff neck *might* be present (separately) ⇒ emergency care obligatory | rejected, correctly: doubts must be joint | — |
| C17 | infant under 3 months with a fever ⇒ emergency care obligatory | proved (step 8) | redflag_infant_fever, caution_seriousInfection |
| C18 | measured **38.0 °C** (the boundary) + stiff neck ⇒ emergency care obligatory | proved (step 8) | fever_of_temp, redflag_meningitis, caution_meningitis |
| C19 | measured **40.0 °C** (the boundary) ⇒ at least urgent care, self-care forbidden | proved (step 8) | caution_highFever, one_pathway |
| C22 | stiff neck + headache, no fever needed ⇒ emergency care obligatory | proved (step 8) | redflag_meningitis_headache, caution_meningitis |
| C23 | 65+ with cough + breathlessness, no fever needed ⇒ at least urgent care, self-care forbidden | proved (step 9) | redflag_pneumonia_older, caution_pneumonia |
| C24 | C11 for a 70-year-old ⇒ urgent care permitted | rejected, correctly: the breathlessness could be cardiac | — |
| C25 | age ≤ **65** and no fever ⇒ pneumonia ruled out (as part of C6) | rejected, correctly: pins the afebrile-pneumonia age | — |
| C26 | age ≤ **65** and no chest/arm pain ⇒ cardiac ruled out (as part of C6) | rejected, correctly: pins the atypical-cardiac age | — |
| C27 | fever + new confusion ⇒ emergency care obligatory | proved (step 10) | redflag_meningitis_confusion, caution_meningitis |
| C28 | the low-risk shortcut (C6c) for a **woman** ⇒ self-care permitted | rejected, correctly: her breathlessness could be cardiac | — |
| C29 | the low-risk shortcut for a **diabetic** man ⇒ self-care permitted | rejected, correctly | — |
| C30 | C11 for a **woman** ⇒ urgent care permitted | rejected, correctly | — |
| C31 | age 1–64, cough of **21 days** (the boundary), no red flags ⇒ at least see a doctor, seeing a doctor permitted, self-care forbidden | proved (step 11): **the "see a doctor" level is finally used** | caution_persistentCough, permit_seeDoctor |
| C32 | self-care now; if the cough reaches 3 weeks, see a doctor then | proved (step 11) | C6, caution_persistentCough, `Eventually` |
| C33 | a cough of **20 days** obliges a doctor's visit | rejected, correctly: pins the threshold at 21 days | — |
| C34 | a persistent cough alone obliges urgent care | rejected, correctly | — |
| C35 | chest pain that is **tender to the touch**, every other red flag absent ⇒ self-care permitted | rejected, correctly: a heart attack can present this way | — |
| C36 | new confusion **possible** ⇒ emergency care obligatory | proved | `caution_newConfusion` (step 12) |
| C37 | non-blanching rash, no fever needed ⇒ emergency care obligatory | proved | `redflag_meningitis_rash` (step 12) |
| C38 | older adult, no fever, cough or breathlessness ⇒ pneumonia ruled out | rejected, correctly: pneumonia can show as confusion alone | — |
| C20 | C6's checklist **without confirming age** ⇒ self-care permitted | rejected, correctly: infant meningitis can be silent | — |
| C20b | same, with age ≥ **11 months** confirmed | rejected, correctly: pins the age gate at 12 months | — |
| C21 | age ≤ **3 months** + fever ⇒ emergency care obligatory | rejected, correctly: pins the infant rule at "under 3 months" | — |
| — | `caution_under_doubt`: a patient who is actually fine is still referred | proved | C14 in a 2-scenario model |
| — | C6 and C11 checklist minimality (13 tests: C6 now has 8 questions, C11 has 5) | proved | — |

Every verdict's hypothesis holds in some test model, so none is true only
because nothing satisfies it. Every test model is checked by `decide`
against every premise.

## Test results (step 12)

- **Layering:** OK.
- **Axiom audit:** 46 results. None uses `sorry` or classical choice.
- **Mutation testing:** 43 of 45 caught. Both survivors were marked benign in
  advance. The harness now reports *every* layer that catches a mutation:

| Mutation | Kind | Caught by |
|----------|------|-----------|
| caution levels lowered (cardiac, meningitis, pneumonia) | unsafe | verdicts |
| caution: pneumonia raised to emergency | cautious | verdicts, models, checklists |
| red flags narrowed (cardiac, meningitis, pneumonia, neck + headache) | unsafe | verdicts |
| red flag: infant fever only under 2 months | unsafe | verdicts (C17) |
| red flag: infant fever under 4 months | cautious | verdicts, models (C21), checklists |
| threshold: fever from 39.0, high fever from 41.0 | unsafe | verdicts (C18, C19 at the boundary) |
| needs: cardiac without arm pain; meningitis without headache | unsafe | **checklists only** |
| needs: meningitis age gate removed | unsafe | models (C20), checklists |
| needs: meningitis age gate lowered to 3 months | unsafe | models (**C20b**, the 11-month boundary), checklists |
| needs: pneumonia also needs headache | unsafe | models, checklists |
| needs: pneumonia without fever at any age | cautious | rules (`ruledOut_pneumonia_noFever` becomes false) |
| needs: pneumonia always needs fever; afebrile only from 70 | unsafe | models (C25 at 65), checklists |
| needs: cardiac never breathlessness alone; atypical only from 70 | unsafe | models (C26 at 65), checklists |
| red flag: older pneumonia also needs fever | unsafe | verdicts (C23) |
| needs: atypical cardiac not in women / not in diabetics | unsafe | models (C28, C29), checklists |
| needs: meningitis without confusion | unsafe | models, checklists |
| red flag: fever + confusion also needs a stiff neck | unsafe | verdicts (C27) |
| **exception: tender chest pain is not cardiac** | unsafe | **models** (`tenderMI`, the clinical counterexample), checklists |
| threshold: persistent cough from 28 days | unsafe | verdicts (C31 at 21 days) |
| threshold: persistent cough from 14 days | cautious | verdicts, models (C33 at 20 days), checklists |
| permit: self-care skips persistent-cough check; see-doctor skips meningitis check | unsafe | verdicts, models, checklists |
| needs: older pneumonia never confusion-only | unsafe | models (`olderConfusionPneumo`, C38), checklists. **Survived until step 12** |
| red flag: rash also needs fever; caution: confusion only urgent care | unsafe | verdicts (C37, C36) |
| needs: meningitis without rash | unsafe | models (`rashOnly`), checklists |
| permit: self-care / urgent care skips confusion check | unsafe | verdicts, models (`confusionNoCause`), checklists |
| permit: any check skipped (meningitis, pneumonia, infant infection, high fever) | unsafe | verdicts, models, checklists |
| permit: self-care also needs viral ruled out | cautious | verdicts, checklists |
| red flag: viral ignores sore throat; needs: viral without headache | benign | survived |

## Observations, by step

**Steps 1–2: single chains.** Each early proof was one chain: confirmed
fact, then red flag, then caution. Testing whether absences license
self-care showed that **absence must be confirmed**: not mentioning a
symptom is not the same as confirming it is absent (C7). Fever alone gives
no verdict (C5, C5′), so "ask more" is a real outcome.

**Step 3: necessity premises carry the most risk.** Red-flag premises can only
make the system *more* cautious. A wrong "needs" premise makes it *less*
cautious, because that is how danger is ruled out. Positive claims can't
catch a weakened "needs" premise, since every claim only gets easier to
prove. Only tests that encode an independent expectation catch it: the
checklist-minimality models.

**Step 4: urgency is ordered.** A yes/no "dangerous" flag over-referred
everything. Grading conditions by care level gave the first middle verdict
(C11, urgent care) and showed the pneumonia pattern doesn't need the ER
(C12). Pneumonia's necessary symptoms turned out to need an "and of ors"
shape: fever **and** (cough **or** breathlessness). Otherwise no cough could
ever qualify for self-care.

**Step 5 (since reverted): tables.** I moved the medical content into
per-condition tables read by generic rules. That bought a decision
procedure for checklists, with a constructive proof that it is sound and
complete, plus generated checklists and a proof that "see a doctor" is
unused (no condition sits at that level). It cost readability: the theory
read as rules plus lookups, not as medical premises, and proofs became
lookups. It also only covers one fragment of medicine, which real triage
leaves quickly: patient context, thresholds, time, exceptions, scores.

**Step 6: uncertainty.**
- **Caution under doubt needs law 4.** "Chest pain confirmed, unsure about
  arm pain" (C14) needs `compat_trans`: the red flag fires in a world the user
  can't exclude, and transitivity carries the danger back.
- **The cost of caution is now a theorem** (`caution_under_doubt`): a patient
  who is actually fine is still sent to the ER.
- **Doubts must be joint.** "Fever might be present" plus "a stiff neck might
  be present" does not mean both might be present together (C15 versus C16).
  The interface has to ask jointly.

**Step 7: back to readable premises, and separated layers.** Each premise is
a named field of `TriageModel` with an English comment. Each claim is proved
directly from named premises, and its comment lists which ones. The proofs
now show their reasoning: ruling out a condition, choosing *which* way to
rule out pneumonia (C6 versus C6b), lifting through time, and carrying danger
back through doubt.

Test models replaced the tables as the cheap testing tool. Each test model
has finitely many worlds, so every premise and every claim about a model is
a finite check that `decide` settles. Building a model *is* checking it
against every premise.

**A testing lesson from step 7: proofs that depend on a premise's exact
shape give false confidence.** At first, unsafe "needs" mutations were
caught only because the derived proofs pattern-matched on the premise's
exact shape. A *stronger* premise still implies the lemma, so those catches
were accidental. After making the proofs robust to the premise's shape, the
same mutations are caught by test models, which is the real guard. For
mutation testing to mean anything, proofs should depend on what a premise
says, not on how it is written.

**Step 8: patient context and thresholds.** These are premises a table
couldn't express.

- **An age-gated premise fixed a known error.** "Meningitis needs a stiff neck
  or a headache" was wrong for infants. It now applies only from age one. As a
  result, the self-care checklist needs one more question, *"is the patient
  at least one year old?"* (C20). The theory found that question; I didn't add
  it by hand.
- **A new dangerous condition forced every permit premise to change.** Adding
  "serious infection in febrile infants" and "40.0 °C or more" as caution
  premises meant both permit premises had to exclude them. Otherwise, for some
  patient, caution would demand urgent care while proportionality permits
  self-care. That patient would have no model, and every claim about them
  would be vacuously true. **Invariant: every caution premise must be blocked
  by every lower permit premise.** The mutation suite confirms that test
  models catch any permit premise that skips a check.
- **Every threshold needs a test exactly at its boundary.** C18 tests 38.0 °C,
  C19 tests 40.0 °C, and C21 tests 3 months. Lowering the meningitis age gate
  from 12 to 3 months *survived* every test until I added C20b at 11 months.
  A threshold with no test at its boundary isn't pinned.
- **Exploring a boundary found a medical gap.** Below 38.0 °C, a stiff neck
  certified nothing, even with a headache. But fever can be absent early in
  meningitis, or masked by paracetamol. I added "stiff neck + headache ⇒
  meningitis can't be ruled out" (C22).
- **Measurements and symptoms link through one premise.** `fever_of_temp` (a
  reading of 38.0 °C or more is a fever) means that ruling out fever also rules
  out any high reading. So C6 needs no temperature question, while C6b (fever
  present) does.
- **Testing:** the harness now attributes each catch to rules, verdicts, test
  models or checklists. Test models build without the verdicts, so a catch
  that only came from a broken proof can be told apart from a catch by a model.
  The ruling-out proofs use `grind`, so they depend on what a premise says,
  not on its exact form.

**Step 9: atypical presentations in older adults.** With age available,
two premises marked CRUDE became more accurate. From 65, pneumonia can come
without a fever, and a cardiac event can be breathlessness alone. A new red
flag covers cough plus breathlessness without fever in older adults (C23).

- **The checklists split by age, and the theory found the split.** C6's
  short self-care checklist (no fever) now holds only for ages 1 to 64. From
  65, "no fever" no longer rules out pneumonia, and "no chest or arm pain"
  no longer rules out a cardiac event. C6b (ask about cough and
  breathlessness instead) works at every adult age, because ruling out
  breathlessness also closes the atypical cardiac route. Patients 65 and over
  need the longer checklist.
- **A middle verdict doesn't transfer to older patients.** C11 (fever, cough
  and breathlessness ⇒ urgent care) is now only for under-65s. For a
  70-year-old the breathlessness could itself be cardiac, so urgent care
  can't be certified (C24).
- **The new age thresholds are pinned at their boundaries** by C25 and C26,
  which test exactly 65. Every age-gate mutation (removed, or moved to 70) is
  caught by test models, not by proofs breaking.
- **The axiom audit caught a regression.** `grind` proved the cardiac
  ruling-out rule using classical choice, because of an age comparison
  inside a disjunction. Replacing it with `simp_all` then `omega` kept the
  proof robust to the premise's form and constructive again.

**Step 10: women, diabetics, and confusion.** Two new patient facts
(diabetes, sex) and one new symptom (acute confusion).

- **Widening a "needs" premise moves the cost onto the group it widens
  for.** A cardiac event can be breathlessness alone in women and
  diabetics too, not only from 65. So for them, "no chest or arm pain" no
  longer rules a cardiac event out, and the theory now certifies less for
  them:
  - The six-question self-care shortcut (C6c) holds only for men without
    diabetes (C28, C29).
  - C11's urgent-care verdict no longer applies to women (C30), because
    their breathlessness could itself be cardiac. They get "not certified"
    instead, which means more referral.

  This is the right direction for safety, but it means over-referral falls
  disproportionately on women, diabetics and older adults. The theory makes
  that trade-off explicit, which a fluent LLM answer never would.
- **Confusion joined the meningitis signs.** It is the third sign of the
  classic triad. A new red flag says fever plus confusion means emergency
  care (C27). The general self-care checklist (C6) now has seven questions,
  and every one is proved necessary.
- **Mutation testing found an idle premise, as predicted.** "From 65,
  pneumonia can show as confusion alone" never changes any verdict. Ruling
  out meningitis already requires confusion to be absent, and every permit
  premise that needs pneumonia ruled out also needs meningitis ruled out.
  Removing the clause survives every test. The premise is medically true,
  but under the current permit premises it is redundant. It would matter
  only if some care level allowed meningitis but not pneumonia, and none
  does.
- **The test script itself had a bug.** The audit's name pattern didn't allow
  capital letters (`c6c_selfcare_lowRisk`), so Lean failed on an unknown
  name and the script exited silently mid-audit. Failures are now loud, and
  `pipefail` makes a failed build stop the script.

**Step 11: duration, and a premise that lowers concern.**

- **"See a doctor" is finally used.** Cough duration became a patient fact,
  and a cough lasting 3 weeks or more needs a doctor's assessment (C31).
  This needed:
  - a new permit premise for that level (`permit_seeDoctor`);
  - one more block on `permit_selfCare`, by the caution/permit invariant from
    step 8;
  - one more self-care question when a cough is present ("has it lasted less
    than 3 weeks?").
  "See a doctor" was proved useless in the step-5 table fragment. Now it is
  certified for its own case and pinned at its boundary: 20 days isn't enough
  (C33), and a persistent cough alone doesn't need urgent care (C34).
- **The temporal modality does real clinical work.** C32 is real
  safety-netting advice: "self-care is fine for this cough now; if it reaches
  3 weeks, see a doctor then."
- **The theory can't safely contain a premise that lowers concern.** In this
  logic, lowering concern means letting something *rule a condition out*. That
  is strengthening a "needs" premise, which is exactly the unsafe direction.
  The tempting rule "chest pain that hurts more when you press on the chest
  wall isn't cardiac" lowers the likelihood but doesn't exclude a heart attack.
  So instead of adding it, I encoded the clinical counterexample as a test
  model (`tenderMI`: a heart attack with a tender chest wall). Any premise
  that let tenderness rule out a cardiac event would make that model fail to
  build, and the mutation suite confirms it does. C35 records the rejection.
  **Test models can encode known clinical counterexamples, which makes them a
  guard against plausible-sounding but unsafe premises.** Evidence that
  *lowers probability* without excluding a condition can't be expressed in a
  qualitative logic. That is the calibration problem again.

**Step 12: a rash, confusion as a symptom-level caution, and clinical counterexamples.**

- **A non-blanching rash is a red flag on its own** (C37): early meningococcal
  disease can show a rash before any fever. Adding it forced
  `meningitis_needs` wider (a rash counts as a sign), so ruling out
  meningitis now takes one more absence. The self-care checklist grew to
  eight questions (C6) and the urgent-care one to five (C11), and minimality
  shows the rash question is load-bearing in both. **Adding a red flag for a
  condition forces its "needs" premise to grow too**, or a patient with
  only the new sign would have no model (and every claim about them would
  hold vacuously).
- **Some cautions belong on a symptom, not a condition.** Before this step
  the theory obliged *nothing* for an acutely confused 30-year-old without
  fever: confusion only mattered as a sign of meningitis or pneumonia. Its
  real causes (stroke, sepsis, low blood sugar) are outside the vocabulary.
  `caution_newConfusion` acts on the symptom directly, and every permit
  premise now blocks it (the step-8 invariant). The model `confusionNoCause`
  catches a permit premise that forgets that block. **A vocabulary of
  conditions will always be incomplete, so the safety of the whole theory
  can't rest on naming every cause.**
- **A library of clinical counterexamples.** `Models.lean` now has a
  section of real, easy-to-miss presentations, written from clinical
  knowledge and not from the premises: a heart attack with a tender chest
  wall, meningococcal rash before fever, pneumonia in an 80-year-old showing
  only as confusion, and confusion with no named cause. Each one rejects
  every premise that would let its condition be ruled out.
- **The idle premise from step 10 is now load-bearing.** Removing
  "pneumonia can be confusion alone from 65" used to survive every test.
  The `olderConfusionPneumo` counterexample now catches it, and C38 states
  the knowledge directly: in an older adult, no fever, cough or
  breathlessness does not rule out pneumonia. The clause was medically true
  all along. It had no test because nothing *relied* on it. **A
  counterexample model tests a premise even when no verdict uses it.**

## Open design questions

1. **How knowledge and time interact.** No frame condition links `compat`
   and `later` yet, for example perfect recall.
2. **More "see a doctor" cases.** Only the persistent cough uses that level
   so far.
3. **Calibration of the atypical-cardiac premise.** Treating every woman's
   breathlessness as possibly cardiac is safe but blunt. A probabilistic or
   risk-score premise could narrow it, but the logic is qualitative. This is
   the plan's "uncertainty" open problem showing up concretely.
4. **Reported versus measured fever.** `fever_of_temp` goes one way only. A
   user who *feels* feverish but measured 37.5 °C has a fever by report and
   not by reading. Which one wins?
5. **A stiff neck alone.** With no fever and no headache, a stiff neck
   certifies nothing. Is that right, or is a stiff neck alone a red flag?
6. **Joint versus separate doubts** (C15): ask jointly, or assume symptoms
   vary independently.

## Candidate next steps

- Grow the clinical counterexample library (step 12 started it), for
  example a diabetic with a silent heart attack, or appendicitis in an
  older adult.
- More symptom-level cautions in the style of `caution_newConfusion`, for
  example sudden severe headache or fainting.
- Give the knowledge-time interaction a frame condition (perfect recall), so
  claims can reason about symptoms that were confirmed earlier.
- Decide the reported-versus-measured fever question and encode it.
