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
| Patient facts | `ageMonths`, `tempTenths` | age in months; highest measured temperature (tenths of °C) |
| Measurements | `fever_of_temp` | a reading of 38.0 °C or more is a fever |
| Red flags | `redflag_cardiac` | chest pain + arm pain ⇒ cardiac can't be ruled out |
| | `redflag_meningitis` | fever + stiff neck ⇒ meningitis can't be ruled out |
| | `redflag_meningitis_headache` | stiff neck + headache ⇒ meningitis can't be ruled out, even with no fever (step 8) |
| | `redflag_pneumonia` | fever + cough + breathlessness ⇒ pneumonia can't be ruled out |
| | `redflag_viral` | fever, cough or sore throat ⇒ viral can't be ruled out |
| | `redflag_infant_fever` | infant under 3 months + fever ⇒ serious infection can't be ruled out (step 8) |
| Necessary symptoms | `cardiac_needs` | cardiac ⇒ chest pain ∨ arm pain (CRUDE) |
| | `meningitis_needs` | **from age 1:** meningitis ⇒ stiff neck ∨ headache (step 8: age-gated) |
| | `pneumonia_needs` | pneumonia ⇒ fever ∧ (cough ∨ breathlessness) (CRUDE) |
| | `viral_needs` | viral ⇒ fever ∨ cough ∨ sore throat ∨ headache |
| | `seriousInfection_needs` | serious infection ⇒ under 3 months ∧ fever (step 8) |
| Caution | `caution_cardiac` | cardiac possible ⇒ emergency care obligatory |
| | `caution_meningitis` | meningitis possible ⇒ emergency care obligatory |
| | `caution_pneumonia` | pneumonia possible ⇒ at least urgent care obligatory |
| | `caution_seriousInfection` | serious infection possible ⇒ emergency care obligatory (step 8) |
| | `caution_highFever` | reading of 40.0 °C or more ⇒ at least urgent care obligatory (step 8) |
| Proportionality | `permit_selfCare` | cardiac, meningitis, pneumonia, serious infection ruled out, and no reading ≥ 40.0 °C possible ⇒ self-care permitted |
| | `permit_urgentCare` | cardiac, meningitis, serious infection ruled out ⇒ urgent care permitted |
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
| C6 | age ≥ 1 year; no chest, arm, stiff neck, headache or fever ⇒ self-care permitted | proved (age added in step 8) | the *_needs premises, fever_of_temp, permit_selfCare |
| C6b | age ≥ 1 year, no reading ≥ 40.0 °C; fever, but no chest, arm, stiff neck, headache, cough or breathlessness ⇒ self-care permitted | proved | same, ruling out pneumonia the other way |
| C8 | chest + arm ⇒ self-care forbidden | proved | C1's premises + one_pathway |
| C9 | red flags eventually ⇒ emergency care eventually obligatory | proved | C1 lifted through `Eventually` |
| C10 | self-care now, emergency care if chest + arm pain later | proved | C6 ∧ C9 |
| C11 | age ≥ 1 year; fever + cough + breathless, with cardiac and meningitis flags absent ⇒ urgent care | proved | 7 premises |
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
| C20 | C6's checklist **without confirming age** ⇒ self-care permitted | rejected, correctly: infant meningitis can be silent | — |
| C20b | same, with age ≥ **11 months** confirmed | rejected, correctly: pins the age gate at 12 months | — |
| C21 | age ≤ **3 months** + fever ⇒ emergency care obligatory | rejected, correctly: pins the infant rule at "under 3 months" | — |
| — | `caution_under_doubt`: a patient who is actually fine is still referred | proved | C14 in a 2-scenario model |
| — | C6 and C11 checklist minimality (8 tests) | proved | — |

Every verdict's hypothesis holds in some test model, so none is true only
because nothing satisfies it. Every test model is checked by `decide`
against every premise.

## Test results (step 8)

- **Layering:** OK.
- **Axiom audit:** 29 results. None uses `sorry` or classical choice.
- **Mutation testing:** 23 of 25 caught. Both survivors were marked benign in
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
| needs: pneumonia without fever | cautious | rules (`ruledOut_pneumonia_noFever` becomes false) |
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

## Open design questions

1. **How knowledge and time interact.** No frame condition links `compat`
   and `later` yet, for example perfect recall.
2. **"See a doctor" has no premise.** Nothing requires or permits it. It needs
   a condition at that level, such as a cough lasting weeks.
3. **Atypical presentations, now that age is available.** Afebrile pneumonia
   in the elderly, and atypical cardiac presentations in older people,
   diabetics and women. `pneumonia_needs` and `cardiac_needs` should get the
   same treatment `meningitis_needs` got.
4. **Reported versus measured fever.** `fever_of_temp` goes one way only. A
   user who *feels* feverish but measured 37.5 °C has a fever by report and
   not by reading. Which one wins?
5. **A stiff neck alone.** With no fever and no headache, a stiff neck
   certifies nothing. Is that right, or is a stiff neck alone a red flag?
6. **Joint versus separate doubts** (C15): ask jointly, or assume symptoms
   vary independently.

## Candidate next steps

- Gate `pneumonia_needs` and `cardiac_needs` by age, as was done for
  meningitis.
- Add duration, so "see a doctor" gets a premise.
- Decide the reported-versus-measured fever question and encode it.
