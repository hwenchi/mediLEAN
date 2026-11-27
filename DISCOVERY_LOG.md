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
    Rejected.lean        test models, witnesses, rejected claims, caution under doubt
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
tests/mutation_test.sh  # corrupt each premise 16 ways, expect failures
```

## Premises (in `Theory/Premises.lean`)

| Group | Premise | Says |
|-------|---------|------|
| Red flags | `redflag_cardiac` | chest pain + arm pain ⇒ cardiac can't be ruled out |
| | `redflag_meningitis` | fever + stiff neck ⇒ meningitis can't be ruled out |
| | `redflag_pneumonia` | fever + cough + breathlessness ⇒ pneumonia can't be ruled out |
| | `redflag_viral` | fever, cough or sore throat ⇒ viral can't be ruled out |
| Necessary symptoms | `cardiac_needs` | cardiac ⇒ chest pain ∨ arm pain (CRUDE) |
| | `meningitis_needs` | meningitis ⇒ stiff neck ∨ headache (CRUDE) |
| | `pneumonia_needs` | pneumonia ⇒ fever ∧ (cough ∨ breathlessness) (CRUDE) |
| | `viral_needs` | viral ⇒ fever ∨ cough ∨ sore throat ∨ headache |
| Caution | `caution_cardiac` | cardiac possible ⇒ emergency care obligatory |
| | `caution_meningitis` | meningitis possible ⇒ emergency care obligatory |
| | `caution_pneumonia` | pneumonia possible ⇒ at least urgent care obligatory |
| Proportionality | `permit_selfCare` | cardiac, meningitis, pneumonia ruled out ⇒ self-care permitted |
| | `permit_urgentCare` | cardiac, meningitis ruled out ⇒ urgent care permitted |
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
| C6 | no chest, arm, stiff neck, headache or fever ⇒ self-care permitted | proved | cardiac/meningitis/pneumonia_needs, permit_selfCare |
| C6b | fever, but no chest, arm, stiff neck, headache, cough or breathlessness ⇒ self-care permitted | proved | same, ruling out pneumonia the other way |
| C8 | chest + arm ⇒ self-care forbidden | proved | C1's premises + one_pathway |
| C9 | red flags eventually ⇒ emergency care eventually obligatory | proved | C1 lifted through `Eventually` |
| C10 | self-care now, emergency care if chest + arm pain later | proved | C6 ∧ C9 |
| C11 | fever + cough + breathless, with cardiac and meningitis flags absent ⇒ urgent care | proved | 6 premises |
| C14 | chest pain confirmed, **unsure** about arm pain ⇒ emergency care obligatory | proved | redflag_cardiac, caution_cardiac, **law 4** |
| C16 | fever and stiff neck might be present **together** ⇒ emergency care obligatory | proved | redflag_meningitis, caution_meningitis, law 4 |
| C5 | fever alone ⇒ emergency care obligatory | rejected, correctly | — |
| C5′ | fever alone ⇒ self-care permitted | rejected, correctly ("ask more") | — |
| C7 | cough alone ⇒ self-care permitted | rejected, correctly | — |
| C12 | pneumonia pattern ⇒ emergency care obligatory | rejected, correctly (no over-referral) | — |
| C13 | C11's checklist without "no stiff neck" ⇒ urgent care permitted | rejected, correctly | — |
| C15 | fever *might* be present, stiff neck *might* be present (separately) ⇒ emergency care obligatory | rejected, correctly: doubts must be joint | — |
| — | `caution_under_doubt`: a patient who is actually fine is still referred | proved | C14 in a 2-scenario model |
| — | C6 and C11 checklist minimality (8 tests) | proved | — |

Every verdict's hypothesis holds in some test model, so none is true only
because nothing satisfies it. Every test model is checked by `decide`
against every premise.

## Test results (step 7)

- **Layering:** OK.
- **Axiom audit:** 22 results. None uses `sorry` or classical choice. Six
  verdicts use no axioms at all.
- **Mutation testing:** 14 of 16 caught. Both survivors were marked benign
  in advance.

| Mutation | Kind | Caught by |
|----------|------|-----------|
| caution levels lowered (cardiac, meningitis, pneumonia) | unsafe | C1, C3, C11 |
| caution: pneumonia raised to emergency | cautious | C11 |
| red flags narrowed (cardiac, meningitis, pneumonia) | unsafe | C1, C3, C11 |
| needs: cardiac without arm pain | unsafe | **checklist test model** (`armOnly`) |
| needs: meningitis without headache | unsafe | **checklist test model** (`headacheOnly`) |
| needs: pneumonia also needs headache | unsafe | **test model** (`pneumo`) |
| needs: pneumonia without fever | cautious | Rules (`ruledOut_pneumonia_noFever` becomes false) |
| permit: urgent care skips meningitis check | unsafe | C11 |
| permit: self-care skips pneumonia check | unsafe | C6 |
| permit: self-care also needs viral ruled out | cautious | C6 |
| red flag: viral ignores sore throat | benign | survived |
| needs: viral without headache | benign | survived |

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

## Open design questions

1. **How knowledge and time interact.** No frame condition links `compat`
   and `later` yet, for example perfect recall.
2. **"See a doctor" has no premise.** Nothing requires or permits it. It needs
   a condition at that level, such as a cough lasting weeks, which needs a
   notion of duration.
3. **Atypical presentations.** The "needs" premises are knowingly crude.
   They should depend on the patient (infant, adult, elderly).
4. **Joint versus separate doubts.** Should the interface ask jointly, or
   should we assume unknown symptoms vary independently? That assumption
   would be a frame condition, and it would make C15 provable.
5. **Premises outside the table shape.** Next, add premises tables could not
   express: patient context ("fever in an infant under 3 months ⇒
   emergency"), thresholds ("temperature ≥ 39.5°C"), exceptions ("chest pain
   that is tender to the touch"). Then see whether proofs start to need real
   search.

## Candidate next steps

- Add patient context and one threshold premise, then pose claims that
  need them.
- Add duration, so "see a doctor" gets a premise and `Always` carries real
  weight.
- Have an LLM propose countermodels as `situation%` terms, with Lean
  checking each one by building it.
