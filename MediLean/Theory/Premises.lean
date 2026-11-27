/-
  ═══════════════════════════════════════════════════════════════════════
  THE THEORY: every assumption mediLEAN makes is in this file.
  ═══════════════════════════════════════════════════════════════════════

  Each premise is a named field of `TriageModel`. A model is any situation
  satisfying all of them. A claim is certified when it holds in every model.

  Nothing outside this file adds assumptions:
    Core/          fixed logic (modal operators, frames, the care scale)
    Theory/Rules   consequences proved from these premises
    Claims/        tests: verdicts, rejected claims, test models

  How to read the modal operators (w is "the situation as it is"):
    Diamond compat P w   P can't be ruled out, given what the user confirmed
    BoxNot  compat P w   P is ruled out
    Box     ideal  P w   P is obligatory (true in every guideline-compliant option)
    Diamond ideal  P w   P is permitted

  SOURCE: the LLM's own medical knowledge. UNREVIEWED; for exploration only.
  Premises marked CRUDE are known simplifications.
-/
import MediLean.Theory.Vocabulary

namespace MediLean

structure TriageModel extends AdvisoryFrame where
  has   : Symptom → W → Prop      -- the patient has this symptom
  cond  : Condition → W → Prop    -- the patient has this condition
  seeks : Urgency → W → Prop      -- the care pathway taken
  ageMonths  : W → Nat            -- the patient's age, in months
  tempTenths : W → Nat            -- highest measured temperature, tenths of °C
                                  -- (385 = 38.5 °C; 0 = not measured)
  diabetic   : W → Prop           -- the patient has diabetes
  female     : W → Prop           -- the patient is female
  coughDays  : W → Nat            -- how many days the cough has lasted (0 = no cough)

  -- ── Measurements ────────────────────────────────────────────────────────

  /-- A measured temperature of 38.0 °C or more is a fever. -/
  fever_of_temp : ∀ w, 380 ≤ tempTenths w → has .fever w
  /-- A cough that has lasted a day or more is a cough. -/
  cough_of_days : ∀ w, 1 ≤ coughDays w → has .cough w

  -- ── Red flags: symptom patterns that make a condition possible ──────────

  /-- Chest pain with arm pain: a cardiac event can't be ruled out. -/
  redflag_cardiac : ∀ w, has .chestPain w → has .armPain w → Diamond compat (cond .cardiac) w
  /-- Fever with a stiff neck: meningitis can't be ruled out. -/
  redflag_meningitis : ∀ w, has .fever w → has .stiffNeck w → Diamond compat (cond .meningitis) w
  /-- A stiff neck with a headache: meningitis can't be ruled out, even with
      no fever (fever can be absent early, or masked by paracetamol). -/
  redflag_meningitis_headache : ∀ w, has .stiffNeck w → has .headache w → Diamond compat (cond .meningitis) w
  /-- Fever with new confusion: meningitis can't be ruled out (the third
      sign of the classic triad). -/
  redflag_meningitis_confusion : ∀ w, has .fever w → has .confusion w → Diamond compat (cond .meningitis) w
  /-- Fever, cough and breathlessness together: pneumonia can't be ruled out. -/
  redflag_pneumonia : ∀ w, has .fever w → has .cough w → has .breathless w → Diamond compat (cond .pneumonia) w
  /-- From 65, cough and breathlessness together: pneumonia can't be ruled out,
      even without a fever (older adults often don't mount one). -/
  redflag_pneumonia_older : ∀ w, 780 ≤ ageMonths w → has .cough w → has .breathless w → Diamond compat (cond .pneumonia) w
  /-- Fever, cough or sore throat: a viral infection can't be ruled out. -/
  redflag_viral : ∀ w, has .fever w ∨ has .cough w ∨ has .soreThroat w → Diamond compat (cond .viral) w
  /-- Any fever in an infant under 3 months: a serious bacterial infection
      can't be ruled out (whatever else is or isn't present). -/
  redflag_infant_fever : ∀ w, ageMonths w < 3 → has .fever w → Diamond compat (cond .seriousInfection) w

  -- ── Necessary symptoms: what a condition can't occur without ────────────
  -- These are how danger gets ruled out, so they carry the most risk.

  /-- A cardiac event comes with chest pain or arm pain. In people at risk of
      an atypical presentation (65 or over, diabetic, or female) it can show
      up as breathlessness alone.
      CRUDE: nausea, fatigue and jaw pain are not in the vocabulary. -/
  cardiac_needs : ∀ w, cond .cardiac w → has .chestPain w ∨ has .armPain w ∨ ((780 ≤ ageMonths w ∨ diabetic w ∨ female w) ∧ has .breathless w)
  /-- From age one, meningitis comes with a stiff neck, a headache or
      confusion. Infants often show none, so for them this gives no way to
      rule it out. -/
  meningitis_needs : ∀ w, 12 ≤ ageMonths w → cond .meningitis w → has .stiffNeck w ∨ has .headache w ∨ has .confusion w
  /-- Pneumonia comes with cough or breathlessness (or, from 65, possibly
      just confusion), and, under 65, with a fever. From 65 it can be afebrile. -/
  pneumonia_needs : ∀ w, cond .pneumonia w → (ageMonths w < 780 → has .fever w) ∧ (has .cough w ∨ has .breathless w ∨ (780 ≤ ageMonths w ∧ has .confusion w))
  /-- A viral infection comes with fever, cough, sore throat or headache. -/
  viral_needs : ∀ w, cond .viral w → has .fever w ∨ has .cough w ∨ has .soreThroat w ∨ has .headache w
  /-- The serious-infection concern here is specific to febrile infants under 3 months. -/
  seriousInfection_needs : ∀ w, cond .seriousInfection w → ageMonths w < 3 ∧ has .fever w

  -- ── Caution: a condition that can't be ruled out obliges care ───────────

  /-- If a cardiac event can't be ruled out, emergency care is obligatory. -/
  caution_cardiac : ∀ w, Diamond compat (cond .cardiac) w → Box ideal (SeeksAtLeast seeks .emergency) w
  /-- If meningitis can't be ruled out, emergency care is obligatory. -/
  caution_meningitis : ∀ w, Diamond compat (cond .meningitis) w → Box ideal (SeeksAtLeast seeks .emergency) w
  /-- If pneumonia can't be ruled out, at least urgent care is obligatory. -/
  caution_pneumonia : ∀ w, Diamond compat (cond .pneumonia) w → Box ideal (SeeksAtLeast seeks .urgentCare) w
  /-- If a serious infection in an infant can't be ruled out, emergency care is obligatory. -/
  caution_seriousInfection : ∀ w, Diamond compat (cond .seriousInfection) w → Box ideal (SeeksAtLeast seeks .emergency) w
  /-- A temperature of 40.0 °C or more needs at least urgent care, whatever the cause. -/
  caution_highFever : ∀ w, 400 ≤ tempTenths w → Box ideal (SeeksAtLeast seeks .urgentCare) w
  /-- A cough lasting 3 weeks or more needs a doctor's assessment (causes
      include asthma, reflux, TB and cancer), whatever else is present. -/
  caution_persistentCough : ∀ w, 21 ≤ coughDays w → Box ideal (SeeksAtLeast seeks .seeDoctor) w

  -- ── Proportionality: lower care is fine once danger is ruled out ────────
  -- Every caution premise above must be blocked here, or the two would
  -- contradict each other for some patient, leaving that patient with no
  -- model and every claim about them vacuously true.

  /-- With cardiac, meningitis, pneumonia and serious infection ruled out, no
      reading of 40.0 °C or more possible, and no cough of 3 weeks or more
      possible, self-care is permitted. -/
  permit_selfCare : ∀ w, BoxNot compat (cond .cardiac) w → BoxNot compat (cond .meningitis) w → BoxNot compat (cond .pneumonia) w → BoxNot compat (cond .seriousInfection) w → Box compat (fun v => tempTenths v < 400) w → Box compat (fun v => coughDays v < 21) w → Diamond ideal (seeks .selfCare) w
  /-- With cardiac, meningitis, pneumonia and serious infection ruled out, and
      no reading of 40.0 °C or more possible, seeing a doctor is permitted
      (a persistent cough is fine at this level). -/
  permit_seeDoctor : ∀ w, BoxNot compat (cond .cardiac) w → BoxNot compat (cond .meningitis) w → BoxNot compat (cond .pneumonia) w → BoxNot compat (cond .seriousInfection) w → Box compat (fun v => tempTenths v < 400) w → Diamond ideal (seeks .seeDoctor) w
  /-- With cardiac, meningitis and serious infection ruled out, urgent care is permitted. -/
  permit_urgentCare : ∀ w, BoxNot compat (cond .cardiac) w → BoxNot compat (cond .meningitis) w → BoxNot compat (cond .seriousInfection) w → Diamond ideal (seeks .urgentCare) w

  -- ── Pathways ────────────────────────────────────────────────────────────

  /-- A person follows one care pathway at a time. -/
  one_pathway : ∀ w u u', seeks u w → seeks u' w → u = u'

end MediLean
