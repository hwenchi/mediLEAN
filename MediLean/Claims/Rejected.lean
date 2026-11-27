/-
  CLAIMS: test models, witnesses, and rejected claims.

  * Consistency: each test model satisfies every premise, so the theory
    has models and "certified" isn't vacuous.
  * Witnesses: each verdict's hypothesis holds in some model, so no verdict
    is true merely because nothing satisfies it.
  * Rejected claims: claims that must NOT follow, each refuted by a model
    of the premises where it fails.
-/
import MediLean.Claims.Verdicts
import MediLean.Claims.Finite

namespace MediLean
open AdvisoryFrame TriageModel

/-! ### Fully known situations -/

abbrev quiet        := situation% [] [] 0
abbrev coldCough    := situation% [.cough, .soreThroat] [.viral] 0
abbrev feverOnly    := situation% [.fever] [.viral] 0
abbrev chestArm     := situation% [.chestPain, .armPain] [.cardiac] 3
abbrev feverStiff   := situation% [.fever, .stiffNeck] [.meningitis, .viral] 3
abbrev pneumo       := situation% [.fever, .cough, .breathless] [.pneumonia, .viral] 2
abbrev pneumoMening := situation% [.fever, .cough, .breathless, .stiffNeck]
                                  [.pneumonia, .meningitis, .viral] 3
abbrev everything   := situation%
  [.chestPain, .armPain, .fever, .stiffNeck, .headache, .cough, .soreThroat, .breathless]
  [.cardiac, .meningitis, .pneumonia, .viral] 3

/-- The world where the patient takes self-care (any pathway would do). -/
abbrev now : Unit × Urgency := ((), .selfCare)

/-! ### A story over time: nothing now, chest + arm pain later -/

/-- Worlds are (later?, pathway). Nothing now; chest and arm pain later. -/
abbrev onset := finite_model% (Bool × Urgency)
  (fun a b => a.1 = b.1) (fun a b => a.1 = false ∨ b.1 = true)
  (fun a b => a.1 = b.1 ∧ (if a.1 then 3 else 0) ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.chestPain, .armPain] else []))
  (fun c w => c ∈ (if w.1 then [Condition.cardiac] else []))
  (fun u w => w.2 = u)

/-! ### Genuine doubt: scenarios the user can't tell apart -/

/-- The user has chest pain and can't say whether their arm hurts.
    Scenario `true`: arm pain and a cardiac event. Scenario `false`: harmless
    chest pain. Guideline options must meet the worst scenario's need. -/
abbrev armUnsure := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.chestPain, .armPain] else [.chestPain]))
  (fun c w => c ∈ (if w.1 then [Condition.cardiac] else []))
  (fun u w => w.2 = u)

/-- Fever in one scenario, a (harmless) stiff neck in the other; never both. -/
abbrev separateDoubts := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 0 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.stiffNeck] else [.fever]))
  (fun c w => c ∈ (if w.1 then [] else [Condition.viral]))
  (fun u w => w.2 = u)

/-- Fever with a stiff neck in one scenario, nothing in the other. -/
abbrev jointDoubt := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.fever, .stiffNeck] else []))
  (fun c w => c ∈ (if w.1 then [Condition.meningitis, .viral] else []))
  (fun u w => w.2 = u)

/-! ### Witnesses: every verdict's hypothesis is satisfiable -/

example : c1_chest_arm.hyp chestArm now := by unfold c1_chest_arm; decide
example : c3_fever_stiffneck.hyp feverStiff now := by unfold c3_fever_stiffneck; decide
example : c6_selfcare.hyp coldCough now := by unfold c6_selfcare; decide
example : c6b_selfcare_fever.hyp feverOnly now := by unfold c6b_selfcare_fever; decide
example : c10_advice.hyp onset (false, .selfCare) := by
  unfold c10_advice c6_selfcare c9_safety_net; decide
example : c11_pneumonia.hyp pneumo now := by unfold c11_pneumonia; decide
example : c16_joint_doubt.hyp jointDoubt (false, .selfCare) := by unfold c16_joint_doubt; decide

/-- C14's hypothesis holds in the scenario where the patient is actually
    fine (no arm pain, no cardiac event)... -/
theorem c14_witness : c14_uncertain_arm.hyp armUnsure (false, .selfCare) := by
  unfold c14_uncertain_arm; decide

/-- ...so emergency care is obligatory there anyway. The caution rule acting
    under genuine doubt, with its cost explicit: a fine patient is referred
    because the dangerous scenario can't be told apart. -/
theorem caution_under_doubt :
    armUnsure.Obligatory (armUnsure.seeks .emergency) (false, .selfCare) ∧
    ¬ armUnsure.has .armPain (false, .selfCare) ∧
    ¬ armUnsure.cond .cardiac (false, .selfCare) :=
  ⟨c14_uncertain_arm.proof _ _ c14_witness, by decide, by decide⟩

/-! ### Rejected claims -/

/-- C5 (rejected). Fever alone does not oblige emergency care. -/
theorem c5_fever_not_emergency :
    ¬ ∀ (M : TriageModel) w, M.Known (M.has .fever) w → M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h feverOnly now (by decide)) (by decide)

/-- C5′ (rejected). Fever alone does not permit self-care either: ask more. -/
theorem c5_fever_not_selfcare :
    ¬ ∀ (M : TriageModel) w, M.Known (M.has .fever) w → M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h feverStiff now (by decide)) (by decide)

/-- C7 (rejected). A confirmed cough doesn't license self-care:
    absence of red flags must be confirmed. -/
theorem c7_cough_not_selfcare :
    ¬ ∀ (M : TriageModel) w, M.Known (M.has .cough) w → M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h everything now (by decide)) (by decide)

/-- C12 (rejected). The pneumonia pattern does NOT oblige emergency care:
    urgent care meets the need. -/
theorem c12_pneumonia_not_emergency :
    ¬ ∀ (M : TriageModel) w, M.KnownAll [.fever, .cough, .breathless] w →
        M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h pneumo now (by decide)) (by decide)

/-- C13 (rejected). Drop "no stiff neck" from C11's checklist and urgent care
    is no longer certified: meningitis hasn't been ruled out. -/
theorem c13_unchecked_neck :
    ¬ ∀ (M : TriageModel) w,
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .headache] w →
        M.Permitted (M.seeks .urgentCare) w :=
  fun h => absurd (h pneumoMening now (by decide) (by decide)) (by decide)

/-- C15 (rejected). *Separate* doubts are not enough: fever might be present
    and a stiff neck might be present, but never together. Meningitis is
    never possible, so emergency care is not obligatory. The interface must
    ask about red-flag symptoms jointly. -/
theorem c15_separate_doubts :
    ¬ ∀ (M : TriageModel) w, M.Possible (M.has .fever) w →
        M.Possible (M.has .stiffNeck) w → M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h separateDoubts (false, .selfCare) (by decide) (by decide)) (by decide)

end MediLean
