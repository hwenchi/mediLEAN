/-
  CLAIMS: test models and rejected claims.

  * Consistency: each test model satisfies every premise (checked by
    `decide` when it is built), so the theory has models and "certified"
    isn't vacuous.
  * Rejected claims: claims that must NOT follow, each refuted by a model of
    the premises where it fails.

  This file deliberately does not import the verdicts, so it builds (and
  checks every premise) even when a verdict breaks.
-/
import MediLean.Theory.Rules
import MediLean.Claims.Finite

set_option synthInstance.maxSize 1024

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
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0)

/-! ### Genuine doubt: scenarios the user can't tell apart -/

/-- The user has chest pain and can't say whether their arm hurts.
    Scenario `true`: arm pain and a cardiac event. Scenario `false`: harmless
    chest pain. Guideline options must meet the worst scenario's need. -/
abbrev armUnsure := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.chestPain, .armPain] else [.chestPain]))
  (fun c w => c ∈ (if w.1 then [Condition.cardiac] else []))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0)

/-- Fever in one scenario, a (harmless) stiff neck in the other; never both. -/
abbrev separateDoubts := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 0 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.stiffNeck] else [.fever]))
  (fun c w => c ∈ (if w.1 then [] else [Condition.viral]))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0)

/-- Fever with a stiff neck in one scenario, nothing in the other. -/
abbrev jointDoubt := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.fever, .stiffNeck] else []))
  (fun c w => c ∈ (if w.1 then [Condition.meningitis, .viral] else []))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0)

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
        M.Known (fun v => 12 ≤ M.ageMonths v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .headache] w →
        M.Permitted (M.seeks .urgentCare) w :=
  fun h => absurd (h pneumoMening now (by decide) (by decide) (by decide)) (by decide)

/-- C15 (rejected). *Separate* doubts are not enough: fever might be present
    and a stiff neck might be present, but never together. Meningitis is
    never possible, so emergency care is not obligatory. The interface must
    ask about red-flag symptoms jointly. -/
theorem c15_separate_doubts :
    ¬ ∀ (M : TriageModel) w, M.Possible (M.has .fever) w →
        M.Possible (M.has .stiffNeck) w → M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h separateDoubts (false, .selfCare) (by decide) (by decide)) (by decide)

/-! ### Patient context and thresholds (step 8) -/

abbrev infantFever     := situationAt% 1 0 [.fever] [.seriousInfection, .viral] 3
abbrev threeMonthFever := situationAt% 3 0 [.fever] [.viral] 0
abbrev infantMening    := situationAt% 1 0 [] [.meningitis] 3
abbrev borderFever     := situationAt% 360 380 [.fever, .stiffNeck] [.meningitis, .viral] 3
abbrev highFever       := situationAt% 360 400 [.fever] [.viral] 2
abbrev neckHeadache    := situation% [.stiffNeck, .headache] [.meningitis] 3


/-- C20 (rejected). C6's checklist *without* confirming the patient's age
    does not certify self-care: an infant can have meningitis with no stiff
    neck, headache or fever. Age is a question the interface must ask. -/
theorem c20_selfcare_needs_age :
    ¬ ∀ (M : TriageModel) w,
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .fever] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h infantMening now (by decide)) (by decide)

abbrev elevenMonthMening := situationAt% 11 0 [] [.meningitis] 3

/-- C20b (rejected, boundary). Even confirming the child is at least 11
    months old isn't enough: under one year, meningitis can still present
    without a stiff neck, headache or fever. Pins the age gate at 12 months. -/
theorem c20b_age_gate_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 11 ≤ M.ageMonths v) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .fever] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h elevenMonthMening now (by decide) (by decide)) (by decide)

/-- C21 (rejected, boundary). At exactly 3 months, fever alone no longer
    obliges emergency care: the infant-fever rule is "under 3 months". -/
theorem c21_three_months_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => M.ageMonths v ≤ 3) w → M.Known (M.has .fever) w →
        M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h threeMonthFever now (by decide) (by decide)) (by decide)

end MediLean
