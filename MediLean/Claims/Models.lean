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
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0)

/-! ### Genuine doubt: scenarios the user can't tell apart -/

/-- The user has chest pain and can't say whether their arm hurts.
    Scenario `true`: arm pain and a cardiac event. Scenario `false`: harmless
    chest pain. Guideline options must meet the worst scenario's need. -/
abbrev armUnsure := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.chestPain, .armPain] else [.chestPain]))
  (fun c w => c ∈ (if w.1 then [Condition.cardiac] else []))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0)

/-- Fever in one scenario, a (harmless) stiff neck in the other; never both. -/
abbrev separateDoubts := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 0 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.stiffNeck] else [.fever]))
  (fun c w => c ∈ (if w.1 then [] else [Condition.viral]))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0)

/-- Fever with a stiff neck in one scenario, nothing in the other. -/
abbrev jointDoubt := finite_model% (Bool × Urgency)
  (fun _ _ => True) (fun a b => a = b)
  (fun a b => a.1 = b.1 ∧ 3 ≤ Urgency.rank b.2)
  (fun s w => s ∈ (if w.1 then [Symptom.fever, .stiffNeck] else []))
  (fun c w => c ∈ (if w.1 then [Condition.meningitis, .viral] else []))
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0)

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
        M.Known (fun v => M.ageMonths v < 780) w →
        M.Known (fun v => ¬ M.diabetic v) w → M.Known (fun v => ¬ M.female v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .headache, .confusion] w →
        M.Permitted (M.seeks .urgentCare) w :=
  fun h => absurd (h pneumoMening now (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) (by decide)

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
        M.Known (fun v => M.coughDays v < 21) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                       .fever, .breathless] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h infantMening now (by decide) (by decide)) (by decide)

abbrev elevenMonthMening := situationAt% 11 0 [] [.meningitis] 3

/-- C20b (rejected, boundary). Even confirming the child is at least 11
    months old isn't enough: under one year, meningitis can still present
    without a stiff neck, headache or fever. Pins the age gate at 12 months. -/
theorem c20b_age_gate_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 11 ≤ M.ageMonths v) w →
        M.Known (fun v => M.coughDays v < 21) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                       .fever, .breathless] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h elevenMonthMening now (by decide) (by decide) (by decide)) (by decide)

/-- C21 (rejected, boundary). At exactly 3 months, fever alone no longer
    obliges emergency care: the infant-fever rule is "under 3 months". -/
theorem c21_three_months_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => M.ageMonths v ≤ 3) w → M.Known (M.has .fever) w →
        M.Obligatory (M.seeks .emergency) w :=
  fun h => absurd (h threeMonthFever now (by decide) (by decide)) (by decide)

/-! ### Older adults (step 9) -/

abbrev olderPneumo        := situationAt% 840 0 [.cough, .breathless] [.pneumonia, .viral] 2
abbrev olderPneumoCardiac := situationAt% 840 0 [.fever, .cough, .breathless]
                                         [.pneumonia, .viral, .cardiac] 3
abbrev afebrile65         := situationAt% 780 0 [.cough] [.pneumonia, .viral] 2
abbrev breathless65       := situationAt% 780 0 [.breathless] [.cardiac] 3

/-- C24 (rejected). C11's urgent-care verdict does not carry over to a
    70-year-old: their breathlessness could itself be a cardiac event, which
    no chest or arm pain question rules out. -/
theorem c24_c11_not_for_older :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w →
        M.Known (fun v => ¬ M.diabetic v) w → M.Known (fun v => ¬ M.female v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion] w →
        M.Permitted (M.seeks .urgentCare) w :=
  fun h => absurd (h olderPneumoCardiac now (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by decide)

/-- C25 (rejected, boundary). At exactly 65, "no fever" no longer rules out
    pneumonia. Pins the afebrile-pneumonia age at 65. -/
theorem c25_afebrile_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v ≤ 780) w →
        M.Known (fun v => M.coughDays v < 21) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                       .fever, .breathless] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h afebrile65 now (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- C26 (rejected, boundary). At exactly 65, no chest or arm pain no longer
    rules out a cardiac event: breathlessness alone could be one. Pins the
    atypical-cardiac age at 65. -/
theorem c26_atypical_cardiac_boundary :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v ≤ 780) w →
        M.Known (fun v => ¬ M.diabetic v) w → M.Known (fun v => ¬ M.female v) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .fever, .cough] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h breathless65 now (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by decide)

/-! ### Women, diabetics, confusion (step 10) -/

abbrev breathlessWoman    := patient% 360 0 False True [.breathless] [.cardiac] 3
abbrev breathlessDiabetic := patient% 360 0 True False [.breathless] [.cardiac] 3
abbrev womanPneumoCardiac := patient% 360 0 False True [.fever, .cough, .breathless]
                                      [.pneumonia, .viral, .cardiac] 3
abbrev feverConfusion     := situation% [.fever, .confusion] [.meningitis, .viral] 3

/-- C28 (rejected). The low-risk shortcut (C6c, no breathlessness question)
    does not work for a woman: a cardiac event can be breathlessness alone. -/
theorem c28_shortcut_not_for_women :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v < 780) w →
        M.Known (fun v => ¬ M.diabetic v) w →
        M.Known (fun v => M.coughDays v < 21) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .fever] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h breathlessWoman now (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- C29 (rejected). Nor for a man with diabetes. -/
theorem c29_shortcut_not_for_diabetics :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v < 780) w →
        M.Known (fun v => ¬ M.female v) w →
        M.Known (fun v => M.coughDays v < 21) w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .fever] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h breathlessDiabetic now (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- C30 (rejected). C11's urgent-care verdict does not carry over to a woman:
    her breathlessness could itself be a cardiac event. -/
theorem c30_c11_not_for_women :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v < 780) w →
        M.Known (fun v => ¬ M.diabetic v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion] w →
        M.Permitted (M.seeks .urgentCare) w :=
  fun h => absurd (h womanPneumoCardiac now (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by decide)

/-! ### Cough duration and chest-wall tenderness (step 11) -/

abbrev cough21 := coughFor% 21 [.cough] [.viral] 1
abbrev cough20 := coughFor% 20 [.cough] [.viral] 0

/-- Cough for 5 days now; for 21 days later. Self-care now, a doctor later. -/
abbrev coughStory := finite_model% (Bool × Urgency)
  (fun a b => a.1 = b.1) (fun a b => a.1 = false ∨ b.1 = true)
  (fun a b => a.1 = b.1 ∧ (if a.1 then 1 else 0) ≤ Urgency.rank b.2)
  (fun s _ => s ∈ [Symptom.cough]) (fun c _ => c ∈ [Condition.viral])
  (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0) (fun _ => False) (fun _ => False)
  (fun w => if w.1 then 21 else 5)

/-- A clinical counterexample: a heart attack in a 50-year-old man whose
    chest pain IS reproduced by pressing on the chest wall. This happens;
    reproducible tenderness lowers the likelihood of a cardiac cause but
    does not exclude it. Any premise that lets tenderness rule out a cardiac
    event makes this model fail to build. -/
abbrev tenderMI := situationAt% 600 0 [.chestPain, .chestWallTender] [.cardiac] 3

/-- C33 (rejected, boundary). A cough of 20 days does not yet oblige a
    doctor's visit. Pins the persistent-cough threshold at 21 days. -/
theorem c33_cough_20_days :
    ¬ ∀ (M : TriageModel) w, M.Known (fun v => 20 ≤ M.coughDays v) w →
        M.Obligatory (M.SeeksAtLeast .seeDoctor) w :=
  fun h => absurd (h cough20 now (by decide)) (by decide)

/-- C34 (rejected). A persistent cough alone does not oblige urgent care. -/
theorem c34_cough_not_urgent :
    ¬ ∀ (M : TriageModel) w, M.Known (fun v => 21 ≤ M.coughDays v) w →
        M.Obligatory (M.SeeksAtLeast .urgentCare) w :=
  fun h => absurd (h cough21 now (by decide)) (by decide)

/-- C35 (rejected). Chest pain that is tender to the touch, with every other
    red flag absent, does NOT certify self-care: the tempting exception
    "tender chest pain isn't cardiac" is not part of the theory, and
    `tenderMI` shows why it must not be. -/
theorem c35_tender_chest_pain_not_selfcare :
    ¬ ∀ (M : TriageModel) w,
        M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v < 780) w →
        M.Known (M.has .chestWallTender) w →
        M.RuledAllOut [.armPain, .stiffNeck, .headache, .confusion, .fever, .breathless, .cough] w →
        M.Permitted (M.seeks .selfCare) w :=
  fun h => absurd (h tenderMI now (by decide) (by decide) (by decide) (by decide)) (by decide)

end MediLean
