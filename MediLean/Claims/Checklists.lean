/-
  CLAIMS: checklist minimality.

  C6 certifies self-care from eight confirmed absences; C11 certifies urgent
  care from five. Each test drops one item and gives a model of the premises
  where the shorter checklist holds but the verdict fails. So every item is
  load-bearing: the interface must ask every question.

  These tests are also the main guard against *unsafe* edits to the
  "needs" premises: weakening one makes danger easier to rule out, which
  every positive verdict survives. Only a test like these notices.
-/
import MediLean.Claims.Models

set_option synthInstance.maxSize 1024

namespace MediLean
open AdvisoryFrame TriageModel

/-- Level `u` is NOT certified for a patient known to be aged 1 to 64, with
    any cough under 3 weeks, by confirming the absence of `ss`. -/
def NotCertified (u : Urgency) (ss : List Symptom) : Prop :=
  ¬ ∀ (M : TriageModel) w, M.Known (fun v => 12 ≤ M.ageMonths v) w →
      M.Known (fun v => M.ageMonths v < 780) w →
      M.Known (fun v => M.coughDays v < 21) w →
      M.RuledAllOut ss w → M.Permitted (M.seeks u) w

theorem notCertified_of (M : TriageModel) (w : M.W) {u : Urgency} {ss : List Symptom}
    (hage : M.Known (fun v => 12 ≤ M.ageMonths v) w)
    (hyoung : M.Known (fun v => M.ageMonths v < 780) w)
    (hcd : M.Known (fun v => M.coughDays v < 21) w)
    (hr : M.RuledAllOut ss w) (hn : ¬ M.Permitted (M.seeks u) w) : NotCertified u ss :=
  fun h => hn (h M w hage hyoung hcd hr)

abbrev chestOnly     := situation% [.chestPain] [.cardiac] 3
abbrev armOnly       := situation% [.armPain] [.cardiac] 3
abbrev stiffOnly     := situation% [.stiffNeck] [.meningitis] 3
abbrev headacheOnly  := situation% [.headache] [.meningitis] 3
abbrev confusionOnly := situation% [.confusion] [.meningitis] 3
abbrev feverCough    := situation% [.fever, .cough] [.pneumonia, .viral] 2

/-- C6: dropping any one of its eight questions breaks the self-care verdict. -/
theorem c6_checklist_minimal :
    NotCertified .selfCare [.armPain, .stiffNeck, .headache, .confusion, .rash, .fever, .breathless] ∧   -- no chest pain
    NotCertified .selfCare [.chestPain, .stiffNeck, .headache, .confusion, .rash, .fever, .breathless] ∧ -- no arm pain
    NotCertified .selfCare [.chestPain, .armPain, .headache, .confusion, .rash, .fever, .breathless] ∧   -- no stiff neck
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .confusion, .rash, .fever, .breathless] ∧  -- no headache
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .headache, .rash, .fever, .breathless] ∧   -- no confusion
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .rash, .breathless] ∧ -- no fever
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .rash, .fever] ∧     -- no breathlessness
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .fever, .breathless]  -- no rash
  :=
  ⟨notCertified_of chestOnly       now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of armOnly         now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of stiffOnly       now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of headacheOnly    now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of confusionOnly   now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of feverCough      now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of breathlessWoman now (by decide) (by decide) (by decide) (by decide) (by decide),
   notCertified_of rashOnly        now (by decide) (by decide) (by decide) (by decide) (by decide)⟩

abbrev pneumoChest     := situation% [.fever, .cough, .breathless, .chestPain]
                                     [.pneumonia, .viral, .cardiac] 3
abbrev pneumoArm       := situation% [.fever, .cough, .breathless, .armPain]
                                     [.pneumonia, .viral, .cardiac] 3
abbrev pneumoHeadache  := situation% [.fever, .cough, .breathless, .headache]
                                     [.pneumonia, .viral, .meningitis] 3
abbrev pneumoConfusion := situation% [.fever, .cough, .breathless, .confusion]
                                     [.pneumonia, .viral, .meningitis] 3
abbrev pneumoRash      := situation% [.fever, .cough, .breathless, .rash]
                                     [.pneumonia, .viral, .meningitis] 3

/-- C11's hypotheses for a man aged 1 to 64 without diabetes, with fever,
    cough and breathlessness confirmed, and the absence of `ss` confirmed. -/
def UrgentNotCertified (ss : List Symptom) : Prop :=
  ¬ ∀ (M : TriageModel) w,
      M.Known (fun v => 12 ≤ M.ageMonths v) w → M.Known (fun v => M.ageMonths v < 780) w →
      M.Known (fun v => ¬ M.diabetic v) w → M.Known (fun v => ¬ M.female v) w →
      M.KnownAll [.fever, .cough, .breathless] w →
      M.RuledAllOut ss w → M.Permitted (M.seeks .urgentCare) w

/-- C11: dropping any one ruled-out item breaks the urgent-care verdict
    (C13 in `Models.lean` is the stiff-neck case). -/
theorem c11_checklist_minimal :
    UrgentNotCertified [.armPain, .stiffNeck, .headache, .confusion, .rash] ∧   -- no chest pain
    UrgentNotCertified [.chestPain, .stiffNeck, .headache, .confusion, .rash] ∧ -- no arm pain
    UrgentNotCertified [.chestPain, .armPain, .stiffNeck, .confusion, .rash] ∧  -- no headache
    UrgentNotCertified [.chestPain, .armPain, .stiffNeck, .headache, .rash] ∧   -- no confusion
    UrgentNotCertified [.chestPain, .armPain, .stiffNeck, .headache, .confusion] -- no rash
  :=
  ⟨fun h => absurd (h pneumoChest now (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoArm now (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoHeadache now (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoConfusion now (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoRash now (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide)⟩

end MediLean
