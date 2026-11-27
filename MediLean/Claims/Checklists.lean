/-
  CLAIMS: checklist minimality.

  C6 certifies self-care from five confirmed absences; C11 certifies urgent
  care from four. Each test drops one item and gives a model of the premises
  where the shorter checklist holds but the verdict fails. So every item is
  load-bearing: the interface must ask every question.

  These tests are also the main guard against *unsafe* edits to the
  "needs" premises: weakening one makes danger easier to rule out, which
  every positive verdict survives. Only a test like these notices.
-/
import MediLean.Claims.Models

namespace MediLean
open AdvisoryFrame TriageModel

/-- Level `u` is NOT certified for a patient known to be at least one year
    old by confirming the absence of `ss`. -/
def NotCertified (u : Urgency) (ss : List Symptom) : Prop :=
  ¬ ∀ (M : TriageModel) w, M.Known (fun v => 12 ≤ M.ageMonths v) w →
      M.RuledAllOut ss w → M.Permitted (M.seeks u) w

theorem notCertified_of (M : TriageModel) (w : M.W) {u : Urgency} {ss : List Symptom}
    (hage : M.Known (fun v => 12 ≤ M.ageMonths v) w)
    (hr : M.RuledAllOut ss w) (hn : ¬ M.Permitted (M.seeks u) w) : NotCertified u ss :=
  fun h => hn (h M w hage hr)

abbrev chestOnly    := situation% [.chestPain] [.cardiac] 3
abbrev armOnly      := situation% [.armPain] [.cardiac] 3
abbrev stiffOnly    := situation% [.stiffNeck] [.meningitis] 3
abbrev headacheOnly := situation% [.headache] [.meningitis] 3
abbrev feverCough   := situation% [.fever, .cough] [.pneumonia, .viral] 2

/-- C6: dropping any single item breaks the self-care verdict. -/
theorem c6_checklist_minimal :
    NotCertified .selfCare [.armPain, .stiffNeck, .headache, .fever] ∧    -- no chest pain check
    NotCertified .selfCare [.chestPain, .stiffNeck, .headache, .fever] ∧  -- no arm pain check
    NotCertified .selfCare [.chestPain, .armPain, .headache, .fever] ∧    -- no stiff neck check
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .fever] ∧   -- no headache check
    NotCertified .selfCare [.chestPain, .armPain, .stiffNeck, .headache]  -- no fever check
  :=
  ⟨notCertified_of chestOnly    now (by decide) (by decide) (by decide),
   notCertified_of armOnly      now (by decide) (by decide) (by decide),
   notCertified_of stiffOnly    now (by decide) (by decide) (by decide),
   notCertified_of headacheOnly now (by decide) (by decide) (by decide),
   notCertified_of feverCough   now (by decide) (by decide) (by decide)⟩

abbrev pneumoChest    := situation% [.fever, .cough, .breathless, .chestPain]
                                    [.pneumonia, .viral, .cardiac] 3
abbrev pneumoArm      := situation% [.fever, .cough, .breathless, .armPain]
                                    [.pneumonia, .viral, .cardiac] 3
abbrev pneumoHeadache := situation% [.fever, .cough, .breathless, .headache]
                                    [.pneumonia, .viral, .meningitis] 3

/-- C11: dropping any single ruled-out item breaks the urgent-care verdict
    (C13 in `Models.lean` is the stiff-neck case). -/
theorem c11_checklist_minimal :
    (¬ ∀ (M : TriageModel) w, M.Known (fun v => 12 ≤ M.ageMonths v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.armPain, .stiffNeck, .headache] w → M.Permitted (M.seeks .urgentCare) w) ∧
    (¬ ∀ (M : TriageModel) w, M.Known (fun v => 12 ≤ M.ageMonths v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .stiffNeck, .headache] w → M.Permitted (M.seeks .urgentCare) w) ∧
    (¬ ∀ (M : TriageModel) w, M.Known (fun v => 12 ≤ M.ageMonths v) w →
        M.KnownAll [.fever, .cough, .breathless] w →
        M.RuledAllOut [.chestPain, .armPain, .stiffNeck] w → M.Permitted (M.seeks .urgentCare) w) :=
  ⟨fun h => absurd (h pneumoChest    now (by decide) (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoArm      now (by decide) (by decide) (by decide)) (by decide),
   fun h => absurd (h pneumoHeadache now (by decide) (by decide) (by decide)) (by decide)⟩

end MediLean
