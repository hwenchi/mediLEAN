/-
  CLAIMS: witnesses. Every verdict's hypothesis holds in some test model,
  so no verdict is true merely because nothing satisfies it.
-/
import MediLean.Claims.Verdicts
import MediLean.Claims.Models

set_option synthInstance.maxSize 1024

namespace MediLean
open AdvisoryFrame TriageModel

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

example : c17_infant_fever.hyp infantFever now := by unfold c17_infant_fever; decide
example : c18_measured_fever_stiffneck.hyp borderFever now := by
  unfold c18_measured_fever_stiffneck; decide
example : c19_high_fever.hyp highFever now := by unfold c19_high_fever; decide
example : c22_neck_headache.hyp neckHeadache now := by unfold c22_neck_headache; decide
example : c23_older_cough_breathless.hyp olderPneumo now := by
  unfold c23_older_cough_breathless; decide
example : c6c_selfcare_lowRisk.hyp coldCough now := by unfold c6c_selfcare_lowRisk; decide
example : c27_fever_confusion.hyp feverConfusion now := by unfold c27_fever_confusion; decide
example : c31_persistent_cough.hyp cough21 now := by unfold c31_persistent_cough; decide
example : c32_cough_safety_net.hyp coughStory (false, .selfCare) := by
  unfold c32_cough_safety_net c6_selfcare; decide

end MediLean
