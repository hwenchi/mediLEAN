/-
  CLAIMS: certified verdicts. Each is proved from the named premises in
  `Theory/Premises.lean`; the proof says which premises it uses.
-/
import MediLean.Theory.Rules

namespace MediLean
open AdvisoryFrame TriageModel

/-- C1. Confirmed chest pain + arm pain ⇒ emergency care is obligatory.
    Uses: redflag_cardiac, caution_cardiac. -/
def c1_chest_arm : CertifiedClaim where
  hyp M w   := M.Known (M.has .chestPain) w ∧ M.Known (M.has .armPain) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast
    (M.caution_cardiac w (M.redflag_cardiac w (known_T h.1) (known_T h.2)))

/-- C2. Same ⇒ emergency care is also *permitted* (frame law D on top of C1). -/
def c2_chest_arm_permitted : CertifiedClaim where
  hyp       := c1_chest_arm.hyp
  concl M w := M.Permitted (M.seeks .emergency) w
  proof M w h := obligatory_D (c1_chest_arm.proof M w h)

/-- C3. Confirmed fever + stiff neck ⇒ emergency care is obligatory.
    Uses: redflag_meningitis, caution_meningitis. -/
def c3_fever_stiffneck : CertifiedClaim where
  hyp M w   := M.Known (M.has .fever) w ∧ M.Known (M.has .stiffNeck) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast
    (M.caution_meningitis w (M.redflag_meningitis w (known_T h.1) (known_T h.2)))

/-- C4. Chest pain + arm pain ⇒ a cardiac event can't be ruled out
    (the explanation shown alongside C1). Uses: redflag_cardiac. -/
def c4_cardiac_not_ruled_out : CertifiedClaim where
  hyp       := c1_chest_arm.hyp
  concl M w := ¬ M.RuledOut (M.cond .cardiac) w
  proof M w h := possible_not_ruledOut (M.redflag_cardiac w (known_T h.1) (known_T h.2))

/-- C6. Patient aged 1 to 64: no chest pain, arm pain, stiff neck, headache,
    confusion, fever or breathlessness, and any cough under 3 weeks ⇒
    self-care is permitted. (A cough-and-sore-throat cold.) The age bounds come from steps 8 and 9;
    confusion and breathlessness from step 10 (meningitis can show as
    confusion; a cardiac event can be breathlessness alone in women and
    diabetics). Older adults: see C6b. Low-risk shortcut: see C6c.
    Uses: all four *_needs premises, fever_of_temp, permit_selfCare. -/
def c6_selfcare : CertifiedClaim where
  hyp M w   := M.Known (fun v => 12 ≤ M.ageMonths v) w ∧
               M.Known (fun v => M.ageMonths v < 780) w ∧
               M.Known (fun v => M.coughDays v < 21) w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                              .fever, .breathless] w
  concl M w := M.Permitted (M.seeks .selfCare) w
  proof M w h :=
    have ⟨h12, hy, hcd, hr⟩ := h
    M.permit_selfCare w
      (ruledOut_cardiac_noBreath (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_meningitis h12 (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_pneumonia_noFever hy (hr _ (by decide)))
      (ruledOut_seriousInfection_noFever (hr _ (by decide)))
      (noHighFever_of_noFever (hr _ (by decide)))
      hcd

/-- C6c. Low-risk shortcut: for a man aged 1 to 64 without diabetes, the
    breathlessness question can be skipped. Chest and arm pain are then
    enough to rule out a cardiac event. Uses: as C6, with the low-risk form
    of cardiac_needs. -/
def c6c_selfcare_lowRisk : CertifiedClaim where
  hyp M w   := M.Known (fun v => 12 ≤ M.ageMonths v) w ∧
               M.Known (fun v => M.ageMonths v < 780) w ∧
               M.Known (fun v => ¬ M.diabetic v) w ∧ M.Known (fun v => ¬ M.female v) w ∧
               M.Known (fun v => M.coughDays v < 21) w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion, .fever] w
  concl M w := M.Permitted (M.seeks .selfCare) w
  proof M w h :=
    have ⟨h12, hy, hnd, hm, hcd, hr⟩ := h
    M.permit_selfCare w
      (ruledOut_cardiac_lowRisk hy hnd hm (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_meningitis h12 (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_pneumonia_noFever hy (hr _ (by decide)))
      (ruledOut_seriousInfection_noFever (hr _ (by decide)))
      (noHighFever_of_noFever (hr _ (by decide)))
      hcd

/-- C6b. A fever is fine too, if cough, breathlessness and confusion are
    ruled out (pneumonia is then excluded the *other* way) and no reading of
    40.0 °C or more is possible. Works at any age from 1 and for anyone. -/
def c6b_selfcare_fever : CertifiedClaim where
  hyp M w   := M.Known (fun v => 12 ≤ M.ageMonths v) w ∧
               M.Known (fun v => M.tempTenths v < 400) w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                              .cough, .breathless] w
  concl M w := M.Permitted (M.seeks .selfCare) w
  proof M w h :=
    have ⟨h12, ht, hr⟩ := h
    M.permit_selfCare w
      (ruledOut_cardiac_noBreath (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_meningitis h12 (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_pneumonia_noCough (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
      (ruledOut_seriousInfection_age (known_age_mono (by decide) h12))
      ht
      (noPersistentCough_of_noCough (hr _ (by decide)))

/-- C8. Chest pain + arm pain ⇒ self-care is *forbidden*.
    Uses: C1's premises plus one_pathway. -/
def c8_selfcare_forbidden : CertifiedClaim where
  hyp       := c1_chest_arm.hyp
  concl M w := M.Forbidden (M.seeks .selfCare) w
  proof M w h := forbidden_below (u0 := .emergency) (by decide)
    (M.caution_cardiac w (M.redflag_cardiac w (known_T h.1) (known_T h.2)))

/-- C9. Safety net: if chest + arm pain are *eventually* confirmed,
    emergency care *eventually* becomes obligatory. -/
def c9_safety_net : CertifiedClaim where
  hyp M w   := M.Eventually (fun v => M.Known (M.has .chestPain) v ∧ M.Known (M.has .armPain) v) w
  concl M w := M.Eventually (M.Obligatory (M.seeks .emergency)) w
  proof M _ h := diamond_mono (fun v hv => c1_chest_arm.proof M v hv) h

/-- C10. The shape of real advice: "self-care is fine now; if chest + arm
    pain ever appear, go to the emergency department then." -/
def c10_advice : CertifiedClaim where
  hyp M w   := c6_selfcare.hyp M w ∧ c9_safety_net.hyp M w
  concl M w := M.Permitted (M.seeks .selfCare) w ∧
               M.Eventually (M.Obligatory (M.seeks .emergency)) w
  proof M w h := ⟨c6_selfcare.proof M w h.1, c9_safety_net.proof M w h.2⟩

/-- C11. A middle verdict. A man aged 1 to 64 without diabetes, with fever,
    cough and breathlessness, and the cardiac and meningitis red flags ruled
    out ⇒ urgent care: at least urgent care is obligatory, urgent care itself
    is permitted (the ER isn't required), self-care and a routine doctor's
    visit are forbidden. For older adults, diabetics and women the
    breathlessness could itself be cardiac (C24, C30).
    Uses: redflag_pneumonia, caution_pneumonia, cardiac_needs,
    meningitis_needs, seriousInfection_needs, permit_urgentCare, one_pathway. -/
def c11_pneumonia : CertifiedClaim where
  hyp M w   := M.Known (fun v => 12 ≤ M.ageMonths v) w ∧
               M.Known (fun v => M.ageMonths v < 780) w ∧
               M.Known (fun v => ¬ M.diabetic v) w ∧ M.Known (fun v => ¬ M.female v) w ∧
               M.KnownAll [.fever, .cough, .breathless] w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion] w
  concl M w := M.Obligatory (M.SeeksAtLeast .urgentCare) w ∧
               M.Permitted (M.seeks .urgentCare) w ∧
               M.Forbidden (M.seeks .selfCare) w ∧
               M.Forbidden (M.seeks .seeDoctor) w
  proof M w h :=
    have ⟨h12, hy, hnd, hm, hk, hr⟩ := h
    have ho := M.caution_pneumonia w (M.redflag_pneumonia w
      (known_T (hk _ (by decide))) (known_T (hk _ (by decide))) (known_T (hk _ (by decide))))
    ⟨ho,
     M.permit_urgentCare w
       (ruledOut_cardiac_lowRisk hy hnd hm (hr _ (by decide)) (hr _ (by decide)))
       (ruledOut_meningitis h12 (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
       (ruledOut_seriousInfection_age (known_age_mono (by decide) h12)),
     forbidden_below (by decide) ho, forbidden_below (by decide) ho⟩

/-- C14. Caution under doubt: chest pain confirmed, the user is *unsure*
    about arm pain ⇒ emergency care is obligatory.
    Uses: redflag_cardiac, caution_cardiac, and frame law 4 (`compat_trans`):
    the red flag fires in a world the user can't exclude, and transitivity
    carries the danger back. -/
def c14_uncertain_arm : CertifiedClaim where
  hyp M w   := M.Known (M.has .chestPain) w ∧ M.Possible (M.has .armPain) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h :=
    have ⟨hc, v, hwv, ha⟩ := h
    emergency_of_atLeast (M.caution_cardiac w
      (possible_4 ⟨v, hwv, M.redflag_cardiac v (hc v hwv) ha⟩))

/-- C16. Joint doubt: fever and stiff neck might be present *together*
    ⇒ emergency care is obligatory. (Separate doubts are not enough: C15.) -/
def c16_joint_doubt : CertifiedClaim where
  hyp M w   := M.Possible (fun v => M.has .fever v ∧ M.has .stiffNeck v) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h :=
    have ⟨v, hwv, hf, hs⟩ := h
    emergency_of_atLeast (M.caution_meningitis w
      (possible_4 ⟨v, hwv, M.redflag_meningitis v hf hs⟩))

/-- C17. An infant under 3 months with a fever ⇒ emergency care is
    obligatory, with no other symptom needed. (Contrast C5: for an adult,
    fever alone obliges nothing.) Uses: redflag_infant_fever,
    caution_seriousInfection. -/
def c17_infant_fever : CertifiedClaim where
  hyp M w   := M.Known (fun v => M.ageMonths v < 3) w ∧ M.Known (M.has .fever) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast
    (M.caution_seriousInfection w (M.redflag_infant_fever w (known_T h.1) (known_T h.2)))

/-- C18. A measured 38.0 °C (exactly at the threshold) and a stiff neck ⇒
    emergency care is obligatory. The reading counts as a fever, which
    triggers the meningitis red flag. Tested at the boundary on purpose.
    Uses: fever_of_temp, redflag_meningitis, caution_meningitis. -/
def c18_measured_fever_stiffneck : CertifiedClaim where
  hyp M w   := M.Known (fun v => 380 ≤ M.tempTenths v) w ∧ M.Known (M.has .stiffNeck) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast (M.caution_meningitis w
    (M.redflag_meningitis w (M.fever_of_temp w (known_T h.1)) (known_T h.2)))

/-- C19. A measured 40.0 °C (exactly at the threshold) ⇒ at least urgent care
    is obligatory and self-care is forbidden, whatever the other symptoms.
    Uses: caution_highFever, one_pathway. -/
def c19_high_fever : CertifiedClaim where
  hyp M w   := M.Known (fun v => 400 ≤ M.tempTenths v) w
  concl M w := M.Obligatory (M.SeeksAtLeast .urgentCare) w ∧ M.Forbidden (M.seeks .selfCare) w
  proof M w h :=
    have ho := M.caution_highFever w (known_T h)
    ⟨ho, forbidden_below (by decide) ho⟩

/-- C22. A stiff neck with a headache, no fever needed ⇒ emergency care is
    obligatory. Uses: redflag_meningitis_headache, caution_meningitis. -/
def c22_neck_headache : CertifiedClaim where
  hyp M w   := M.Known (M.has .stiffNeck) w ∧ M.Known (M.has .headache) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast (M.caution_meningitis w
    (M.redflag_meningitis_headache w (known_T h.1) (known_T h.2)))

/-- C23. An older adult (65+) with cough and breathlessness, no fever needed
    ⇒ at least urgent care is obligatory, self-care forbidden.
    Uses: redflag_pneumonia_older, caution_pneumonia, one_pathway. -/
def c23_older_cough_breathless : CertifiedClaim where
  hyp M w   := M.Known (fun v => 780 ≤ M.ageMonths v) w ∧
               M.Known (M.has .cough) w ∧ M.Known (M.has .breathless) w
  concl M w := M.Obligatory (M.SeeksAtLeast .urgentCare) w ∧ M.Forbidden (M.seeks .selfCare) w
  proof M w h :=
    have ho := M.caution_pneumonia w
      (M.redflag_pneumonia_older w (known_T h.1) (known_T h.2.1) (known_T h.2.2))
    ⟨ho, forbidden_below (by decide) ho⟩


/-- C27. Fever with new confusion ⇒ emergency care is obligatory.
    Uses: redflag_meningitis_confusion, caution_meningitis. -/
def c27_fever_confusion : CertifiedClaim where
  hyp M w   := M.Known (M.has .fever) w ∧ M.Known (M.has .confusion) w
  concl M w := M.Obligatory (M.seeks .emergency) w
  proof M w h := emergency_of_atLeast (M.caution_meningitis w
    (M.redflag_meningitis_confusion w (known_T h.1) (known_T h.2)))

/-- C31. "See a doctor", finally used. Patient aged 1 to 64 with a cough of
    3 weeks or more and none of C6's red flags ⇒ seeing a doctor is
    obligatory (at least), permitted (no urgent care or ER needed), and
    self-care is forbidden. Tested at exactly 21 days.
    Uses: caution_persistentCough, the *_needs premises, permit_seeDoctor. -/
def c31_persistent_cough : CertifiedClaim where
  hyp M w   := M.Known (fun v => 12 ≤ M.ageMonths v) w ∧
               M.Known (fun v => M.ageMonths v < 780) w ∧
               M.Known (fun v => 21 ≤ M.coughDays v) w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .confusion,
                              .fever, .breathless] w
  concl M w := M.Obligatory (M.SeeksAtLeast .seeDoctor) w ∧
               M.Permitted (M.seeks .seeDoctor) w ∧
               M.Forbidden (M.seeks .selfCare) w
  proof M w h :=
    have ⟨h12, hy, hcd, hr⟩ := h
    have ho := M.caution_persistentCough w (known_T hcd)
    ⟨ho,
     M.permit_seeDoctor w
       (ruledOut_cardiac_noBreath (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
       (ruledOut_meningitis h12 (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)))
       (ruledOut_pneumonia_noFever hy (hr _ (by decide)))
       (ruledOut_seriousInfection_noFever (hr _ (by decide)))
       (noHighFever_of_noFever (hr _ (by decide))),
     forbidden_below (by decide) ho⟩

/-- C32. Safety-netting with a duration: "self-care is fine for this cough
    now; if it reaches 3 weeks, see a doctor then." The temporal modality
    carries a real clinical instruction. Uses: C6, caution_persistentCough. -/
def c32_cough_safety_net : CertifiedClaim where
  hyp M w   := c6_selfcare.hyp M w ∧ M.Eventually (M.Known (fun v => 21 ≤ M.coughDays v)) w
  concl M w := M.Permitted (M.seeks .selfCare) w ∧
               M.Eventually (M.Obligatory (M.SeeksAtLeast .seeDoctor)) w
  proof M w h :=
    ⟨c6_selfcare.proof M w h.1,
     diamond_mono (fun v hv => M.caution_persistentCough v (known_T hv)) h.2⟩

end MediLean
