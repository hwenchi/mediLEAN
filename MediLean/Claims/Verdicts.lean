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

/-- C6. No chest pain, arm pain, stiff neck, headache or fever ⇒ self-care
    is permitted. (A cough-and-sore-throat cold.)
    Uses: cardiac_needs, meningitis_needs, pneumonia_needs, permit_selfCare. -/
def c6_selfcare : CertifiedClaim where
  hyp M w   := M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .fever] w
  concl M w := M.Permitted (M.seeks .selfCare) w
  proof M w h := M.permit_selfCare w
    (ruledOut_cardiac (h _ (by decide)) (h _ (by decide)))
    (ruledOut_meningitis (h _ (by decide)) (h _ (by decide)))
    (ruledOut_pneumonia_noFever (h _ (by decide)))

/-- C6b. Fever is fine too, if cough and breathlessness are ruled out:
    pneumonia is then excluded the *other* way. -/
def c6b_selfcare_fever : CertifiedClaim where
  hyp M w   := M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache, .cough, .breathless] w
  concl M w := M.Permitted (M.seeks .selfCare) w
  proof M w h := M.permit_selfCare w
    (ruledOut_cardiac (h _ (by decide)) (h _ (by decide)))
    (ruledOut_meningitis (h _ (by decide)) (h _ (by decide)))
    (ruledOut_pneumonia_noCough (h _ (by decide)) (h _ (by decide)))

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

/-- C11. A middle verdict. Fever + cough + breathlessness, with the cardiac
    and meningitis red flags ruled out ⇒ urgent care: at least urgent care
    is obligatory, urgent care itself is permitted (the ER isn't required),
    self-care and a routine doctor's visit are forbidden.
    Uses: redflag_pneumonia, caution_pneumonia, cardiac_needs,
    meningitis_needs, permit_urgentCare, one_pathway. -/
def c11_pneumonia : CertifiedClaim where
  hyp M w   := M.KnownAll [.fever, .cough, .breathless] w ∧
               M.RuledAllOut [.chestPain, .armPain, .stiffNeck, .headache] w
  concl M w := M.Obligatory (M.SeeksAtLeast .urgentCare) w ∧
               M.Permitted (M.seeks .urgentCare) w ∧
               M.Forbidden (M.seeks .selfCare) w ∧
               M.Forbidden (M.seeks .seeDoctor) w
  proof M w h :=
    have ho := M.caution_pneumonia w (M.redflag_pneumonia w
      (known_T (h.1 _ (by decide))) (known_T (h.1 _ (by decide))) (known_T (h.1 _ (by decide))))
    ⟨ho,
     M.permit_urgentCare w
       (ruledOut_cardiac (h.2 _ (by decide)) (h.2 _ (by decide)))
       (ruledOut_meningitis (h.2 _ (by decide)) (h.2 _ (by decide))),
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

end MediLean
