/-
  THEORY, DERIVED: consequences of the premises. Nothing here is assumed;
  every lemma is proved from `Theory/Premises.lean` and the frame laws.

  Also defines `CertifiedClaim`, the shape of every answer.
-/
import MediLean.Theory.Premises

namespace MediLean
open AdvisoryFrame

/-- Every answer is an implication holding in every model of the premises.
    Bundling the proof means any value of this type is certified by construction. -/
structure CertifiedClaim where
  hyp   : (M : TriageModel) → M.W → Prop
  concl : (M : TriageModel) → M.W → Prop
  proof : ∀ (M : TriageModel) (w : M.W), hyp M w → concl M w

namespace TriageModel

/-! ### Vocabulary for claims (definitions, not assumptions) -/
section
variable (M : TriageModel)

/-- Seeking care at level `u0` or higher. -/
abbrev SeeksAtLeast (u0 : Urgency) : M.W → Prop := MediLean.SeeksAtLeast M.seeks u0

/-- The user confirmed every symptom in the list. -/
abbrev KnownAll (ss : List Symptom) (w : M.W) : Prop := ∀ s ∈ ss, M.Known (M.has s) w

/-- The user confirmed the *absence* of every symptom in the list.
    Not mentioning a symptom is not the same as confirming its absence. -/
abbrev RuledAllOut (ss : List Symptom) (w : M.W) : Prop := ∀ s ∈ ss, M.RuledOut (M.has s) w
end

/-! ### Derived rules -/
section
variable {M : TriageModel} {w : M.W}

/-- Ruling out a cardiac event in a low-risk patient (under 65, not
    diabetic, not female): no chest pain and no arm pain is enough. -/
theorem ruledOut_cardiac_lowRisk (hyoung : M.Known (fun v => M.ageMonths v < 780) w)
    (hnd : M.Known (fun v => ¬ M.diabetic v) w) (hm : M.Known (fun v => ¬ M.female v) w)
    (hc : M.RuledOut (M.has .chestPain) w)
    (ha : M.RuledOut (M.has .armPain) w) : M.RuledOut (M.cond .cardiac) w :=
  by
    intro v hv hx; have := M.cardiac_needs v hx; have := hyoung v hv; have := hnd v hv
    have := hm v hv; have := hc v hv; have := ha v hv; simp_all <;> omega

/-- Ruling out a cardiac event in anyone: no chest pain, no arm pain and
    no breathlessness. -/
theorem ruledOut_cardiac_noBreath (hc : M.RuledOut (M.has .chestPain) w)
    (ha : M.RuledOut (M.has .armPain) w)
    (hb : M.RuledOut (M.has .breathless) w) : M.RuledOut (M.cond .cardiac) w :=
  by intro v hv hx; have := M.cardiac_needs v hx; have := hc v hv; have := ha v hv; have := hb v hv; grind

/-- Ruling out meningitis: the patient is known to be at least one year old,
    and has no stiff neck, no headache and no confusion. (For infants there is no way to
    rule it out from symptoms.) -/
theorem ruledOut_meningitis (hage : M.Known (fun v => 12 ≤ M.ageMonths v) w)
    (hs : M.RuledOut (M.has .stiffNeck) w) (hh : M.RuledOut (M.has .headache) w)
    (hcf : M.RuledOut (M.has .confusion) w) : M.RuledOut (M.cond .meningitis) w :=
  by
    intro v hv hx; have := M.meningitis_needs v; have := hage v hv; have := hs v hv
    have := hh v hv; have := hcf v hv; grind

/-- Ruling out a serious infection in an infant: the patient is known to be
    at least 3 months old. -/
theorem ruledOut_seriousInfection_age (hage : M.Known (fun v => 3 ≤ M.ageMonths v) w) :
    M.RuledOut (M.cond .seriousInfection) w := by
  intro v hv hx
  have h1 := (M.seriousInfection_needs v hx).1
  have h2 : 3 ≤ M.ageMonths v := hage v hv
  omega

/-- Ruling out a serious infection in an infant: no fever. -/
theorem ruledOut_seriousInfection_noFever (hf : M.RuledOut (M.has .fever) w) :
    M.RuledOut (M.cond .seriousInfection) w :=
  fun v hv hx => hf v hv (M.seriousInfection_needs v hx).2

/-- No fever rules out any reading of 38.0 °C or more, so in particular
    any reading of 40.0 °C or more. -/
theorem noHighFever_of_noFever (hf : M.RuledOut (M.has .fever) w) :
    M.Known (fun v => M.tempTenths v < 400) w := fun v hv =>
  Nat.lt_of_not_le fun h => hf v hv (M.fever_of_temp v (Nat.le_trans (by decide) h))

/-- Knowing the patient is at least `a` months old means knowing they are at
    least `b` months old, for any `b ≤ a`. -/
theorem known_age_mono {a b : Nat} (hab : b ≤ a) (h : M.Known (fun v => a ≤ M.ageMonths v) w) :
    M.Known (fun v => b ≤ M.ageMonths v) w :=
  fun v hv => Nat.le_trans hab (h v hv)

/-- Ruling out pneumonia, first way (under 65 only): no fever. -/
theorem ruledOut_pneumonia_noFever (hyoung : M.Known (fun v => M.ageMonths v < 780) w)
    (hf : M.RuledOut (M.has .fever) w) : M.RuledOut (M.cond .pneumonia) w :=
  by intro v hv hx; have := M.pneumonia_needs v hx; have := hyoung v hv; have := hf v hv; grind

/-- Ruling out pneumonia, second way (any age): no cough, no breathlessness
    and no confusion. -/
theorem ruledOut_pneumonia_noCough (hc : M.RuledOut (M.has .cough) w)
    (hb : M.RuledOut (M.has .breathless) w) (hcf : M.RuledOut (M.has .confusion) w) :
    M.RuledOut (M.cond .pneumonia) w :=
  by
    intro v hv hx; have := M.pneumonia_needs v hx; have := hc v hv; have := hb v hv
    have := hcf v hv; simp_all

/-- "At least emergency" is just "emergency" (it's the top level). -/
theorem emergency_of_atLeast :
    M.Obligatory (M.SeeksAtLeast .emergency) w → M.Obligatory (M.seeks .emergency) w :=
  box_mono fun _ ⟨_, hu, hle⟩ => Urgency.eq_emergency hle ▸ hu

/-- If care at level `u0` or above is obligatory, every lower level is forbidden. -/
theorem forbidden_below {u u0 : Urgency} (hlt : u.rank < u0.rank) :
    M.Obligatory (M.SeeksAtLeast u0) w → M.Forbidden (M.seeks u) w := by
  intro ho v hv hs
  obtain ⟨u', hu', hle⟩ := ho v hv
  cases M.one_pathway v _ _ hs hu'
  omega

end
end TriageModel
end MediLean
