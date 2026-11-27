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

/-- Ruling out a cardiac event: no chest pain and no arm pain. -/
theorem ruledOut_cardiac (hc : M.RuledOut (M.has .chestPain) w)
    (ha : M.RuledOut (M.has .armPain) w) : M.RuledOut (M.cond .cardiac) w :=
  by intro v hv hx; have := M.cardiac_needs v hx; have := hc v hv; have := ha v hv; simp_all

/-- Ruling out meningitis: no stiff neck and no headache. -/
theorem ruledOut_meningitis (hs : M.RuledOut (M.has .stiffNeck) w)
    (hh : M.RuledOut (M.has .headache) w) : M.RuledOut (M.cond .meningitis) w :=
  by intro v hv hx; have := M.meningitis_needs v hx; have := hs v hv; have := hh v hv; simp_all

/-- Ruling out pneumonia, first way: no fever. -/
theorem ruledOut_pneumonia_noFever (hf : M.RuledOut (M.has .fever) w) :
    M.RuledOut (M.cond .pneumonia) w :=
  by intro v hv hx; have := M.pneumonia_needs v hx; have := hf v hv; simp_all

/-- Ruling out pneumonia, second way: no cough and no breathlessness. -/
theorem ruledOut_pneumonia_noCough (hc : M.RuledOut (M.has .cough) w)
    (hb : M.RuledOut (M.has .breathless) w) : M.RuledOut (M.cond .pneumonia) w :=
  by intro v hv hx; have := M.pneumonia_needs v hx; have := hc v hv; have := hb v hv; simp_all

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
