/-
  §1 Core operators: necessity and possibility over any relation,
  written once and shared by every modality.
-/
namespace MediLean

def Box {W : Type} (R : W → W → Prop) (P : W → Prop) : W → Prop :=
  fun w => ∀ v, R w v → P v

def Diamond {W : Type} (R : W → W → Prop) (P : W → Prop) : W → Prop :=
  fun w => ∃ v, R w v ∧ P v

/-- Necessarily not: `P` fails in every related world. -/
abbrev BoxNot {W : Type} (R : W → W → Prop) (P : W → Prop) : W → Prop :=
  Box R (fun v => ¬ P v)

section
variable {W : Type} {R : W → W → Prop} {P Q : W → Prop} {w : W}

/-- K: necessity distributes over implication (holds in every frame). -/
theorem box_K : Box R (fun v => P v → Q v) w → Box R P w → Box R Q w :=
  fun hpq hp v hv => hpq v hv (hp v hv)

/-- Necessity is monotone. -/
theorem box_mono (h : ∀ v, P v → Q v) : Box R P w → Box R Q w :=
  fun hp v hv => h v (hp v hv)

/-- Possibility is monotone. -/
theorem diamond_mono (h : ∀ v, P v → Q v) : Diamond R P w → Diamond R Q w :=
  fun ⟨v, hv, hp⟩ => ⟨v, hv, h v hp⟩

/-- Duality: possible P iff not necessarily not-P. -/
theorem diamond_iff_not_box_not : Diamond R P w ↔ ¬ Box R (fun v => ¬ P v) w := by
  constructor
  · rintro ⟨v, hv, hp⟩ hb
    exact hb v hv hp
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h fun v hv hp => hn ⟨v, hv, hp⟩

end
end MediLean
