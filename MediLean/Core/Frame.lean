/-
  §2 Frames, §3 Vocabulary, §4 Laws.
-/
import MediLean.Core.Modal

namespace MediLean

/-- Worlds are complete possible situations; three relations, three modalities. -/
structure ModalFrame where
  W      : Type
  compat : W → W → Prop   -- epistemic: consistent with what the user confirmed
  later  : W → W → Prop   -- temporal: now or a later state
  ideal  : W → W → Prop   -- deontic: guideline-compliant alternatives

structure AdvisoryFrame extends ModalFrame where
  compat_refl  : ∀ w, compat w w                             -- T: confirmed facts are true
  compat_trans : ∀ u v w, compat u v → compat v w → compat u w -- 4: added in step 6 (C14)
  later_refl   : ∀ w, later w w                              -- S4: later includes now
  later_trans  : ∀ u v w, later u v → later v w → later u w  -- S4: later than later is later
  ideal_serial : ∀ w, ∃ v, ideal w v                         -- D: guidelines never demand the impossible

namespace AdvisoryFrame

/-! §3 Vocabulary -/
section
variable (M : AdvisoryFrame)

abbrev Known      := Box M.compat
abbrev Possible   := Diamond M.compat
abbrev Always     := Box M.later
abbrev Eventually := Diamond M.later
abbrev Obligatory := Box M.ideal
abbrev Permitted  := Diamond M.ideal
abbrev RuledOut  (P : M.W → Prop) : M.W → Prop := Box M.compat (fun v => ¬ P v)
abbrev Forbidden (P : M.W → Prop) : M.W → Prop := Box M.ideal  (fun v => ¬ P v)
end

/-! §4 Laws, proved once from the frame conditions. -/
section
variable {M : AdvisoryFrame} {P : M.W → Prop} {w : M.W}

/-- T for knowledge: what is known is true. -/
theorem known_T : M.Known P w → P w :=
  fun h => h w (M.compat_refl w)

/-- T for time: what always holds holds now. -/
theorem always_T : M.Always P w → P w :=
  fun h => h w (M.later_refl w)

/-- 4 for time: always implies always-always. -/
theorem always_4 : M.Always P w → M.Always (M.Always P) w :=
  fun h _ hv _ hu => h _ (M.later_trans _ _ _ hv hu)

/-- D: what is obligatory is permitted. -/
theorem obligatory_D : M.Obligatory P w → M.Permitted P w := by
  intro h
  obtain ⟨v, hv⟩ := M.ideal_serial w
  exact ⟨v, hv, h v hv⟩

/-- Nothing is both obligatory and forbidden (consequence of D). -/
theorem not_obligatory_and_forbidden : ¬ (M.Obligatory P w ∧ M.Forbidden P w) := by
  rintro ⟨ho, hf⟩
  obtain ⟨v, hv⟩ := M.ideal_serial w
  exact hf v hv (ho v hv)

/-- What is possible has not been ruled out. -/
theorem possible_not_ruledOut : M.Possible P w → ¬ M.RuledOut P w :=
  fun ⟨v, hv, hp⟩ hr => hr v hv hp

/-- Known facts are possible (T makes the epistemic relation non-empty). -/
theorem known_possible : M.Known P w → M.Possible P w :=
  fun h => ⟨w, M.compat_refl w, h w (M.compat_refl w)⟩

/-- 4 for possibility: what might possibly be, might be. Needs `compat_trans`. -/
theorem possible_4 : M.Possible (M.Possible P) w → M.Possible P w :=
  fun ⟨_, hv, _, hx, hp⟩ => ⟨_, M.compat_trans _ _ _ hv hx, hp⟩

/-- A known fact holds alongside anything possible. -/
theorem known_possible_and {Q : M.W → Prop} :
    M.Known P w → M.Possible Q w → M.Possible (fun v => P v ∧ Q v) w :=
  fun hp ⟨v, hv, hq⟩ => ⟨v, hv, hp v hv, hq⟩

/-- Contradictory confirmations are impossible (by T). If the interface let
    a user confirm both P and ¬P, every claim would hold vacuously. -/
theorem known_consistent : M.Known P w → M.RuledOut P w → False :=
  fun hp hn => hn w (M.compat_refl w) (hp w (M.compat_refl w))

end
end AdvisoryFrame
end MediLean
