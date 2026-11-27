/-
  FIXED CORE: the care scale.

  Every version of the theory grades care on these four ordered levels.
-/
import MediLean.Core.Frame

namespace MediLean

inductive Urgency
  | selfCare | seeDoctor | urgentCare | emergency
  deriving DecidableEq, Repr

/-- Urgency levels are ordered: seeking a higher level satisfies a lower need. -/
def Urgency.rank : Urgency → Nat
  | .selfCare => 0 | .seeDoctor => 1 | .urgentCare => 2 | .emergency => 3

def Urgency.all : List Urgency := [.selfCare, .seeDoctor, .urgentCare, .emergency]

theorem Urgency.mem_all (u : Urgency) : u ∈ Urgency.all := by cases u <;> decide

theorem Urgency.rank_le_three (u : Urgency) : u.rank ≤ 3 := by cases u <;> decide

theorem Urgency.eq_emergency {u : Urgency} (h : Urgency.emergency.rank ≤ u.rank) :
    u = .emergency := by
  cases u <;> first | rfl | (revert h; decide)

/-- Seeking care at level `u0` or higher. -/
abbrev SeeksAtLeast {W : Type} (seeks : Urgency → W → Prop) (u0 : Urgency) : W → Prop :=
  fun v => ∃ u, seeks u v ∧ u0.rank ≤ u.rank

end MediLean
