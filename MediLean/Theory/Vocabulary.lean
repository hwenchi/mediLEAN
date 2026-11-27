/-
  THEORY: vocabulary. The symptoms and conditions the premises talk about.
  Grows by adding constructors.
-/
import MediLean.Core.Urgency

namespace MediLean

inductive Symptom
  | chestPain | armPain | fever | stiffNeck | headache | cough | soreThroat | breathless
  deriving DecidableEq, Repr

inductive Condition
  | cardiac | meningitis | pneumonia | viral
  deriving DecidableEq, Repr

def Condition.all : List Condition := [.cardiac, .meningitis, .pneumonia, .viral]

theorem Condition.mem_all (c : Condition) : c ∈ Condition.all := by cases c <;> decide

end MediLean
