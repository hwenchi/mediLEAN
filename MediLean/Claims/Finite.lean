/-
  CLAIMS, INFRASTRUCTURE: finite test models.

  A test model has finitely many worlds, so every premise, and every claim
  about a specific world, is a finite check that `decide` settles. Building
  a model therefore *checks* that it satisfies all the premises: if a
  premise is added or changed, any test model that violates it stops
  building.

  When a premise is added to `TriageModel`, add its name to `finite_model%`.
-/
import MediLean.Theory.Rules

namespace MediLean

/-! ### Finite enumeration and decidability -/

class Enum (α : Type) where
  all : List α
  complete : ∀ a, a ∈ all

instance {α : Type} [Enum α] (p : α → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ (Enum.all : List α), p a)
    ⟨fun h a => h a (Enum.complete a), fun h a _ => h a⟩

instance {α : Type} [Enum α] (p : α → Prop) [DecidablePred p] : Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ (Enum.all : List α), p a)
    ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Enum.complete a, h⟩⟩

instance : Enum Unit := ⟨[()], fun () => by decide⟩
instance : Enum Bool := ⟨[false, true], fun b => by cases b <;> decide⟩
instance : Enum Urgency := ⟨Urgency.all, Urgency.mem_all⟩

instance {α β : Type} [Enum α] [Enum β] : Enum (α × β) where
  all := (Enum.all : List α).flatMap fun a => (Enum.all : List β).map fun b => (a, b)
  complete := fun ⟨a, b⟩ =>
    List.mem_flatMap.2 ⟨a, Enum.complete a, List.mem_map.2 ⟨b, Enum.complete b, rfl⟩⟩

instance {W : Type} [Enum W] {R : W → W → Prop} [∀ a b, Decidable (R a b)]
    {P : W → Prop} [DecidablePred P] {w : W} : Decidable (Box R P w) := by
  unfold Box; infer_instance

instance {W : Type} [Enum W] {R : W → W → Prop} [∀ a b, Decidable (R a b)]
    {P : W → Prop} [DecidablePred P] {w : W} : Decidable (Diamond R P w) := by
  unfold Diamond; infer_instance

instance {W : Type} [Enum W] {R : W → W → Prop} [∀ a b, Decidable (R a b)]
    {P : W → Prop} [DecidablePred P] {w : W} : Decidable (BoxNot R P w) := by
  unfold BoxNot Box; infer_instance

/-! ### Building test models -/

/-- A finite test model. Every frame law and every premise is discharged by
    `decide`, so a model that breaks any premise fails to build. -/
macro "finite_model%" W:term:max compat:term:max later:term:max ideal:term:max
    has:term:max cond:term:max seeks:term:max age:term:max temp:term:max
    diab:term:max fem:term:max cdays:term:max : term =>
  `(({ W := $W, compat := $compat, later := $later, ideal := $ideal,
       has := $has, cond := $cond, seeks := $seeks,
       ageMonths := $age, tempTenths := $temp, diabetic := $diab, female := $fem,
       coughDays := $cdays, cough_of_days := by decide,
       fever_of_temp := by decide,
       compat_refl := by decide, compat_trans := by decide,
       later_refl := by decide, later_trans := by decide,
       ideal_serial := by decide,
       redflag_cardiac := by decide, redflag_meningitis := by decide,
       redflag_pneumonia := by decide, redflag_viral := by decide,
       redflag_meningitis_headache := by decide, redflag_pneumonia_older := by decide,
       redflag_meningitis_confusion := by decide,
       redflag_infant_fever := by decide, seriousInfection_needs := by decide,
       cardiac_needs := by decide, meningitis_needs := by decide,
       pneumonia_needs := by decide, viral_needs := by decide,
       caution_cardiac := by decide, caution_meningitis := by decide,
       caution_pneumonia := by decide, caution_seriousInfection := by decide,
       caution_highFever := by decide, caution_persistentCough := by decide,
       permit_seeDoctor := by decide,
       permit_selfCare := by decide, permit_urgentCare := by decide,
       one_pathway := by decide } : TriageModel))

/-- One fully known situation: patient age (months), temperature reading
    (tenths of °C, 0 = none), diabetic?, female?, the symptoms `S`, the
    conditions `C`, and the care level `need` that the guideline-compliant
    options must meet. Worlds are the four care pathways the patient could take. -/
macro "patient%" age:term:max temp:term:max diab:term:max fem:term:max
    S:term:max C:term:max need:term:max : term =>
  `(finite_model% (Unit × Urgency)
      (fun _ _ => True) (fun _ _ => True)
      (fun _ b => $need ≤ Urgency.rank b.2)
      (fun s _ => s ∈ ($S : List Symptom)) (fun c _ => c ∈ ($C : List Condition))
      (fun u w => w.2 = u) (fun _ => $age) (fun _ => $temp)
      (fun _ => $diab) (fun _ => $fem) (fun _ => 0))

/-- A 30-year-old man without diabetes whose cough has lasted `days` days. -/
macro "coughFor%" days:term:max S:term:max C:term:max need:term:max : term =>
  `(finite_model% (Unit × Urgency)
      (fun _ _ => True) (fun _ _ => True)
      (fun _ b => $need ≤ Urgency.rank b.2)
      (fun s _ => s ∈ ($S : List Symptom)) (fun c _ => c ∈ ($C : List Condition))
      (fun u w => w.2 = u) (fun _ => 360) (fun _ => 0)
      (fun _ => False) (fun _ => False) (fun _ => $days))

/-- A man without diabetes, of the given age and temperature reading. -/
macro "situationAt%" age:term:max temp:term:max S:term:max C:term:max need:term:max : term =>
  `(patient% $age $temp False False $S $C $need)

/-- A 30-year-old man without diabetes, with no temperature reading. -/
macro "situation%" S:term:max C:term:max need:term:max : term =>
  `(situationAt% 360 0 $S $C $need)

end MediLean
