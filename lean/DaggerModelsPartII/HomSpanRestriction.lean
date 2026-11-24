import DaggerModelsPartII.JTGraphCylinderSpanProjection
import DaggerModelsPartII.TotalElementsWeakComparison
import Mathlib.Data.Finite.Sigma

/-! Restrict the original hom-element spans along a diagram of simplices. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.HomSpanRestriction

variable {B D : Type} [SmallCategory B] [SmallCategory D]

/-- An object is an actual arrow, with arrows given by its factorizations. -/
abbrev Spans (B : Type) [SmallCategory B] := (Functor.hom B).Elementsᵒᵖ

/-- Apply the same functor to all three arrows of an actual factorization. -/
def map (F : B ⥤ D) : Spans B ⥤ Spans D :=
  (show (Functor.hom B).Elements ⥤ (Functor.hom D).Elements from {
    obj A := ⟨(op (F.obj A.fst.1.unop), F.obj A.fst.2), F.map A.snd⟩
    map f := CategoryOfElements.homMk _ _ (F.op.map f.val.1, F.map f.val.2) (by
      change F.map f.val.1.unop ≫ F.map _ ≫ F.map f.val.2 = _
      rw [← F.map_comp, ← F.map_comp]
      exact F.congr_map f.property)
    map_id A := by
      apply CategoryOfElements.ext
      exact Prod.ext (F.op.map_id A.fst.1) (F.map_id A.fst.2)
    map_comp f g := by
      apply CategoryOfElements.ext
      exact Prod.ext (F.op.map_comp f.val.1 g.val.1) (F.map_comp f.val.2 g.val.2) }).op

/-- The domain of the factored arrow, covariant in the opposite elements category. -/
abbrev smaller (B : Type) [SmallCategory B] : Spans B ⥤ B :=
  (CategoryOfElements.π (Functor.hom B) ⋙ CategoryTheory.Prod.fst Bᵒᵖ B).op ⋙ unopUnop B

theorem smaller_natural (F : B ⥤ D) :
    map F ⋙ smaller D = smaller B ⋙ F := rfl

theorem smaller_weak (B : Type) [SmallCategory B] : WeakEquivalence (nerveMap (smaller B)) := by
  let p := CategoryOfElements.π (Functor.hom B) ⋙ CategoryTheory.Prod.fst Bᵒᵖ B
  letI : WeakEquivalence (nerveMap p.op) := (TotalElementsWeakComparison.nerveMap_op_iff p).mpr
    (JTGraphCylinderSpanProjection.homElements_source_weak B)
  letI : WeakEquivalence (nerveMap (unopUnop B)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (nerveMap p.op ≫ nerveMap (unopUnop B))
  infer_instance

/-- The actual set of factorizations has finitely many objects when the
underlying category has finitely many objects and each hom type is finite. -/
theorem finite_objects (B : Type) [SmallCategory B] [Finite B]
    (h : ∀ a b : B, Finite (a ⟶ b)) : Finite (Spans B) := by
  letI (X : Bᵒᵖ × B) : Finite ((Functor.hom B).obj X) := h X.1.unop X.2
  letI : Finite Bᵒᵖ := Finite.of_injective (f := Opposite.unop) Opposite.unop_injective
  have hSigma : Finite (Σ X : Bᵒᵖ × B, (Functor.hom B).obj X) := inferInstance
  exact @Finite.of_injective (Spans B) (Σ X : Bᵒᵖ × B, (Functor.hom B).obj X) hSigma
    Opposite.unop Opposite.unop_injective

/-- Between any two of these objects there are only finitely many
commutative factorization operators. -/
theorem finite_hom (h : ∀ a b : B, Finite (a ⟶ b)) (s t : Spans B) :
    Finite (s ⟶ t) := by
  letI : Finite (s.unop.fst.1.unop ⟶ t.unop.fst.1.unop) := h _ _
  letI : Finite (t.unop.fst.2 ⟶ s.unop.fst.2) := h _ _
  apply Finite.of_injective (f := fun a : s ⟶ t ↦
    (a.unop.val.1.unop, a.unop.val.2))
  intro a b e
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  have e₁ : a.unop.val.1.unop = b.unop.val.1.unop :=
    congrArg (fun q ↦ q.1) e
  have e₂ : a.unop.val.2 = b.unop.val.2 := congrArg (fun q ↦ q.2) e
  exact Prod.ext (Quiver.Hom.unop_inj e₁) e₂

end DaggerModels.PartII.HomSpanRestriction
