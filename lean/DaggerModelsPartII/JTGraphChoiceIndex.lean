import DaggerModelsPartII.JTFiniteCoefficientBridgeTime
import DaggerModelsPartII.JTSemiSimplexElementsWeak
import DaggerModelsPartII.SimplicialResolutionFunctor

/-! Semisimplicial families of choices and the exact whole-copy time functor. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphChoiceIndex

noncomputable section

private abbrev choiceSpace (C : Type) :=
  DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj C
private abbrev choices (C : Type) :=
  SemiSimplexCategory.toSimplexCategory.op ⋙ choiceSpace C

/-- A simplex of graph choices, with injective face operators only. -/
abbrev Index (C : Type) := (choices C).Elementsᵒᵖ

/-- Include a prescribed nonempty ordered family in the category of choices. -/
def ofFamily {C : Type} {k : ℕ} (f : Fin (k + 1) → C) : Index C :=
  op ⟨op ⦋k⦌ₛ, Codiscrete.functor f⟩

/-- The exact inclusion of a nonempty ordered subfamily of the given choices. -/
def ofFamily_face {C : Type} {k l : ℕ} (a : ⦋k⦌ₛ ⟶ ⦋l⦌ₛ) (f : Fin (l + 1) → C) :
    ofFamily (fun i ↦ f ((SemiSimplexCategory.homEquiv a) i)) ⟶ ofFamily f := by
  apply Quiver.Hom.op
  exact ⟨a.op, rfl⟩

theorem ofFamily_face_id {C : Type} {k : ℕ} (f : Fin (k + 1) → C) :
    ofFamily_face (𝟙 ⦋k⦌ₛ) f = 𝟙 (ofFamily f) := rfl

theorem ofFamily_face_comp {C : Type} {k l m : ℕ}
    (a : ⦋k⦌ₛ ⟶ ⦋l⦌ₛ) (b : ⦋l⦌ₛ ⟶ ⦋m⦌ₛ) (f : Fin (m + 1) → C) :
    ofFamily_face a (fun i ↦ f ((SemiSimplexCategory.homEquiv b) i)) ≫ ofFamily_face b f =
      ofFamily_face (a ≫ b) f := rfl

/-- The original phase simplex underlying a graph-choice simplex. -/
def phase (C : Type) : Index C ⥤ SimplexCategory :=
  (CategoryOfElements.π (choices C)).leftOp ⋙
    SemiSimplexCategory.toSimplexCategory

/-- Read the graph choice at a specified phase vertex. -/
def vertex {C : Type} (i : Index C)
    (v : Fin (((phase C).obj i).len + 1)) : C :=
  ((i.unop.2).obj v).as

/-- The category-of-elements equation is the exact proper-face equation. -/
theorem vertex_map {C : Type} {i j : Index C} (f : i ⟶ j)
    (v : Fin (((phase C).obj i).len + 1)) :
    vertex i v = vertex j (((phase C).map f).toOrderHom v) := by
  exact congrArg (fun z : (choiceSpace C).obj (op ((phase C).obj i)) ↦ (z.obj v).as)
    f.unop.property.symm

theorem phase_injective {C : Type} {i j : Index C} (f : i ⟶ j) :
    Function.Injective ((phase C).map f).toOrderHom :=
  (SemiSimplexCategory.homEquiv f.unop.val.unop).injective

/-- Lexicographic copies of one external time simplex, one for each phase vertex. -/
def time (C : Type) (n : SimplexCategory) : Index C ⥤ SimplexCategory where
  obj i := JTFiniteCoefficientBridgeTime.time
    (((CategoryOfElements.π (choices C)).leftOp.obj i).1) n
  map f := JTFiniteCoefficientBridgeTime.mapCopies ((phase C).map f) (phase_injective f) n
  map_id i := by
    ext v : 3
    obtain ⟨x, rfl⟩ := (JTFiniteCoefficientBridgeTime.timeVertexEquiv
      (((CategoryOfElements.π (choices C)).leftOp.obj i).1) n).surjective v
    have H := JTFiniteCoefficientBridgeTime.mapCopies_vertex
      ((phase C).map (𝟙 i)) (phase_injective (𝟙 i)) n x
    rw [H]
    rw [(phase C).map_id]
    rfl
  map_comp f g := by
    ext v : 3
    obtain ⟨x, rfl⟩ := (JTFiniteCoefficientBridgeTime.timeVertexEquiv
      (((CategoryOfElements.π (choices C)).leftOp.obj _).1) n).surjective v
    have H₀ := JTFiniteCoefficientBridgeTime.mapCopies_vertex
      ((phase C).map (f ≫ g)) (phase_injective (f ≫ g)) n x
    have H₁ := JTFiniteCoefficientBridgeTime.mapCopies_vertex
      ((phase C).map f) (phase_injective f) n x
    have H₂ := JTFiniteCoefficientBridgeTime.mapCopies_vertex
      ((phase C).map g) (phase_injective g) n
        (((phase C).map f).toOrderHom x.1, x.2)
    rw [H₀]
    change _ = (JTFiniteCoefficientBridgeTime.mapCopies ((phase C).map g)
      (phase_injective g) n).toOrderHom
        ((JTFiniteCoefficientBridgeTime.mapCopies ((phase C).map f)
          (phase_injective f) n).toOrderHom
            (JTFiniteCoefficientBridgeTime.timeVertexEquiv _ n x))
    rw [H₁]
    have hc := SimplexCategory.congr_toOrderHom_apply ((phase C).map_comp f g) x.1
    exact (congrArg (fun y ↦
      JTFiniteCoefficientBridgeTime.timeVertexEquiv _ n (y, x.2)) hc).trans H₂.symm

/-- Every phase-face arrow acts by the exact whole-copy inclusion. -/
theorem time_map {C : Type} (n : SimplexCategory) {i j : Index C} (f : i ⟶ j) :
    (time C n).map f =
      JTFiniteCoefficientBridgeTime.mapCopies ((phase C).map f) (phase_injective f) n := rfl

/-- A nonempty codiscrete choice set has a weakly contractible exact
semisimplicial category of graph choices. -/
theorem index_point_GW (C : Type) [Nonempty C] :
    GW (pointMap (nerve (Index C))) := by
  let X := choiceSpace C
  let p := pointMap X
  have ht := DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration p pointIsTerminal
  haveI : WeakEquivalence p := ((mem_trivialFibrations_iff _).mp ht).2
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  haveI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  haveI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  let q := pointMap (nerve X.Elementsᵒᵖ)
  have h : e ≫ q = a ≫ p := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence q := by
    apply (weakEquivalence_precomp_iff e q).mp
    rw [h]
    infer_instance
  let F := JTSemiSimplexElementsWeak.elementForget X
  haveI : WeakEquivalence (nerveMap F) :=
    JTSemiSimplexElementsWeak.elementForget_weakEquivalence X
  have hF : nerveMap F ≫ q = pointMap (nerve (Index C)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← hF]
  infer_instance

end
end DaggerModels.PartII.JTGraphChoiceIndex
