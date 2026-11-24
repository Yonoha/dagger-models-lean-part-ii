import DaggerModelsPartII.LengthStageCellData
import DaggerModelsPartII.ReversalOuterFaceQuotient
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Local triviality of the actual length-cell boundary inclusion

The displayed indexed cell object is the categorical coproduct of its plain
and strict-orbit summands. This allows direct application of the model
category's closure of trivial cofibrations under coproducts.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.LengthCellLocality

open LengthStageAttaching PathOrbitCells ReversalOuterFaceSubobject
open ReversalOuterFaceAction C2InvolutionActions
open SegalLocalizers

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  injectiveSegalModel

private def indexedFamily {C : Type*} [Category C]
    (R S : Type 0) (F G : C ⥤ Type 0) :
    R ⊕ S → (C ⥤ Type 0)
  | .inl _ => F
  | .inr _ => G

private def indexedInclusion {C : Type*} [Category C]
    (R S : Type 0) (F G : C ⥤ Type 0) (j : R ⊕ S) :
    indexedFamily R S F G j ⟶ indexedCells R S F G := by
  cases j with
  | inl r =>
    exact { app := fun _ x => Sum.inl (r, x)
            naturality := by intros; rfl }
  | inr s =>
    exact { app := fun _ x => Sum.inr (s, x)
            naturality := by intros; rfl }

private def indexedCofan {C : Type*} [Category C]
    (R S : Type 0) (F G : C ⥤ Type 0) :
    Cofan (indexedFamily R S F G) :=
  Cofan.mk (indexedCells R S F G) (indexedInclusion R S F G)

private def indexedCofan_isColimit {C : Type*} [Category C]
    (R S : Type 0) (F G : C ⥤ Type 0) :
    IsColimit (indexedCofan R S F G) := by
  refine mkCofanColimit _
    (fun t => indexedCellsElim
      (fun r : R => t.inj (.inl r)) (fun s : S => t.inj (.inr s))) ?_ ?_
  · intro t j
    cases j with
    | inl r =>
      ext c x
      rfl
    | inr s =>
      ext c x
      rfl
  · intro t u hu
    ext c x
    rcases x with ⟨r, y⟩ | ⟨s, y⟩
    · have h := congrFun (NatTrans.congr_app (hu (.inl r)) c) y
      exact h
    · have h := congrFun (NatTrans.congr_app (hu (.inr s)) c) y
      exact h

private def indexedFamilyMap {C : Type*} [Category C]
    {R S : Type 0} {F G F' G' : C ⥤ Type 0}
    (α : F ⟶ F') (β : G ⟶ G') (j : R ⊕ S) :
    indexedFamily R S F G j ⟶ indexedFamily R S F' G' j := by
  cases j with
  | inl _ => exact α
  | inr _ => exact β

private theorem indexedInclusion_map {C : Type*} [Category C]
    {R S : Type 0} {F G F' G' : C ⥤ Type 0}
    (α : F ⟶ F') (β : G ⟶ G') (j : R ⊕ S) :
    indexedInclusion R S F G j ≫ indexedCellsMap α β =
      indexedFamilyMap α β j ≫ indexedInclusion R S F' G' j := by
  cases j with
  | inl r =>
    ext c x
    rfl
  | inr s =>
    ext c x
    rfl

private theorem discrete_indexedCellsMap_trivial
    {R S : Type 0}
    {F G F' G' : ReverseSimplexᵒᵖ ⥤ Type 0}
    (α : F ⟶ F') (β : G ⟶ G')
    (hα : (trivialCofibrations ReverseDaggerSpace.{0})
      (discreteDiagram.map α))
    (hβ : (trivialCofibrations ReverseDaggerSpace.{0})
      (discreteDiagram.map β)) :
    (trivialCofibrations ReverseDaggerSpace.{0})
      (discreteDiagram.map (indexedCellsMap (R := R) (S := S) α β)) := by
  let J := R ⊕ S
  let d : (ReverseSimplexᵒᵖ ⥤ Type 0) ⥤ ReverseDaggerSpace.{0} :=
    discreteDiagram
  haveI : PreservesColimitsOfShape (Discrete J)
      (SimplicialObject.const (Type 0)) := by
    change PreservesColimitsOfShape (Discrete J)
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ :
        Type 0 ⥤ (SimplexCategoryᵒᵖ ⥤ Type 0))
    infer_instance
  haveI : PreservesColimitsOfShape (Discrete J) d := by
    dsimp [d, discreteDiagram]
    infer_instance
  let c₁ := d.mapCocone (indexedCofan R S F G)
  let c₂ := d.mapCocone (indexedCofan R S F' G')
  have hc₁ : IsColimit c₁ := isColimitOfPreserves d (indexedCofan_isColimit R S F G)
  have hc₂ : IsColimit c₂ := isColimitOfPreserves d (indexedCofan_isColimit R S F' G')
  let f : (Discrete.functor (indexedFamily R S F G) ⋙ d) ⟶
      (Discrete.functor (indexedFamily R S F' G') ⋙ d) :=
    Discrete.natTrans (fun j => d.map (indexedFamilyMap α β j.as))
  have hf : (trivialCofibrations ReverseDaggerSpace.{0}).functorCategory
      (Discrete J) f := by
    rintro ⟨j⟩
    cases j with
    | inl _ =>
      change (trivialCofibrations ReverseDaggerSpace.{0}) (d.map α)
      exact hα
    | inr _ =>
      change (trivialCofibrations ReverseDaggerSpace.{0}) (d.map β)
      exact hβ
  have hcomm : ∀ j, c₁.ι.app j ≫ d.map (indexedCellsMap (R := R) (S := S) α β) =
      f.app j ≫ c₂.ι.app j := by
    intro j
    change d.map (indexedInclusion R S F G j.as) ≫
      d.map (indexedCellsMap (R := R) (S := S) α β) =
        d.map (indexedFamilyMap α β j.as) ≫
          d.map (indexedInclusion R S F' G' j.as)
    rw [← d.map_comp, ← d.map_comp, indexedInclusion_map]
  exact (MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := trivialCofibrations ReverseDaggerSpace.{0})
    _ _ c₁ c₂ hc₁ hc₂ f hf
    (d.map (indexedCellsMap (R := R) (S := S) α β)) hcomm)

/-- The actual indexed boundary inclusion for every length at least two is
a local trivial cofibration in the injective Segal model. -/
theorem boundaryToCell_localTrivial (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (discreteDiagram.map (boundaryToCell m ℓ (by omega))) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (discreteDiagram.map (boundaryToCell m ℓ (by omega))) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, ℓ = t + 2 := ⟨ℓ - 2, by omega⟩
  have hplain :=
    ReversalOuterFaceQuotient.discreteOuterFaceInclusion_localTrivial t
  have hquot :=
    ReversalOuterFaceQuotient.outerFaceStrictOrbitInclusion_localTrivial t
  have hα : (trivialCofibrations ReverseDaggerSpace.{0})
      (discreteDiagram.map (outerFaceSubpresheafAt (t + 2) (by omega)).ι) := by
    have hh : injectiveSegalModel.categoryWithCofibrations.cofibrations
          (discreteDiagram.map (outerFaceSubpresheafAt (t + 2) (by omega)).ι) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          (discreteDiagram.map (outerFaceSubpresheafAt (t + 2) (by omega)).ι) := by
      exact hplain
    exact hh
  have hβ : (trivialCofibrations ReverseDaggerSpace.{0})
      (discreteDiagram.map (boundaryOrbitTypeInclusion (t + 2) (by omega))) := by
    have hh : injectiveSegalModel.categoryWithCofibrations.cofibrations
          (discreteDiagram.map (boundaryOrbitTypeInclusion (t + 2) (by omega))) ∧
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
          (discreteDiagram.map (boundaryOrbitTypeInclusion (t + 2) (by omega))) := by
      exact hquot
    exact hh
  have h := discrete_indexedCellsMap_trivial
    (R := NonpalOrbit m (t + 2)) (S := PalOrbit m (t + 2))
    (outerFaceSubpresheafAt (t + 2) (by omega)).ι
    (boundaryOrbitTypeInclusion (t + 2) (by omega)) hα hβ
  change (trivialCofibrations ReverseDaggerSpace.{0})
    (discreteDiagram.map (boundaryToCell m (t + 2) (by omega))) at h
  exact h

end

end DaggerModels.PartII.LengthCellLocality
