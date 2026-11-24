import OriginalQuillenAProjectionsReconciledRecovered
import NativeSimplicialReplacement
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# The original Theorem A comparison is the actual comma-weight replacement

The retained fixed-degree column isomorphisms are made natural in every
target-chain operator. The resulting full diagonal augmentation to the nerve
of the original source is weak without a comma-contractibility hypothesis.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.TheoremAReplacementComparison

noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

/-- Mathlib's actual covariant comma functor, followed by the original nerve. -/
def commaNerves : D ⥤ SSet.{u} := CostructuredArrow.functor F ⋙ nerveFunctor

/-- The retained original comparison column at each target-chain degree. -/
def columnIso (q : SimplexCategoryᵒᵖ) :
    (DaggerNerveTheoremA.comparison F).flip.obj q ≅ (replacement (commaNerves F)).obj q :=
  DaggerNerveTheoremA.columnFamilyIso F q

/-- The fixed-degree isomorphism respects EVERY target-chain operator. -/
theorem columnIso_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (DaggerNerveTheoremA.comparison F).flip.map α ≫ (columnIso F r).hom =
      (columnIso F q).hom ≫ (replacement (commaNerves F)).map α := by
  apply NatTrans.ext
  funext k x
  change DaggerNerveTheoremA.columnToFamily F k r
      (DaggerNerveTheoremA.Cell.map F (𝟙 k) α x) =
    horizontal (commaNerves F) α k (DaggerNerveTheoremA.columnToFamily F k q x)
  change (⟨(nerve D).map α x.target,
      DaggerNerveTheoremA.cellCommaChain F (DaggerNerveTheoremA.Cell.map F (𝟙 k) α x)⟩ :
      (DaggerOriginalProductGadget.familySSet (DaggerNerveTheoremA.columnFamily F r)).obj k) =
    ⟨(nerve D).map α x.target,
      DaggerNerveTheoremA.cellCommaChain F x ⋙
        CostructuredArrow.map (initialArrow α x.target)⟩
  apply congrArg (fun t ↦ (⟨(nerve D).map α x.target, t⟩ :
    (DaggerOriginalProductGadget.familySSet (DaggerNerveTheoremA.columnFamily F r)).obj k))
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj =>
    intro i
    dsimp [DaggerNerveTheoremA.cellCommaChain, DaggerNerveTheoremA.Cell.map]
    congr 1
    simp only [initialArrow, Category.assoc]
    rw [x.source.map_id]
    change F.map (x.source.map (homOfLE (Fin.le_last i))) ≫
        F.map (𝟙 _) ≫ x.bridge ≫ initialArrow α x.target =
      F.map (x.source.map (homOfLE (Fin.le_last i))) ≫ x.bridge ≫ initialArrow α x.target
    rw [F.map_id, Category.id_comp]
  case h_map =>
    intro i j f
    apply CostructuredArrow.hom_ext
    simp [DaggerNerveTheoremA.cellCommaChain, DaggerNerveTheoremA.Cell.map,
      CostructuredArrow.eqToHom_left]
    rfl

/-- The FULL original bisimplicial comparison is the actual comma-weight replacement. -/
def comparisonIso :
    (DaggerNerveTheoremA.comparison F).flip ≅ replacement (commaNerves F) :=
  NatIso.ofComponents (columnIso F) (by intro q r α; exact columnIso_natural F α)

/-- The exact diagonal isomorphism, retaining both whole operator directions. -/
def diagonalIso : DaggerBisimplicialDiagonal.diag (replacement (commaNerves F)) ≅
    DaggerBisimplicialDiagonal.diag (DaggerNerveTheoremA.comparison F) :=
  (DaggerBisimplicialDiagonal.diagonalFunctor.mapIso (comparisonIso F)).symm ≪≫
    DaggerBisimplicialDiagonal.diagFlipIso (DaggerNerveTheoremA.comparison F)

/-- The entire actual comma replacement augments to the original source nerve. -/
def augmentation : DaggerBisimplicialDiagonal.diag (replacement (commaNerves F)) ⟶
    nerve C :=
  (diagonalIso F).hom ≫ DaggerNerveTheoremA.sourceDiagonal F

/-- The actual augmentation is Kan weak without fiber contractibility or fibrancy. -/
theorem augmentation_weak : WeakEquivalence (augmentation F) := by
  have : WeakEquivalence (DaggerNerveTheoremA.sourceDiagonal F) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerNerveTheoremA.sourceDiagonal_GW F)
  change WeakEquivalence ((diagonalIso F).hom ≫ DaggerNerveTheoremA.sourceDiagonal F)
  infer_instance

end

end DaggerModels.PartII.TheoremAReplacementComparison
