import BisimplicialRowBarZeroAugmentation
import BisimplicialCommaDiagonalReconstruction
import BisimplicialCommaParameterProjection

/-!
# Exact total reconstruction on the original zero-row fiber

The reconstruction acts on a whole source simplicial set by the original
pullback projection and all original outer degeneracies.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)

namespace DaggerModels.PartII.BisimplicialCommaZeroTotalReconstruction

open BisimplicialBaseSimplexFibers (fiberDiagram)
open BisimplicialCommaDiagonalReconstruction
open BisimplicialCommaParameterProjection (zeroSimplexIndex)
open BisimplicialRowBarZeroAugmentation

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- Every map out of a constant outer diagram is the original degeneracy extension. -/
theorem outerConstantValue_eq {A : SSet.{0}} {B : BiSSet.{0}}
    (η : constantBi A ⟶ B) : outerConstantValue B (η.app zero) = η := by
  apply NatTrans.ext
  funext q
  have h := η.naturality (BisimplicialCommaZeroPointCalibration.zeroTo q)
  change 𝟙 A ≫ η.app q =
    η.app zero ≫ B.map (BisimplicialCommaZeroPointCalibration.zeroTo q) at h
  change η.app zero ≫ B.map (BisimplicialCommaZeroPointCalibration.zeroTo q) = η.app q
  simpa only [Category.id_comp] using h.symm

/-- The whole comma fiber at the chosen zero row enters the original row bar
by its actual total-coordinate projection. -/
theorem zeroFiber_totalBarMap (f : Arrow BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj zero) :
    diagonalInclusion (fiberDiagram f) (zeroSimplexIndex f zero b) ≫
        diagonalFunctor.map (BisimplicialCommaBarReconstruction.totalBarMap f) =
      pullback.fst (f.hom.app zero) b ≫ diagonalInclusion f.left zero := by
  apply NatTrans.ext
  funext q x
  apply Sigma.ext
  · refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
    intro i j a
    rfl
  · exact HEq.rfl

/-- With an arbitrary whole source, reconstruction is precisely the original
zero-row total map extended by every outer degeneracy. -/
theorem zeroFiber_totalReconstruction {A : SSet.{0}} (f : Arrow BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj zero)
    (c : A ⟶ (fiberDiagram f).obj (zeroSimplexIndex f zero b)) :
    (c ≫ diagonalInclusion (fiberDiagram f) (zeroSimplexIndex f zero b)) ≫
        diagonalFunctor.map (totalReconstruction f) =
      (constantDiagonalIso A).inv ≫ diagonalFunctor.map
        (outerConstantValue f.left (c ≫ pullback.fst (f.hom.app zero) b)) := by
  have h := zeroFiber_totalBarMap f b
  calc
    _ = ((c ≫ diagonalInclusion (fiberDiagram f) (zeroSimplexIndex f zero b)) ≫
          diagonalFunctor.map (BisimplicialCommaBarReconstruction.totalBarMap f)) ≫
            diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation f.left) := by
      rw [totalReconstruction, diagonalFunctor.map_comp]
      simp only [Category.assoc]
    _ = ((c ≫ pullback.fst (f.hom.app zero) b) ≫
          diagonalInclusion f.left zero) ≫
            diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation f.left) := by
      simpa only [Category.assoc] using congrArg
        (fun m ↦ (c ≫ m) ≫
          diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation f.left)) h
    _ = _ := zeroInclusion_reconstruction f.left _

#print axioms outerConstantValue_eq
#print axioms zeroFiber_totalBarMap
#print axioms zeroFiber_totalReconstruction

end

end DaggerModels.PartII.BisimplicialCommaZeroTotalReconstruction
