import BisimplicialCommaZeroPointCalibration

/-!
# Zero-row values under the original row-bar augmentation

The source is an arbitrary original simplicial set, not just a vertex.
The equality retains every outer degeneracy of the original zero row.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacementWeightsChange (changeWeights)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)

namespace DaggerModels.PartII.BisimplicialRowBarZeroAugmentation

open BisimplicialCommaZeroPointCalibration (zeroTo zeroTo_comp)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- The original simplicial set placed in every outer degree. -/
def constantBi (A : SSet.{0}) : BiSSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj A

/-- The diagonal retains the complete original inner simplicial set. -/
def constantDiagonalIso (A : SSet.{0}) : diagonalFunctor.obj (constantBi A) ≅ A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The zero-chain inclusion augments by the identity on every original value. -/
theorem constant_augmentation (A : SSet.{0}) :
    diagonalInclusion (constantBi A) zero ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation (constantBi A)) =
      (constantDiagonalIso A).inv := by
  apply NatTrans.ext
  funext q x
  rfl

/-- A whole zero-row map extends by all actual outer degeneracies. -/
def outerConstantValue {A : SSet.{0}} (B : BiSSet.{0}) (a : A ⟶ B.obj zero) :
    constantBi A ⟶ B where
  app q := a ≫ B.map (zeroTo q)
  naturality {q r} α := by
    change 𝟙 A ≫ (a ≫ B.map (zeroTo r)) =
      (a ≫ B.map (zeroTo q)) ≫ B.map α
    rw [Category.id_comp, Category.assoc, ← B.map_comp, zeroTo_comp α]

/-- The original whole value in the zero row reconstructs with its exact degeneracies. -/
theorem zeroInclusion_reconstruction {A : SSet.{0}}
    (B : BiSSet.{0}) (a : A ⟶ B.obj zero) :
    (a ≫ diagonalInclusion B zero) ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B) =
      (constantDiagonalIso A).inv ≫ diagonalFunctor.map (outerConstantValue B a) := by
  let η := outerConstantValue B a
  have hη : η.app zero = a := by
    change a ≫ B.map (zeroTo zero) = a
    rw [BisimplicialCommaZeroPointCalibration.zeroTo_zero, B.map_id, Category.comp_id]
  have hincl : diagonalInclusion (constantBi A) zero ≫
      diagonalFunctor.map (changeWeights η) = a ≫ diagonalInclusion B zero := by
    rw [← hη]
    apply NatTrans.ext
    funext q x
    rfl
  have hnat := BisimplicialRowBarAugmentation.augmentation_natural η
  calc
    _ = (diagonalInclusion (constantBi A) zero ≫
          diagonalFunctor.map (changeWeights η)) ≫
            diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B) :=
      congrArg (fun m ↦ m ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B)) hincl.symm
    _ = diagonalInclusion (constantBi A) zero ≫ diagonalFunctor.map
          (changeWeights η ≫ BisimplicialRowBarAugmentation.augmentation B) := by
      rw [diagonalFunctor.map_comp]
      simp only [Category.assoc]
    _ = diagonalInclusion (constantBi A) zero ≫ diagonalFunctor.map
          (BisimplicialRowBarAugmentation.augmentation (constantBi A) ≫ η) :=
      congrArg (fun m ↦ diagonalInclusion (constantBi A) zero ≫ diagonalFunctor.map m) hnat
    _ = (diagonalInclusion (constantBi A) zero ≫
          diagonalFunctor.map
            (BisimplicialRowBarAugmentation.augmentation (constantBi A))) ≫
              diagonalFunctor.map η := by
      rw [diagonalFunctor.map_comp]
      simp only [Category.assoc]
    _ = _ := congrArg (fun m ↦ m ≫ diagonalFunctor.map η) (constant_augmentation A)

#print axioms constant_augmentation
#print axioms zeroInclusion_reconstruction

end

end DaggerModels.PartII.BisimplicialRowBarZeroAugmentation
