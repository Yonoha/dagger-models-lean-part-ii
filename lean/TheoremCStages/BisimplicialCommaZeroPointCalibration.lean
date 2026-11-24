import BisimplicialCommaParameterProjection
import SimplicialReplacementChosenHomotopyFiber

/-!
# Calibration of the chosen zero-simplex point

The chosen point in the complete comma parameter bar reconstructs the
literal constant outer point induced by its original zero-row simplex.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement)
open DaggerNativeSimplicialReplacementWeightsChange (changeWeights)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion constantChain)
open DaggerModels.PartII.SimplicialReplacementChosenHomotopyFiber

namespace DaggerModels.PartII.BisimplicialCommaZeroPointCalibration
noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- The unique outer degeneracy from the original zero row. -/
def zeroTo (q : SimplexCategoryᵒᵖ) : zero ⟶ q :=
  (SimplexCategory.isTerminalZero.from q.unop).op

theorem zeroTo_comp {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    zeroTo q ≫ α = zeroTo r := by
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.isTerminalZero.hom_ext _ _

theorem zeroTo_zero : zeroTo zero = 𝟙 zero := by
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.isTerminalZero.hom_ext _ _

/-- The original zero-row simplex extends coherently by every outer degeneracy. -/
def outerConstantPoint (B : BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ B.obj zero) : pointBi.{0} ⟶ B where
  app q := b ≫ B.map (zeroTo q)
  naturality {q r} α := by
    change 𝟙 (Δ[0] : SSet.{0}) ≫ (b ≫ B.map (zeroTo r)) =
      (b ≫ B.map (zeroTo q)) ≫ B.map α
    rw [Category.id_comp, Category.assoc, ← B.map_comp, zeroTo_comp α]

theorem outerConstantPoint_zero (B : BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ B.obj zero) :
    (outerConstantPoint B b).app zero = b := by
  change b ≫ B.map (zeroTo zero) = b
  rw [zeroTo_zero, B.map_id, Category.comp_id]

/-- The diagonal point is formed from the actual zero-row simplex and all
of its outer degeneracies, with the point-diagonal isomorphism explicit. -/
def diagonalPoint (B : BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ B.obj zero) :
    (Δ[0] : SSet.{0}) ⟶ diagonalFunctor.obj B :=
  pointDiagonalIso.inv ≫ diagonalFunctor.map (outerConstantPoint B b)

private theorem diagonalInclusion_changeWeights
    {C : Type} [SmallCategory C] {G H : C ⥤ SSet.{0}}
    (η : G ⟶ H) (c : C) :
    diagonalInclusion G c ≫ diagonalFunctor.map (changeWeights η) =
      η.app c ≫ diagonalInclusion H c := by
  apply NatTrans.ext
  funext q x
  rfl

private theorem pointBar_augments_to_point :
    diagonalInclusion pointBi.{0} zero ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation pointBi.{0}) =
      pointDiagonalIso.inv := by
  exact (SSet.stdSimplex.isTerminalObj₀.ofIso pointDiagonalIso.symm).hom_ext _ _

/-- In any bisimplicial base, the constant zero-row bar point maps to
the original diagonal point with all its outer degeneracies. -/
theorem constantBarPoint_reconstruction (B : BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ B.obj zero) :
    (b ≫ diagonalInclusion B zero) ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B) =
      diagonalPoint B b := by
  let η := outerConstantPoint B b
  have hη : η.app zero = b := outerConstantPoint_zero B b
  have hnat := BisimplicialRowBarAugmentation.augmentation_natural η
  calc
    (b ≫ diagonalInclusion B zero) ≫
        diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B) =
      (diagonalInclusion pointBi.{0} zero ≫
        diagonalFunctor.map (changeWeights η)) ≫
          diagonalFunctor.map (BisimplicialRowBarAugmentation.augmentation B) := by
        rw [diagonalInclusion_changeWeights η zero, hη]
    _ = diagonalInclusion pointBi.{0} zero ≫
          diagonalFunctor.map
            (changeWeights η ≫ BisimplicialRowBarAugmentation.augmentation B) := by
        rw [diagonalFunctor.map_comp]
        simp only [Category.assoc]
    _ = diagonalInclusion pointBi.{0} zero ≫
          diagonalFunctor.map
            (BisimplicialRowBarAugmentation.augmentation pointBi.{0} ≫ η) := by
        rw [hnat]
    _ = (diagonalInclusion pointBi.{0} zero ≫
          diagonalFunctor.map
            (BisimplicialRowBarAugmentation.augmentation pointBi.{0})) ≫
              diagonalFunctor.map η := by
        rw [diagonalFunctor.map_comp]
        simp only [Category.assoc]
    _ = diagonalPoint B b := by
        rw [pointBar_augments_to_point]
        rfl

/-- The complete comma parameter point retains precisely the original
zero-row simplex after passing to the row bar. -/
theorem zeroPoint_parameterBarMap (f : Arrow BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj zero) :
    BisimplicialCommaParameterProjection.zeroSimplexParameterPoint f zero b ≫
        diagonalFunctor.map
          (BisimplicialCommaDiagonalReconstruction.parameterBarMap f) =
      b ≫ diagonalInclusion f.right zero := by
  apply NatTrans.ext
  funext q x
  apply Sigma.ext
  · refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
    intro i j a
    rfl
  · exact HEq.rfl

/-- The chosen complete comma point reconstructs the literal original
diagonal point; the whole original map is unchanged. -/
theorem zeroPoint_baseReconstruction (f : Arrow BiSSet.{0})
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj zero) :
    BisimplicialCommaParameterProjection.zeroSimplexParameterPoint f zero b ≫
        diagonalFunctor.map
          (BisimplicialCommaDiagonalReconstruction.baseReconstruction f) =
      diagonalPoint f.right b := by
  calc
    _ = (BisimplicialCommaParameterProjection.zeroSimplexParameterPoint f zero b ≫
          diagonalFunctor.map
            (BisimplicialCommaDiagonalReconstruction.parameterBarMap f)) ≫
              diagonalFunctor.map
                (BisimplicialRowBarAugmentation.augmentation f.right) := by
        rw [BisimplicialCommaDiagonalReconstruction.baseReconstruction,
          diagonalFunctor.map_comp]
        simp only [Category.assoc]
    _ = (b ≫ diagonalInclusion f.right zero) ≫
          diagonalFunctor.map
            (BisimplicialRowBarAugmentation.augmentation f.right) := by
        rw [zeroPoint_parameterBarMap]
    _ = diagonalPoint f.right b := constantBarPoint_reconstruction f.right b

#print axioms zeroTo_comp
#print axioms outerConstantPoint
#print axioms constantBarPoint_reconstruction
#print axioms zeroPoint_parameterBarMap
#print axioms zeroPoint_baseReconstruction

end
end DaggerModels.PartII.BisimplicialCommaZeroPointCalibration
