import DaggerModelsPartII.JTHigherGraphExtensionComma
import DaggerModelsPartII.JTFixedLiftSpaceInterleavedTrivialFibration
import OriginalSimplicialTrivialFibrationTensor

/-!
# The paired enlargement space projects by a Kan trivial fibration
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHigherGraphExtensionTrivialFibration

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTOrdinaryGraphNormalizationSpace JTEndpointNormalizationLifts
open JTHigherGraphExtensionComma JTFixedLiftSpaceInterleaved
open JTFixedLiftSpaceInterleavedProjection JTFixedLiftSpaceInterleavedTrivialFibration
open DaggerOriginalSimplicialTrivialFibrationTensor

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W y)

private abbrev ls := leftSquare W ⦋d⦌ k f s x hx
private abbrev rs := rightSquare W ⦋d⦌ k f s y hy

private def choicesTensor :
    choices f s hx hy ≅ extensionSpace (ls f s hx) ⊗ extensionSpace (rs f s hy) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def fstChoice : choices f s hx hy ⟶ extensionSpace (ls f s hx) where
  app _ := Prod.fst
  naturality := by intros; rfl

private def sndChoice : choices f s hx hy ⟶ extensionSpace (rs f s hy) where
  app _ := Prod.snd
  naturality := by intros; rfl

private def choicesProduct :
    choices f s hx hy ≅ extensionSpace (ls f s hx) ⨯ extensionSpace (rs f s hy) :=
  choicesTensor f s hx hy ≪≫ tensorProductIso _ _

private theorem choicesProduct_fst :
    (choicesProduct f s hx hy).hom ≫ prod.fst = fstChoice f s hx hy := by
  rw [choicesProduct, Iso.trans_hom, Category.assoc, tensorProductIso_fst]
  rfl

private theorem choicesProduct_snd :
    (choicesProduct f s hx hy).hom ≫ prod.snd = sndChoice f s hx hy := by
  rw [choicesProduct, Iso.trans_hom, Category.assoc, tensorProductIso_snd]
  rfl

/-- The original paired projection is a trivial fibration for each
fixed graph and both original ordered endpoints. -/
theorem forgetChoices_trivialFibration [Fibration (endpointArrow W)] :
    trivialFibrations SSet.{0} (forgetChoices f s hx hy) := by
  let p₁ := projection (ls f s hx)
  let p₂ := projection (rs f s hy)
  have h : forgetChoices f s hx hy = (choicesProduct f s hx hy).hom ≫ prod.map p₁ p₂ := by
    apply prod.hom_ext
    · change prod.lift (fstChoice f s hx hy ≫ p₁) (sndChoice f s hx hy ≫ p₂) ≫ prod.fst = _
      calc
        _ = fstChoice f s hx hy ≫ p₁ := prod.lift_fst _ _
        _ = ((choicesProduct f s hx hy).hom ≫ prod.fst) ≫ p₁ := by
          rw [choicesProduct_fst]
        _ = _ := by
          rw [Category.assoc, ← prod.map_fst p₁ p₂, ← Category.assoc]
          rfl
    · change prod.lift (fstChoice f s hx hy ≫ p₁) (sndChoice f s hx hy ≫ p₂) ≫ prod.snd = _
      calc
        _ = sndChoice f s hx hy ≫ p₂ := prod.lift_snd _ _
        _ = ((choicesProduct f s hx hy).hom ≫ prod.snd) ≫ p₂ := by
          rw [choicesProduct_snd]
        _ = _ := by
          rw [Category.assoc, ← prod.map_snd p₁ p₂, ← Category.assoc]
          rfl
  have h₁ : trivialFibrations SSet.{0} p₁ := projection_trivialFibration (ls f s hx)
  have h₂ : trivialFibrations SSet.{0} p₂ := projection_trivialFibration (rs f s hy)
  rw [h]
  exact (trivialFibrations SSet.{0}).comp_mem _ _
    ((trivialFibrations SSet.{0}).of_isIso _) (prodMap_trivialFibration p₁ p₂ h₁ h₂)

end

end DaggerModels.PartII.JTHigherGraphExtensionTrivialFibration
