import DaggerModelsPartII.JTRelativeLabelPrismRaw

/-! Full raw equations for relative label families with arbitrary simplicial time. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTRelativeFamilyPrismRaw

open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels)
open JTConstantOrderedLabel (constantCoefficient)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (z : Vertex W) (T : NecklaceCode)
variable {s k d : SimplexCategory} (u : s ⟶ k) [Mono u] (α : d ⟶ k)
variable (hα : Function.Surjective α.toOrderHom)
variable {V : SSet.{0}} (H : std.obj k ⊗ V ⟶ labels W T)
variable (hstationary : (std.map u ▷ V) ≫ H =
  fst (std.obj s) V ≫ constantCoefficient W z T s)
variable (t : std.obj d ⟶ V)

/-- Restrict a full relative family along a coefficient chain and arbitrary time map. -/
def chainCoefficient : std.obj d ⟶ labels W T :=
  lift (std.map α) t ≫ H

private abbrev face := JTOrdinalFaceInverseImage.ordinal u α
private abbrev faceIncl := JTOrdinalFaceInverseImage.incl u α hα
private abbrev faceToOld := JTOrdinalFaceInverseImage.toFace u α hα
  (SimplexCategory.mono_iff_injective.mp ‹Mono u›)

include hstationary in
/-- The full inverse image remains constant for every higher family parameter. -/
theorem chainCoefficient_onFace :
    std.map (faceIncl u α hα) ≫
        chainCoefficient W T α H t =
      constantCoefficient W z T (face u α) := by
  have hface := JTOrdinalFaceInverseImage.toFace_fac u α hα
    (SimplexCategory.mono_iff_injective.mp ‹Mono u›)
  have hp : std.map (faceIncl u α hα) ≫
      lift (std.map α) t =
    lift (std.map (faceToOld u α hα))
      (std.map (faceIncl u α hα) ≫ t) ≫
      (std.map u ▷ V) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerRight_fst, lift_fst, lift_fst_assoc,
        ← std.map_comp, hface]
    · simp only [Category.assoc, whiskerRight_snd, lift_snd]
  unfold chainCoefficient
  rw [← Category.assoc, hp, Category.assoc, hstationary,
    ← Category.assoc, lift_fst]
  exact (JTConstantOrderedLabel.constantCoefficient_ordinal W z T
    (faceToOld u α hα)).symm

variable {X : SSet.{0}} (h : X ⟶ T.toSSet) (θ : X ⟶ J.obj d)
variable (q : X ⟶ J.obj s)

include hα hstationary in
/-- A graph with supported old parameter retains the literal joint raw point,
including simultaneous homotopy time and all higher choice parameters. -/
theorem chain_raw (hθ : θ ≫ J.map α = q ≫ J.map u) :
    lift h θ ≫ realizedLabel T.toSSet W d
        (SSet.yonedaEquiv (chainCoefficient W T α H t)) =
      h ≫ term T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  let q' := JTOrdinalFaceParameterPullback.factor u α hα θ q hθ
  have hq : q' ≫ J.map (faceIncl u α hα) = θ :=
    JTOrdinalFaceParameterPullback.factor_incl u α hα θ q hθ
  rw [← hq]
  rw [JTWhiskerEdgeGraphRaw.coefficient_reindex]
  rw [chainCoefficient_onFace W z T u α hα H hstationary t]
  have hr := JTComposedPrismLabels.rawProduct_constant W z T
    (snd T.toSSet (J.obj (face u α)))
  dsimp only [JTComposedPrismLabels.rawProduct,
    JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr, lift_fst_assoc]

end
end DaggerModels.PartII.JTRelativeFamilyPrismRaw
