import DaggerModelsPartII.JTConstantOrderedLabel
import DaggerModelsPartII.JTConstantOrderedLabelDiagram
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! A constant ordered coefficient does not constrain its groupoid parameter. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointTraceObstruction

open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints
open JTProjectiveOrderedFiberComparison (row)
open JTRealizedLabelEndpoints JTNecklaceLabelRealization
open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev F := discreteFree.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev terminal := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (z : Vertex W) (T : NecklaceCode) (k : SimplexCategory)

private def zero : (Δ[0] : SSet.{0}).obj (op k) :=
  SSet.yonedaEquiv (terminal (std.obj k))

private theorem constant_label_as_zero :
    orderedLabel W z z T k (JTConstantOrderedLabel.constantLabel W z T k) =
      (diagramMappingPrecomp (F.map (terminal T.toSSet)) W).app (op k)
        ((zeroPoint W z).app (op k) (zero k)) := by
  have h := congrArg SSet.yonedaEquiv
    (JTConstantOrderedLabel.coefficient_constantLabel W z T k)
  simp only [JTOrderedLabelBinaryGlue.coefficient, Equiv.apply_symm_apply,
    JTConstantOrderedLabel.constantCoefficient, SSet.yonedaEquiv_comp] at h
  exact h

/-- The full product realization of a constant ordered label is the raw
zero vertex, regardless of the groupoid parameter. -/
theorem constant_realizeProduct (p : T.toSSet ⊗ J.obj k ⟶ J.obj k) :
    JTBinaryPrismRealization.realizeProduct W k p
      (orderedLabel W z z T k (JTConstantOrderedLabel.constantLabel W z T k)) =
        fst T.toSSet (J.obj k) ≫ terminal T.toSSet ≫
          SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [JTBinaryPrismRealization.realizeProduct]
  rw [constant_label_as_zero]
  have h := realizedLabel_natural_X (terminal T.toSSet) W k
    ((zeroPoint W z).app (op k) (zero k))
  rw [realizedZeroPoint_family] at h
  change (terminal T.toSSet ⊗ₘ 𝟙 (J.obj k)) ≫
      (fst (Δ[0] : SSet.{0}) (J.obj k) ≫
        SSet.yonedaEquiv.symm (rawVertex W z)) = _ at h
  rw [← Category.assoc, tensorHom_fst, Category.assoc] at h
  change fst T.toSSet (J.obj k) ≫ terminal T.toSSet ≫
      SSet.yonedaEquiv.symm (rawVertex W z) =
    realizedLabel T.toSSet W k
      ((diagramMappingPrecomp (F.map (terminal T.toSSet)) W).app (op k)
        ((zeroPoint W z).app (op k) (zero k))) at h
  rw [← h]
  simp only [← Category.assoc]
  rw [lift_fst]

private theorem constant_realizedLabel :
    realizedNecklaceLabel T W k
      (orderedLabel W z z T k (JTConstantOrderedLabel.constantLabel W z T k)) =
        fst T.toSSet (J.obj k) ≫ terminal T.toSSet ≫
          SSet.yonedaEquiv.symm (rawVertex W z) := by
  have h := constant_realizeProduct W z T k (snd T.toSSet (J.obj k))
  simpa only [JTBinaryPrismRealization.realizeProduct, lift_fst_snd,
    Category.id_comp] using h

private theorem constant_rawBoundary :
    rawBoundary W z z = endpointInclusion T ≫ terminal T.toSSet ≫
      SSet.yonedaEquiv.symm (rawVertex W z) := by
  apply SSet.boundary₁.hom_ext
  · change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc (rawVertex W z) (rawVertex W z) =
      (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last) ≫
        terminal T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)
    rw [SSet.boundary₁.ι₀_desc, SSet.boundary₁.ι₀_desc]
    have ht : SSet.yonedaEquiv.symm T.first ≫ terminal T.toSSet =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, ht, Category.id_comp]
  · change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc (rawVertex W z) (rawVertex W z) =
      (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last) ≫
        terminal T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)
    rw [SSet.boundary₁.ι₁_desc, SSet.boundary₁.ι₁_desc]
    have ht : SSet.yonedaEquiv.symm T.last ≫ terminal T.toSSet =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, ht, Category.id_comp]

/-- The entire reduced cylinder descends to the same raw zero vertex. -/
theorem constant_descend :
    descend W z z T k (JTConstantOrderedLabel.constantLabel W z T k) =
      augmentation T k ≫ terminal T.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W z) := by
  apply (isPushout T k).hom_ext
  · rw [← Category.assoc, descend_cylinder, constant_realizedLabel,
      ← Category.assoc, augmentation_cylinder]
    simp only [Category.assoc]
  · rw [← Category.assoc, descend_boundary, constant_rawBoundary W z T,
      ← Category.assoc, augmentation_boundary]
    simp only [Category.assoc]

private theorem cylinderMap_augmentation (n : SimplexCategory)
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    JTInterpolatedReducedCylinder.cylinderMap T p ≫ augmentation T k =
      augmentation T n := by
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_cylinder,
      Category.assoc, augmentation_cylinder, augmentation_cylinder]
    simp only [lift_fst]
  · rw [← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_boundary,
      augmentation_boundary, augmentation_boundary]

/-- The exact raw equation on the whole reduced cylinder for any time and
any groupoid parameter carried by the constant ordered label. -/
theorem constant_raw (n : SimplexCategory)
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (JTParametrizedTargetLiftTransport.graph
      (i := JTConstantOrderedLabel.constantIndex W z T k) (m := n) p).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W z z).app
        (JTConstantOrderedLabel.constantIndex W z T k)).right =
      augmentation T n ≫ terminal T.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W z) := by
  change JTInterpolatedReducedCylinder.cylinderMap T p ≫
    descend W z z T k (JTConstantOrderedLabel.constantLabel W z T k) = _
  rw [constant_descend W z T k, ← Category.assoc, cylinderMap_augmentation T k n p]

/-- The raw equation in the exact form of the `Family.raw` field, over the
literal point necklace at the original raw vertex. -/
theorem constant_raw_overPoint (n : SimplexCategory)
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (JTParametrizedTargetLiftTransport.graph
      (i := JTConstantOrderedLabel.constantIndex W z T k) (m := n) p).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W z z).app
        (JTConstantOrderedLabel.constantIndex W z T k)).right =
      augmentation T n ≫ (JTOrderedLabelJointInsertion.toPoint T).map ≫
        (NecklacesOver.point (rawVertex W z)).map := by
  have h : (JTOrderedLabelJointInsertion.toPoint T).map = terminal T.toSSet :=
    JTOrderedLabelJointInsertion.pointIsTerminal.hom_ext _ _
  rw [h]
  exact constant_raw W z T k n p

end

end DaggerModels.PartII.JTJointTraceObstruction
