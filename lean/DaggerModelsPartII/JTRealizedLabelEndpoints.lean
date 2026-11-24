import DaggerModelsPartII.JTNecklaceLabelRealization
import DaggerModelsPartII.JTProjectiveRealizationMappingWeak
import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.ActualUnitNativeComparison

/-!
# Full ordered endpoint calibration of the realized necklace label

For an actual ordered pullback label, the realized necklace label restricts at
both original endpoints to the corresponding raw zero-generator vertex on the
entire groupoid parameter `J[k]`. The endpoint restrictions use the general
simplicial naturality of realized labels because a single endpoint inclusion
need not be an endpoint-preserving necklace morphism.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerModels
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.OrderedNecklaceLabelDiagram
open DaggerModels.PartII.OrderedNecklaceVertexPoints
open DaggerModels.PartII.JTProjectiveOrderedFiberComparison
open DaggerModels.PartII.JTNecklaceLabelRealization

namespace DaggerModels.PartII.JTRealizedLabelEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev F := discreteFree.{0}
private abbrev R (W : Source) : SSet.{0} :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

/-- The actual first pullback projection of a fixed-boundary necklace label. -/
def orderedLabel (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (diagramMappingSpace (F.obj T.toSSet) W).obj (op k) :=
  (pullback.fst ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)).app (op k) z

/-- The unchanged original raw zero-generator vertex as a constant map on
all of `J[k]`, with the first projection preserving the parameter. -/
def constantRawEndpoint (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (k : SimplexCategory) :
    (Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj k ⟶ R W :=
  CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
      (GroupoidSimplex.parameter.obj k) ≫
    SSet.yonedaEquiv.symm
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)

/-- The actual native first endpoint, tensored with the identity on all of `J[k]`. -/
def firstTensor (T : NCode) (k : SimplexCategory) :
    (Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj k ⟶
      T.toSSet ⊗ GroupoidSimplex.parameter.obj k :=
  SSet.yonedaEquiv.symm T.first ⊗ₘ 𝟙 _

/-- The actual native last endpoint, tensored with the identity on all of `J[k]`. -/
def lastTensor (T : NCode) (k : SimplexCategory) :
    (Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj k ⟶
      T.toSSet ⊗ GroupoidSimplex.parameter.obj k :=
  SSet.yonedaEquiv.symm T.last ⊗ₘ 𝟙 _

private def zeroSimplex : (Δ[0] : SSet.{0}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)

/-- The zero label evaluated on the *actual* free-dagger-unit generator is
the original raw zero-row vertex. -/
theorem zeroLabel_on_freeUnit (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    ((zeroLabel W x).app (op (ReverseSimplex.inclusion.obj ⦋0⦌))).app
        (op ⦋0⦌)
        (((freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0})).app (op ⦋0⦌)
          zeroSimplex), zeroSimplex) = x := by
  change ((representableTensorHomFrom (ReverseSimplex.inclusion.obj ⦋0⦌)
      (vertexPoint W x ≫ (rowRestrictionIso W ⦋0⦌).hom)).app
        (op (ReverseSimplex.inclusion.obj ⦋0⦌))).app (op ⦋0⦌)
      (((SegalRepresentables.freeSimplexRepresentable 0).hom.app
        (op (ReverseSimplex.inclusion.obj ⦋0⦌))).app (op ⦋0⦌)
          ((freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0})).app (op ⦋0⦌)
            zeroSimplex), zeroSimplex) = x
  have hu :
      ((SegalRepresentables.freeSimplexRepresentable 0).hom.app
        (op (ReverseSimplex.inclusion.obj ⦋0⦌))).app (op ⦋0⦌)
          ((freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0})).app (op ⦋0⦌)
            zeroSimplex) =
        ULift.up (𝟙 (ReverseSimplex.inclusion.obj ⦋0⦌)) := by
    simpa [zeroSimplex] using
      (ActualUnitNativeComparison.freeSimplexRepresentable_unit_id 0 (op ⦋0⦌))
  rw [hu]
  simp [representableTensorHomFrom, vertexPoint, rowRestrictionIso,
    zeroSimplex]

/-- The actual raw zero-generator map is constant across the entire zero
groupoid parameter, via the specified terminal section. -/
theorem constantRawEndpoint_zero_generator (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    constantRawEndpoint W x ⦋0⦌ =
      JTRealizationGenerators.generator (JTReversalInput.ordinaryInput.obj W)
        (⦋0⦌, ⦋0⦌) x := by
  change CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫
      SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv
          (JTGtildeOrderedFiberAction.zeroTensorVertex ≫
            JTRealizationGenerators.generator
              (JTReversalInput.ordinaryInput.obj W) (⦋0⦌, ⦋0⦌) x)) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc,
    JTGtildeOrderedFiberAction.fst_zeroTensorVertex, Category.id_comp]

/-- The label of the original raw vertex realizes to its literal zero
coend generator, with no replacement of the target or chosen point. -/
theorem realizedZeroLabel (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    realizedLabel (Δ[0] : SSet.{0}) W ⦋0⦌ (zeroLabel W x) =
      constantRawEndpoint W x ⦋0⦌ := by
  have hf := realizedLabel_generator_formula (Δ[0] : SSet.{0}) W
    ⦋0⦌ ⦋0⦌ ⦋0⦌ (zeroLabel W x) zeroSimplex zeroSimplex
  rw [zeroLabel_on_freeUnit] at hf
  have hzero :
      (SSet.yonedaEquiv.symm zeroSimplex ⊗ₘ
        GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv zeroSimplex)) =
      𝟙 ((Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj ⦋0⦌) := by
    have hvertex : SSet.yonedaEquiv.symm zeroSimplex =
        𝟙 (Δ[0] : SSet.{0}) := by
      apply SSet.yonedaEquiv.injective
      rfl
    rw [hvertex]
    have hindex : SSet.stdSimplex.objEquiv zeroSimplex = 𝟙 ⦋0⦌ := by
      simp [zeroSimplex]
    rw [hindex, GroupoidSimplex.parameter.map_id]
    exact tensorHom_id _ _
  rw [hzero, Category.id_comp] at hf
  rw [constantRawEndpoint_zero_generator]
  exact hf

/-- Every simplex of the original zero-point map is the same zero label
restricted along the unique map to the zero simplex. -/
theorem zeroPoint_label (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (k : SimplexCategory)
    (t : (Δ[0] : SSet.{0}).obj (op k)) :
    (zeroPoint W x).app (op k) t =
      (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map
        (SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from k)) ≫
          zeroLabel W x := by
  let σ := SimplexCategory.isTerminalZero.from k
  have ht : t = (Δ[0] : SSet.{0}).map σ.op zeroSimplex := by
    apply SSet.stdSimplex.objEquiv.injective
    exact SimplexCategory.isTerminalZero.hom_ext _ _
  rw [ht]
  have h := congrFun ((zeroPoint W x).naturality σ.op) zeroSimplex
  change (zeroPoint W x).app (op k)
      ((Δ[0] : SSet.{0}).map σ.op zeroSimplex) =
    (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map
      (SSet.stdSimplex.map σ) ≫ zeroLabel W x at h
  exact h

/-- The entire `J[k]`-family of a zero-point label is constant at the
unchanged original raw zero-generator vertex. -/
theorem realizedZeroPoint_family (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) (k : SimplexCategory)
    (t : (Δ[0] : SSet.{0}).obj (op k)) :
    realizedLabel (Δ[0] : SSet.{0}) W k ((zeroPoint W x).app (op k) t) =
      constantRawEndpoint W x k := by
  let σ := SimplexCategory.isTerminalZero.from k
  rw [zeroPoint_label W x k t]
  rw [← realizedLabel_natural_k (Δ[0] : SSet.{0}) W σ (zeroLabel W x)]
  rw [realizedZeroLabel]
  change (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ GroupoidSimplex.parameter.map σ) ≫
      (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫
          SSet.yonedaEquiv.symm
            (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)) =
      constantRawEndpoint W x k
  rw [← Category.assoc]
  exact congrArg
    (fun h : ((Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj k) ⟶
      (Δ[0] : SSet.{0}) ↦
        h ≫ SSet.yonedaEquiv.symm
          (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The first endpoint restriction of an actual ordered pullback label is
the specified zero-point label in the same inner simplex degree. -/
theorem orderedLabel_first (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.first)) W).app
        (op k) (orderedLabel W x y T k z) =
      (zeroPoint W x).app (op k)
        ((pullback.snd ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y)).app (op k) z) := by
  let b := boundaryPoint W x y
  let r := (necklaceBoundaryRestriction W).app (op T)
  let η := orderedLabel W x y T k z
  let ζ := (pullback.snd r b).app (op k) z
  have hpmap : pullback.fst r b ≫ r = pullback.snd r b ≫ b := pullback.condition
  have hp := congrFun (NatTrans.congr_app hpmap (op k)) z
  change (r.app (op k)) η = (b.app (op k)) ζ at hp
  have hh := congrArg
    (fun a ↦ (diagramMappingPrecomp
      (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W).app (op k) a) hp
  have hleg :
      (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundaryNecklace T = F.map (SSet.yonedaEquiv.symm T.first) := by
    simp only [boundaryNecklace, coprod.inl_desc]
  have hcomp :
      r ≫ diagramMappingPrecomp
          (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
        diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.first)) W := by
    change diagramMappingPrecomp (boundaryNecklace T) W ≫
      diagramMappingPrecomp coprod.inl W = _
    rw [← diagramMappingPrecomp_comp, hleg]
  change (r ≫ diagramMappingPrecomp coprod.inl W).app (op k) η =
    (b ≫ diagramMappingPrecomp coprod.inl W).app (op k) ζ at hh
  rw [hcomp, boundaryPoint_first W x y] at hh
  exact hh

/-- The last endpoint restriction of an actual ordered pullback label is
the specified second zero-point label in the same inner simplex degree. -/
theorem orderedLabel_last (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.last)) W).app
        (op k) (orderedLabel W x y T k z) =
      (zeroPoint W y).app (op k)
        ((pullback.snd ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y)).app (op k) z) := by
  let b := boundaryPoint W x y
  let r := (necklaceBoundaryRestriction W).app (op T)
  let η := orderedLabel W x y T k z
  let ζ := (pullback.snd r b).app (op k) z
  have hpmap : pullback.fst r b ≫ r = pullback.snd r b ≫ b := pullback.condition
  have hp := congrFun (NatTrans.congr_app hpmap (op k)) z
  change (r.app (op k)) η = (b.app (op k)) ζ at hp
  have hh := congrArg
    (fun a ↦ (diagramMappingPrecomp
      (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W).app (op k) a) hp
  have hleg :
      (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundaryNecklace T = F.map (SSet.yonedaEquiv.symm T.last) := by
    simp only [boundaryNecklace, coprod.inr_desc]
  have hcomp :
      r ≫ diagramMappingPrecomp
          (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
        diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.last)) W := by
    change diagramMappingPrecomp (boundaryNecklace T) W ≫
      diagramMappingPrecomp coprod.inr W = _
    rw [← diagramMappingPrecomp_comp, hleg]
  change (r ≫ diagramMappingPrecomp coprod.inr W).app (op k) η =
    (b ≫ diagramMappingPrecomp coprod.inr W).app (op k) ζ at hh
  rw [hcomp, boundaryPoint_last W x y] at hh
  exact hh

/-- The realized ordered necklace label has the original first raw vertex
as its constant endpoint on the entire `J[k]` parameter. -/
theorem realizedNecklaceLabel_first (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    firstTensor T k ≫
        realizedNecklaceLabel T W k (orderedLabel W x y T k z) =
      constantRawEndpoint W x k := by
  let η := orderedLabel W x y T k z
  let t := (pullback.snd ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)).app (op k) z
  have hn := realizedLabel_natural_X (SSet.yonedaEquiv.symm T.first) W k η
  change firstTensor T k ≫ realizedNecklaceLabel T W k η =
    realizedLabel (Δ[0] : SSet.{0}) W k
      ((diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.first)) W).app
        (op k) η) at hn
  rw [orderedLabel_first W x y T k z] at hn
  exact hn.trans (realizedZeroPoint_family W x k t)

/-- The realized ordered necklace label has the original last raw vertex
as its constant endpoint on the entire `J[k]` parameter. -/
theorem realizedNecklaceLabel_last (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    lastTensor T k ≫
        realizedNecklaceLabel T W k (orderedLabel W x y T k z) =
      constantRawEndpoint W y k := by
  let η := orderedLabel W x y T k z
  let t := (pullback.snd ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)).app (op k) z
  have hn := realizedLabel_natural_X (SSet.yonedaEquiv.symm T.last) W k η
  change lastTensor T k ≫ realizedNecklaceLabel T W k η =
    realizedLabel (Δ[0] : SSet.{0}) W k
      ((diagramMappingPrecomp (F.map (SSet.yonedaEquiv.symm T.last)) W).app
        (op k) η) at hn
  rw [orderedLabel_last W x y T k z] at hn
  exact hn.trans (realizedZeroPoint_family W y k t)

end
end DaggerModels.PartII.JTRealizedLabelEndpoints
