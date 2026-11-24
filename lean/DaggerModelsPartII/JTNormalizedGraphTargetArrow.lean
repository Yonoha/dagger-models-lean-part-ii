import DaggerModelsPartII.JTRowGraphCommonCoefficientComparison
import DaggerModelsPartII.JTMixedGraphRawRefinement
import DaggerModelsPartII.JTGraphRefinementParameterArrow
import OriginalFlagNormalizedBeads

/-! Exact target-comma arrows induced by reindexing normalized graphs. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNormalizedGraphTargetArrow

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTRowGraphFiber JTRowGraphNormalizationDiagram
open JTMixedGraphRawRefinement JTGraphRefinement JTGraphRefinementParameterArrow
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev nativeMap (q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)) :=
  (singleIso d).hom ≫ q

include hx in
private theorem nativeMap_first :
    (nativeMap q).app (op ⦋0⦌) (single d).first = rawVertex W x := by
  rw [← hx, SSet.yonedaEquiv_comp]
  change q.app _ ((singleIso d).hom.app _ (single d).first) = _
  rw [singleIso_first, vertex, SSet.stdSimplex.yonedaEquiv_map]
  rfl

include hy in
private theorem nativeMap_last :
    (nativeMap q).app (op ⦋0⦌) (single d).last = rawVertex W y := by
  rw [← hy, SSet.yonedaEquiv_comp]
  change q.app _ ((singleIso d).hom.app _ (single d).last) = _
  rw [singleIso_last, vertex, SSet.stdSimplex.yonedaEquiv_map]
  rfl

/-- The fixed raw simplex with its original ordered endpoints. -/
def target : NecklacesOver (realization.obj (ordinaryInput.obj W))
    (rawVertex W x) (rawVertex W y) where
  code := single d
  map := nativeMap q
  first := nativeMap_first hx
  last := nativeMap_last hy

private abbrev coefficient (G : Fiber q) :
    (SSet.stdSimplex.{0}.obj G.obj.degree) ⟶ row W ⦋d⦌ :=
  SSet.yonedaEquiv.symm G.obj.coefficient

private theorem raw_eq (G : Fiber q) :
    rawGraph W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter = q := by
  unfold rawGraph
  rw [Equiv.apply_symm_apply]
  exact G.property

/-- A normalization vertex specifies a graph refinement over the exact
fixed target, with the given endpoint families. -/
def refinement (G : Fiber q) (v : ((diagram hx hy).obj (op G)).obj (op ⦋0⦌)) :
    Refinement W x y (target hx hy) :=
  refinementOfGraph (familiesAtZero hx hy G v)
    (congrArg (fun a ↦ (singleIso d).hom ≫ a) (raw_eq G))
    (nativeMap_first hx) (nativeMap_last hy)

private theorem refinement_eq {Q : NecklacesOver (realization.obj (ordinaryInput.obj W))
    (rawVertex W x) (rawVertex W y)}
    (T : NecklaceCode) (k : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj (op T)).obj (op k))
    {s s' : T.toSSet ⟶ GroupoidSimplex.parameter.obj k} (h : s = s')
    (c : T ⟶ Q.code)
    (p : realizeGraph W k s (JTRealizedLabelEndpoints.orderedLabel W x y T k z) =
      c.map ≫ Q.map)
    (p' : realizeGraph W k s' (JTRealizedLabelEndpoints.orderedLabel W x y T k z) =
      c.map ≫ Q.map) :
    (⟨T, k, z, s, c, p⟩ : Refinement W x y Q) = ⟨T, k, z, s', c, p'⟩ := by
  cases h
  rfl

set_option maxHeartbeats 1000000 in
/-- Reindexing an exact normalization gives an arrow of the actual fixed-target
comma category, with the literal coefficient operator. -/
def reindexArrow {G H : Fiber q} (u : G ⟶ H)
    (v : ((diagram hx hy).obj (op H)).obj (op ⦋0⦌)) :
    (refinement hx hy G (((diagram hx hy).map u.op).app _ v)).toComma ⟶
      (refinement hx hy H v).toComma := by
  let a := refinement hx hy G (((diagram hx hy).map u.op).app _ v)
  let b := refinement hx hy H v
  let j := u.hom.operator
  have hlabel : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj (op a.code)).map
        j.op b.label = a.label := (normalizedLabel_reindex hx hy u v).symm
  have hparam : a.parameter ≫ GroupoidSimplex.parameter.map j = b.parameter :=
    JTRowGraphCommonCoefficientComparison.nativeGraphParameter_arrow u
  have h : extendDegree a j b.label hlabel = b :=
    refinement_eq a.code b.degree b.label hparam a.collapse _ _
  exact toCommaArrow a j b.label hlabel ≫
    eqToHom (congrArg (fun z : Refinement W x y (target hx hy) ↦ z.toComma) h)

end

end DaggerModels.PartII.JTNormalizedGraphTargetArrow
