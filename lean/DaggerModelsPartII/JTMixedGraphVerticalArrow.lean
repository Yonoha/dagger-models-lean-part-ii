import DaggerModelsPartII.JTRowGraphRelations
import DaggerModelsPartII.JTGraphRefinementParameterArrow
import DaggerModelsPartII.JTMixedGraphEdgeFamilyExtension
import DaggerModelsPartII.JTMixedGraphRawRefinement

/-!
# A vertical coend step lifts to an actual target-comma arrow

Choose the endpoint families on the larger coefficient and restrict them
along the same operator on the smaller graph. This retains the two complete
ordered labels, the full traversal, and the unchanged collapse to the
specified native target.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphVerticalArrow

open OrdinaryJTRealization JTRealizationGenerators JTReversalInput
open JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement JTMixedGraphEdgeFamilyReindex
open JTGraphRefinement JTGraphRefinementParameterArrow
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {k l : SimplexCategory}
variable (j : k ⟶ l) (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)

theorem nativeRawGraph_reindex :
    nativeRawGraph W d k (SSet.stdSimplex.map j ≫ f) s =
      nativeRawGraph W d l f (s ≫ J.map j) := by
  let w := SSet.yonedaEquiv f
  have h := (JTRowGraphRelations.Step.along (W := ordinaryInput.obj W) (d := ⦋d⦌) j w s).value_eq
  have hw : (ordinaryInput.obj W).map
      (show (⦋d⦌, k) ⟶ (⦋d⦌, l) from (𝟙 ⦋d⦌, j)).op w =
      SSet.yonedaEquiv (SSet.stdSimplex.map j ≫ f) := by
    change (row W ⦋d⦌).map j.op w = _
    rw [SSet.yonedaEquiv_map_comp]
  unfold nativeRawGraph
  congr 1
  change _ ≫ generator (ordinaryInput.obj W) (⦋d⦌, k)
      ((ordinaryInput.obj W).map
        (show (⦋d⦌, k) ⟶ (⦋d⦌, l) from (𝟙 ⦋d⦌, j)).op w) =
    _ ≫ generator (ordinaryInput.obj W) (⦋d⦌, l) w at h
  rw [hw] at h
  exact h

variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (e : EdgeFamilies W ⦋d⦌ l f (s ≫ J.map j) x y)
variable {q : (single d).toSSet ⟶ R W}
variable (hmap : nativeRawGraph W d l f (s ≫ J.map j) = q)
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev small := refinementOfGraph (restrictEdgeFamilies j f s e)
  ((nativeRawGraph_reindex j f s).trans hmap) qx qy

private abbrev large := refinementOfGraph e hmap qx qy

/-- An elementary vertical coend relation is represented by a morphism of
the two normalized decorated-cylinder presentations over the same target,
when the smaller endpoint families are the restrictions of the larger ones. -/
def verticalArrow :
    (small j f s e hmap qx qy).toComma ⟶ (large j f s e hmap qx qy).toComma := by
  let D := small j f s e hmap qx qy
  let E := large j f s e hmap qx qy
  let u := JTMixedGraphOrderedLabel.orderedPoint e
  have hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label := (orderedPoint_reindex j f s e).symm
  have hE : extendDegree D j u hu = E := by
    dsimp only [D, E, small, large, extendDegree, refinementOfGraph, u]
    simp only [nativeGraphParameter_map]
  exact toCommaArrow D j u hu ≫ eqToHom (congrArg Refinement.toComma hE)

/-- For an injective operator, any given small-side normalization extends
to a larger normalization along an actual arrow of the same target comma. -/
theorem exists_verticalArrow_from
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    [Mono j] (D : EdgeFamilies W ⦋d⦌ k (SSet.stdSimplex.map j ≫ f) s x y) :
    ∃ E : EdgeFamilies W ⦋d⦌ l f (s ≫ J.map j) x y,
      Nonempty ((refinementOfGraph D ((nativeRawGraph_reindex j f s).trans hmap)
        qx qy).toComma ⟶ (large j f s E hmap qx qy).toComma) := by
  obtain ⟨E, hE⟩ := JTMixedGraphEdgeFamilyExtension.exists_extension j f s D hW
  refine ⟨E, ?_⟩
  rw [← hE]
  exact ⟨verticalArrow j f s E hmap qx qy⟩

end

end DaggerModels.PartII.JTMixedGraphVerticalArrow
