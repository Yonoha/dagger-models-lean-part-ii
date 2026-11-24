import DaggerModelsPartII.JTMixedGraphRawRefinement
import DaggerModelsPartII.JTGraphBinaryRefinement
import OriginalFlagSourceAssemblyIso

/-!
# Strict refinements over all native finite necklaces

The existing ordered source prefix decomposes the supplied necklace over the
same raw target. Each joint is lifted through the original zero-vertex
equivalence, and each successor adjoins the next original bead.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTFiniteNecklaceGraphRefinement

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTGraphRefinement DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source}

/-- Reindex the endpoint proofs of the supplied necklace. Its code and
complete map over the original target are the literal original fields. -/
def atRaw {a b : (R W).obj (op ⦋0⦌)} (P : NecklacesOver (R W) a b)
    {x y : Vertex W} (hx : a = rawVertex W x) (hy : b = rawVertex W y) :
    NecklacesOver (R W) (rawVertex W x) (rawVertex W y) where
  code := P.code
  map := P.map
  first := P.first.trans hx
  last := P.last.trans hy

private theorem prefix_refinement (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    {a b : (R W).obj (op ⦋0⦌)} (Q : NecklacesOver (R W) a b)
    (n : ℕ) (hn : n ≤ beadCount Q.code)
    {x y : Vertex W} (hx : jointVertex Q 0 = rawVertex W x)
    (hy : jointVertex Q ⟨n, Nat.lt_succ_of_le hn⟩ = rawVertex W y) :
    Nonempty (Refinement W x y (atRaw (orderedPrefix Q n hn).source hx hy)) := by
  induction n generalizing y with
  | zero =>
    exact JTMixedGraphRawRefinement.singleGraphRefinement_nonempty W hW x y 0 _
      (code_zero_eq_point (single 0) rfl).symm
  | succ n ih =>
    let i : Fin (beadCount Q.code) :=
      ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let c := jointBead Q.code i
    let u := jointVertex Q i.castSucc
    let e := JTRawVertexRecovery.zeroVertexEquiv (ordinaryInput.obj W)
    let z : Vertex W := e.symm u
    have hz : u = rawVertex W z := (e.apply_symm_apply u).symm
    obtain ⟨D⟩ := ih (Nat.le_of_succ_le hn) hz
    obtain ⟨E⟩ := JTMixedGraphRawRefinement.singleGraphRefinement_nonempty W hW z y c.length
      (atRaw (sourceBeadOver Q c) hz hy) rfl
    exact ⟨JTGraphBinaryRefinement.wedge D E⟩

/-- Every original finite native necklace in the raw realization admits a
strict graph refinement from the original decorated-cylinder presentation. -/
theorem graphRefinement_nonempty (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : Vertex W) (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)) :
    Nonempty (Refinement W x y Q) := by
  obtain ⟨D⟩ := prefix_refinement W hW Q (beadCount Q.code) le_rfl
    (jointVertex_first Q) (jointVertex_last Q)
  let D' : Refinement W x y (assembledSource Q) := D
  let f := (sourceAssemblyIso Q).hom
  exact ⟨{ code := D'.code
           degree := D'.degree
           label := D'.label
           parameter := D'.parameter
           collapse := D'.collapse ≫ f.hom
           comm := by
             rw [D'.comm]
             change _ = (D'.collapse.map ≫ f.hom.map) ≫ Q.map
             rw [Category.assoc, f.w] }⟩

/-- Nonemptiness holds in the actual target comma for every native necklace,
with all original endpoints and its full map to the raw realization. -/
theorem targetComma_nonempty (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : Vertex W) (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)) :
    Nonempty (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q) :=
  (graphRefinement_nonempty W hW x y Q).map Refinement.toComma

end

end DaggerModels.PartII.JTFiniteNecklaceGraphRefinement
