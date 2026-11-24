import DaggerModelsPartII.JTFiniteCoefficientBridgeVertexLift
import DaggerModelsPartII.JTChangingCoefficientBridgeFamilies
import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeFamilies

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointNormalizationLifts JTMixedGraphEdgeFamilyReindex
open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgePrism
open JTFiniteCoefficientBridgeVertexLift
open JTChangingCoefficientBridgeFamilies
  (leftBase rightBase identityAt leftBase_precomp rightBase_precomp)
open JTFiniteCoefficientBridgeTime

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
variable (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)

abbrev sideRow {W : Source} {d : ℕ} (f : Δ b' ⟶ row W ⦋d⦌)
    (e : Fin (m + 1)) : Δ (JTHigherInterleavedParameter.common k n) ⟶ row W ⦋d⦌ :=
  SSet.stdSimplex.map (side c u h hu n e) ≫ SSet.stdSimplex.map (base c u n) ≫ f

abbrev sideSlice (e : Fin (m + 1)) : k ⟶ JTHigherInterleavedParameter.common k n :=
  JTCommonCoefficientParameter.slice (c e) n 0

private theorem vertex_slice_vertical (a : Fin (k.len + 1)) :
    vertex (bridge k n m) ((slice c u n 0).toOrderHom a) =
      vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

set_option maxHeartbeats 800000 in
theorem exists_bridgeFamilies {W : Source}
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (d : ℕ) (f : Δ b' ⟶ row W ⦋d⦌)
    (s : Δ ⦋d⦌ ⟶ J.obj k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv
      (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k
        (SSet.stdSimplex.map u ≫ f) s) = rawVertex W x)
    (hy : SSet.yonedaEquiv
      (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k
        (SSet.stdSimplex.map u ≫ f) s) = rawVertex W y)
    (E : (e : Fin (m + 1)) → EdgeFamilies W ⦋d⦌
      (JTHigherInterleavedParameter.common k n) (sideRow c u h hu n f e)
      (s ≫ J.map (sideSlice c n e)) x y)
    (hleft : ∀ e, SSet.stdSimplex.map
      (sideVertical c n (graphIndex ⦋d⦌ k s 0) e) ≫ (E e).left =
        term (Δ n) ≫ identityAt x)
    (hright : ∀ e, SSet.stdSimplex.map
      (sideVertical c n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫ (E e).right =
        term (Δ n) ≫ identityAt y) :
    ∃ B : EdgeFamilies W ⦋d⦌ (bridge k n m)
      (SSet.stdSimplex.map (base c u n) ≫ f)
      (s ≫ J.map (slice c u n 0)) x y,
      (∀ e, SSet.stdSimplex.map (side c u h hu n e) ≫ B.left = (E e).left) ∧
      (∀ e, SSet.stdSimplex.map (side c u h hu n e) ≫ B.right = (E e).right) ∧
      SSet.stdSimplex.map
        (vertical c u n (graphIndex ⦋d⦌ k s 0)) ≫ B.left =
          term (Δ (time m n)) ≫ identityAt x ∧
      SSet.stdSimplex.map
        (vertical c u n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ B.right =
          term (Δ (time m n)) ≫ identityAt y := by
  let e := chosenEdgeFamilies W hW ⦋d⦌ k
    (SSet.stdSimplex.map u ≫ f) s x y hx hy
  let a := graphIndex ⦋d⦌ k s 0
  let b := graphIndex ⦋d⦌ k s (Fin.last d)
  have hL : identityAt x ≫ endpointArrow W =
      vertex k a ≫ leftBase (SSet.stdSimplex.map u ≫ f) x := by
    calc
      _ = (vertex k a ≫ e.left) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.left_degenerate.symm
      _ = _ := by rw [Category.assoc, e.left_boundary]
  have hR : identityAt y ≫ endpointArrow W =
      vertex k b ≫ rightBase (SSet.stdSimplex.map u ≫ f) y := by
    calc
      _ = (vertex k b ≫ e.right) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.right_degenerate.symm
      _ = _ := by rw [Category.assoc, e.right_boundary]; rfl
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let sqL : CommSq (identityAt x) (vertex k a) (endpointArrow W)
      (SSet.stdSimplex.map u ≫ leftBase f x) :=
    ⟨hL.trans (congrArg (fun u ↦ vertex k a ≫ u)
      (leftBase_precomp u f x).symm)⟩
  let sqR : CommSq (identityAt y) (vertex k b) (endpointArrow W)
      (SSet.stdSimplex.map u ≫ rightBase f y) :=
    ⟨hR.trans (congrArg (fun u ↦ vertex k b ≫ u)
      (rightBase_precomp u f y).symm)⟩
  have hbaseL (v : Fin (m + 1)) : (E v).left ≫ endpointArrow W =
      SSet.stdSimplex.map (side c u h hu n v) ≫ SSet.stdSimplex.map (base c u n) ≫
        leftBase f x := by
    calc
      _ = leftBase (sideRow c u h hu n f v) x := (E v).left_boundary
      _ = SSet.stdSimplex.map (side c u h hu n v) ≫
          leftBase (SSet.stdSimplex.map (base c u n) ≫ f) x :=
        (leftBase_precomp (side c u h hu n v)
          (SSet.stdSimplex.map (base c u n) ≫ f) x).symm
      _ = _ := by rw [← leftBase_precomp (base c u n) f x]
  have hbaseR (v : Fin (m + 1)) : (E v).right ≫ endpointArrow W =
      SSet.stdSimplex.map (side c u h hu n v) ≫ SSet.stdSimplex.map (base c u n) ≫
        rightBase f y := by
    calc
      _ = rightBase (sideRow c u h hu n f v) y := (E v).right_boundary
      _ = SSet.stdSimplex.map (side c u h hu n v) ≫
          rightBase (SSet.stdSimplex.map (base c u n) ≫ f) y :=
        (rightBase_precomp (side c u h hu n v)
          (SSet.stdSimplex.map (base c u n) ≫ f) y).symm
      _ = _ := by rw [← rightBase_precomp (base c u n) f y]
  obtain ⟨L, hLs, hLb, hLv⟩ := exists_vertex_extension c u h hu n
    (leftBase f x) a (identityAt x) sqL (fun v ↦ (E v).left) hbaseL hleft
  obtain ⟨R, hRs, hRb, hRv⟩ := exists_vertex_extension c u h hu n
    (rightBase f y) b (identityAt y) sqR (fun v ↦ (E v).right) hbaseR hright
  refine ⟨{
    left := L
    right := R
    left_boundary := hLb.trans (leftBase_precomp (base c u n) f x)
    right_boundary := hRb.trans (rightBase_precomp (base c u n) f y)
    left_degenerate := ?_
    right_degenerate := ?_ }, hLs, hRs, hLv, hRv⟩
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n a) ≫ L =
      identityAt x
    rw [hLv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time m n) 0 ≫ term (Δ (time m n))) (𝟙 _), Category.id_comp]
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n b) ≫ R =
      identityAt y
    rw [hRv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time m n) 0 ≫ term (Δ (time m n))) (𝟙 _), Category.id_comp]

/-- All three row maps give the exact prescribed label on every side. -/
theorem orderedPoint_side {W : Source} {d : ℕ}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (f : Δ b' ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
    (B : EdgeFamilies W ⦋d⦌ (bridge k n m) (SSet.stdSimplex.map (base c u n) ≫ f)
      (s ≫ J.map (slice c u n 0)) x y)
    (e : Fin (m + 1))
    (D : EdgeFamilies W ⦋d⦌ (JTHigherInterleavedParameter.common k n) (sideRow c u h hu n f e)
      (s ≫ J.map (sideSlice c n e)) x y)
    (hleft : SSet.stdSimplex.map (side c u h hu n e) ≫ B.left = D.left)
    (hright : SSet.stdSimplex.map (side c u h hu n e) ≫ B.right = D.right) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (TripleBeadEndpointLabel.code d))).map (side c u h hu n e).op
          (JTMixedGraphOrderedLabel.orderedPoint B) = JTMixedGraphOrderedLabel.orderedPoint D := by
  symm
  apply orderedPoint_reindex_of_rows (side c u h hu n e)
    (JTMixedGraphOrderedLabel.families B) (JTMixedGraphOrderedLabel.families D)
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, hleft]
  · dsimp only [JTMixedGraphOrderedLabel.families, sideRow]
    rw [Category.assoc]
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, hright]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeFamilies
