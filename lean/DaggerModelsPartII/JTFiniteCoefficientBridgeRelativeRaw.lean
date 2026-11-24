import DaggerModelsPartII.JTFiniteCoefficientBridgeRelativeVertex
import DaggerModelsPartII.JTFiniteCoefficientBridgeFamilies
import DaggerModelsPartII.JTFiniteCoefficientBridgePullback

/-!
# The original raw comparison with overlapping prescribed coefficient faces
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

universe w

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeRaw

open JTFiniteCoefficientBridgeOrder (bridge base)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgePrism (slice vertical)
open JTFiniteCoefficientBridgeCopyFace (copyFace timeFace)
open JTFiniteCoefficientBridgeFaceCover (facePrism)
open JTFiniteCoefficientBridgeRelativeVertex (exists_vertex_extension_of_faces)
open JTChangingCoefficientBridgeFamilies
  (leftBase rightBase identityAt leftBase_precomp rightBase_precomp)
open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts JTMixedGraphEdgeFamilyReindex
open JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open JTNecklaceEndpointCylinder JTFiniteCoefficientBridgePullback

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable {ι : Type w} (S : ι → Finset (Fin (m + 1)))

/-- One actual endpoint row on each specified face, with its original
base, stationary equation, and agreement on the whole intersections. -/
structure EndpointFaces {W : Source}
    (a : Fin (k.len + 1)) (g : Δ b' ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌)
    (t : Δ ⦋0⦌ ⟶ row W ⦋1⦌) where
  map (e : ι) : (copyFace.{0} c u n (S e)).toSSet ⟶ row W ⦋1⦌
  base_eq (e : ι) :
    map e ≫ endpointArrow W = (copyFace.{0} c u n (S e)).ι ≫
      SSet.stdSimplex.map (base c u n) ≫ g
  stationary (e : ι) :
    (vertex k a ▷ (timeFace.{0} n (S e)).toSSet) ≫ facePrism c u n (S e) ≫ map e =
      fst (Δ ⦋0⦌) (timeFace.{0} n (S e)).toSSet ≫ t
  overlap (e e' : ι) :
    SSet.Subcomplex.homOfLE (inf_le_left :
      copyFace.{0} c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e)) ≫ map e =
    SSet.Subcomplex.homOfLE (inf_le_right :
      copyFace.{0} c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e')) ≫ map e'

private theorem vertex_slice_vertical (a : Fin (k.len + 1)) :
    vertex (bridge k n m) ((slice c u n 0).toOrderHom a) =
      vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

variable {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (f : Δ b' ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable (E₀ : EndpointFaces c u n S (graphIndex ⦋d⦌ k s 0) (leftBase f x) (identityAt x))
variable (E₁ : EndpointFaces c u n S (graphIndex ⦋d⦌ k s (Fin.last d)) (rightBase f y) (identityAt y))

set_option maxHeartbeats 800000 in
/-- Both actual outside families extend from their overlapping prescribed
faces. The center is the original row over the final coefficient. -/
theorem exists_families [Fintype ι]
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫
      rawGraph W ⦋d⦌ k (SSet.stdSimplex.map u ≫ f) s) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫
      rawGraph W ⦋d⦌ k (SSet.stdSimplex.map u ≫ f) s) = rawVertex W y) :
    ∃ B : EdgeFamilies W ⦋d⦌ (bridge k n m) (SSet.stdSimplex.map (base c u n) ≫ f)
        (s ≫ J.map (slice c u n 0)) x y,
      (∀ e, (copyFace.{0} c u n (S e)).ι ≫ B.left = E₀.map e) ∧
      (∀ e, (copyFace.{0} c u n (S e)).ι ≫ B.right = E₁.map e) ∧
      SSet.stdSimplex.map (vertical c u n (graphIndex ⦋d⦌ k s 0)) ≫ B.left =
        term (Δ (time m n)) ≫ identityAt x ∧
      SSet.stdSimplex.map (vertical c u n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ B.right =
        term (Δ (time m n)) ≫ identityAt y := by
  let e := chosenEdgeFamilies W hW ⦋d⦌ k (SSet.stdSimplex.map u ≫ f) s x y hx hy
  let a := graphIndex ⦋d⦌ k s 0
  let b := graphIndex ⦋d⦌ k s (Fin.last d)
  have hL : identityAt x ≫ endpointArrow W =
      vertex k a ≫ leftBase (SSet.stdSimplex.map u ≫ f) x := by
    calc
      _ = (vertex k a ≫ e.left) ≫ endpointArrow W :=
        congrArg (fun v ↦ v ≫ endpointArrow W) e.left_degenerate.symm
      _ = _ := by rw [Category.assoc, e.left_boundary]
  have hR : identityAt y ≫ endpointArrow W =
      vertex k b ≫ rightBase (SSet.stdSimplex.map u ≫ f) y := by
    calc
      _ = (vertex k b ≫ e.right) ≫ endpointArrow W :=
        congrArg (fun v ↦ v ≫ endpointArrow W) e.right_degenerate.symm
      _ = _ := by
        rw [Category.assoc, e.right_boundary]
        rfl
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let sqL : CommSq (identityAt x) (vertex k a) (endpointArrow W)
      (SSet.stdSimplex.map u ≫ leftBase f x) :=
    ⟨hL.trans (congrArg (fun v ↦ vertex k a ≫ v) (leftBase_precomp u f x).symm)⟩
  let sqR : CommSq (identityAt y) (vertex k b) (endpointArrow W)
      (SSet.stdSimplex.map u ≫ rightBase f y) :=
    ⟨hR.trans (congrArg (fun v ↦ vertex k b ≫ v) (rightBase_precomp u f y).symm)⟩
  obtain ⟨L, hLs, hLb, hLv⟩ := exists_vertex_extension_of_faces c u n S
    (leftBase f x) a (identityAt x) sqL E₀.map E₀.overlap E₀.base_eq E₀.stationary
  obtain ⟨R, hRs, hRb, hRv⟩ := exists_vertex_extension_of_faces c u n S
    (rightBase f y) b (identityAt y) sqR E₁.map E₁.overlap E₁.base_eq E₁.stationary
  refine ⟨{
    left := L
    right := R
    left_boundary := hLb.trans (leftBase_precomp (base c u n) f x)
    right_boundary := hRb.trans (rightBase_precomp (base c u n) f y)
    left_degenerate := ?_
    right_degenerate := ?_ }, hLs, hRs, hLv, hRv⟩
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n a) ≫ L = identityAt x
    rw [hLv, ← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time m n) 0 ≫ term (Δ (time m n))) (𝟙 _), Category.id_comp]
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n b) ≫ R = identityAt y
    rw [hRv, ← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time m n) 0 ≫ term (Δ (time m n))) (𝟙 _), Category.id_comp]

set_option maxHeartbeats 800000 in
/-- The actual target pullback comparison retains the prescribed
outside maps on every overlapping face and both original projections. -/
theorem exists_lift_over_raw_of_faces [Fintype ι]
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    {q : (single d).toSSet ⟶ Raw W}
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map u ≫ f) s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y) :
    let Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) := ⟨single d, q, qx, qy⟩
    ∃ B : EdgeFamilies W ⦋d⦌ (bridge k n m) (SSet.stdSimplex.map (base c u n) ≫ f)
        (s ≫ J.map (slice c u n 0)) x y,
      (∀ e, (copyFace.{0} c u n (S e)).ι ≫ B.left = E₀.map e) ∧
      (∀ e, (copyFace.{0} c u n (S e)).ι ≫ B.right = E₁.map e) ∧
      let z := JTMixedGraphOrderedLabel.orderedPoint B
      ∃ U : (under (code d)).obj (time m n) ⟶
          (JTTargetCommaPullback.diagram W x y Q).obj (bridgeIndex n z),
        U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
          bridgeCylinder c u n z (nativeGraphParameter s) ∧
        U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z) =
          JTHigherMixedGraphTargetLift.toNativeTarget d (time m n) := by
  intro Q
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hq qx qy
  obtain ⟨B, hB₀, hB₁, hL, hR⟩ := exists_families c u n S f s E₀ E₁ hW hx hy
  exact ⟨B, hB₀, hB₁, exists_lift_over_raw c u n f s hq qx qy B hL hR⟩

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeRaw
