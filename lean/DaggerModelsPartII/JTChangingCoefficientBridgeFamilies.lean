import DaggerModelsPartII.JTChangingCoefficientBridgeLift
import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChangingCoefficientBridgeFamilies

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointNormalizationLifts JTMixedGraphEdgeFamilyReindex
open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgePrism
open JTChangingCoefficientBridgeLift
open JTChangingCoefficientBridgeTime

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory)

abbrev sideRow {W : Source} {d : ℕ} (f : Δ b' ⟶ row W ⦋d⦌)
    (e : Fin 2) : Δ (JTHigherInterleavedParameter.common k n) ⟶ row W ⦋d⦌ :=
  SSet.stdSimplex.map (side c h n e) ≫ SSet.stdSimplex.map (base c h n) ≫ f

abbrev sideSlice (e : Fin 2) : k ⟶ JTHigherInterleavedParameter.common k n :=
  if e = 0 then JTCommonCoefficientParameter.slice c n 0
  else JTCommonCoefficientParameter.slice (c ≫ h) n 0

abbrev leftBase {W : Source} {d : ℕ} {l : SimplexCategory}
    (f : Δ l ⟶ row W ⦋d⦌) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (term (Δ l) ≫ vertexPoint W x) (f ≫ rowVertex W ⦋d⦌ 0)

abbrev rightBase {W : Source} {d : ℕ} {l : SimplexCategory}
    (f : Δ l ⟶ row W ⦋d⦌) (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (f ≫ rowVertex W ⦋d⦌ (Fin.last d)) (term (Δ l) ≫ vertexPoint W y)

abbrev identityAt {W : Source} (z : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  vertexPoint W z ≫ identityFamily W

theorem leftBase_precomp {W : Source} {d : ℕ} {l m : SimplexCategory}
    (j : l ⟶ m) (f : Δ m ⟶ row W ⦋d⦌)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map j ≫ leftBase f x =
      leftBase (SSet.stdSimplex.map j ≫ f) x := by
  apply prod.hom_ext
  · simp only [leftBase, Category.assoc, prod.lift_fst]
    have ht : SSet.stdSimplex.map j ≫ term (Δ m) = term (Δ l) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, ht]
  · simp only [leftBase, Category.assoc, prod.lift_snd]

theorem rightBase_precomp {W : Source} {d : ℕ} {l m : SimplexCategory}
    (j : l ⟶ m) (f : Δ m ⟶ row W ⦋d⦌)
    (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map j ≫ rightBase f y =
      rightBase (SSet.stdSimplex.map j ≫ f) y := by
  apply prod.hom_ext
  · simp only [rightBase, Category.assoc, prod.lift_fst]
  · simp only [rightBase, Category.assoc, prod.lift_snd]
    have ht : SSet.stdSimplex.map j ≫ term (Δ m) = term (Δ l) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, ht]

private theorem vertex_slice_vertical (a : Fin (k.len + 1)) :
    vertex (bridge k n) ((slice c h n 0).toOrderHom a) =
      vertex (time n) 0 ≫ SSet.stdSimplex.map (vertical c h n a) := by
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
        (SSet.stdSimplex.map (c ≫ h) ≫ f) s) = rawVertex W x)
    (hy : SSet.yonedaEquiv
      (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k
        (SSet.stdSimplex.map (c ≫ h) ≫ f) s) = rawVertex W y)
    (E : (e : Fin 2) → EdgeFamilies W ⦋d⦌
      (JTHigherInterleavedParameter.common k n) (sideRow c h n f e)
      (s ≫ J.map (sideSlice c h n e)) x y)
    (hleft : ∀ e, SSet.stdSimplex.map
      (sideVertical c h n (graphIndex ⦋d⦌ k s 0) e) ≫ (E e).left =
        term (Δ n) ≫ identityAt x)
    (hright : ∀ e, SSet.stdSimplex.map
      (sideVertical c h n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫ (E e).right =
        term (Δ n) ≫ identityAt y) :
    ∃ B : EdgeFamilies W ⦋d⦌ (bridge k n)
      (SSet.stdSimplex.map (base c h n) ≫ f)
      (s ≫ J.map (slice c h n 0)) x y,
      (∀ e, SSet.stdSimplex.map (side c h n e) ≫ B.left = (E e).left) ∧
      (∀ e, SSet.stdSimplex.map (side c h n e) ≫ B.right = (E e).right) ∧
      SSet.stdSimplex.map
        (vertical c h n (graphIndex ⦋d⦌ k s 0)) ≫ B.left =
          term (Δ (time n)) ≫ identityAt x ∧
      SSet.stdSimplex.map
        (vertical c h n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ B.right =
          term (Δ (time n)) ≫ identityAt y := by
  let e := chosenEdgeFamilies W hW ⦋d⦌ k
    (SSet.stdSimplex.map (c ≫ h) ≫ f) s x y hx hy
  let a := graphIndex ⦋d⦌ k s 0
  let b := graphIndex ⦋d⦌ k s (Fin.last d)
  have hL : identityAt x ≫ endpointArrow W =
      vertex k a ≫ leftBase (SSet.stdSimplex.map (c ≫ h) ≫ f) x := by
    calc
      _ = (vertex k a ≫ e.left) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.left_degenerate.symm
      _ = _ := by rw [Category.assoc, e.left_boundary]
  have hR : identityAt y ≫ endpointArrow W =
      vertex k b ≫ rightBase (SSet.stdSimplex.map (c ≫ h) ≫ f) y := by
    calc
      _ = (vertex k b ≫ e.right) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.right_degenerate.symm
      _ = _ := by rw [Category.assoc, e.right_boundary]; rfl
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let sqL : CommSq (identityAt x) (vertex k a) (endpointArrow W)
      (SSet.stdSimplex.map (c ≫ h) ≫ leftBase f x) :=
    ⟨hL.trans (congrArg (fun u ↦ vertex k a ≫ u)
      (leftBase_precomp (c ≫ h) f x).symm)⟩
  let sqR : CommSq (identityAt y) (vertex k b) (endpointArrow W)
      (SSet.stdSimplex.map (c ≫ h) ≫ rightBase f y) :=
    ⟨hR.trans (congrArg (fun u ↦ vertex k b ≫ u)
      (rightBase_precomp (c ≫ h) f y).symm)⟩
  have hbaseL (v : Fin 2) : (E v).left ≫ endpointArrow W =
      SSet.stdSimplex.map (side c h n v) ≫ SSet.stdSimplex.map (base c h n) ≫
        leftBase f x := by
    calc
      _ = leftBase (sideRow c h n f v) x := (E v).left_boundary
      _ = SSet.stdSimplex.map (side c h n v) ≫
          leftBase (SSet.stdSimplex.map (base c h n) ≫ f) x :=
        (leftBase_precomp (side c h n v)
          (SSet.stdSimplex.map (base c h n) ≫ f) x).symm
      _ = _ := by rw [← leftBase_precomp (base c h n) f x]
  have hbaseR (v : Fin 2) : (E v).right ≫ endpointArrow W =
      SSet.stdSimplex.map (side c h n v) ≫ SSet.stdSimplex.map (base c h n) ≫
        rightBase f y := by
    calc
      _ = rightBase (sideRow c h n f v) y := (E v).right_boundary
      _ = SSet.stdSimplex.map (side c h n v) ≫
          rightBase (SSet.stdSimplex.map (base c h n) ≫ f) y :=
        (rightBase_precomp (side c h n v)
          (SSet.stdSimplex.map (base c h n) ≫ f) y).symm
      _ = _ := by rw [← rightBase_precomp (base c h n) f y]
  obtain ⟨L, hLs, hLb, hLv⟩ := exists_vertex_extension c h n
    (leftBase f x) a (identityAt x) sqL (fun v ↦ (E v).left) hbaseL hleft
  obtain ⟨R, hRs, hRb, hRv⟩ := exists_vertex_extension c h n
    (rightBase f y) b (identityAt y) sqR (fun v ↦ (E v).right) hbaseR hright
  refine ⟨{
    left := L
    right := R
    left_boundary := hLb.trans (leftBase_precomp (base c h n) f x)
    right_boundary := hRb.trans (rightBase_precomp (base c h n) f y)
    left_degenerate := ?_
    right_degenerate := ?_ }, hLs, hRs, hLv, hRv⟩
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time n) 0 ≫ SSet.stdSimplex.map (vertical c h n a) ≫ L =
      identityAt x
    rw [hLv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time n) 0 ≫ term (Δ (time n))) (𝟙 _), Category.id_comp]
  · rw [graphIndex_reindex, vertex_slice_vertical]
    change vertex (time n) 0 ≫ SSet.stdSimplex.map (vertical c h n b) ≫ R =
      identityAt y
    rw [hRv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time n) 0 ≫ term (Δ (time n))) (𝟙 _), Category.id_comp]

end

end DaggerModels.PartII.JTChangingCoefficientBridgeFamilies
