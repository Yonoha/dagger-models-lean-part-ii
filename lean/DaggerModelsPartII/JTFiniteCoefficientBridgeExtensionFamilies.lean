import DaggerModelsPartII.JTFiniteCoefficientBridgeExtension
import DaggerModelsPartII.JTFiniteCoefficientBridgeFamilies

/-!
# Exact finite-bridge extensions as mixed-graph edge families
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeExtensionFamilies

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTMixedGraphEdgeFamilyReindex JTEndpointNormalizationLifts
open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism JTFiniteCoefficientBridgeExtension
open JTChangingCoefficientBridgeFamilies
  (leftBase rightBase identityAt leftBase_precomp rightBase_precomp)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem verticalSection_vertex (k n : SimplexCategory)
    (a : Fin (k.len + 1)) :
    lift (term (Δ n)) (𝟙 (Δ n)) ≫ (vertex k a ▷ Δ n) =
      JTHigherInterleavedParameter.verticalSection k n a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc,
      JTHigherInterleavedParameter.verticalSection, lift_fst]
    have h : term (Δ n) =
        SSet.stdSimplex.map (SimplexCategory.const n ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, vertex, ← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
    rfl
  · simp only [JTHigherInterleavedParameter.verticalSection,
      Category.assoc, whiskerRight_snd, lift_snd]

/-- The full joined time simplex at the selected source vertex is stationary. -/
theorem vertical_stationary {m : ℕ} {k b' : SimplexCategory}
    {b : Fin (m + 1) → SimplexCategory}
    (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
    {X Y : SSet.{0}} {p : X ⟶ Y} {g : Δ b' ⟶ Y}
    {t : Δ ⦋0⦌ ⟶ X} (a : Fin (k.len + 1))
    (sq : CommSq t (vertex k a) p (SSet.stdSimplex.map u ≫ g))
    (E : Extension c u sq n) :
    SSet.stdSimplex.map (vertical c u n a) ≫ E.map =
      term (Δ (time m n)) ≫ t := by
  rw [← verticalSection_prism, ← verticalSection_vertex,
    Category.assoc, Category.assoc, E.stationary, lift_fst_assoc]

private theorem vertex_slice_vertical {m : ℕ} {k b' : SimplexCategory}
    {b : Fin (m + 1) → SimplexCategory}
    (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
    (a : Fin (k.len + 1)) :
    vertex (bridge k n m) ((slice c u n 0).toOrderHom a) =
      vertex (time m n) 0 ≫ SSet.stdSimplex.map (vertical c u n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

private theorem degenerate {m : ℕ} {k b' : SimplexCategory}
    {b : Fin (m + 1) → SimplexCategory}
    (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
    {X Y : SSet.{0}} {p : X ⟶ Y} {g : Δ b' ⟶ Y}
    {t : Δ ⦋0⦌ ⟶ X} (a : Fin (k.len + 1))
    (sq : CommSq t (vertex k a) p (SSet.stdSimplex.map u ≫ g))
    (E : Extension c u sq n) :
    vertex (bridge k n m) ((slice c u n 0).toOrderHom a) ≫ E.map = t := by
  rw [vertex_slice_vertical, Category.assoc, vertical_stationary c u n a sq E,
    ← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex (time m n) 0 ≫ term (Δ (time m n))) (𝟙 _), Category.id_comp]

variable {W : Source} {d m : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable (f : Δ b' ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
variable {sqL : CommSq (identityAt x)
    (vertex k (graphIndex ⦋d⦌ k s 0)) (endpointArrow W)
    (SSet.stdSimplex.map u ≫ leftBase f x)}
variable {sqR : CommSq (identityAt y)
    (vertex k (graphIndex ⦋d⦌ k s (Fin.last d))) (endpointArrow W)
    (SSet.stdSimplex.map u ≫ rightBase f y)}
variable (L : Extension c u sqL n) (R : Extension c u sqR n)

/-- The exact paired extensions supply the original mixed-graph edge families. -/
def choiceFamilies :
    EdgeFamilies W ⦋d⦌ (bridge k n m)
      (SSet.stdSimplex.map (base c u n) ≫ f)
      (s ≫ J.map (slice c u n 0)) x y where
  left := L.map
  right := R.map
  left_boundary := L.over.trans (leftBase_precomp (base c u n) f x)
  right_boundary := R.over.trans (rightBase_precomp (base c u n) f y)
  left_degenerate := by
    rw [graphIndex_reindex]
    exact degenerate c u n _ sqL L
  right_degenerate := by
    rw [graphIndex_reindex]
    exact degenerate c u n (graphIndex ⦋d⦌ k s (Fin.last d)) sqR R

@[simp] theorem choiceFamilies_left :
    (choiceFamilies c u n f s x y L R).left = L.map := rfl

@[simp] theorem choiceFamilies_right :
    (choiceFamilies c u n f s x y L R).right = R.map := rfl

theorem choiceFamilies_left_vertical :
    SSet.stdSimplex.map (vertical c u n (graphIndex ⦋d⦌ k s 0)) ≫
      (choiceFamilies c u n f s x y L R).left =
      term (Δ (time m n)) ≫ identityAt x :=
  vertical_stationary c u n _ sqL L

theorem choiceFamilies_right_vertical :
    SSet.stdSimplex.map (vertical c u n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫
      (choiceFamilies c u n f s x y L R).right =
      term (Δ (time m n)) ≫ identityAt y :=
  vertical_stationary c u n _ sqR R

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeExtensionFamilies
