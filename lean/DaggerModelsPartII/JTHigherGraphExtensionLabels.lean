import DaggerModelsPartII.JTFixedLiftSpaceInterleaved
import DaggerModelsPartII.JTOrdinaryGraphNormalizationSpace
import DaggerModelsPartII.JTHigherMixedGraphTargetLift

/-!
# The actual labels of enlarged fixed-square coefficient families
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTHigherGraphExtensionLabels

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTOrdinaryGraphNormalizationSpace JTEndpointNormalizationLifts
open JTFixedLiftSpaceInterleaved JTHigherInterleavedParameter
open JTMixedGraphEdgeFamilyReindex

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev code := MixedGraphCylinderTraversal.code

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W y)

abbrev leftExtension (n : SimplexCategory) :=
  Extension (leftSquare W ⦋d⦌ k f s x hx) n

abbrev rightExtension (n : SimplexCategory) :=
  Extension (rightSquare W ⦋d⦌ k f s y hy) n

private theorem verticalSection_vertex (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    lift (term (simplex n)) (𝟙 (simplex n)) ≫ (vertex k a ▷ simplex n) =
      verticalSection k n a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, verticalSection, lift_fst]
    have h : term (simplex n) =
        SSet.stdSimplex.map (SimplexCategory.const n ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, vertex, ← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
    rfl
  · simp only [verticalSection, Category.assoc, whiskerRight_snd, lift_snd]

private theorem vertical_eq {n : SimplexCategory} (a : Fin (k.len + 1))
    {X Y : SSet.{0}} {p : X ⟶ Y} {b : simplex k ⟶ Y} {t : simplex ⦋0⦌ ⟶ X}
    {sq : CommSq t (vertex k a) p b} (E : Extension sq n) :
    SSet.stdSimplex.map (vertical k n a) ≫ E.map = term (simplex n) ≫ t := by
  rw [← verticalSection_prism, ← verticalSection_vertex, Category.assoc, Category.assoc,
    E.stationary, lift_fst_assoc]

theorem left_vertical {n : SimplexCategory} (L : leftExtension f s hx n) :
    SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s 0)) ≫ L.map =
      term (simplex n) ≫ vertexPoint W x ≫ identityFamily W :=
  vertical_eq (graphIndex ⦋d⦌ k s 0) L

theorem right_vertical {n : SimplexCategory} (R : rightExtension f s hy n) :
    SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ R.map =
      term (simplex n) ≫ vertexPoint W y ≫ identityFamily W :=
  vertical_eq (graphIndex ⦋d⦌ k s (Fin.last d)) R

private theorem vertex_slice (k n : SimplexCategory) (a : Fin (k.len + 1))
    (v : Fin (n.len + 1)) :
    vertex (common k n) ((slice k n v).toOrderHom a) =
      vertex n v ≫ SSet.stdSimplex.map (vertical k n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

/-- The two enlarged coefficient maps define the original ordered label
at every time slice. -/
def families {n : SimplexCategory} (L : leftExtension f s hx n)
    (R : rightExtension f s hy n) (v : Fin (n.len + 1)) :
    EdgeFamilies W ⦋d⦌ (common k n) (SSet.stdSimplex.map (ret k n) ≫ f)
      (s ≫ J.map (slice k n v)) x y where
  left := L.map
  right := R.map
  left_boundary := by
    rw [L.over]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      rw [← Category.assoc (SSet.stdSimplex.map (ret k n))]
      exact congrArg (fun u ↦ u ≫ vertexPoint W x)
        (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    · simp only [Category.assoc, prod.lift_snd]
  right_boundary := by
    rw [R.over]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc (SSet.stdSimplex.map (ret k n))]
      exact congrArg (fun u ↦ u ≫ vertexPoint W y)
        (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  left_degenerate := by
    rw [graphIndex_reindex, vertex_slice, Category.assoc, left_vertical f s hx L]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex n v ≫ term (simplex n)) (𝟙 _), Category.id_comp]
  right_degenerate := by
    rw [graphIndex_reindex, vertex_slice, Category.assoc]
    change vertex n v ≫ SSet.stdSimplex.map
      (vertical k n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ R.map = _
    rw [right_vertical f s hy R, ← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex n v ≫ term (simplex n)) (𝟙 _), Category.id_comp]

private theorem orderedPoint_congr {m : SimplexCategory}
    {f₀ f₁ : simplex m ⟶ row W ⦋d⦌} {s₀ s₁ : simplex ⦋d⦌ ⟶ J.obj m}
    (E₀ : EdgeFamilies W ⦋d⦌ m f₀ s₀ x y) (E₁ : EdgeFamilies W ⦋d⦌ m f₁ s₁ x y)
    (hf : f₀ = f₁) (hL : E₀.left = E₁.left) (hR : E₀.right = E₁.right) :
    JTMixedGraphOrderedLabel.orderedPoint E₀ = JTMixedGraphOrderedLabel.orderedPoint E₁ := by
  subst f₁
  have h : JTMixedGraphOrderedLabel.families E₀ = JTMixedGraphOrderedLabel.families E₁ := by
    cases E₀
    cases E₁
    dsimp only at hL hR
    subst_vars
    rfl
  exact congrArg TripleBeadEndpointLabel.orderedPoint h

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints

/-- The actual ordered label of the enlarged coefficient. -/
def label {n : SimplexCategory} (L : leftExtension f s hx n) (R : rightExtension f s hy n) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).obj (op (common k n)) :=
  JTMixedGraphOrderedLabel.orderedPoint (families f s hx hy L R 0)

theorem label_at_slice {n : SimplexCategory} (L : leftExtension f s hx n)
    (R : rightExtension f s hy n) (v : Fin (n.len + 1)) :
    JTMixedGraphOrderedLabel.orderedPoint (families f s hx hy L R v) = label f s hx hy L R :=
  orderedPoint_congr _ _ rfl rfl rfl

/-- The coefficient restriction along every time operator is the exact
presheaf restriction of the original ordered label. -/
theorem label_mapTime {m n : SimplexCategory} (j : m ⟶ n)
    (L : leftExtension f s hx n) (R : rightExtension f s hy n) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).map
        (mapTime k j).op (label f s hx hy L R) =
      label f s hx hy
        (restrict (leftSquare W ⦋d⦌ k f s x hx) j L)
        (restrict (rightSquare W ⦋d⦌ k f s y hy) j R) := by
  let u := mapTime k j
  let fN := SSet.stdSimplex.map (ret k n) ≫ f
  let sM := s ≫ J.map (slice k m 0)
  let v := j.toOrderHom 0
  have hp : sM ≫ J.map u = s ≫ J.map (slice k n v) := by
    dsimp only [sM, u, v]
    rw [Category.assoc, ← J.map_comp, slice_mapTime]
  let F := families f s hx hy L R v
  let E : EdgeFamilies W ⦋d⦌ (common k n) fN (sM ≫ J.map u) x y :=
    { left := F.left
      right := F.right
      left_boundary := F.left_boundary
      right_boundary := F.right_boundary
      left_degenerate := by rw [hp]; exact F.left_degenerate
      right_degenerate := by rw [hp]; exact F.right_degenerate }
  have hN : JTMixedGraphOrderedLabel.orderedPoint E = label f s hx hy L R :=
    (orderedPoint_congr E F rfl rfl rfl).trans (label_at_slice f s hx hy L R v)
  have hf : SSet.stdSimplex.map u ≫ fN = SSet.stdSimplex.map (ret k m) ≫ f := by
    dsimp only [u, fN]
    rw [← Category.assoc, ← SSet.stdSimplex.map_comp, mapTime_ret]
  rw [← hN]
  have hre := orderedPoint_reindex u fN sM E
  change JTMixedGraphOrderedLabel.orderedPoint (restrictEdgeFamilies u fN sM E) =
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).map
      (mapTime k j).op (JTMixedGraphOrderedLabel.orderedPoint E) at hre
  rw [← hre]
  exact orderedPoint_congr _ _ hf rfl rfl

end

end DaggerModels.PartII.JTHigherGraphExtensionLabels
