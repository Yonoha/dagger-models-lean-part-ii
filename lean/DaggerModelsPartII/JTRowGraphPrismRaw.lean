import DaggerModelsPartII.JTHigherGroupoidParameterPrism
import DaggerModelsPartII.JTHigherMixedGraphTargetLift

/-!
# A common raw-target comparison for graph prisms
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTRowGraphPrismRaw

open JTHigherGroupoidParameterPrism (timeSlice timeSlice_natural)
open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement JTMixedGraphVerticalArrow
open JTNecklaceLabelRealization JTRealizedLabelEndpoints JTGraphRefinement ReversalDiscreteFreeColimits
open MixedGraphCylinderTraversal JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open JTParameterContraction

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev A := single 1
private abbrev B (d : ℕ) := single d
private abbrev L (d : ℕ) := tripleRightT.{0} A (B d) A
private abbrev M (d : ℕ) := tripleRightU.{0} A (B d) A
private abbrev P (d : ℕ) := tripleRightV.{0} A (B d) A
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The parameter data used by the original raw graph calculation. -/
structure PrismData (k τ K b : SimplexCategory) where
  coefficient : k ⟶ b
  base : K ⟶ b
  slice : k ⟶ K
  vertical : Fin (k.len + 1) → (τ ⟶ K)
  slice_base : slice ≫ base = coefficient
  paired : J.obj k ⊗ J.obj τ ⟶ J.obj K
  paired_base : paired ≫ J.map base = fst (J.obj k) (J.obj τ) ≫ J.map coefficient
  paired_slice : timeSlice (J.obj k) τ 0 ≫ paired = J.map slice
  paired_vertex (a : Fin (k.len + 1)) :
    (parameterVertex k a ⊗ₘ 𝟙 (J.obj τ)) ≫ paired =
      snd (Δ[0] : SSet.{0}) (J.obj τ) ≫ J.map (vertical a)

variable {k τ K b : SimplexCategory} (D : PrismData k τ K b)

/-- The actual necklace coordinate remains fixed along the joining prism. -/
def graphPrism {X : SSet.{0}} (s : X ⟶ J.obj k) :
    X ⊗ J.obj τ ⟶ X ⊗ J.obj K :=
  lift (fst X (J.obj τ)) ((s ⊗ₘ 𝟙 (J.obj τ)) ≫ D.paired)

private theorem graphPrism_natural {X Y : SSet.{0}} (f : X ⟶ Y) (s : Y ⟶ J.obj k) :
    (f ⊗ₘ 𝟙 (J.obj τ)) ≫ graphPrism D s =
      graphPrism D (f ≫ s) ≫ (f ⊗ₘ 𝟙 (J.obj K)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

private theorem graphPrism_base {X : SSet.{0}} (s : X ⟶ J.obj k) :
    graphPrism D s ≫ (𝟙 X ⊗ₘ J.map D.base) =
      fst X (J.obj τ) ≫ lift (𝟙 X) (s ≫ J.map D.coefficient) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [D.paired_base, tensorHom_fst_assoc]

private theorem graphPrism_constant {X : SSet.{0}} (a : Fin (k.len + 1)) :
    graphPrism D (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) =
      𝟙 X ⊗ₘ J.map (D.vertical a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 (J.obj τ)), ← tensorHom_comp_tensorHom,
      Category.assoc, D.paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

private theorem graphPrism_slice {X : SSet.{0}} (s : X ⟶ J.obj k) :
    timeSlice X τ 0 ≫ graphPrism D s = lift (𝟙 X) (s ≫ J.map D.slice) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, graphPrism, Category.assoc, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, D.paired_slice]

private theorem tripleTensor_hom_ext (d : ℕ) (n : SimplexCategory) {Y : SSet.{0}}
    {f g : (code d).toSSet ⊗ J.obj n ⟶ Y}
    (hl : (L d ⊗ₘ 𝟙 (J.obj n)) ≫ f = (L d ⊗ₘ 𝟙 (J.obj n)) ≫ g)
    (hm : (M d ⊗ₘ 𝟙 (J.obj n)) ≫ f = (M d ⊗ₘ 𝟙 (J.obj n)) ≫ g)
    (hr : (P d ⊗ₘ 𝟙 (J.obj n)) ≫ f = (P d ⊗ₘ 𝟙 (J.obj n)) ≫ g) : f = g := by
  apply ((wedgeIsPushout A (wedge (B d) A)).map (tensorRight (J.obj n))).hom_ext
  · exact hl
  · apply ((wedgeIsPushout (B d) A).map (tensorRight (J.obj n))).hom_ext
    · change (wedgeιLeft (B d) A ⊗ₘ 𝟙 (J.obj n)) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 (J.obj n)) ≫ f =
        (wedgeιLeft (B d) A ⊗ₘ 𝟙 (J.obj n)) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 (J.obj n)) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hm
    · change (wedgeιRight (B d) A ⊗ₘ 𝟙 (J.obj n)) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 (J.obj n)) ≫ f =
        (wedgeιRight (B d) A ⊗ₘ 𝟙 (J.obj n)) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 (J.obj n)) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hr

private theorem local_time_invariance {X Y Z : SSet.{0}} (n : SimplexCategory) (j : X ⟶ Y)
    (m : Y ⊗ J.obj n ⟶ Z) (u : X ⟶ Z)
    (h : (j ⊗ₘ 𝟙 (J.obj n)) ≫ m = fst X (J.obj n) ≫ u) :
    (j ⊗ₘ 𝟙 (J.obj n)) ≫ m =
      (j ⊗ₘ 𝟙 (J.obj n)) ≫ fst Y (J.obj n) ≫ timeSlice Y n 0 ≫ m := by
  calc
    _ = fst X (J.obj n) ≫ u := h
    _ = fst X (J.obj n) ≫ timeSlice X n 0 ≫ (j ⊗ₘ 𝟙 (J.obj n)) ≫ m := by
      have hs : timeSlice X n 0 ≫ fst X (J.obj n) = 𝟙 X := lift_fst _ _
      rw [h, ← Category.assoc (timeSlice X n 0), hs, Category.id_comp]
    _ = _ := by
      simp only [tensorHom_fst_assoc]
      rw [← Category.assoc (timeSlice X n 0), timeSlice_natural, Category.assoc]

variable {W : Source} {d : ℕ}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (f : simplex b ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable (E : EdgeFamilies W ⦋d⦌ K (SSet.stdSimplex.map D.base ≫ f)
  (s ≫ J.map D.slice) x y)

private abbrev η :=
  orderedLabel W x y (code d) K (JTMixedGraphOrderedLabel.orderedPoint E)

private def productRaw : (code d).toSSet ⊗ J.obj τ ⟶ R W :=
  graphPrism D (nativeGraphParameter s) ≫ realizedLabel (code d).toSSet W K (η D f s E)

private theorem identity_edge_restrict (u : simplex K ⟶ row W ⦋1⦌)
    (j : τ ⟶ K) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hu : SSet.stdSimplex.map j ≫ u =
      term (simplex τ) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (diagramTensor (discreteFree.obj A.toSSet)).map (SSet.stdSimplex.map j) ≫
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) =
    identityCoefficient W z τ := by
  change (TripleBeadEndpointLabel.labels W A).map j.op
    (SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  rw [← SSet.yonedaEquiv_map_comp, ← Category.assoc, hu]
  unfold identityCoefficient
  let r := SimplexCategory.const τ ⦋0⦌ 0
  change _ = (TripleBeadEndpointLabel.labels W A).map r.op
    (JTIdentityRowRealization.identityEdgeLabel W z)
  rw [JTIdentityRowRealization.identityEdgeLabel]
  erw [← SSet.yonedaEquiv_map_comp]
  have H : SSet.stdSimplex.map r = term (simplex τ) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [H]
  simp only [Category.assoc]

private theorem side_factor (i : A.toSSet ⟶ (code d).toSSet)
    (v : Fin (k.len + 1)) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (u : simplex K ⟶ row W ⦋1⦌)
    (hi : i ≫ nativeGraphParameter s = constantParameter A k v)
    (hlabel : Functor.whiskerRight (discreteFree.map i)
        (tensorRight (simplex K)) ≫ η D f s E =
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W))
    (hEdge : SSet.stdSimplex.map (D.vertical v) ≫ u =
      term (simplex τ) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (i ⊗ₘ 𝟙 (J.obj τ)) ≫ productRaw D f s E =
      fst A.toSSet (J.obj τ) ≫ (term A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    realizedLabel_natural_X, hi]
  erw [hlabel]
  change graphPrism D (term A.toSSet ≫ parameterVertex k v) ≫ _ = _
  rw [graphPrism_constant, realizedLabel_natural_k]
  erw [identity_edge_restrict u (D.vertical v) z hEdge]
  rw [realizedIdentityCoefficient, ← Category.assoc]
  congr 1

private theorem middle_factor :
    (M d ⊗ₘ 𝟙 (J.obj τ)) ≫ productRaw D f s E =
      fst (B d).toSSet (J.obj τ) ≫
        realizeGraph W b (((singleIso d).hom ≫ s) ≫ J.map D.coefficient)
          (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc]
  erw [realizedLabel_natural_X (M d) W K (η D f s E)]
  erw [TripleBeadEndpointLabel.orderedPoint_middle_coefficient (JTMixedGraphOrderedLabel.families E)]
  have hp : M d ≫ nativeGraphParameter s = (singleIso d).hom ≫ s := by
    unfold nativeGraphParameter
    rw [graphParameter_middle]
  rw [hp]
  have hc :
      (diagramTensor (discreteFree.obj (B d).toSSet)).map
          (SSet.stdSimplex.map D.base) ≫
        SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d) =
      SSet.yonedaEquiv ((SSet.stdSimplex.map D.base ≫ f) ≫
        JTNativeRowLabel.labelFromRow W d) := by
    change (TripleBeadEndpointLabel.labels W (B d)).map D.base.op
      (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) = _
    rw [← SSet.yonedaEquiv_map_comp, Category.assoc]
    rfl
  erw [← hc, ← realizedLabel_natural_k]
  rw [← Category.assoc, graphPrism_base, Category.assoc]
  rfl

private theorem productRaw_time_invariant
    (hL : SSet.stdSimplex.map (D.vertical (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex τ) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (D.vertical (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex τ) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    productRaw D f s E =
      fst (code d).toSSet (J.obj τ) ≫ timeSlice (code d).toSSet τ 0 ≫
        productRaw D f s E := by
  apply tripleTensor_hom_ext d τ
  · apply local_time_invariance τ
    apply side_factor D f s E (L d) (graphIndex ⦋d⦌ k s 0) x E.left _ _ hL
    · unfold nativeGraphParameter
      rw [graphParameter_left]
    · exact TripleBeadEndpointLabel.orderedPoint_left_coefficient (JTMixedGraphOrderedLabel.families E)
  · apply local_time_invariance τ
    exact middle_factor D f s E
  · apply local_time_invariance τ
    apply side_factor D f s E (P d) (graphIndex ⦋d⦌ k s (Fin.last d)) y E.right _ _ hR
    · unfold nativeGraphParameter
      rw [graphParameter_right]
    · exact TripleBeadEndpointLabel.orderedPoint_right_coefficient (JTMixedGraphOrderedLabel.families E)

/-- The whole joining cylinder has the same original raw target map. -/
theorem whole_raw {q : (single d).toSSet ⟶ R W}
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map D.coefficient ≫ f) s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (hL : SSet.stdSimplex.map (D.vertical (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex τ) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (D.vertical (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex τ) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W)
    (C : (value (code d)).obj τ ⟶ (value (code d)).obj K)
    (hC : (cylinder (code d)).app τ ≫ C =
      graphPrism D (nativeGraphParameter s) ≫ (cylinder (code d)).app K)
    (hB : (boundary (code d)).app τ ≫ C = (boundary (code d)).app K) :
    C ≫
        descend W x y (code d) K (JTMixedGraphOrderedLabel.orderedPoint E) =
      augmentation (code d) τ ≫ (collapseOuter d).map ≫ q := by
  have hqK : nativeRawGraph W d K (SSet.stdSimplex.map D.base ≫ f)
      (s ≫ J.map D.slice) = q := by
    rw [nativeRawGraph_reindex, Category.assoc, ← J.map_comp, D.slice_base,
      ← nativeRawGraph_reindex]
    exact hq
  apply (isPushout (code d) τ).hom_ext
  · rw [← Category.assoc, hC, Category.assoc, descend_cylinder,
      ← Category.assoc ((cylinder (code d)).app τ), augmentation_cylinder]
    change productRaw D f s E = _
    rw [productRaw_time_invariant D f s E hL hR]
    unfold productRaw
    rw [← Category.assoc (timeSlice (code d).toSSet τ 0), graphPrism_slice]
    change fst (code d).toSSet (J.obj τ) ≫ realizeGraph W K
      (nativeGraphParameter s ≫ GroupoidSimplex.parameter.map D.slice)
      (η D f s E) = _
    rw [nativeGraphParameter_map D.slice s]
    exact congrArg (fun u ↦ fst (code d).toSSet (J.obj τ) ≫ u)
      (refinementOfGraph E hqK qx qy).comm
  · rw [← Category.assoc, hB, descend_boundary,
      ← Category.assoc ((boundary (code d)).app τ), augmentation_boundary,
      ← Category.assoc (endpointInclusion (code d)), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, qx, qy]


end

end DaggerModels.PartII.JTRowGraphPrismRaw
