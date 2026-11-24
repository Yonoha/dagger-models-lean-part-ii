import DaggerModelsPartII.JTHigherGraphPrismCylinder
import DaggerModelsPartII.JTCommonCoefficientCylinder
import DaggerModelsPartII.JTMixedGraphRawRefinement

/-!
# Higher-time mixed graph prisms have a time-independent raw realization
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTHigherMixedGraphPrismRealization

open JTHigherInterleavedParameter JTHigherGroupoidParameterPrism JTHigherGraphPrismCylinder
open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement JTNecklaceLabelRealization
open JTRealizedLabelEndpoints JTGraphRefinement ReversalDiscreteFreeColimits
open MixedGraphCylinderTraversal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev K := common
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev A := single 1
private abbrev B (d : ℕ) := single d
private abbrev L (d : ℕ) := tripleRightT.{0} A (B d) A
private abbrev M (d : ℕ) := tripleRightU.{0} A (B d) A
private abbrev P (d : ℕ) := tripleRightV.{0} A (B d) A
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

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

private theorem higher_timeSlice_fst (X : SSet.{0}) (n : SimplexCategory)
    (t : Fin (n.len + 1)) :
    timeSlice X n t ≫ fst X (J.obj n) = 𝟙 X := by
  exact lift_fst _ _

private theorem local_time_invariance {X Y Z : SSet.{0}} (n : SimplexCategory) (j : X ⟶ Y)
    (m : Y ⊗ J.obj n ⟶ Z) (u : X ⟶ Z)
    (h : (j ⊗ₘ 𝟙 (J.obj n)) ≫ m = fst X (J.obj n) ≫ u) :
    (j ⊗ₘ 𝟙 (J.obj n)) ≫ m =
      (j ⊗ₘ 𝟙 (J.obj n)) ≫ fst Y (J.obj n) ≫ timeSlice Y n 0 ≫ m := by
  calc
    (j ⊗ₘ 𝟙 (J.obj n)) ≫ m = fst X (J.obj n) ≫ u := h
    _ = fst X (J.obj n) ≫ timeSlice X n 0 ≫ (j ⊗ₘ 𝟙 (J.obj n)) ≫ m := by
      rw [h, ← Category.assoc (timeSlice X n 0), higher_timeSlice_fst, Category.id_comp]
    _ = _ := by
      simp only [tensorHom_fst_assoc]
      rw [← Category.assoc (timeSlice X n 0), timeSlice_natural, Category.assoc]

variable {W : Source} {d : ℕ} {k n : SimplexCategory}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (f : Δ k ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable (E : EdgeFamilies W ⦋d⦌ (K k n) (SSet.stdSimplex.map (ret k n) ≫ f)
  (s ≫ J.map (slice k n 0)) x y)

private abbrev η :=
  orderedLabel W x y (code d) (K k n) (JTMixedGraphOrderedLabel.orderedPoint E)

private abbrev a := graphIndex ⦋d⦌ k s 0
private abbrev b := graphIndex ⦋d⦌ k s (Fin.last d)

/-- The raw realization of the full graph prism with its enlarged label. -/
def productRaw : (code d).toSSet ⊗ J.obj n ⟶ R W :=
  graphPrism (nativeGraphParameter s) n ≫ realizedLabel (code d).toSSet W (K k n) (η f s E)

/-- Every time slice is the exact enlarged graph at that time vertex. -/
theorem productRaw_slice (t : Fin (n.len + 1)) :
    timeSlice (code d).toSSet n t ≫ productRaw f s E =
      realizeGraph W (K k n)
        (nativeGraphParameter s ≫ J.map (slice k n t)) (η f s E) := by
  unfold productRaw realizeGraph
  rw [← Category.assoc, graphPrism_slice]

/-- The raw prism is the cylinder leg of the descended map. -/
theorem productRaw_cylinder :
    (JTNecklaceEndpointCylinder.cylinder (code d)).app n ≫
        cylinderMap (code d) (nativeGraphParameter s) n ≫
          JTNecklaceEndpointCylinder.descend W x y (code d) (K k n)
            (JTMixedGraphOrderedLabel.orderedPoint E) = productRaw f s E := by
  rw [← Category.assoc, cylinderMap_cylinder, Category.assoc,
    JTNecklaceEndpointCylinder.descend_cylinder]
  rfl

private theorem identity_edge_restrict {l : SimplexCategory} (u : Δ l ⟶ row W ⦋1⦌)
    (j : n ⟶ l) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hu : SSet.stdSimplex.map j ≫ u =
      term (Δ n) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (diagramTensor (discreteFree.obj A.toSSet)).map (SSet.stdSimplex.map j) ≫
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) =
    identityCoefficient W z n := by
  change (TripleBeadEndpointLabel.labels W A).map j.op
    (SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  rw [← SSet.yonedaEquiv_map_comp, ← Category.assoc, hu]
  unfold identityCoefficient
  let r := SimplexCategory.const n ⦋0⦌ 0
  change _ = (TripleBeadEndpointLabel.labels W A).map r.op
    (JTIdentityRowRealization.identityEdgeLabel W z)
  rw [JTIdentityRowRealization.identityEdgeLabel]
  erw [← SSet.yonedaEquiv_map_comp]
  have h : SSet.stdSimplex.map r = term (Δ n) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]
  simp only [Category.assoc]

private theorem side_factor (i : A.toSSet ⟶ (code d).toSSet)
    (v : Fin (k.len + 1)) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (u : Δ (K k n) ⟶ row W ⦋1⦌)
    (hi : i ≫ nativeGraphParameter s = constantParameter A k v)
    (hlabel : Functor.whiskerRight (discreteFree.map i)
        (tensorRight (Δ (K k n))) ≫ η f s E =
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W))
    (hEdge : SSet.stdSimplex.map (vertical k n v) ≫ u =
      term (Δ n) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (i ⊗ₘ 𝟙 (J.obj n)) ≫ productRaw f s E =
      fst A.toSSet (J.obj n) ≫ (term A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    realizedLabel_natural_X, hi]
  erw [hlabel]
  change graphPrism (term A.toSSet ≫ JTParameterContraction.parameterVertex k v) n ≫ _ = _
  rw [graphPrism_constant, realizedLabel_natural_k]
  erw [identity_edge_restrict u (vertical k n v) z hEdge]
  rw [realizedIdentityCoefficient, ← Category.assoc]
  congr 1

private theorem middle_factor :
    (M d ⊗ₘ 𝟙 (J.obj n)) ≫ productRaw f s E =
      fst (B d).toSSet (J.obj n) ≫
        realizeGraph W k ((singleIso d).hom ≫ s)
          (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc]
  erw [realizedLabel_natural_X (M d) W (K k n) (η f s E)]
  erw [TripleBeadEndpointLabel.orderedPoint_middle_coefficient
    (JTMixedGraphOrderedLabel.families E)]
  have hp : M d ≫ nativeGraphParameter s = (singleIso d).hom ≫ s := by
    unfold nativeGraphParameter
    rw [graphParameter_middle]
  rw [hp]
  have hc :
      (diagramTensor (discreteFree.obj (B d).toSSet)).map
          (SSet.stdSimplex.map (ret k n)) ≫
        SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d) =
      SSet.yonedaEquiv ((SSet.stdSimplex.map (ret k n) ≫ f) ≫
        JTNativeRowLabel.labelFromRow W d) := by
    change (TripleBeadEndpointLabel.labels W (B d)).map (ret k n).op
      (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) = _
    rw [← SSet.yonedaEquiv_map_comp, Category.assoc]
    rfl
  erw [← hc, ← realizedLabel_natural_k]
  rw [← Category.assoc, graphPrism_ret, Category.assoc]
  rfl

/-- In the actual raw realization, the entire mixed prism factors through
the fixed zero-time traversal. The chosen vertex edges of the outside families
are prescribed on the full vertical time simplex. -/
theorem productRaw_time_invariant
    (hl : SSet.stdSimplex.map (vertical k n (a s)) ≫ E.left =
      term (Δ n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hr : SSet.stdSimplex.map (vertical k n (b s)) ≫ E.right =
      term (Δ n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    productRaw f s E =
      fst (code d).toSSet (J.obj n) ≫ timeSlice (code d).toSSet n 0 ≫ productRaw f s E := by
  apply tripleTensor_hom_ext d n
  · apply local_time_invariance n
    apply side_factor f s E (L d) (a s) x E.left _ _ hl
    · unfold nativeGraphParameter
      rw [graphParameter_left]
    · exact TripleBeadEndpointLabel.orderedPoint_left_coefficient
        (JTMixedGraphOrderedLabel.families E)
  · apply local_time_invariance n
    exact middle_factor f s E
  · apply local_time_invariance n
    apply side_factor f s E (P d) (b s) y E.right _ _ hr
    · unfold nativeGraphParameter
      rw [graphParameter_right]
    · exact TripleBeadEndpointLabel.orderedPoint_right_coefficient
        (JTMixedGraphOrderedLabel.families E)


section CommonCoefficient

variable {B₀ : SimplexCategory} (c : k ⟶ B₀)
variable (g : Δ B₀ ⟶ row W ⦋d⦌)
variable (F : EdgeFamilies W ⦋d⦌ (K k n)
  (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ g)
  (s ≫ J.map (JTCommonCoefficientParameter.slice c n 0)) x y)

private abbrev commonLabel := orderedLabel W x y (code d) (K k n)
  (JTMixedGraphOrderedLabel.orderedPoint F)

/-- The realization of a complete groupoid prism with the actual
common-coefficient ordered label. -/
def commonProductRaw : (code d).toSSet ⊗ J.obj n ⟶ R W :=
  JTCommonCoefficientParameter.graphPrism c (nativeGraphParameter s) n ≫
    realizedLabel (code d).toSSet W (K k n) (commonLabel s c g F)

theorem commonProductRaw_slice (t : Fin (n.len + 1)) :
    timeSlice (code d).toSSet n t ≫ commonProductRaw s c g F =
      realizeGraph W (K k n)
        (nativeGraphParameter s ≫ J.map (JTCommonCoefficientParameter.slice c n t))
        (commonLabel s c g F) := by
  unfold commonProductRaw realizeGraph
  rw [← Category.assoc, JTCommonCoefficientParameter.graphPrism_slice]

theorem commonProductRaw_cylinder :
    (JTNecklaceEndpointCylinder.cylinder (code d)).app n ≫
        JTCommonCoefficientParameter.cylinderMap (code d) c (nativeGraphParameter s) n ≫
          JTNecklaceEndpointCylinder.descend W x y (code d) (K k n)
            (JTMixedGraphOrderedLabel.orderedPoint F) = commonProductRaw s c g F := by
  rw [← Category.assoc, JTCommonCoefficientParameter.cylinderMap_cylinder, Category.assoc,
    JTNecklaceEndpointCylinder.descend_cylinder]
  rfl

private theorem common_side_factor (i : A.toSSet ⟶ (code d).toSSet)
    (v : Fin (k.len + 1)) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (u : Δ (K k n) ⟶ row W ⦋1⦌)
    (hi : i ≫ nativeGraphParameter s = constantParameter A k v)
    (hlabel : Functor.whiskerRight (discreteFree.map i)
        (tensorRight (Δ (K k n))) ≫ commonLabel s c g F =
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W))
    (hEdge : SSet.stdSimplex.map (JTCommonCoefficientParameter.vertical c n v) ≫ u =
      term (Δ n) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (i ⊗ₘ 𝟙 (J.obj n)) ≫ commonProductRaw s c g F =
      fst A.toSSet (J.obj n) ≫ (term A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) := by
  unfold commonProductRaw
  rw [← Category.assoc, JTCommonCoefficientParameter.graphPrism_natural, Category.assoc,
    realizedLabel_natural_X, hi]
  erw [hlabel]
  change JTCommonCoefficientParameter.graphPrism c
    (term A.toSSet ≫ JTParameterContraction.parameterVertex k v) n ≫ _ = _
  rw [JTCommonCoefficientParameter.graphPrism_constant, realizedLabel_natural_k]
  erw [identity_edge_restrict u (JTCommonCoefficientParameter.vertical c n v) z hEdge]
  rw [realizedIdentityCoefficient, ← Category.assoc]
  congr 1

private theorem common_middle_factor :
    (M d ⊗ₘ 𝟙 (J.obj n)) ≫ commonProductRaw s c g F =
      fst (B d).toSSet (J.obj n) ≫
        realizeGraph W B₀ (((singleIso d).hom ≫ s) ≫ J.map c)
          (SSet.yonedaEquiv (g ≫ JTNativeRowLabel.labelFromRow W d)) := by
  unfold commonProductRaw
  rw [← Category.assoc, JTCommonCoefficientParameter.graphPrism_natural, Category.assoc]
  erw [realizedLabel_natural_X (M d) W (K k n) (commonLabel s c g F)]
  erw [TripleBeadEndpointLabel.orderedPoint_middle_coefficient
    (JTMixedGraphOrderedLabel.families F)]
  have hp : M d ≫ nativeGraphParameter s = (singleIso d).hom ≫ s := by
    unfold nativeGraphParameter
    rw [graphParameter_middle]
  rw [hp]
  let β := JTCommonCoefficientParameter.base c n
  have hc : (diagramTensor (discreteFree.obj (B d).toSSet)).map (SSet.stdSimplex.map β) ≫
        SSet.yonedaEquiv (g ≫ JTNativeRowLabel.labelFromRow W d) =
      SSet.yonedaEquiv ((SSet.stdSimplex.map β ≫ g) ≫ JTNativeRowLabel.labelFromRow W d) := by
    change (TripleBeadEndpointLabel.labels W (B d)).map β.op
      (SSet.yonedaEquiv (g ≫ JTNativeRowLabel.labelFromRow W d)) = _
    rw [← SSet.yonedaEquiv_map_comp, Category.assoc]
    rfl
  erw [← hc, ← realizedLabel_natural_k]
  rw [← Category.assoc, JTCommonCoefficientParameter.graphPrism_base, Category.assoc]
  rfl

/-- Time-independence of the actual raw prism with two arbitrary chosen
common-coefficient enlargements which are stationary at the prescribed ends. -/
theorem commonProductRaw_time_invariant
    (hl : SSet.stdSimplex.map (JTCommonCoefficientParameter.vertical c n (a s)) ≫ F.left =
      term (Δ n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hr : SSet.stdSimplex.map (JTCommonCoefficientParameter.vertical c n (b s)) ≫ F.right =
      term (Δ n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    commonProductRaw s c g F =
      fst (code d).toSSet (J.obj n) ≫ timeSlice (code d).toSSet n 0 ≫
        commonProductRaw s c g F := by
  apply tripleTensor_hom_ext d n
  · apply local_time_invariance n
    apply common_side_factor s c g F (L d) (a s) x F.left _ _ hl
    · unfold nativeGraphParameter
      rw [graphParameter_left]
    · exact TripleBeadEndpointLabel.orderedPoint_left_coefficient
        (JTMixedGraphOrderedLabel.families F)
  · apply local_time_invariance n
    exact common_middle_factor s c g F
  · apply local_time_invariance n
    apply common_side_factor s c g F (P d) (b s) y F.right _ _ hr
    · unfold nativeGraphParameter
      rw [graphParameter_right]
    · exact TripleBeadEndpointLabel.orderedPoint_right_coefficient
        (JTMixedGraphOrderedLabel.families F)

end CommonCoefficient

end
end DaggerModels.PartII.JTHigherMixedGraphPrismRealization
