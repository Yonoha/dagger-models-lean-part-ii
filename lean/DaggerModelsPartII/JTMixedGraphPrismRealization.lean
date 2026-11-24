import DaggerModelsPartII.JTGraphPrismCylinder
import DaggerModelsPartII.JTMixedGraphRawRefinement

/-!
# The whole mixed graph prism has a time-independent raw realization
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphPrismRealization

open JTInterleavedParameter JTGroupoidParameterPrism JTGraphPrismCylinder
open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement JTNecklaceLabelRealization
open JTRealizedLabelEndpoints JTGraphRefinement ReversalDiscreteFreeColimits
open MixedGraphCylinderTraversal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev I := J.obj ⦋1⦌
private abbrev K := common
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev A := single 1
private abbrev B (d : ℕ) := single d
private abbrev L (d : ℕ) := tripleRightT.{0} A (B d) A
private abbrev M (d : ℕ) := tripleRightU.{0} A (B d) A
private abbrev P (d : ℕ) := tripleRightV.{0} A (B d) A
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private theorem tripleTensor_hom_ext (d : ℕ) {Y : SSet.{0}}
    {f g : (code d).toSSet ⊗ I ⟶ Y}
    (hl : (L d ⊗ₘ 𝟙 I) ≫ f = (L d ⊗ₘ 𝟙 I) ≫ g)
    (hm : (M d ⊗ₘ 𝟙 I) ≫ f = (M d ⊗ₘ 𝟙 I) ≫ g)
    (hr : (P d ⊗ₘ 𝟙 I) ≫ f = (P d ⊗ₘ 𝟙 I) ≫ g) : f = g := by
  apply ((wedgeIsPushout A (wedge (B d) A)).map (tensorRight I)).hom_ext
  · exact hl
  · apply ((wedgeIsPushout (B d) A).map (tensorRight I)).hom_ext
    · change (wedgeιLeft (B d) A ⊗ₘ 𝟙 I) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 I) ≫ f =
        (wedgeιLeft (B d) A ⊗ₘ 𝟙 I) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 I) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hm
    · change (wedgeιRight (B d) A ⊗ₘ 𝟙 I) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 I) ≫ f =
        (wedgeιRight (B d) A ⊗ₘ 𝟙 I) ≫ (wedgeιRight A (wedge (B d) A) ⊗ₘ 𝟙 I) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hr

private theorem local_time_invariance {X Y Z : SSet.{0}} (j : X ⟶ Y)
    (m : Y ⊗ I ⟶ Z) (u : X ⟶ Z)
    (h : (j ⊗ₘ 𝟙 I) ≫ m = fst X I ≫ u) :
    (j ⊗ₘ 𝟙 I) ≫ m =
      (j ⊗ₘ 𝟙 I) ≫ fst Y I ≫ timeSlice Y 0 ≫ m := by
  calc
    (j ⊗ₘ 𝟙 I) ≫ m = fst X I ≫ u := h
    _ = fst X I ≫ timeSlice X 0 ≫ (j ⊗ₘ 𝟙 I) ≫ m := by
      rw [h, ← Category.assoc (timeSlice X 0), timeSlice_fst, Category.id_comp]
    _ = _ := by
      simp only [tensorHom_fst_assoc]
      rw [← Category.assoc (timeSlice X 0), timeSlice_natural, Category.assoc]

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (f : Δ k ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
variable (E : EdgeFamilies W ⦋d⦌ (K k) (SSet.stdSimplex.map (ret k) ≫ f)
  (s ≫ J.map (slice k 0)) x y)

private abbrev η :=
  orderedLabel W x y (code d) (K k) (JTMixedGraphOrderedLabel.orderedPoint E)

private abbrev a := graphIndex ⦋d⦌ k s 0
private abbrev b := graphIndex ⦋d⦌ k s (Fin.last d)

/-- The raw realization of the full graph prism with its enlarged label. -/
def productRaw : (code d).toSSet ⊗ I ⟶ R W :=
  graphPrism (nativeGraphParameter s) ≫ realizedLabel (code d).toSSet W (K k) (η f s E)

private theorem identity_edge_restrict (u : Δ (K k) ⟶ row W ⦋1⦌)
    (j : ⦋1⦌ ⟶ K k) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hu : SSet.stdSimplex.map j ≫ u =
      term (Δ ⦋1⦌) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (diagramTensor (discreteFree.obj A.toSSet)).map (SSet.stdSimplex.map j) ≫
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) =
    identityCoefficient W z ⦋1⦌ := by
  change (TripleBeadEndpointLabel.labels W A).map j.op
    (SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  rw [← SSet.yonedaEquiv_map_comp, ← Category.assoc, hu]
  unfold identityCoefficient
  let r := SimplexCategory.const ⦋1⦌ ⦋0⦌ 0
  change _ = (TripleBeadEndpointLabel.labels W A).map r.op
    (JTIdentityRowRealization.identityEdgeLabel W z)
  rw [JTIdentityRowRealization.identityEdgeLabel]
  erw [← SSet.yonedaEquiv_map_comp]
  have h : SSet.stdSimplex.map r = term (Δ ⦋1⦌) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]
  simp only [Category.assoc]

private theorem side_factor (i : A.toSSet ⟶ (code d).toSSet)
    (v : Fin (k.len + 1)) (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (u : Δ (K k) ⟶ row W ⦋1⦌)
    (hi : i ≫ nativeGraphParameter s = constantParameter A k v)
    (hlabel : Functor.whiskerRight (discreteFree.map i)
        (tensorRight (Δ (K k))) ≫ η f s E =
      SSet.yonedaEquiv (u ≫ TwoBeadEndpointLabel.edgeLabelFromRow W))
    (hEdge : SSet.stdSimplex.map (edge k v) ≫ u =
      term (Δ ⦋1⦌) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) :
    (i ⊗ₘ 𝟙 I) ≫ productRaw f s E =
      fst A.toSSet I ≫ (term A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    realizedLabel_natural_X, hi]
  erw [hlabel]
  change graphPrism (term A.toSSet ≫ JTParameterContraction.parameterVertex k v) ≫ _ = _
  rw [graphPrism_constant, realizedLabel_natural_k]
  erw [identity_edge_restrict u (edge k v) z hEdge]
  rw [realizedIdentityCoefficient, ← Category.assoc]
  congr 1

private theorem middle_factor :
    (M d ⊗ₘ 𝟙 I) ≫ productRaw f s E =
      fst (B d).toSSet I ≫
        realizeGraph W k ((singleIso d).hom ≫ s)
          (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) := by
  unfold productRaw
  rw [← Category.assoc, graphPrism_natural, Category.assoc]
  erw [realizedLabel_natural_X (M d) W (K k) (η f s E)]
  erw [TripleBeadEndpointLabel.orderedPoint_middle_coefficient
    (JTMixedGraphOrderedLabel.families E)]
  have hp : M d ≫ nativeGraphParameter s = (singleIso d).hom ≫ s := by
    unfold nativeGraphParameter
    rw [graphParameter_middle]
  rw [hp]
  have hc :
      (diagramTensor (discreteFree.obj (B d).toSSet)).map
          (SSet.stdSimplex.map (ret k)) ≫
        SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d) =
      SSet.yonedaEquiv ((SSet.stdSimplex.map (ret k) ≫ f) ≫
        JTNativeRowLabel.labelFromRow W d) := by
    change (TripleBeadEndpointLabel.labels W (B d)).map (ret k).op
      (SSet.yonedaEquiv (f ≫ JTNativeRowLabel.labelFromRow W d)) = _
    rw [← SSet.yonedaEquiv_map_comp, Category.assoc]
    rfl
  erw [← hc, ← realizedLabel_natural_k]
  rw [← Category.assoc, graphPrism_ret, Category.assoc]
  rfl

/-- In the actual raw realization, the entire mixed prism factors through
either fixed traversal. The chosen vertex edges of the outside families
are prescribed on all of the duplicate interval, not just its endpoints. -/
theorem productRaw_time_invariant
    (hl : SSet.stdSimplex.map (edge k (a s)) ≫ E.left =
      term (Δ ⦋1⦌) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hr : SSet.stdSimplex.map (edge k (b s)) ≫ E.right =
      term (Δ ⦋1⦌) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    productRaw f s E =
      fst (code d).toSSet I ≫ timeSlice (code d).toSSet 0 ≫ productRaw f s E := by
  apply tripleTensor_hom_ext d
  · apply local_time_invariance
    apply side_factor f s E (L d) (a s) x E.left _ _ hl
    · unfold nativeGraphParameter
      rw [graphParameter_left]
    · exact TripleBeadEndpointLabel.orderedPoint_left_coefficient
        (JTMixedGraphOrderedLabel.families E)
  · apply local_time_invariance
    exact middle_factor f s E
  · apply local_time_invariance
    apply side_factor f s E (P d) (b s) y E.right _ _ hr
    · unfold nativeGraphParameter
      rw [graphParameter_right]
    · exact TripleBeadEndpointLabel.orderedPoint_right_coefficient
        (JTMixedGraphOrderedLabel.families E)

end

end DaggerModels.PartII.JTMixedGraphPrismRealization
