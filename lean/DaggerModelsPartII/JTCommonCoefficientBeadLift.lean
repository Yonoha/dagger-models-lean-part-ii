import DaggerModelsPartII.JTHigherMixedGraphTargetLift

/-! The actual common-coefficient cylinder descends to the original raw simplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTHigherMixedGraphTargetLift

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTHigherInterleavedParameter (common)
open JTMixedGraphRawRefinement JTMixedGraphVerticalArrow MixedGraphCylinderTraversal
open JTHigherMixedGraphPrismRealization
open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open OrderedNecklaceVertexPoints
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {d : ℕ} {k b n : SimplexCategory} {x y : Vertex W}
variable (c : k ⟶ b) (f : simplex b ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {q : (single d).toSSet ⟶ Raw W}
variable (hq : nativeRawGraph W d b f (s ≫ J.map c) = q)
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
variable (E : EdgeFamilies W ⦋d⦌ (common k n)
  (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ f)
  (s ≫ J.map (JTCommonCoefficientParameter.slice c n 0)) x y)

include hq qx qy in
/-- The full common-coefficient prism with its actual label has the same raw
composite as the original augmentation followed by the outer collapse. -/
theorem common_whole_raw
    (hL : SSet.stdSimplex.map
        (JTCommonCoefficientParameter.vertical c n (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map
        (JTCommonCoefficientParameter.vertical c n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    JTCommonCoefficientParameter.cylinderMap (code d) c (nativeGraphParameter s) n ≫
        descend W x y (code d) (common k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
      augmentation (code d) n ≫ (collapseOuter d).map ≫ q := by
  have hqK : nativeRawGraph W d (common k n)
      (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ f)
      (s ≫ J.map (JTCommonCoefficientParameter.slice c n 0)) = q := by
    rw [nativeRawGraph_reindex, Category.assoc, ← J.map_comp,
      JTCommonCoefficientParameter.slice_base]
    exact hq
  apply (isPushout (code d) n).hom_ext
  · rw [commonProductRaw_cylinder, ← Category.assoc ((cylinder (code d)).app n),
      augmentation_cylinder]
    rw [commonProductRaw_time_invariant s c f E hL hR, commonProductRaw_slice,
      nativeGraphParameter_map]
    exact congrArg (fun u ↦ CartesianMonoidalCategory.fst (code d).toSSet (J.obj n) ≫ u)
      (refinementOfGraph E hqK qx qy).comm
  · rw [← Category.assoc, JTCommonCoefficientParameter.cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary (code d)).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion (code d)), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, qx, qy]

/-- The complete common-coefficient cylinder comparison under the actual endpoints. -/
def commonToDecorated : (under (code d)).obj n ⟶ (under (code d)).obj (common k n) :=
  Under.homMk (JTCommonCoefficientParameter.cylinderMap (code d) c (nativeGraphParameter s) n)
    (JTCommonCoefficientParameter.cylinderMap_boundary (code d) c (nativeGraphParameter s) n)


/-- The actual common-coefficient cylinder map preserves the original
coefficient and injective time arrows under both endpoints. -/
theorem commonToDecorated_natural {l m : SimplexCategory} {c' : l ⟶ b}
    (a : k ⟶ l) (ha : a ≫ c' = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (s' : simplex ⦋d⦌ ⟶ J.obj l) (hs : s ≫ J.map a = s') :
    commonToDecorated (n := n) c s ≫
        (under (code d)).map (JTCommonCoefficientParameter.map a ha j hj) =
      (under (code d)).map j ≫ commonToDecorated (n := m) c' s' := by
  apply Under.UnderMorphism.ext
  change JTCommonCoefficientParameter.cylinderMap (code d) c (nativeGraphParameter s) n ≫
      (value (code d)).map (JTCommonCoefficientParameter.map a ha j hj) =
    (value (code d)).map j ≫ JTCommonCoefficientParameter.cylinderMap (code d) c'
      (nativeGraphParameter s') m
  apply JTCommonCoefficientParameter.cylinderMap_map
  rw [nativeGraphParameter_map, hs]

private abbrev targetBead := (⟨single d, q, qx, qy⟩ :
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

variable {c f s} in
private abbrev commonIndex :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code d) (common k n)
    (JTMixedGraphOrderedLabel.orderedPoint E)

variable (hraw : JTCommonCoefficientParameter.cylinderMap (code d) c (nativeGraphParameter s) n ≫
    descend W x y (code d) (common k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
  augmentation (code d) n ≫ (collapseOuter d).map ≫ q)

/-- The full common-coefficient cylinder maps into the original decorated
and native pullback over the chosen raw bead. -/
def commonLift :
    (under (code d)).obj n ⟶
      (JTTargetCommaPullback.diagram W x y (targetBead qx qy)).obj (commonIndex E) :=
  pullback.lift (commonToDecorated c s) (toNativeTarget d n) (by
    apply Under.UnderMorphism.ext
    exact hraw)

@[reassoc]
theorem commonLift_decorated :
    commonLift c f s qx qy E hraw ≫
      JTTargetCommaPullback.fst W x y (targetBead qx qy) (commonIndex E) =
        commonToDecorated c s :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem commonLift_native :
    commonLift c f s qx qy E hraw ≫
      JTTargetCommaPullback.snd W x y (targetBead qx qy) (commonIndex E) =
        toNativeTarget d n :=
  pullback.lift_snd _ _ _

end
end DaggerModels.PartII.JTHigherMixedGraphTargetLift
