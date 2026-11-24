import DaggerModelsPartII.JTHigherMixedGraphPrismRealization
import DaggerModelsPartII.JTMixedGraphVerticalArrow
import DaggerModelsPartII.JTHigherCommonMixedGraphFamilies
import DaggerModelsPartII.JTTargetCommaPullback

/-!
# Higher mixed graph comparisons over the actual native target
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTHigherMixedGraphTargetLift

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTHigherInterleavedParameter JTHigherGraphPrismCylinder
open JTMixedGraphRawRefinement JTMixedGraphVerticalArrow MixedGraphCylinderTraversal
open JTHigherMixedGraphPrismRealization
open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open OrderedNecklaceVertexPoints JTTargetCommaPullback
open DecoratedCylinderNecklacePresentation (underCocone underDiagram)
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

variable {W : Source} {d : ℕ} {k n : SimplexCategory} {x y : Vertex W}
variable (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {q : (single d).toSSet ⟶ Raw W}
variable (hq : nativeRawGraph W d k f s = q)
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
variable (E : EdgeFamilies W ⦋d⦌ (common k n) (SSet.stdSimplex.map (ret k n) ≫ f)
  (s ≫ J.map (slice k n 0)) x y)

private abbrev target := (⟨single d, q, qx, qy⟩ :
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

variable {f s} in
private abbrev index :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code d) (common k n)
    (JTMixedGraphOrderedLabel.orderedPoint E)

include hq qx qy in
/-- The entire higher prism composed with the actual descended label equals
the original native collapse followed by the original raw target map. -/
theorem whole_raw
    (hL : SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    cylinderMap (code d) (nativeGraphParameter s) n ≫
        descend W x y (code d) (common k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
      augmentation (code d) n ≫ (collapseOuter d).map ≫ q := by
  have hqK : nativeRawGraph W d (common k n) (SSet.stdSimplex.map (ret k n) ≫ f)
      (s ≫ J.map (slice k n 0)) = q := by
    rw [nativeRawGraph_reindex, Category.assoc, ← J.map_comp, slice_ret,
      J.map_id, Category.comp_id]
    exact hq
  apply (isPushout (code d) n).hom_ext
  · rw [productRaw_cylinder, ← Category.assoc ((cylinder (code d)).app n),
      augmentation_cylinder]
    rw [productRaw_time_invariant f s E hL hR, productRaw_slice, nativeGraphParameter_map]
    exact congrArg (fun u ↦ CartesianMonoidalCategory.fst (code d).toSSet (J.obj n) ≫ u)
      (refinementOfGraph E hqK qx qy).comm
  · rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary (code d)).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion (code d)), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, qx, qy]

/-- The augmentation and native collapse, as one map under the actual ends. -/
def toNativeTarget (d : ℕ) (n : SimplexCategory) :
    (under (code d)).obj n ⟶ necklaceUnder.obj (single d) :=
  Under.homMk (augmentation (code d) n ≫ (collapseOuter d).map) (by
    change (boundary (code d)).app n ≫ augmentation (code d) n ≫ (collapseOuter d).map =
      endpointInclusion (single d)
    rw [← Category.assoc, augmentation_boundary, endpointInclusion_natural])

theorem toNativeTarget_natural (d : ℕ) {m n : SimplexCategory} (j : m ⟶ n) :
    (under (code d)).map j ≫ toNativeTarget d n = toNativeTarget d m := by
  apply Under.UnderMorphism.ext
  change (value (code d)).map j ≫ augmentation (code d) n ≫ (collapseOuter d).map = _
  rw [← Category.assoc, augmentation_parameter_natural]
  rfl

/-- The graph comparison under the two original endpoints. -/
def toDecorated (d : ℕ) {k : SimplexCategory}
    (s : simplex ⦋d⦌ ⟶ J.obj k) (n : SimplexCategory) :
    (under (code d)).obj n ⟶ (under (code d)).obj (common k n) :=
  Under.homMk (cylinderMap (code d) (nativeGraphParameter s) n)
    (cylinderMap_boundary (code d) (nativeGraphParameter s) n)

/-- A full prism map into the pullback of the original decorated cylinder
and the actual native target over the raw realization. -/
def lift
    (hraw : cylinderMap (code d) (nativeGraphParameter s) n ≫
        descend W x y (code d) (common k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
      augmentation (code d) n ≫ (collapseOuter d).map ≫ q) :
    (under (code d)).obj n ⟶ (diagram W x y (target qx qy)).obj (index E) :=
  pullback.lift (toDecorated d s n) (toNativeTarget d n) (by
    apply Under.UnderMorphism.ext
    exact hraw)

variable (hraw : cylinderMap (code d) (nativeGraphParameter s) n ≫
      descend W x y (code d) (common k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
    augmentation (code d) n ≫ (collapseOuter d).map ≫ q)

/-- The native projection retains the exact augmentation and collapse. -/
theorem lift_native :
    lift f s qx qy E hraw ≫ JTTargetCommaPullback.snd W x y (target qx qy) (index E) =
      toNativeTarget d n :=
  pullback.lift_snd _ _ _

/-- The decorated projection is the original full cylinder prism. -/
theorem lift_decorated :
    lift f s qx qy E hraw ≫ JTTargetCommaPullback.fst W x y (target qx qy) (index E) =
      toDecorated d s n :=
  pullback.lift_fst _ _ _

/-- The entire source cylinder in any time face or degeneracy maps into
the same decorated pullback. -/
def restrict {m : SimplexCategory} (j : m ⟶ n) :
    (under (code d)).obj m ⟶ (diagram W x y (target qx qy)).obj (index E) :=
  (under (code d)).map j ≫ lift f s qx qy E hraw

theorem restrict_native {m : SimplexCategory} (j : m ⟶ n) :
    restrict f s qx qy E hraw j ≫ JTTargetCommaPullback.snd W x y (target qx qy) (index E) =
      toNativeTarget d m := by
  rw [restrict, Category.assoc, lift_native, toNativeTarget_natural]

/-- Under the projection to the decorated cylinder the restricted map is
the actual lower-degree graph prism followed by its time operator. -/
theorem restrict_decorated {m : SimplexCategory} (j : m ⟶ n) :
    (restrict f s qx qy E hraw j ≫ JTTargetCommaPullback.fst W x y (target qx qy) (index E)).right =
      cylinderMap (code d) (nativeGraphParameter s) m ≫
        (value (code d)).map (mapTime k j) := by
  rw [restrict, Category.assoc, lift_decorated]
  exact (cylinderMap_mapTime (code d) (nativeGraphParameter s) j).symm

/-- The restrictions commute with all compositions of time operators in
the same original decorated pullback. -/
theorem restrict_comp {l m : SimplexCategory} (i : l ⟶ m) (j : m ⟶ n) :
    restrict f s qx qy E hraw (i ≫ j) =
      (under (code d)).map i ≫ restrict f s qx qy E hraw j := by
  rw [restrict, Functor.map_comp, Category.assoc]
  rfl

/-- The diagram of entire cylinders over the category of time simplices
mapping into the specified top time simplex. -/
def timeDiagram (d : ℕ) (n : SimplexCategory) :
    Over n ⥤ Under JTXiEndpointCollapse.boundary :=
  Over.forget n ⋙ under (code d)

/-- All internal native necklaces in all time degrees map to the same
actual decorated pullback. Time changes and native changes are carried
by the original maps of the cylinders and necklaces. -/
def toPullbackFiber :
    BoundaryNecklaceComma.Presentation (timeDiagram d n) ⥤
      CostructuredArrow necklaceUnder ((diagram W x y (target qx qy)).obj (index E)) where
  obj P := CostructuredArrow.mk
    (P.fiber.hom ≫ restrict f s qx qy E hraw P.base.hom)
  map {P P'} u := CostructuredArrow.homMk u.fiber.left (by
    change necklaceUnder.map u.fiber.left ≫ P'.fiber.hom ≫
        restrict f s qx qy E hraw P'.base.hom =
      P.fiber.hom ≫ restrict f s qx qy E hraw P.base.hom
    have hu : necklaceUnder.map u.fiber.left ≫ P'.fiber.hom =
        P.fiber.hom ≫ (under (code d)).map u.base.left := CostructuredArrow.w u.fiber
    rw [← Category.assoc, hu, Category.assoc, ← restrict_comp, Over.w])
  map_id P := by
    apply CostructuredArrow.hom_ext
    exact (BoundaryNecklaceComma.sourceCode (timeDiagram d n)).map_id P
  map_comp u v := by
    apply CostructuredArrow.hom_ext
    exact (BoundaryNecklaceComma.sourceCode (timeDiagram d n)).map_comp u v

/-- The functor's native projection is exactly the original augmentation
of the internal necklace followed by the original collapse. -/
theorem toPullbackFiber_native
    (P : BoundaryNecklaceComma.Presentation (timeDiagram d n)) :
    ((toPullbackFiber f s qx qy E hraw).obj P).hom ≫
        JTTargetCommaPullback.snd W x y (target qx qy) (index E) =
      P.fiber.hom ≫ toNativeTarget d P.base.left := by
  change (P.fiber.hom ≫ restrict f s qx qy E hraw P.base.hom) ≫
      JTTargetCommaPullback.snd W x y (target qx qy) (index E) = _
  rw [Category.assoc, restrict_native]
  rfl

/-- The whole category of parameterized native comparisons maps into the
original target comma via its checked pullback presentation. -/
def toComma :
    BoundaryNecklaceComma.Presentation (timeDiagram d n) ⥤
      CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy) :=
  toPullbackFiber f s qx qy E hraw ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y (target qx qy))) (index E) ⋙
      (JTTargetCommaPullback.equivalence W x y (target qx qy)).inverse

include hq in
/-- Every compatible pair of outside boundaries on a fixed mixed graph
has a common ordered label and an actual full cylinder comparison over
the unchanged native target. -/
theorem exists_relative_target_lift
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (r : ℕ)
    (g : JTHigherCommonMixedGraphFamilies.BoundaryFamilies W d k r f s x y) :
    ∃ E' : EdgeFamilies W ⦋d⦌ (common k ⦋r⦌) (SSet.stdSimplex.map (ret k ⦋r⦌) ≫ f)
        (s ≫ J.map (slice k ⦋r⦌ 0)) x y,
      (simplex k ◁ (SSet.boundary r).ι) ≫ prism k ⦋r⦌ ≫ E'.left = g.left.map ∧
      (simplex k ◁ (SSet.boundary r).ι) ≫ prism k ⦋r⦌ ≫ E'.right = g.right.map ∧
      ∃ U : (under (code d)).obj ⦋r⦌ ⟶ (diagram W x y (target qx qy)).obj (index E'),
        U ≫ JTTargetCommaPullback.fst W x y (target qx qy) (index E') = toDecorated d s ⦋r⦌ ∧
        U ≫ JTTargetCommaPullback.snd W x y (target qx qy) (index E') = toNativeTarget d ⦋r⦌ := by
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hq qx qy
  obtain ⟨E', hB₀, hB₁, hL, hR⟩ :=
    JTHigherCommonMixedGraphFamilies.exists_commonFamilies hW d k r f s x y hx hy g
  have h := whole_raw f s hq qx qy E' (by simpa only [Category.assoc] using hL)
    (by simpa only [Category.assoc] using hR)
  exact ⟨E', hB₀, hB₁, lift f s qx qy E' h, lift_decorated f s qx qy E' h,
    lift_native f s qx qy E' h⟩

end

end DaggerModels.PartII.JTHigherMixedGraphTargetLift
