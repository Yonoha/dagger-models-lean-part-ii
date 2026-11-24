import DaggerModelsPartII.JTCommonMixedGraphFamilies
import DaggerModelsPartII.JTMixedGraphPrismRealization
import DaggerModelsPartII.JTHomotopyTargetComma
import DaggerModelsPartII.JTRowGraphCommaComparison

/-!
# Independently specified endpoint families on one graph are connected
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphNormalizationZigzag

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open JTInterleavedParameter JTGroupoidParameterPrism JTGraphPrismCylinder
open JTRealizedLabelEndpoints JTGraphRefinement JTGraphRefinementParameterArrow
open JTNecklaceEndpointCylinder OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTMixedGraphPrismRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev I := J.obj ⦋1⦌
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev aug := NecklaceCylinderAugmentation.augmentation

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev diagram :=
  DecoratedCylinderNecklacePresentation.underDiagram W x y

private def sliceFiber (T : NecklaceCode) (t : Fin 2) :
    CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj ⦋1⦌) :=
  CostructuredArrow.mk (Y := T)
    (Under.homMk (timeSlice T.toSSet t ≫ (cylinder T).app ⦋1⦌) (timeSlice_boundary T t))

private theorem slice_augmentationCode (T : NecklaceCode) (t : Fin 2) :
    JTHomotopyTargetComma.augmentationCode T (sliceFiber T t) = 𝟙 T := by
  apply NecklaceCode.Hom.ext
  change (timeSlice T.toSSet t ≫ (cylinder T).app ⦋1⦌) ≫ aug T ⦋1⦌ =
    𝟙 T.toSSet
  rw [Category.assoc, NecklaceCylinderAugmentation.augmentation_cylinder, timeSlice_fst]

variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}

private def mkComma (i : DecoratedNecklaceHomDiagram.Index W x y) (T : NecklaceCode)
    (p : T.toSSet ⟶ ((diagram (W := W) (x := x) (y := y)).obj i).right)
    (hp : endpointInclusion T ≫ p = ((diagram (W := W) (x := x) (y := y)).obj i).hom)
    (c : T ⟶ Q.code)
    (hc : c.map ≫ Q.map =
      p ≫ ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i).right) :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q := by
  let Y : DecoratedCylinderNecklacePresentation.Presentation W x y :=
    ⟨i, CostructuredArrow.mk (Y := T) (Under.homMk p hp)⟩
  exact CostructuredArrow.mk (Y := Y) { hom := c, w := hc }

private theorem mkComma_congr (i : DecoratedNecklaceHomDiagram.Index W x y) (T : NecklaceCode)
    {p p' : T.toSSet ⟶ ((diagram (W := W) (x := x) (y := y)).obj i).right}
    {hp : endpointInclusion T ≫ p = ((diagram (W := W) (x := x) (y := y)).obj i).hom}
    {hp' : endpointInclusion T ≫ p' = ((diagram (W := W) (x := x) (y := y)).obj i).hom}
    {c c' : T ⟶ Q.code}
    {hc : c.map ≫ Q.map =
      p ≫ ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i).right}
    {hc' : c'.map ≫ Q.map =
      p' ≫ ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i).right}
    (h : p = p') (h' : c = c') :
    mkComma i T p hp c hc = mkComma i T p' hp' c' hc' := by
  subst p'
  subst c'
  rfl

variable {d : ℕ} {k : SimplexCategory}
variable {f : Δ k ⟶ row W ⦋d⦌} {s : Δ ⦋d⦌ ⟶ J.obj k}
variable {q : (single d).toSSet ⟶ R W}
variable (hq : nativeRawGraph W d k f s = q)
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target := (⟨single d, q, qx, qy⟩ :
  NecklacesOver (R W) (rawVertex W x) (rawVertex W y))
private abbrev T := code d
private abbrev c := collapseOuter d
private abbrev K := common k

variable (E : EdgeFamilies W ⦋d⦌ (common k) (SSet.stdSimplex.map (ret k) ≫ f)
  (s ≫ J.map (slice k 0)) x y)

private abbrev z := JTMixedGraphOrderedLabel.orderedPoint E
private abbrev index :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (T (d := d)) (K (k := k)) (z E)

private def prismUnder : (under (T (d := d))).obj ⦋1⦌ ⟶
    ((diagram (W := W) (x := x) (y := y)).obj (index E)) :=
  Under.homMk (cylinderMap (T (d := d)) (nativeGraphParameter s))
    (cylinderMap_boundary (T (d := d)) (nativeGraphParameter s))

include hq qx qy in
private theorem whole_raw
    (D₀ : EdgeFamilies W ⦋d⦌ k f s x y)
    (h₀ : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (T (d := d)))).map
      (slice k 0).op (z E) = JTMixedGraphOrderedLabel.orderedPoint D₀)
    (hL : SSet.stdSimplex.map (edge k (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      SSet.stdSimplex.isTerminalObj₀.from (Δ ⦋1⦌) ≫ vertexPoint W x ≫
        JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (edge k (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      SSet.stdSimplex.isTerminalObj₀.from (Δ ⦋1⦌) ≫ vertexPoint W y ≫
        JTEndpointNormalizationLifts.identityFamily W) :
    (prismUnder E).right ≫ ((DecoratedCylinderNecklacePresentation.underCocone W x y).app
      (index E)).right = aug (T (d := d)) ⦋1⦌ ≫ (c (d := d)).map ≫ q := by
  let T' := T (d := d)
  let D := refinementOfGraph D₀ hq qx qy
  let D' := extendDegree D (slice k 0) (z E) h₀
  change cylinderMap T' (nativeGraphParameter s) ≫ descend W x y T' (common k) (z E) =
    aug T' ⦋1⦌ ≫ (c (d := d)).map ≫ q
  apply (isPushout T' ⦋1⦌).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, descend_cylinder,
      ← Category.assoc ((cylinder T').app ⦋1⦌) (aug T' ⦋1⦌),
      NecklaceCylinderAugmentation.augmentation_cylinder]
    change productRaw f s E = fst T'.toSSet I ≫ (c (d := d)).map ≫ q
    calc
      productRaw f s E = fst T'.toSSet I ≫ timeSlice T'.toSSet 0 ≫ productRaw f s E :=
        productRaw_time_invariant f s E hL hR
      _ = fst T'.toSSet I ≫ realizeGraph W D'.degree D'.parameter
          (orderedLabel W x y D'.code D'.degree D'.label) := by
        unfold productRaw realizeGraph
        rw [← Category.assoc (timeSlice T'.toSSet 0), graphPrism_slice]
        rfl
      _ = _ := congrArg (fun u ↦ fst T'.toSSet I ≫ u) D'.comm
  · rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary T').app ⦋1⦌) (aug T' ⦋1⦌),
      NecklaceCylinderAugmentation.augmentation_boundary,
      ← Category.assoc (endpointInclusion T'), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, qx, qy]

private theorem slice_object (D₀ : EdgeFamilies W ⦋d⦌ k f s x y)
    (t : Fin 2)
    (ht : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (T (d := d)))).map
      (slice k t).op (z E) = JTMixedGraphOrderedLabel.orderedPoint D₀)
    (hh : (prismUnder E).right ≫ ((DecoratedCylinderNecklacePresentation.underCocone W x y).app
      (index E)).right = aug (T (d := d)) ⦋1⦌ ≫ (c (d := d)).map ≫ q) :
    ((JTHomotopyTargetComma.toComma W x y (index E) (target qx qy) (T (d := d))
      (c (d := d)) (prismUnder E) hh).obj (sliceFiber (T (d := d)) t)) =
      (extendDegree (refinementOfGraph D₀ hq qx qy) (slice k t) (z E) ht).toComma := by
  apply mkComma_congr (index E) (T (d := d))
    (hp := Under.w ((CostructuredArrow.map (prismUnder E)).obj (sliceFiber (T (d := d)) t)).hom)
  · exact cylinderMap_slice (T (d := d)) (nativeGraphParameter s) t
  · change JTHomotopyTargetComma.augmentationCode (T (d := d)) (sliceFiber (T (d := d)) t) ≫
      (c (d := d)) = c (d := d)
    rw [slice_augmentationCode]
    exact Category.id_comp (obj := NecklaceCode) (X := T (d := d)) (Y := single d) (c (d := d))

/-- Every two prescribed normalizations of the same mixed graph are
connected by actual arrows of its original target comma. -/
theorem same_graph_zigzag
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (D₀ D₁ : EdgeFamilies W ⦋d⦌ k f s x y) :
    Relation.EqvGen (fun A B : CostructuredArrow
      (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy) ↦ Nonempty (A ⟶ B))
      (refinementOfGraph D₀ hq qx qy).toComma (refinementOfGraph D₁ hq qx qy).toComma := by
  obtain ⟨E, _, _, _, _, hL, hR, h₀, h₁⟩ :=
    JTCommonMixedGraphFamilies.exists_commonFamilies hW d k f s x y D₀ D₁
  let G₀ := refinementOfGraph D₀ hq qx qy
  let G₁ := refinementOfGraph D₁ hq qx qy
  let G₀' := extendDegree G₀ (slice k 0) (z E) h₀
  let G₁' := extendDegree G₁ (slice k 1) (z E) h₁
  have hh := whole_raw hq qx qy E D₀ h₀ hL hR
  have h := JTHomotopyTargetComma.target_zigzag W x y (index E) (target qx qy) (T (d := d))
    (c (d := d)) (prismUnder E) hh (sliceFiber (T (d := d)) 0) (sliceFiber (T (d := d)) 1)
  rw [slice_object hq qx qy E D₀ 0 h₀ hh, slice_object hq qx qy E D₁ 1 h₁ hh] at h
  exact Relation.EqvGen.trans _ G₀'.toComma _
    (Relation.EqvGen.rel _ _ ⟨toCommaArrow G₀ (slice k 0) (z E) h₀⟩)
    (Relation.EqvGen.trans _ G₁'.toComma _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨toCommaArrow G₁ (slice k 1) (z E) h₁⟩)))

open JTRowGraphCommaComparison in
/-- The two endpoint normalizations can now be prescribed independently,
even for different graph representatives of the same single-bead target. -/
theorem arbitrary_row_normalizations_zigzag
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G H : RowGraph W d) (hG : nativeValue G = q) (hH : nativeValue H = q)
    (A : Families G x y) (B : Families H x y) :
    Relation.EqvGen (fun P P' : CostructuredArrow
      (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy) ↦
        Nonempty (P ⟶ P'))
      (commaObject qx qy G hG A) (commaObject qx qy H hH B) := by
  have hmap (S : RowGraph W d) (hS : nativeValue S = q) :
      nativeRawGraph W d S.degree (coefficientMap S) S.parameter = q := by
    unfold nativeRawGraph rawGraph coefficientMap
    erw [Equiv.apply_symm_apply]
    exact hS
  obtain ⟨A', B', h⟩ := exists_connected_normalizations qx qy hW G H hG hH
  have hA := same_graph_zigzag (hmap G hG) qx qy hW A A'
  have hB := same_graph_zigzag (hmap H hH) qx qy hW B' B
  exact Relation.EqvGen.trans _ (commaObject qx qy G hG A') _ hA
    (Relation.EqvGen.trans _ (commaObject qx qy H hH B') _ h hB)


end

end DaggerModels.PartII.JTMixedGraphNormalizationZigzag
