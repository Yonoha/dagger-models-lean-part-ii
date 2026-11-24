import DaggerModelsPartII.JTMixedGraphOrderedLabel
import DaggerModelsPartII.MixedGraphCylinderTraversal
import DaggerModelsPartII.JTRealizedConstantBead
import DaggerModelsPartII.JTGraphRefinement

/-!
# A strict target refinement for a native single bead of the raw realization
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphRawRefinement

open OrdinaryJTRealization JTReversalInput ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTNativeRowLabel JTNecklaceLabelRealization MixedGraphCylinderTraversal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev F := discreteFree.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable {f : Δ k ⟶ row W ⦋d⦌} {s : Δ ⦋d⦌ ⟶ J k}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev A := single 1
private abbrev B (d : ℕ) := single d
private abbrev L (d : ℕ) := tripleRightT A (B d) A
private abbrev M (d : ℕ) := tripleRightU A (B d) A
private abbrev P (d : ℕ) := tripleRightV A (B d) A

private abbrev a (s : Δ ⦋d⦌ ⟶ J k) := graphIndex ⦋d⦌ k s 0
private abbrev b (s : Δ ⦋d⦌ ⟶ J k) := graphIndex ⦋d⦌ k s (Fin.last d)

private abbrev nativeParameter (s : Δ ⦋d⦌ ⟶ J k) :
    (B d).toSSet ⟶ J k := (singleIso d).hom ≫ s

private theorem nativeParameter_vertex (s : Δ ⦋d⦌ ⟶ J k) (i : Fin (d + 1)) :
    pointAt (B d) (ULift.up i) ≫ nativeParameter s =
      JTParameterContraction.parameterVertex k (graphIndex ⦋d⦌ k s i) := by
  dsimp only [nativeParameter]
  rw [← Category.assoc, nativeVertex, graphIndex_vertex]

/-- The original graph on the native single bead. -/
def nativeRawGraph (W : Source) (d : ℕ) (k : SimplexCategory)
    (f : Δ k ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J k) : (B d).toSSet ⟶ R W :=
  (singleIso d).hom ≫ rawGraph W ⦋d⦌ k f s

private theorem nativeRawGraph_vertex (i : Fin (d + 1)) :
    pointAt (B d) (ULift.up i) ≫ nativeRawGraph W d k f s =
      vertex ⦋d⦌ i ≫ rawGraph W ⦋d⦌ k f s := by
  unfold nativeRawGraph
  rw [← Category.assoc, nativeVertex]

private abbrev cylinderMap (s : Δ ⦋d⦌ ⟶ J k) :=
  cylinderTraversal d k (a s) (b s) (nativeParameter s)
    (nativeParameter_vertex s 0) (nativeParameter_vertex s (Fin.last d))

private abbrev graphMap (s : Δ ⦋d⦌ ⟶ J k) :=
  productTraversal d k (a s) (b s) (nativeParameter s)
    (nativeParameter_vertex s 0) (nativeParameter_vertex s (Fin.last d))

variable (e : EdgeFamilies W ⦋d⦌ k f s x y)

private abbrev η : (diagramMappingSpace (F.obj (code d).toSSet) W).obj (op k) :=
  JTRealizedLabelEndpoints.orderedLabel W x y (code d) k
    (JTMixedGraphOrderedLabel.orderedPoint e)

/-- The actual presentation object over the reduced cylinder of the same
three-bead ordered label. -/
def presentationObject : DecoratedCylinderNecklacePresentation.Presentation W x y where
  base := OrderedLabelElements.mk W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
    (code d) k (JTMixedGraphOrderedLabel.orderedPoint e)
  fiber := CostructuredArrow.mk (Y := code d)
    (Under.homMk (cylinderMap s)
      (cylinderTraversal_boundary d k (a s) (b s) (nativeParameter s)
        (nativeParameter_vertex s 0) (nativeParameter_vertex s (Fin.last d))))

private theorem middle_realization :
    M d ≫ graphMap s ≫ realizedLabel (code d).toSSet W k (η e) =
      nativeRawGraph W d k f s := by
  rw [← Category.assoc, productTraversal_middle]
  have h : CartesianMonoidalCategory.lift (M d) (nativeParameter s) =
      CartesianMonoidalCategory.lift (𝟙 (B d).toSSet) (nativeParameter s) ≫
        (M d ⊗ₘ 𝟙 (J k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd, Category.comp_id,
        CartesianMonoidalCategory.lift_snd]
  rw [h, Category.assoc]
  erw [realizedLabel_natural_X (M d) W k (η e)]
  change _ = nativeRawGraph W d k f s
  erw [TripleBeadEndpointLabel.orderedPoint_middle_coefficient
    (JTMixedGraphOrderedLabel.families e)]
  change CartesianMonoidalCategory.lift (𝟙 (B d).toSSet) (nativeParameter s) ≫
    realizedLabel (B d).toSSet W k (SSet.yonedaEquiv (f ≫ labelFromRow W d)) = _
  rw [realized_nativeLabel, ← Category.assoc]
  unfold nativeRawGraph rawGraph
  rw [← Category.assoc]
  congr 1

private theorem left_realization :
    L d ≫ graphMap s ≫ realizedLabel (code d).toSSet W k (η e) =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W x) := by
  rw [← Category.assoc, productTraversal_left]
  apply JTRealizedConstantBead.realized_constant_bead
  erw [TripleBeadEndpointLabel.orderedPoint_left_coefficient
    (JTMixedGraphOrderedLabel.families e)]
  exact JTMixedGraphOrderedLabel.left_identity_face e

private theorem right_realization :
    P d ≫ graphMap s ≫ realizedLabel (code d).toSSet W k (η e) =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W y) := by
  rw [← Category.assoc, productTraversal_right]
  apply JTRealizedConstantBead.realized_constant_bead
  erw [TripleBeadEndpointLabel.orderedPoint_right_coefficient
    (JTMixedGraphOrderedLabel.families e)]
  exact JTMixedGraphOrderedLabel.right_identity_face e

variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) =
  rawVertex W y)

include hx in
private theorem nativeRawGraph_first :
    pointAt (B d) (ULift.up 0) ≫ nativeRawGraph W d k f s =
      SSet.yonedaEquiv.symm (rawVertex W x) := by
  rw [nativeRawGraph_vertex, ← hx, Equiv.symm_apply_apply]

include hy in
private theorem nativeRawGraph_last :
    pointAt (B d) (ULift.up (Fin.last d)) ≫ nativeRawGraph W d k f s =
      SSet.yonedaEquiv.symm (rawVertex W y) := by
  rw [nativeRawGraph_vertex, ← hy, Equiv.symm_apply_apply]

include hx hy in
/-- The full descended map is the original raw graph after the native collapse. -/
theorem descendedGraph :
    ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentationObject e)).map =
      (collapseOuter d).map ≫ nativeRawGraph W d k f s := by
  change cylinderMap s ≫ JTNecklaceEndpointCylinder.descend W x y (code d) k
      (JTMixedGraphOrderedLabel.orderedPoint e) = _
  change (graphMap s ≫ (JTNecklaceEndpointCylinder.cylinder (code d)).app k) ≫
    JTNecklaceEndpointCylinder.descend W x y (code d) k
      (JTMixedGraphOrderedLabel.orderedPoint e) = _
  rw [Category.assoc, JTNecklaceEndpointCylinder.descend_cylinder]
  change graphMap s ≫ realizedLabel (code d).toSSet W k (η e) =
    collapseMap d ≫ nativeRawGraph W d k f s
  apply tripleRight_hom_ext (T := A) (U := B d) (V := A)
  · rw [left_realization, ← Category.assoc, collapseMap_left, Category.assoc,
      nativeRawGraph_first hx]
  · rw [middle_realization, ← Category.assoc, collapseMap_middle, Category.id_comp]
  · rw [right_realization, ← Category.assoc, collapseMap_right, Category.assoc]
    erw [nativeRawGraph_last hy]

include hx hy in
/-- The raw target carries the original endpoints on the actual single bead. -/
def graphNecklace :
    NecklacesOver (R W) (rawVertex W x) (rawVertex W y) where
  code := B d
  map := nativeRawGraph W d k f s
  first := by
    have h := congrArg SSet.yonedaEquiv (nativeRawGraph_first hx)
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, Equiv.apply_symm_apply, first] using h
  last := by
    have h := congrArg SSet.yonedaEquiv (nativeRawGraph_last hy)
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, Equiv.apply_symm_apply, last] using h

/-- One actual object of the original target comma over the given raw graph. -/
def graphTargetCommaObject :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y)
      (graphNecklace hx hy) :=
  CostructuredArrow.mk
    (Y := presentationObject e)
    { hom := collapseOuter d
      w := (descendedGraph e hx hy).symm }

/-- The whole parameter map of the mixed graph on the original three-bead code. -/
def nativeGraphParameter (s : Δ ⦋d⦌ ⟶ J k) : (code d).toSSet ⟶ J k :=
  graphParameter d k (a s) (b s) (nativeParameter s)
    (nativeParameter_vertex s 0) (nativeParameter_vertex s (Fin.last d))

/-- All three parts of the native traversal commute with an arbitrary
parameter operator. -/
theorem nativeGraphParameter_map {l : SimplexCategory} (j : k ⟶ l)
    (s : Δ ⦋d⦌ ⟶ J k) :
    nativeGraphParameter s ≫ GroupoidSimplex.parameter.map j =
      nativeGraphParameter (s ≫ GroupoidSimplex.parameter.map j) := by
  have hv (i : Fin (d + 1)) :
      JTParameterContraction.parameterVertex k (graphIndex ⦋d⦌ k s i) ≫
          GroupoidSimplex.parameter.map j =
        JTParameterContraction.parameterVertex l
          (graphIndex ⦋d⦌ l (s ≫ GroupoidSimplex.parameter.map j) i) := by
    rw [← graphIndex_vertex ⦋d⦌ k s i, Category.assoc, graphIndex_vertex]
  unfold nativeGraphParameter
  apply tripleRight_hom_ext (T := A) (U := B d) (V := A)
  · rw [← Category.assoc, graphParameter_left, graphParameter_left]
    change (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ _) ≫
      GroupoidSimplex.parameter.map j = SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ _
    rw [Category.assoc, hv 0]
  · rw [← Category.assoc, graphParameter_middle, graphParameter_middle]
    unfold nativeParameter
    exact Category.assoc _ _ _
  · rw [← Category.assoc, graphParameter_right, graphParameter_right]
    change (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ _) ≫
      GroupoidSimplex.parameter.map j = SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ _
    rw [Category.assoc, hv (Fin.last d)]

variable {q : (B d).toSSet ⟶ R W}

/-- The prescribed native target map supplies the exact endpoint equations
for any graph representing it. -/
theorem graph_endpoints_of_native_map (hmap : nativeRawGraph W d k f s = q)
    (qx : q.app (op ⦋0⦌) (B d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (B d).last = rawVertex W y) :
    SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x ∧
    SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W y := by
  have hp (i : Fin (d + 1)) :
      vertex ⦋d⦌ i ≫ rawGraph W ⦋d⦌ k f s = pointAt (B d) (ULift.up i) ≫ q :=
    (nativeRawGraph_vertex (W := W) (f := f) (s := s) i).symm.trans
      (congrArg (fun u ↦ pointAt (B d) (ULift.up i) ≫ u) hmap)
  constructor
  · rw [hp, SSet.yonedaEquiv_comp, pointAt_vertex]
    exact qx
  · rw [hp, SSet.yonedaEquiv_comp, pointAt_vertex]
    exact qy

/-- Use the supplied endpoint families over the given original native
single-bead map. The resulting label and traversal retain those choices. -/
def refinementOfGraph (e : EdgeFamilies W ⦋d⦌ k f s x y)
    (hmap : nativeRawGraph W d k f s = q)
    (qx : q.app (op ⦋0⦌) (B d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (B d).last = rawVertex W y) :
    JTGraphRefinement.Refinement W x y ⟨B d, q, qx, qy⟩ where
  code := code d
  degree := k
  label := JTMixedGraphOrderedLabel.orderedPoint e
  parameter := nativeGraphParameter s
  collapse := collapseOuter d
  comm := by
    rw [← JTGraphRefinement.presentation_target_map]
    change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentationObject e)).map = (collapseOuter d).map ≫ q
    obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hmap qx qy
    rw [descendedGraph e hx hy, hmap]

/-- Every actual single-bead target has a strict refinement retaining the
ordered label and the whole parameter map, including for length zero. -/
theorem singleGraphRefinement_nonempty (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (d : ℕ)
    (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d) :
    Nonempty (JTGraphRefinement.Refinement W x y Q) := by
  obtain ⟨T, q, qx, qy⟩ := Q
  change T = single d at hQ
  subst T
  let g : Δ ⦋d⦌ ⟶ R W := (singleIso d).inv ≫ q
  obtain ⟨k, w, s, hg⟩ := JTRealizationGraphGenerator.exists_graph_realizedRowCoefficient W d g
  let f : Δ k ⟶ row W ⦋d⦌ := SSet.yonedaEquiv.symm w
  have h : g = rawGraph W ⦋d⦌ k f s := by
    rw [hg, JTRowRealizationGenerator.realizedRowCoefficient_eq_generator, rawGraph]
    simp only [f, Equiv.apply_symm_apply]
  have hmap : nativeRawGraph W d k f s = q := by
    rw [nativeRawGraph, ← h]
    exact Iso.hom_inv_id_assoc _ _
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hmap qx qy
  let e := chosenEdgeFamilies W hW ⦋d⦌ k f s x y hx hy
  exact ⟨refinementOfGraph e hmap qx qy⟩

/-- Every actual single-bead target has a strict refinement from the
decorated-cylinder presentation, for all bead lengths including zero. -/
theorem singleTargetComma_nonempty (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (d : ℕ)
    (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d) :
    Nonempty (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q) :=
  (singleGraphRefinement_nonempty W hW x y d Q hQ).map
    JTGraphRefinement.Refinement.toComma

end

end DaggerModels.PartII.JTMixedGraphRawRefinement
