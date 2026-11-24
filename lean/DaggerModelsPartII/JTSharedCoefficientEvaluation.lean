import DaggerModelsPartII.JTBinaryPrismRealization
import DaggerModelsPartII.JTParametrizedTargetLiftTransport
import DaggerModelsPartII.JTBinaryPrismNativeLabels

/-! Evaluation and restriction of an actual shared coefficient in the fixed-target comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTSharedCoefficientEvaluation

open JTOrderedLabelBinaryGlue (Inputs code orderedTriplePoint orderedTriplePoint_map reindex)
open JTBinaryPrismRealization (realizeInputs realizeOrderedProduct_reindex realizeProduct_reindexTime)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open DecoratedCylinderNecklacePresentation (underCocone toTarget)
open JTParametrizedTargetLiftTransport (graph)
open JTInterpolatedReducedCylinder (cylinderMap_cylinder cylinderMap_boundary)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {k m n n' : SimplexCategory}

/-- The actual decorated label for the common-coefficient input. -/
def index (d : Inputs W T U m x z y) : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code T U) m (orderedTriplePoint d)

/-- Restrict the shared coefficient through its actual category of elements. -/
def indexRestriction (r : k ⟶ m) (d : Inputs W T U m x z y) :
    index (reindex r d) ⟶ index d := by
  let C := code T U
  let F := orderedNecklaceLabels W (boundaryPoint W x y)
  let a : (C, k) ⟶ (C, m) := (𝟙 C, r)
  refine (CategoryOfElements.homMk (index d).unop (index (reindex r d)).unop a.op ?_).op
  change (F.obj (op C)).map r.op ((F.map (𝟙 C).op).app (op m) (orderedTriplePoint d)) =
    orderedTriplePoint (reindex r d)
  rw [op_id, F.map_id]
  exact orderedTriplePoint_map r d

theorem indexRestriction_projection (r : k ⟶ m) (d : Inputs W T U m x z y) :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map (indexRestriction r d) =
      (𝟙 (code T U), r) := rfl

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : code T U ⟶ Q.code)
variable (d : Inputs W T U m x z y) (p : (code T U).toSSet ⊗ J.obj n ⟶ J.obj m)

/-- A raw equality on the full product descends to the two-ended cylinder. -/
theorem graph_raw
    (h : realizeInputs d p = fst (code T U).toSSet (J.obj n) ≫ c.map ≫ Q.map) :
    (graph (i := index d) p).right ≫ ((underCocone W x y).app (index d)).right =
      augmentation (code T U) n ≫ c.map ≫ Q.map := by
  apply (isPushout (code T U) n).hom_ext
  · change (cylinder (code T U)).app n ≫ JTInterpolatedReducedCylinder.cylinderMap
      (code T U) p ≫ descend W x y _ m (orderedTriplePoint d) = _
    rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, descend_cylinder,
      ← Category.assoc ((cylinder _).app n), augmentation_cylinder]
    exact h
  · change (boundary (code T U)).app n ≫ JTInterpolatedReducedCylinder.cylinderMap
      (code T U) p ≫ descend W x y _ m (orderedTriplePoint d) = _
    rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary _).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion _), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, Q.first, Q.last]
    rfl

/-- Evaluate every internal necklace over the original fixed target. -/
def evaluate
    (h : realizeInputs d p = fst (code T U).toSSet (J.obj n) ≫ c.map ≫ Q.map) :
    CostructuredArrow necklaceUnder ((under (code T U)).obj n) ⥤
      CostructuredArrow (toTarget W x y) Q :=
  JTCylinderOverTarget.functor W x y Q (index d) (code T U) n
    (graph (i := index d) p) c (graph_raw Q c d p h)

theorem evaluate_congr {d' : Inputs W T U m x z y}
    {h : realizeInputs d p = fst (code T U).toSSet (J.obj n) ≫ c.map ≫ Q.map}
    {h' : realizeInputs d' p = fst (code T U).toSSet (J.obj n) ≫ c.map ≫ Q.map}
    (hd : d = d') : evaluate Q c d p h = evaluate Q c d' p h' := by
  subst d'
  rfl

variable (r : k ⟶ m) (j : n ⟶ n') (p' : (code T U).toSSet ⊗ J.obj n' ⟶ J.obj m)
variable (s : (code T U).toSSet ⊗ J.obj n ⟶ J.obj k)

/-- Raw comparison is retained exactly by restricting both the coefficient and time. -/
theorem restrict_raw
    (h : realizeInputs d p' = fst (code T U).toSSet (J.obj n') ≫ c.map ≫ Q.map)
    (he : (code T U).toSSet ◁ J.map j ≫ p' = s ≫ J.map r) :
    realizeInputs (reindex r d) s = fst (code T U).toSSet (J.obj n) ≫ c.map ≫ Q.map := by
  unfold realizeInputs at *
  rw [← orderedTriplePoint_map, ← realizeOrderedProduct_reindex, ← he,
    ← realizeProduct_reindexTime, h, whiskerLeft_fst_assoc]

/-- Map the original reduced cylinder along a time operator with the native code fixed. -/
abbrev timeMap (j : n ⟶ n') :=
  NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (code T U, n) ⟶ (code T U, n') from (𝟙 (code T U), j))

/-- The coefficient and time restriction gives a natural comparison of the
two original evaluations, with every internal necklace retained. -/
def compare
    (h : realizeInputs d p' = fst (code T U).toSSet (J.obj n') ≫ c.map ≫ Q.map)
    (he : (code T U).toSSet ◁ J.map j ≫ p' = s ≫ J.map r) :
    evaluate Q c (reindex r d) s (restrict_raw Q c d r j p' s h he) ⟶
      CostructuredArrow.map (timeMap (T := T) (U := U) j) ⋙ evaluate Q c d p' h := by
  let a := indexRestriction r d
  have hc : ((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).1 ≫ c = c := by
    rw [indexRestriction_projection]
    exact Category.id_comp c
  have hp :
      ((((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).1).map ⊗ₘ J.map j) ≫ p' =
      s ≫ J.map ((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).2 := by
    rw [indexRestriction_projection]
    change (NecklaceCode.simplicialFunctor.map (𝟙 (code T U)) ⊗ₘ J.map j) ≫ p' = _
    rw [NecklaceCode.simplicialFunctor.map_id]
    exact he
  exact JTParametrizedTargetLiftTransport.compare Q a j s p' c c hc hp
    (graph_raw Q c (reindex r d) s (restrict_raw Q c d r j p' s h he)) (graph_raw Q c d p' h)


section Native

variable {T' U' : NecklaceCode}
variable (f : T ⟶ T') (g : U ⟶ U') (r : k ⟶ m)
variable (d' : Inputs W T' U' m x z y)

/-- Native side arrows and one coefficient arrow define a single original
ordered-label morphism. -/
def indexTransport :
    index (reindex r (JTBinaryPrismNativeLabels.restrictInputs f g d')) ⟶ index d' := by
  let C := code T U
  let C' := code T' U'
  let F := orderedNecklaceLabels W (boundaryPoint W x y)
  let h : C ⟶ C' := JTBinaryPrismParameter.sideMap f g
  let a : (C, k) ⟶ (C', m) := (h, r)
  refine (CategoryOfElements.homMk (index d').unop
    (index (reindex r (JTBinaryPrismNativeLabels.restrictInputs f g d'))).unop a.op ?_).op
  change (F.obj (op C)).map r.op
      ((F.map h.op).app (op m)
        (orderedTriplePoint d')) =
    orderedTriplePoint (reindex r (JTBinaryPrismNativeLabels.restrictInputs f g d'))
  have hn : ((F.map h.op).app (op m) (orderedTriplePoint d')) =
      orderedTriplePoint (JTBinaryPrismNativeLabels.restrictInputs f g d') :=
    JTBinaryPrismNativeLabels.orderedTriplePoint_native f g d'
  rw [hn]
  exact orderedTriplePoint_map r (JTBinaryPrismNativeLabels.restrictInputs f g d')

theorem indexTransport_projection :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map
        (indexTransport f g r d') =
      (JTBinaryPrismParameter.sideMap f g, r) := by
  change (JTBinaryPrismParameter.sideMap f g, r) = _
  rfl

variable (j : n ⟶ n')
variable (c₀ : code T U ⟶ Q.code) (c₁ : code T' U' ⟶ Q.code)
variable (p₀ : (code T U).toSSet ⊗ J.obj n ⟶ J.obj k)
variable (p₁ : (code T' U').toSSet ⊗ J.obj n' ⟶ J.obj m)

/-- The exact full-parameter square and native collapse define a comparison
on every internal necklace, with both source codes and the coefficient moving. -/
def compareNative
    (hc : JTBinaryPrismParameter.sideMap f g ≫ c₁ = c₀)
    (hp : ((JTBinaryPrismParameter.sideMap f g).map ⊗ₘ J.map j) ≫ p₁ =
      p₀ ≫ J.map r)
    (h₀ : realizeInputs (reindex r (JTBinaryPrismNativeLabels.restrictInputs f g d')) p₀ =
      fst (code T U).toSSet (J.obj n) ≫ c₀.map ≫ Q.map)
    (h₁ : realizeInputs d' p₁ =
      fst (code T' U').toSSet (J.obj n') ≫ c₁.map ≫ Q.map) := by
  let a := indexTransport f g r d'
  have hc' : ((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).1 ≫
      c₁ = c₀ := by
    rw [indexTransport_projection]
    exact hc
  have hp' :
      ((((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).1).map ⊗ₘ
          J.map j) ≫ p₁ =
        p₀ ≫ J.map ((OrderedLabelElements.projection W (boundaryPoint W x y)).map a).2 := by
    rw [indexTransport_projection]
    exact hp
  exact JTParametrizedTargetLiftTransport.compare Q a j p₀ p₁ c₀ c₁ hc' hp'
    (graph_raw Q c₀ (reindex r (JTBinaryPrismNativeLabels.restrictInputs f g d')) p₀ h₀)
    (graph_raw Q c₁ d' p₁ h₁)

end Native

end

end DaggerModels.PartII.JTSharedCoefficientEvaluation
