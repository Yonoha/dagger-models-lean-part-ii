import DaggerModelsPartII.JTGraphRefinementMixedArrow
import DaggerModelsPartII.JTNecklaceParameterSupport
import DaggerModelsPartII.GrothendieckContractibleFibers

/-!
# Remove unused coefficient vertices in a whole diagram of exact refinements

The native necklace and its map to the original target stay fixed at each
object. Both operators on every arrow descend to the used coefficient vertices.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen
open DaggerChosenRigidificationNecklace CartesianMonoidalCategory

namespace DaggerModels.PartII.JTGraphRefinementSupport

open JTGraphRefinement JTGraphRefinementMixedArrow JTNecklaceEndpointCylinder
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceParameterSupport
open JTRowGraphParameterSupport (supportOrdinal inclusion inclusion_mono)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev L (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  orderedNecklaceLabels W (boundaryPoint W x y)
private abbrev P (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)

private abbrev degree (D : Refinement W x y Q) := supportOrdinal (ambient D.parameter)
private abbrev inc (D : Refinement W x y Q) := inclusion (ambient D.parameter)
private abbrev pair (D : Refinement W x y Q) : (D.code, degree D) ⟶ (D.code, D.degree) :=
  (𝟙 D.code, inc D)

private abbrev restrictedLabel (D : Refinement W x y Q) :=
  (P W x y).map (pair D).op D.label

private theorem restrictedLabel_eq (D : Refinement W x y Q) :
    restrictedLabel D = ((L W x y).obj (op D.code)).map (inc D).op D.label := by
  change ((L W x y).obj (op D.code)).map (inc D).op
    (((L W x y).map (𝟙 (op D.code))).app (op D.degree) D.label) = _
  rw [(L W x y).map_id]
  rfl

private theorem supported_raw (D : Refinement W x y Q) :
    realizeGraph W (degree D) (supportedParameter D.parameter)
      (orderedLabel W x y D.code (degree D) (restrictedLabel D)) = D.collapse.map ≫ Q.map := by
  let p := supportedParameter D.parameter
  have h := traversal_map (𝟙 D.code) (inc D) p
  change (lift (𝟙 D.code.toSSet) p ≫ (cylinder D.code).app (degree D)) ≫
      (nativeMap (𝟙 D.code) (degree D) ≫ (value D.code).map (inc D)) =
    lift (𝟙 D.code.toSSet) (p ≫ J.map (inc D)) ≫ (cylinder D.code).app D.degree at h
  rw [nativeMap_id, Category.id_comp, supportedParameter_factor] at h
  change lift (𝟙 D.code.toSSet) p ≫
    JTNecklaceLabelRealization.realizedNecklaceLabel D.code W (degree D)
      (orderedLabel W x y D.code (degree D) (restrictedLabel D)) = _
  rw [← descend_cylinder, restrictedLabel_eq, ← descend_parameter_natural, ← Category.assoc,
    ← Category.assoc, h, Category.assoc, descend_cylinder]
  exact D.comm

/-- Remove only coefficient vertices unused by the original parameter. -/
def supportedObj (D : Refinement W x y Q) : Refinement W x y Q where
  code := D.code
  degree := degree D
  label := restrictedLabel D
  parameter := supportedParameter D.parameter
  collapse := D.collapse
  comm := supported_raw D

private def labelArrow {D E : Refinement W x y Q} (g : (D.code, D.degree) ⟶ (E.code, E.degree))
    (h : (P W x y).map g.op E.label = D.label) : base D ⟶ base E :=
  (CategoryOfElements.homMk (base E).unop (base D).unop g.op h).op

/-- The comparison retains the full internal necklace and target collapse. -/
def inclusionArrow (D : Refinement W x y Q) : supportedObj D ⟶ D where
  label := labelArrow (pair D) rfl
  parameter := (supportedParameter_factor D.parameter).trans (Category.id_comp D.parameter).symm
  collapse := Category.id_comp _

private abbrev operator {D E : Refinement W x y Q} (a : D ⟶ E) :=
  JTRowGraphHorizontalSupport.operator (ordinal a.native) a.coefficient
    (ambient_mixed a.native a.coefficient a.parameter)

private abbrev supportedPair {D E : Refinement W x y Q} (a : D ⟶ E) :
    (D.code, degree D) ⟶ (E.code, degree E) := (a.native, operator a)

private theorem supportedPair_comm {D E : Refinement W x y Q} (a : D ⟶ E) :
    supportedPair a ≫ pair E = pair D ≫ projection.map a.label := by
  apply Prod.ext
  · change a.native ≫ 𝟙 E.code = 𝟙 D.code ≫ a.native
    rw [Category.comp_id, Category.id_comp]
  · exact JTRowGraphHorizontalSupport.operator_inclusion (ordinal a.native) a.coefficient
      (ambient_mixed a.native a.coefficient a.parameter)

private theorem supportedLabel_comm {D E : Refinement W x y Q} (a : D ⟶ E) :
    (P W x y).map (supportedPair a).op (restrictedLabel E) = restrictedLabel D := by
  change ((P W x y).map (pair E).op ≫ (P W x y).map (supportedPair a).op) E.label = _
  rw [← (P W x y).map_comp, ← op_comp, supportedPair_comm,
    op_comp, (P W x y).map_comp]
  have h : (P W x y).map (projection.map a.label).op E.label = D.label :=
    a.label.unop.property
  change (P W x y).map (pair D).op ((P W x y).map (projection.map a.label).op E.label) = _
  rw [h]

private def supportedArrow {D E : Refinement W x y Q} (a : D ⟶ E) :
    supportedObj D ⟶ supportedObj E where
  label := labelArrow (supportedPair a) (supportedLabel_comm a)
  parameter := supportedParameter_mixed a.native a.coefficient a.parameter
  collapse := a.collapse

private instance : (projection (W := W) (x := x) (y := y)).Faithful := by
  unfold JTGraphRefinementMixedArrow.projection OrderedLabelElements.projection
  infer_instance

private theorem comparison_natural {D E : Refinement W x y Q} (a : D ⟶ E) :
    supportedArrow a ≫ inclusionArrow E = inclusionArrow D ≫ a := by
  apply JTGraphRefinementMixedArrow.Arrow.ext
  apply (projection (W := W) (x := x) (y := y)).map_injective
  change projection.map ((supportedArrow a).label ≫ (inclusionArrow E).label) =
    projection.map ((inclusionArrow D).label ≫ a.label)
  rw [projection.map_comp, projection.map_comp]
  exact supportedPair_comm a

private theorem cancel_inclusion {D E : Refinement W x y Q}
    {f g : D ⟶ supportedObj E}
    (h : f ≫ inclusionArrow E = g ≫ inclusionArrow E) : f = g := by
  apply JTGraphRefinementMixedArrow.Arrow.ext
  apply (projection (W := W) (x := x) (y := y)).map_injective
  have h' := congrArg (fun a : D ⟶ E ↦ projection.map a.label) h
  change projection.map (f.label ≫ (inclusionArrow E).label) =
    projection.map (g.label ≫ (inclusionArrow E).label) at h'
  rw [projection.map_comp, projection.map_comp] at h'
  apply Prod.ext
  · have h₀ := congrArg Prod.fst h'
    change (projection.map f.label).1 ≫ 𝟙 E.code = (projection.map g.label).1 ≫ 𝟙 E.code at h₀
    simpa only [Category.comp_id] using h₀
  · letI := inclusion_mono (ambient E.parameter)
    exact (cancel_mono (inc E)).mp (congrArg Prod.snd h')

/-- The same restriction works simultaneously on every strict mixed diagram. -/
def supported (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    Refinement W x y Q ⥤ Refinement W x y Q where
  obj := supportedObj
  map := supportedArrow
  map_id D := by
    apply cancel_inclusion
    rw [comparison_natural, Category.comp_id, Category.id_comp]
  map_comp {A B C} a b := by
    apply cancel_inclusion
    calc
      _ = inclusionArrow A ≫ (a ≫ b) := comparison_natural (a ≫ b)
      _ = (inclusionArrow A ≫ a) ≫ b := (Category.assoc _ _ _).symm
      _ = (supportedArrow a ≫ inclusionArrow B) ≫ b :=
        congrArg (fun f ↦ f ≫ b) (comparison_natural a).symm
      _ = supportedArrow a ≫ (inclusionArrow B ≫ b) := Category.assoc _ _ _
      _ = supportedArrow a ≫ (supportedArrow b ≫ inclusionArrow C) :=
        congrArg (fun f ↦ supportedArrow a ≫ f) (comparison_natural b).symm
      _ = _ := (Category.assoc _ _ _).symm

/-- The simultaneous restriction compares naturally to the original refinement. -/
def supportInclusion (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    supported Q ⟶ 𝟭 (Refinement W x y Q) where
  app := inclusionArrow
  naturality _ _ a := comparison_natural a

/-- The exact graphs using every vertex of their coefficient. -/
def usesAllVertices (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    ObjectProperty (Refinement W x y Q) :=
  fun D ↦ Function.Surjective (JTRowGraphParameterSupport.label (ambient D.parameter))

private theorem supported_all (D : Refinement W x y Q) : usesAllVertices Q (supportedObj D) := by
  have h : ambient (supportedObj D).parameter =
      JTRowGraphParameterSupport.source (ambient D.parameter) := by
    apply inclusion_injective (T := D.code)
    rw [inclusion_ambient]
    rfl
  change Function.Surjective (JTRowGraphParameterSupport.label
    (ambient (supportedObj D).parameter))
  rw [h]
  exact JTRowGraphParameterSupport.source_vertex_surjective _

/-- Reducing the coefficient restricts to the full subcategory of supported graphs. -/
def toSupported (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    Refinement W x y Q ⥤ (usesAllVertices Q).FullSubcategory :=
  (usesAllVertices Q).lift (supported Q) supported_all

/-- The full subcategory with no unused coefficient vertices has the same weak nerve type. -/
theorem supported_inclusion_weak (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    WeakEquivalence (nerveMap (usesAllVertices Q).ι) := by
  let F := (usesAllVertices Q).ι
  let G := toSupported Q
  let s : F ⋙ G ⟶ 𝟭 _ :=
    { app D := ObjectProperty.homMk ((supportInclusion Q).app D.obj)
      naturality _ _ a := ObjectProperty.hom_ext _ ((supportInclusion Q).naturality a.hom) }
  apply (weakEquivalence_iff_GW _).mpr
  exact nerveMap_geometricW F G (.rel _ _ ⟨s⟩) (.rel _ _ ⟨supportInclusion Q⟩)

end

end DaggerModels.PartII.JTGraphRefinementSupport
