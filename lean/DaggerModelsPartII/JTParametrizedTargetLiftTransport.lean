import DaggerModelsPartII.JTBinaryPrismSideTransport
import DaggerModelsPartII.JTCylinderOverTargetBaseChange

/-! Simultaneous change of source, time and coefficient for the original target lift. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetLiftTransport

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedCylinderNecklacePresentation (underCocone underDiagram)
open JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation augmentation_parameter_natural augmentation_native_natural)
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_boundary)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev projection := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev code (i : I W x y) := ((projection.obj i)).1
private abbrev degree (i : I W x y) := ((projection.obj i)).2

variable {i i' : I W x y} (a : i ⟶ i')
variable {m n : SimplexCategory} (j : m ⟶ n)
variable (p : (code i).toSSet ⊗ J.obj m ⟶ J.obj (degree i))
variable (p' : (code i').toSSet ⊗ J.obj n ⟶ J.obj (degree i'))

private abbrev h := (projection.map a).1
private abbrev k := (projection.map a).2

/-- The actual under-boundary graph comparison associated with a full parameter. -/
def graph {i : I W x y} {m : SimplexCategory}
    (p : (code i).toSSet ⊗ J.obj m ⟶ J.obj (degree i)) :
    (under (code i)).obj m ⟶ (underDiagram W x y).obj i :=
  Under.homMk (cylinderMap (code i) p) (cylinderMap_boundary (code i) p)

variable (c : code i ⟶ Q.code) (c' : code i' ⟶ Q.code)
variable (hc : h a ≫ c' = c)
variable (hp : ((h a).map ⊗ₘ J.map j) ≫ p' = p ≫ J.map (k a))

private abbrev rawEquation {i : I W x y} {n : SimplexCategory}
    (c : code i ⟶ Q.code) (p : (code i).toSSet ⊗ J.obj n ⟶ J.obj (degree i)) :=
  (graph p).right ≫ ((underCocone W x y).app i).right = augmentation (code i) n ≫ c.map ≫ Q.map

variable (hr : rawEquation Q c p) (hr' : rawEquation Q c' p')

private abbrev nativeOperator :=
  NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (code i, m) ⟶ (code i', n) from (h a, j))

include hp in
theorem graph_square :
    graph p ≫ (underDiagram W x y).map a = nativeOperator a j ≫ graph p' := by
  apply Under.UnderMorphism.ext
  exact JTBinaryPrismSideTransport.mixedCylinderSquare (h a) (k a) j p p' hp

include hc in
private theorem native_square :
    JTCylinderOverTarget.native W x y Q (code i) m c =
      nativeOperator a j ≫ JTCylinderOverTarget.native W x y Q (code i') n c' := by
  apply Under.UnderMorphism.ext
  change augmentation (code i) m ≫ c.map =
    (nativeMap (h a) m ≫ (value (code i')).map j) ≫ augmentation (code i') n ≫ c'.map
  have hh : (h a).map ≫ c'.map = c.map :=
    congrArg (fun f : code i ⟶ Q.code ↦ f.map) hc
  rw [Category.assoc, ← Category.assoc ((value (code i')).map j), augmentation_parameter_natural,
    ← Category.assoc (nativeMap (h a) m), augmentation_native_natural, Category.assoc, hh]

include hc hp in
/-- Both original projections commute with any compatible native, time, and
coefficient operators in the original fixed-target comma construction. -/
theorem lift_square :
    JTCylinderOverTarget.lift W x y Q i (code i) m (graph p) c hr ≫
        (JTTargetCommaPullback.diagram W x y Q).map a =
      nativeOperator a j ≫ JTCylinderOverTarget.lift W x y Q i' (code i') n (graph p') c' hr' :=
  JTCylinderOverTargetBaseChange.lift_compare W x y Q i i' (code i) (code i') m n
    (graph p) (graph p') c c' hr hr' (nativeOperator a j) a
    (graph_square a j p p' hp) (native_square Q a j c c' hc)


include hc hp in
/-- The mixed comparison also transports the original functors on all
internal necklaces into the fixed-target comma. -/
def compare :
    JTCylinderOverTarget.functor W x y Q i (code i) m (graph p) c hr ⟶
      CostructuredArrow.map (nativeOperator a j) ⋙
        JTCylinderOverTarget.functor W x y Q i' (code i') n (graph p') c' hr' :=
  JTCylinderOverTargetBaseChange.compare W x y Q i i' (code i) (code i') m n
    (graph p) (graph p') c c' hr hr' (nativeOperator a j) a
    (graph_square a j p p' hp) (native_square Q a j c c' hc)

end

end DaggerModels.PartII.JTParametrizedTargetLiftTransport
