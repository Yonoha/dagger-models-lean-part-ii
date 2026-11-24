import DaggerModelsPartII.JTParametrizedTargetLiftTransport

/-! Pull back a whole reduced-cylinder graph along an ordered-label map. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetPullback

open JTParametrizedTargetLiftTransport (graph graph_square)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTNecklaceEndpointCylinder (nativeMap value)
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y

variable {W : Source} {x y : Vertex W}
private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev code (i : I W x y) := (pr.obj i).1
private abbrev degree (i : I W x y) := (pr.obj i).2

variable {i j : I W x y} (r : i ⟶ j) (n : SimplexCategory)
variable (s : degree j ⟶ degree i)
variable (hs : s ≫ (pr.map r).2 = 𝟙 (degree j))
variable (p : (code j).toSSet ⊗ J.obj n ⟶ J.obj (degree j))

/-- Precompose the whole prism with the native map and apply the coefficient section. -/
def parameter : (code i).toSSet ⊗ J.obj n ⟶ J.obj (degree i) :=
  ((pr.map r).1.map ⊗ₘ 𝟙 (J.obj n)) ≫ p ≫ J.map s

include hs in
theorem parameter_square :
    ((pr.map r).1.map ⊗ₘ J.map (𝟙 n)) ≫ p =
      parameter r n s p ≫ J.map (pr.map r).2 := by
  rw [parameter, J.map_id]
  simp only [Category.assoc, ← J.map_comp, hs, J.map_id, Category.comp_id]

private abbrev nativeOperator :=
  NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (code i, n) ⟶ (code j, n) from ((pr.map r).1, 𝟙 n))

include hs in
/-- Both routes give the same actual map on the entire reduced decorated cylinder. -/
theorem decorated_square :
    graph (i := i) (parameter r n s p) ≫ (underDiagram W x y).map r =
      nativeOperator r n ≫ graph (i := j) p :=
  graph_square r (𝟙 n) (parameter r n s p) p (parameter_square r n s hs p)

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : code j ⟶ Q.code)
variable (hr : (graph (i := j) p).right ≫ ((underCocone W x y).app j).right =
  augmentation (code j) n ≫ c.map ≫ Q.map)

include hs hr in
set_option maxHeartbeats 500000 in
/-- The pullback graph has the original target after the exact native composition. -/
theorem pulled_raw :
    (graph (i := i) (parameter r n s p)).right ≫ ((underCocone W x y).app i).right =
      augmentation (code i) n ≫ ((pr.map r).1 ≫ c).map ≫ Q.map := by
  let f : code i ⟶ code j := (pr.map r).1
  let g := graph (i := i) (parameter r n s p)
  let h := graph (i := j) p
  have hh : g.right ≫ ((underDiagram W x y).map r).right =
      nativeMap f n ≫ h.right := by
    have sq := congrArg (fun a ↦ a.right) (decorated_square r n s hs p)
    change g.right ≫ ((underDiagram W x y).map r).right =
      (nativeMap f n ≫ (value (code j)).map (𝟙 n)) ≫ h.right at sq
    rw [(value (code j)).map_id, Category.comp_id] at sq
    exact sq
  have hc : ((underDiagram W x y).map r).right ≫ ((underCocone W x y).app j).right =
      ((underCocone W x y).app i).right :=
    congrArg (fun a ↦ a.right) ((underCocone W x y).naturality r)
  change g.right ≫ ((underCocone W x y).app i).right = _
  rw [← hc, ← Category.assoc, hh, Category.assoc, hr,
    ← Category.assoc (nativeMap f n), augmentation_native_natural f n]
  simp only [Category.assoc]
  rfl

/-- The collapse compares all actual internal necklaces over the same original fixed target. -/
def compare :=
  JTParametrizedTargetLiftTransport.compare Q r (𝟙 n)
    (parameter r n s p) p ((pr.map r).1 ≫ c) c rfl (parameter_square r n s hs p)
    (pulled_raw r n s hs p Q c hr) hr

end

end DaggerModels.PartII.JTParametrizedTargetPullback
