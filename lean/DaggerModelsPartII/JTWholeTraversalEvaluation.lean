import DaggerModelsPartII.JTParametrizedBeadGraph
import DaggerModelsPartII.JTInternalTraversalLifts
import DaggerModelsPartII.JTParametrizedEvaluationOperators
import DaggerModelsPartII.JTGraphTransportRestriction

/-! Full prism lifts recover exact graph predecessors in the original fixed-target comma. -/

set_option autoImplicit false
set_option maxHeartbeats 220000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTWholeTraversalEvaluation

open JTNecklaceEndpointCylinder
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_cylinder cylinderMap_boundary)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open JTInternalTraversalLifts (ArrowIndex lifts traversal intoPrism intoPrism_cylinder prism_map)
open JTParametrizedTargetFamilies (Family codes evaluate evaluate_decorated evaluate_native
  evaluate_map_operators)
open JTGraphLiftTransport (GraphLift degreeOperator)
open JTGraphLiftRestriction (restrict)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private theorem graph_augmentation (T : NecklaceCode) {n k : SimplexCategory}
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    cylinderMap T p ≫ augmentation T k = augmentation T n := by
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, augmentation_cylinder,
      lift_fst, augmentation_cylinder]
  · rw [← Category.assoc, cylinderMap_boundary, augmentation_boundary, augmentation_boundary]

private theorem applyWholePrism {X : SSet.{0}} {T : NecklaceCode} {n k : SimplexCategory}
    {g : X ⟶ (value T).obj n} (s : JTInternalTraversalLifts.Lift g)
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    lift (g ≫ augmentation T n) (intoPrism s ≫ p) ≫ (cylinder T).app k =
      g ≫ cylinderMap T p := by
  calc
    _ = intoPrism s ≫ (lift (fst T.toSSet (J.obj n)) p ≫ (cylinder T).app k) := by
      rw [← Category.assoc, comp_lift, intoPrism, lift_fst]
    _ = intoPrism s ≫ ((cylinder T).app n ≫ cylinderMap T p) := by rw [cylinderMap_cylinder]
    _ = _ := by rw [← Category.assoc, intoPrism_cylinder]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev I := ArrowIndex (codes L) time
private abbrev a₀ (a : I (L := L) (time := time)) := a.fst.2.base
private abbrev S (a : I (L := L) (time := time)) := a.fst.1.unop.fiber.left
private abbrev U (a : I (L := L) (time := time)) := (evaluate F).obj a.fst.2
private abbrev V (a : I (L := L) (time := time)) := (evaluate F).obj a.fst.1.unop
private abbrev c (a : I (L := L) (time := time)) :
    S a ⟶ (U F a).left.fiber.left := a.snd.fiber.left
private abbrev d (a : I (L := L) (time := time)) :=
  traversal (codes L) time a

private theorem traversal_eq (a : I (L := L) (time := time)) :
    (c F a).map ≫ a.fst.2.fiber.hom.right = d a :=
  congrArg (fun f ↦ f.right) (CostructuredArrow.w a.snd.fiber)

private theorem decoratedTraversal (a : I (L := L) (time := time)) :
    (c F a).map ≫ (U F a).left.fiber.hom.right =
      d a ≫ cylinderMap ((codes L).obj (a₀ a)) (F.parameter (a₀ a)) := by
  have h := evaluate_decorated F a.fst.2
  rw [h, ← Category.assoc, traversal_eq F a]
  rfl

private theorem horizontal (a : I (L := L) (time := time)) :
    (c F a ≫ JTCommaGraphPredecessor.augmentationCode (U F a).left).map =
      d a ≫ augmentation ((codes L).obj (a₀ a)) (time.obj (a₀ a)) := by
  change (c F a).map ≫ (U F a).left.fiber.hom.right ≫ augmentation _ _ = _
  rw [← Category.assoc, decoratedTraversal F a, Category.assoc]
  exact congrArg (d a ≫ ·) (graph_augmentation _ (F.parameter (a₀ a)))

/-- The whole lift is a graph over the original decorated target, with exactly the
native collapse of the specified original internal-necklace arrow. -/
def graphLift (a : I (L := L) (time := time)) (s : (lifts (codes L) time).obj a) :
    GraphLift (U F a).left (S a) where
  collapse := c F a
  parameter := intoPrism s ≫ F.parameter (a₀ a)
  comm := by
    rw [horizontal F a, decoratedTraversal F a]
    exact applyWholePrism s (F.parameter (a₀ a))

/-- The graph predecessor maps to the whole evaluated necklace in the original comma. -/
def toOriginal (a : I (L := L) (time := time)) (s : (lifts (codes L) time).obj a) :
    JTGraphRestrictionRaw.predecessor (U := U F a) (graphLift F a s) ⟶ U F a :=
  JTGraphTransportNaturality.toComma (graphLift F a s)


private abbrev ACode := BoundaryNecklaceComma.sourceCode
  (JTInternalTraversalLifts.cylinders (codes L) time)

private abbrev degOp {a b : I (L := L) (time := time)} (f : a ⟶ b) :=
  ((OrderedLabelElements.projection W (boundaryPoint W x y)).map (L.map f.val.2.base)).2

/-- Transport the entire decorated coefficient through both original factorization operators. -/
theorem graphLift_parameter_map {a b : I (L := L) (time := time)} (f : a ⟶ b)
    (s : (lifts (codes L) time).obj a) :
    (graphLift F b ((lifts (codes L) time).map f s)).parameter =
      ((ACode (L := L) (time := time)).map f.val.1.unop).map ≫
        (graphLift F a s).parameter ≫ J.map (degOp f) := by
  change intoPrism ((lifts (codes L) time).map f s) ≫ F.parameter (a₀ b) = _
  let v := f.val.2.base
  have h : (((codes L).map v).map ⊗ₘ J.map (time.map v)) ≫ F.parameter (a₀ b) =
      F.parameter (a₀ a) ≫ J.map (degOp f) := F.parameter_map v
  rw [prism_map]
  simp only [Category.assoc]
  rw [h]
  rfl


/-- Interpretation of a whole lift commutes with the actual transport and restriction
of graph lifts in the original fixed-target comma. -/
theorem graphLift_factorization {a b : I (L := L) (time := time)} (f : a ⟶ b)
    (s : (lifts (codes L) time).obj a) :
    graphLift F b ((lifts (codes L) time).map f s) =
      restrict ((graphLift F a s).transport ((evaluate F).map f.val.2).left)
        f.val.1.unop.fiber.left := by
  have hTarget := evaluate_map_operators F f.val.2
  apply GraphLift.ext
  · change b.snd.fiber.left = f.val.1.unop.fiber.left ≫ a.snd.fiber.left ≫
      ((evaluate F).map f.val.2).left.fiber.left
    rw [hTarget.2]
    let C := ACode (L := L) (time := time)
    have h : C.map (f.val.1.unop ≫ a.snd ≫ f.val.2) = C.map b.snd :=
      congrArg C.map f.property
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h.symm
  · change (graphLift F b ((lifts (codes L) time).map f s)).parameter =
      f.val.1.unop.fiber.left.map ≫
        ((graphLift F a s).parameter ≫ J.map (degreeOperator ((evaluate F).map f.val.2).left))
    rw [degreeOperator, hTarget.1]
    exact graphLift_parameter_map F f s

variable (a : I (L := L) (time := time)) (s : (lifts (codes L) time).obj a)
variable {e : ℕ} (i : (NecklaceCode.single e).toSSet ⟶ (S a).toSSet)

private abbrev beadNative := i ≫ d a ≫ augmentation ((codes L).obj (a₀ a)) (time.obj (a₀ a))

/-- Restricting the whole graph to a bead gives the exact coefficient parameter
of its prism simplex, including when the time varies on that bead. -/
theorem bead_parameter :
    JTParametrizedBeadGraph.beadParameterWithTime F (a₀ a) e (beadNative a i) (i ≫ s.val) =
      i ≫ (graphLift F a s).parameter := by
  unfold JTParametrizedBeadGraph.beadParameterWithTime
  change _ = i ≫ (intoPrism s ≫ F.parameter (a₀ a))
  rw [← Category.assoc i, intoPrism, comp_lift]
  rfl

/-- The raw value of this local graph is the restriction of the whole original
native leg in the actual fixed-target comma. -/
theorem bead_value :
    JTParametrizedBeadGraph.beadRaw F (a₀ a) e (beadNative a i) =
      i ≫ (c F a).map ≫ (U F a).hom.hom.map ≫ Q.map := by
  rw [JTParametrizedBeadGraph.beadRaw, evaluate_native F a.fst.2]
  simp only [Category.assoc]
  rw [← Category.assoc (c F a).map a.fst.2.fiber.hom.right, traversal_eq F a]

end
end DaggerModels.PartII.JTWholeTraversalEvaluation
