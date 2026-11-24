import DaggerModelsPartII.JTEndpointGraphOverlapEvaluation
import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTParametrizedTargetCoefficientPadding

/-! The joined fixed-simplex overlap as an actual parametrized target family. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped Prod

namespace DaggerModels.PartII.JTEndpointGraphOverlapParametrizedFamily

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice
open JTEndpointRowGraphOperators
open JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphOverlapFamilies
open JTEndpointGraphOverlapCylinder
open JTEndpointGraphOverlapEvaluation
open JTMixedGraphRawRefinement (nativeGraphParameter)
open JTFiniteCoefficientBridgeCylinder (graphPrism)
open JTGraphFactoredPresentation (TargetComma)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d m : ℕ} {q : std.obj ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev I := Index P parents refineTo hx hy
private abbrev F := projection P parents refineTo hx hy
private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy
private abbrev L := labelIndex P parents refineTo hx hy
private abbrev time := F P parents refineTo hx hy ⋙ joinedTime P parents refineTo

private theorem collapse_natural {U V : I P parents refineTo hx hy} (f : U ⟶ V) :
    (JTParametrizedTargetFamilies.codes (L P parents refineTo hx hy)).map f ≫
        MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy V) ≫
        toFixedBead P parents refineTo hx hy V =
      MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U) ≫
        toFixedBead P parents refineTo hx hy U := by
  let r := (F P parents refineTo hx hy).map f
  let a := (horizontal.map r.1.hom).left
  have h : bead.map a ≫ toFixedBead P parents refineTo hx hy V =
      toFixedBead P parents refineTo hx hy U := by
    change bead.map a ≫ bead.map ((horizontal.obj (child P parents refineTo hx hy V).left).hom) =
      bead.map ((horizontal.obj (child P parents refineTo hx hy U).left).hom)
    rw [← bead.map_comp]
    exact congrArg bead.map (Over.w (horizontal.map r.1.hom))
  change JTMixedGraphHorizontalTraversal.padded (bead.map a) ≫
      MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy V) ≫
      toFixedBead P parents refineTo hx hy V = _
  have hc := JTMixedGraphHorizontalTraversal.collapse_natural (bead.map a)
  calc
    _ = (MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U) ≫
        bead.map a) ≫ toFixedBead P parents refineTo hx hy V := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ toFixedBead P parents refineTo hx hy V) hc
    _ = _ := by simp only [Category.assoc, h]

/-- The actual joined overlap, with the original label index and time diagram. -/
def family : JTParametrizedTargetFamilies.Family (Q hx hy)
    (L P parents refineTo hx hy) (time P parents refineTo hx hy) where
  collapse := {
    app U := MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U) ≫
      toFixedBead P parents refineTo hx hy U
    naturality := by
      intro U V f
      change (JTParametrizedTargetFamilies.codes (L P parents refineTo hx hy)).map f ≫
          MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy V) ≫
          toFixedBead P parents refineTo hx hy V =
        (MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U) ≫
          toFixedBead P parents refineTo hx hy U) ≫ 𝟙 _
      simpa only [Category.comp_id, Category.assoc] using
        collapse_natural P parents refineTo hx hy f }
  parameter U :=
    graphPrism (c P parents refineTo hx hy U)
      (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
      (nativeGraphParameter (d := dim P parents refineTo hx hy U)
        (param P parents refineTo hx hy U)) ≫
      snd (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U)).toSSet
        (J.obj ((F P parents refineTo hx hy ⋙ bridgeParameter P parents refineTo).obj U))
  parameter_map := by
    intro U V f
    let r := (F P parents refineTo hx hy).map f
    let a := r.1.hom.unop.base.unop.left
    let v := (nativeCodes P parents refineTo).map r
    let k := (degree P parents refineTo).map r.1
    let j := (joinedTime P parents refineTo).map r
    let b := (bridgeParameter P parents refineTo).map r
    have hp : nativeGraphParameter (d := dim P parents refineTo hx hy U)
        (param P parents refineTo hx hy U) ≫ J.map k =
        v.map ≫ nativeGraphParameter (d := dim P parents refineTo hx hy V)
          (param P parents refineTo hx hy V) :=
      JTMixedGraphHorizontalTraversal.parameter_mixed
        (d := dim P parents refineTo hx hy U) (e := dim P parents refineTo hx hy V)
        a.1 a.2.1 a.2.2 k r.1.hom.unop.fiber.unop.hom.parameter
    have hs := JTFiniteCoefficientBridgeMixedCylinder.graphPrism_mixed
      (c P parents refineTo hx hy U) (u P parents refineTo hx hy U)
      (n P parents refineTo hx hy U) (c P parents refineTo hx hy V)
      (u P parents refineTo hx hy V) (n P parents refineTo hx hy V)
      v k (nativeGraphParameter (d := dim P parents refineTo hx hy U)
        (param P parents refineTo hx hy U))
      (nativeGraphParameter (d := dim P parents refineTo hx hy V)
        (param P parents refineTo hx hy V)) hp j b (paired_natural r)
    have hh := congrArg (fun z ↦ z ≫ snd
      (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy V)).toSSet
      (J.obj ((bridgeParameter P parents refineTo).obj ((F P parents refineTo hx hy).obj V)))) hs
    simpa only [Category.assoc, tensorHom_snd] using hh.symm
  raw U := by
    change JTFiniteCoefficientBridgeCylinder.cylinderMap (c P parents refineTo hx hy U)
        (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
        (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (nativeGraphParameter (d := dim P parents refineTo hx hy U)
          (param P parents refineTo hx hy U)) ≫
      JTNecklaceEndpointCylinder.descend W x y
        (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (JTFiniteCoefficientBridgeOrder.bridge
          (graph (childGraph P parents refineTo hx hy U)).obj.degree
          (n P parents refineTo hx hy U) m)
        (JTMixedGraphOrderedLabel.orderedPoint (families P parents refineTo hx hy U)) =
      NecklaceCylinderAugmentation.augmentation
        (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (JTFiniteCoefficientBridgeTime.time m (n P parents refineTo hx hy U)) ≫
      (MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U) ≫
        toFixedBead P parents refineTo hx hy U).map ≫ (Q hx hy).map
    simpa only [Category.assoc] using whole_raw P parents refineTo hx hy U

/-- The parametrized graph is the existing joined cylinder map at each overlap. -/
theorem graph_right_join (U : I P parents refineTo hx hy) :
    (JTParametrizedTargetLiftTransport.graph
      ((family P parents refineTo hx hy).parameter U)).right =
    ((join P parents refineTo).app ((F P parents refineTo hx hy).obj U)).right := by
  rfl

/-- The generic fixed-target lift recovers the overlap lift already used for evaluation. -/
theorem lift_component_eq (U : I P parents refineTo hx hy) :
    (JTParametrizedTargetFamilies.liftNatural (family P parents refineTo hx hy)).app U =
      (lifts P parents refineTo hx hy).app U := by
  apply pullback.hom_ext
  · dsimp only [JTParametrizedTargetFamilies.liftNatural]
    change _ ≫ JTTargetCommaPullback.fst W x y (Q hx hy)
        ((L P parents refineTo hx hy).obj U) =
      _ ≫ JTTargetCommaPullback.fst W x y (Q hx hy)
        ((L P parents refineTo hx hy).obj U)
    rw [JTCylinderOverTarget.lift_decorated,
      JTEndpointGraphOverlapEvaluation.lifts_decorated]
    change JTParametrizedTargetLiftTransport.graph
        ((family P parents refineTo hx hy).parameter U) =
      (join P parents refineTo).app ((F P parents refineTo hx hy).obj U)
    apply Under.UnderMorphism.ext
    exact graph_right_join P parents refineTo hx hy U
  · dsimp only [JTParametrizedTargetFamilies.liftNatural]
    change _ ≫ JTTargetCommaPullback.snd W x y (Q hx hy)
        ((L P parents refineTo hx hy).obj U) =
      _ ≫ JTTargetCommaPullback.snd W x y (Q hx hy)
        ((L P parents refineTo hx hy).obj U)
    rw [JTCylinderOverTarget.lift_native,
      JTEndpointGraphOverlapEvaluation.lifts_native]
    apply Under.UnderMorphism.ext
    rfl

/-- The full natural transformations of pullback lifts coincide. -/
theorem liftNatural_eq :
    JTParametrizedTargetFamilies.liftNatural (family P parents refineTo hx hy) =
      lifts P parents refineTo hx hy := by
  apply NatTrans.ext
  funext U
  exact lift_component_eq P parents refineTo hx hy U

/-- The generic family evaluation is the existing exact overlap evaluation. -/
theorem evaluation_eq :
    JTParametrizedTargetFamilies.evaluate (family P parents refineTo hx hy) =
      evaluation P parents refineTo hx hy := by
  unfold JTParametrizedTargetFamilies.evaluate
    JTEndpointGraphOverlapEvaluation.evaluation
    JTDecoratedIntervalCylinder.evaluateFromProjections
  rw [liftNatural_eq]
  rfl

/-- The padded choices retain the joined time through the original comparison projection. -/
def paddedSynchronized :
    JTMarkedFiniteParametrizedTargetFamilies.Synchronized
      (JTOrderedLabelCoefficientPadding.base (L P parents refineTo hx hy) ⋙
        time P parents refineTo hx hy) (Q hx hy) :=
  JTParametrizedTargetCoefficientPadding.synchronized (family P parents refineTo hx hy)

/-- The old and padded pullback lifts agree along the middle coefficient face. -/
theorem comparison_lifts
    (p : JTOrderedLabelCoefficientPadding.Extensions (L P parents refineTo hx hy)) :
    (JTParametrizedTargetFamilies.liftNatural
      ((family P parents refineTo hx hy).precomp
        (JTOrderedLabelCoefficientPadding.base (L P parents refineTo hx hy)))).app p ≫
      (JTTargetCommaPullback.diagram W x y (Q hx hy)).map
        ((JTOrderedLabelCoefficientPadding.comparison (L P parents refineTo hx hy)).app p) =
    (JTParametrizedTargetFamilies.liftNatural
      (JTParametrizedTargetCoefficientPadding.paddedFamily
        (family P parents refineTo hx hy))).app p :=
  JTParametrizedTargetCoefficientPadding.comparison_lifts
    (family P parents refineTo hx hy) p

end

end DaggerModels.PartII.JTEndpointGraphOverlapParametrizedFamily
