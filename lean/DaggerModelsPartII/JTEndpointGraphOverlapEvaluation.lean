import DaggerModelsPartII.JTEndpointGraphOverlapFamilies
import DaggerModelsPartII.JTEndpointGraphOverlapCylinder
import DaggerModelsPartII.JTEndpointGraphCoefficientEvaluation

/-! Evaluate the joined bridge families in the original fixed-target comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen Prod

namespace DaggerModels.PartII.JTEndpointGraphOverlapEvaluation

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphOverlapFamilies
open JTEndpointGraphOverlapCylinder
open JTHigherMixedGraphTargetLift (toNativeTarget)
open BoundaryNecklaceComma (necklaceUnder)
open JTGraphFactoredPresentation (TargetComma)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

variable {W : Source} {d m : ℕ} {q : std.obj ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy
private abbrev I := Index P parents refineTo hx hy
private abbrev F := projection P parents refineTo hx hy
private abbrev codesAt := F P parents refineTo hx hy ⋙ nativeCodes P parents refineTo
private abbrev bridgeAt := F P parents refineTo hx hy ⋙ bridgeParameter P parents refineTo
private abbrev timeAt := F P parents refineTo hx hy ⋙ joinedTime P parents refineTo
private abbrev tagged := (codesAt P parents refineTo hx hy).prod' (bridgeAt P parents refineTo hx hy)

private theorem middle_map {U V : I P parents refineTo hx hy} (f : U ⟶ V) :
    std.map (JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
      (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)) ≫ rowAt P parents refineTo hx hy U =
    std.map ((bridgeAt P parents refineTo hx hy).map f) ≫
      (std.map (JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy V)
        (u P parents refineTo hx hy V) (n P parents refineTo hx hy V)) ≫ rowAt P parents refineTo hx hy V) ≫
      (rows W).map (((F P parents refineTo hx hy).map f).1.hom.unop.base.unop.left.1.op) := by
  let r := (F P parents refineTo hx hy).map f
  let b := JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
    (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
  let b' := JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy V)
    (u P parents refineTo hx hy V) (n P parents refineTo hx hy V)
  let a := (bridgeAt P parents refineTo hx hy).map f
  let h := (rows W).map r.1.hom.unop.base.unop.left.1.op
  calc
    _ = std.map b ≫ (rowAt P parents refineTo hx hy V ≫ h) :=
      congrArg (std.map b ≫ ·)
        (parentRow_natural P ((toCommon P parents refineTo).map r.1)).symm
    _ = (std.map a ≫ std.map b') ≫ (rowAt P parents refineTo hx hy V ≫ h) := by
      have he : a ≫ b' = b := bridgeParameter_base r
      rw [← std.map_comp, he]
    _ = _ := by simp only [Category.assoc]; rfl

private abbrev orderedPoint (U : I P parents refineTo hx hy) :=
  JTMixedGraphOrderedLabel.orderedPoint (families P parents refineTo hx hy U)

private theorem orderedPoint_map {U V : I P parents refineTo hx hy} (f : U ⟶ V) :
    (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)).map
      (((tagged P parents refineTo hx hy).map f).op) (orderedPoint P parents refineTo hx hy V) =
      orderedPoint P parents refineTo hx hy U := by
  let r := (F P parents refineTo hx hy).map f
  let a := r.1.hom.unop.base.unop.left
  have h := choice_maps P parents refineTo hx hy f
  exact (JTMixedGraphOrderedLabelTransport.orderedPoint_mixed_reindex_joint
    (d := dim P parents refineTo hx hy U) (e := dim P parents refineTo hx hy V)
    a.1 a.2.1 a.2.2 ((bridgeAt P parents refineTo hx hy).map f)
    (families P parents refineTo hx hy U) (families P parents refineTo hx hy V)
    h.1 (middle_map P parents refineTo hx hy f) h.2).symm

/-- The original decorated labels of the bridge with arbitrary compatible extensions. -/
def labelIndex : I P parents refineTo hx hy ⥤ OrderedLabelElements.Index W (boundaryPoint W x y) where
  obj U := op ⟨op ((tagged P parents refineTo hx hy).obj U), orderedPoint P parents refineTo hx hy U⟩
  map f := Quiver.Hom.op ⟨((tagged P parents refineTo hx hy).map f).op, orderedPoint_map P parents refineTo hx hy f⟩
  map_id U := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((tagged P parents refineTo hx hy).map_id U)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((tagged P parents refineTo hx hy).map_comp f g)

abbrev sourceCylinders := F P parents refineTo hx hy ⋙
  cylinders P parents refineTo (joinedTime P parents refineTo)

private def decoratedLeg : sourceCylinders P parents refineTo hx hy ⟶
    labelIndex P parents refineTo hx hy ⋙ underDiagram W x y :=
  Functor.whiskerLeft (F P parents refineTo hx hy) (join P parents refineTo)

private def nativeLeg : sourceCylinders P parents refineTo hx hy ⟶
    (Functor.const (I P parents refineTo hx hy)).obj (necklaceUnder.obj (Q hx hy).code) where
  app U := toNativeTarget (dim P parents refineTo hx hy U) ((timeAt P parents refineTo hx hy).obj U) ≫
    necklaceUnder.map (toFixedBead P parents refineTo hx hy U)
  naturality {U V} f := by
    let r := (F P parents refineTo hx hy).map f
    let a := (horizontal.map r.1.hom).left
    have h : bead.map a ≫ toFixedBead P parents refineTo hx hy V = toFixedBead P parents refineTo hx hy U := by
      change bead.map a ≫ bead.map ((horizontal.obj (child P parents refineTo hx hy V).left).hom) =
        bead.map ((horizontal.obj (child P parents refineTo hx hy U).left).hom)
      have he : a ≫ (horizontal.obj (child P parents refineTo hx hy V).left).hom =
          (horizontal.obj (child P parents refineTo hx hy U).left).hom :=
        Over.w (horizontal.map r.1.hom)
      rw [← bead.map_comp, he]
    rw [show ((Functor.const (I P parents refineTo hx hy)).obj
      (necklaceUnder.obj (Q hx hy).code)).map f = 𝟙 _ from rfl, Category.comp_id]
    calc
      _ = toNativeTarget (dim P parents refineTo hx hy U) ((timeAt P parents refineTo hx hy).obj U) ≫
          necklaceUnder.map (bead.map a ≫ toFixedBead P parents refineTo hx hy V) :=
        JTEndpointGraphCoefficientEvaluation.native_leg_natural (h := dim P parents refineTo hx hy U)
          (k := dim P parents refineTo hx hy V) (l := d)
          (bead.map a) (toFixedBead P parents refineTo hx hy V) ((timeAt P parents refineTo hx hy).map f)
      _ = _ := congrArg (fun g ↦ toNativeTarget (dim P parents refineTo hx hy U)
        ((timeAt P parents refineTo hx hy).obj U) ≫ necklaceUnder.map g) h

private theorem sameRaw (U : I P parents refineTo hx hy) :
    (decoratedLeg P parents refineTo hx hy).app U ≫
      (underCocone W x y).app ((labelIndex P parents refineTo hx hy).obj U) =
    (nativeLeg P parents refineTo hx hy).app U ≫ JTTargetCommaPullback.targetMap W x y (Q hx hy) := by
  apply Under.UnderMorphism.ext
  simpa only [Category.assoc] using whole_raw P parents refineTo hx hy U

/-- The exact lift into the decorated and native target pullback. -/
def lifts : sourceCylinders P parents refineTo hx hy ⟶
    labelIndex P parents refineTo hx hy ⋙ JTTargetCommaPullback.diagram W x y (Q hx hy) :=
  JTDecoratedIntervalCylinder.liftFromProjections (Q hx hy) (labelIndex P parents refineTo hx hy)
    (sourceCylinders P parents refineTo hx hy) (decoratedLeg P parents refineTo hx hy)
    (nativeLeg P parents refineTo hx hy) (sameRaw P parents refineTo hx hy)

theorem lifts_decorated (U : I P parents refineTo hx hy) :
    (lifts P parents refineTo hx hy).app U ≫
      JTTargetCommaPullback.fst W x y (Q hx hy) ((labelIndex P parents refineTo hx hy).obj U) =
    (join P parents refineTo).app ((F P parents refineTo hx hy).obj U) :=
  JTDecoratedIntervalCylinder.liftFromProjections_fst (Q hx hy) (labelIndex P parents refineTo hx hy)
    (sourceCylinders P parents refineTo hx hy) (decoratedLeg P parents refineTo hx hy)
    (nativeLeg P parents refineTo hx hy) (sameRaw P parents refineTo hx hy) U

theorem lifts_native (U : I P parents refineTo hx hy) :
    (lifts P parents refineTo hx hy).app U ≫
      JTTargetCommaPullback.snd W x y (Q hx hy) ((labelIndex P parents refineTo hx hy).obj U) =
    toNativeTarget (dim P parents refineTo hx hy U) ((timeAt P parents refineTo hx hy).obj U) ≫
      necklaceUnder.map (toFixedBead P parents refineTo hx hy U) :=
  JTDecoratedIntervalCylinder.liftFromProjections_snd (Q hx hy) (labelIndex P parents refineTo hx hy)
    (sourceCylinders P parents refineTo hx hy) (decoratedLeg P parents refineTo hx hy)
    (nativeLeg P parents refineTo hx hy) (sameRaw P parents refineTo hx hy) U

abbrev Resolution := BoundaryNecklaceComma.Presentation (sourceCylinders P parents refineTo hx hy)

/-- Evaluate all internal necklaces and their exact operators in the fixed-target comma. -/
def evaluation : Resolution P parents refineTo hx hy ⥤ TargetComma (Q hx hy) :=
  JTDecoratedIntervalCylinder.evaluateFromProjections (Q hx hy) (labelIndex P parents refineTo hx hy)
    (sourceCylinders P parents refineTo hx hy) (decoratedLeg P parents refineTo hx hy)
    (nativeLeg P parents refineTo hx hy) (sameRaw P parents refineTo hx hy)

/-- Taking the full original internal-necklace presentation preserves the nerve weak type. -/
theorem projection_weak :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (sourceCylinders P parents refineTo hx hy)))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun U ↦
    JTHomotopyTargetComma.fiber_point_GW_at
      ((codesAt P parents refineTo hx hy).obj U) ((timeAt P parents refineTo hx hy).obj U))

end
end DaggerModels.PartII.JTEndpointGraphOverlapEvaluation
