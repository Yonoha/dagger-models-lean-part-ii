import DaggerModelsPartII.JTEndpointGraphCoefficientLabels
import DaggerModelsPartII.JTCommonCoefficientHorizontalCylinder
import DaggerModelsPartII.JTEndpointHorizontalChoice
import DaggerModelsPartII.JTDecoratedIntervalCylinder

/-! Evaluate the entire mixed common-coefficient slice in the original fixed-target comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerChosenRigidificationNecklace.NecklaceCode (single)
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen Prod

namespace DaggerModels.PartII.JTEndpointGraphCoefficientEvaluation

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientChoices (Index base semiTime leftChoice rightChoice index_point_GW)
open JTEndpointGraphCoefficientFamilies JTEndpointGraphCoefficientLabels
open JTEndpointNormalizationLifts JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open JTHigherMixedGraphTargetLift
open JTGraphInterpolatedSourceComparison (sourceMap sourceMap_time)
open BoundaryNecklaceComma (necklaceUnder)
open JTGraphFactoredPresentation (TargetComma)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open NecklaceCylinderJointDiagram (cylinderUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable {q : std.obj ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy

/-- The actual reduced time cylinders, with all original horizontal and time operators. -/
abbrev cylinders : Index P hx hy ⥤ Under B :=
  ((nativeCodes P hx hy).prod' (time P hx hy)) ⋙ cylinderUnder

private abbrev native (U : Index P hx hy) :
    (cylinders P hx hy).obj U ⟶ necklaceUnder.obj (Q hx hy).code :=
  toNativeTarget (dim P hx hy U) (timeDegree P hx hy U) ≫
    necklaceUnder.map (toFixedBead P hx hy U)

private abbrev decorated (U : Index P hx hy) :
    (cylinders P hx hy).obj U ⟶
      (underDiagram W x y).obj ((labelIndex P hx hy).obj U) :=
  commonToDecorated (d := dim P hx hy U) (n := timeDegree P hx hy U)
    (coeff P hx hy U) (param P hx hy U)

private theorem joint_map {S T : NecklaceCode} {m n : SimplexCategory}
    (u : S ⟶ T) (f : m ⟶ n) :
    cylinderUnder.map (X := (S, m)) (Y := (T, n)) (u ×ₘ f) =
      (under S).map f ≫ sourceMap u n := by
  apply Under.UnderMorphism.ext
  exact (nativeMap_parameter_natural u f).symm

theorem native_leg_natural {h k l : ℕ} {m n : SimplexCategory}
    (u : single h ⟶ single k) (v : single k ⟶ single l) (j : m ⟶ n) :
    cylinderUnder.map
        (JTMixedGraphHorizontalTraversal.padded u ×ₘ j) ≫
      (toNativeTarget k n ≫ necklaceUnder.map v) =
    toNativeTarget h m ≫ necklaceUnder.map (u ≫ v) := by
  rw [joint_map, Category.assoc, ← Category.assoc (sourceMap _ _),
    JTEndpointHorizontalChoice.native_after_source]
  simp only [← Category.assoc, toNativeTarget_natural, necklaceUnder.map_comp]

private theorem native_natural {U V : Index P hx hy} (f : U ⟶ V) :
    (cylinders P hx hy).map f ≫ native P hx hy V = native P hx hy U := by
  let u := (base P hx hy).map f
  let a := (horizontal.map u.left).left
  have h : bead.map a ≫ toFixedBead P hx hy V = toFixedBead P hx hy U := by
    change bead.map a ≫ bead.map ((horizontal.obj (child P hx hy V).left).hom) =
      bead.map ((horizontal.obj (child P hx hy U).left).hom)
    rw [← bead.map_comp, Over.w (horizontal.map u.left)]
  calc
    _ = toNativeTarget (dim P hx hy U) (timeDegree P hx hy U) ≫
        necklaceUnder.map (bead.map a ≫ toFixedBead P hx hy V) :=
      native_leg_natural (h := dim P hx hy U) (k := dim P hx hy V) (l := d)
        (bead.map a) (toFixedBead P hx hy V) ((time P hx hy).map f)
    _ = _ := congrArg (fun g ↦ toNativeTarget (dim P hx hy U) (timeDegree P hx hy U) ≫
      necklaceUnder.map g) h

private theorem decorated_natural {U V : Index P hx hy} (f : U ⟶ V) :
    decorated P hx hy U ≫ (underDiagram W x y).map ((labelIndex P hx hy).map f) =
      (cylinders P hx hy).map f ≫ decorated P hx hy V := by
  let u := (base P hx hy).map f
  let g := (coefficients P).map u
  let t := (semiTime P hx hy).map f
  let j := (time P hx hy).map f
  let a : ⦋dim P hx hy U⦌ ⟶ ⦋dim P hx hy V⦌ := u.left.unop.base.unop.left.1
  let v := (nativeCodes P hx hy).map f
  let C := JTEndpointGraphCoefficientChoices.enlarged P hx hy
  let k := C.map f
  have hp : param P hx hy U ≫ J.map g.left = std.map a ≫ param P hx hy V :=
    u.left.unop.fiber.unop.hom.parameter
  have h := JTCommonCoefficientHorizontalCylinder.cylinderMap_padded_mixed a
    u.left.unop.base.unop.left.2.1 u.left.unop.base.unop.left.2.2
    (c := coeff P hx hy U) (c' := coeff P hx hy V) g.left (Over.w g)
    j (SemiSimplexCategory.homEquiv t).injective (param P hx hy U) (param P hx hy V) hp
  apply Under.UnderMorphism.ext
  change (decorated P hx hy U).right ≫
      (nativeMap v (C.obj U) ≫ (value ((nativeCodes P hx hy).obj V)).map k) =
    (nativeMap v ((time P hx hy).obj U) ≫ (value ((nativeCodes P hx hy).obj V)).map j) ≫
      (decorated P hx hy V).right
  have hk := nativeMap_parameter_natural v k
  have hj := nativeMap_parameter_natural v j
  rw [← hk, ← hj, Category.assoc]
  exact h

private theorem sameRaw (U : Index P hx hy) :
    decorated P hx hy U ≫ (underCocone W x y).app ((labelIndex P hx hy).obj U) =
    native P hx hy U ≫ JTTargetCommaPullback.targetMap W x y (Q hx hy) := by
  let c := coeff P hx hy U
  let f := parentRow P (child P hx hy U)
  let s := param P hx hy U
  let E := families P hx hy U
  let target := (toFixedBead P hx hy U).map ≫ (Q hx hy).map
  have hq := raw_eq P hx hy U
  have qx : target.app (op ⦋0⦌) (NecklaceCode.single (dim P hx hy U)).first = rawVertex W x := by
    change (Q hx hy).map.app (op ⦋0⦌)
      ((toFixedBead P hx hy U).map.app (op ⦋0⦌) (NecklaceCode.single (dim P hx hy U)).first) = _
    rw [(toFixedBead P hx hy U).first]
    exact (Q hx hy).first
  have qy : target.app (op ⦋0⦌) (NecklaceCode.single (dim P hx hy U)).last = rawVertex W y := by
    change (Q hx hy).map.app (op ⦋0⦌)
      ((toFixedBead P hx hy U).map.app (op ⦋0⦌) (NecklaceCode.single (dim P hx hy U)).last) = _
    rw [(toFixedBead P hx hy U).last]
    exact (Q hx hy).last
  have hL := JTHigherCommonMixedGraphFamilies.common_vertical_stationary c _
    (JTEndpointGraphCoefficientChoices.leftSquare P hx (child P hx hy U)) (leftChoice P hx hy U)
  have hR := JTHigherCommonMixedGraphFamilies.common_vertical_stationary c _
    (JTEndpointGraphCoefficientChoices.rightSquare P hy (child P hx hy U)) (rightChoice P hx hy U)
  apply Under.UnderMorphism.ext
  simpa only [Category.assoc, target] using common_whole_raw (d := dim P hx hy U)
    c f s hq qx qy E hL hR

private abbrev D := JTTargetCommaPullback.diagram W x y (Q hx hy)

private def decoratedLeg : cylinders P hx hy ⟶ labelIndex P hx hy ⋙ underDiagram W x y where
  app := decorated P hx hy
  naturality _ _ f := (decorated_natural P hx hy f).symm

private def nativeLeg : cylinders P hx hy ⟶
    (Functor.const (Index P hx hy)).obj (necklaceUnder.obj (Q hx hy).code) where
  app := native P hx hy
  naturality _ _ f := (native_natural P hx hy f).trans (Category.comp_id _).symm

/-- Exact simultaneous lift of both the decorated and original fixed-target legs. -/
def lifts : cylinders P hx hy ⟶ labelIndex P hx hy ⋙ D hx hy :=
  JTDecoratedIntervalCylinder.liftFromProjections (Q hx hy) (labelIndex P hx hy)
    (cylinders P hx hy) (decoratedLeg P hx hy) (nativeLeg P hx hy) (sameRaw P hx hy)

/-- The decorated leg of every lift is the original common-coefficient cylinder. -/
theorem lifts_decorated (U : Index P hx hy) :
    (lifts P hx hy).app U ≫
      JTTargetCommaPullback.fst W x y (Q hx hy) ((labelIndex P hx hy).obj U) =
    commonToDecorated (d := dim P hx hy U) (n := timeDegree P hx hy U)
      (coeff P hx hy U) (param P hx hy U) :=
  JTDecoratedIntervalCylinder.liftFromProjections_fst (Q hx hy) (labelIndex P hx hy)
    (cylinders P hx hy) (decoratedLeg P hx hy) (nativeLeg P hx hy) (sameRaw P hx hy) U

/-- The native leg of every lift uses the original horizontal map to the fixed target. -/
theorem lifts_native (U : Index P hx hy) :
    (lifts P hx hy).app U ≫
      JTTargetCommaPullback.snd W x y (Q hx hy) ((labelIndex P hx hy).obj U) =
    toNativeTarget (dim P hx hy U) (timeDegree P hx hy U) ≫
      necklaceUnder.map (toFixedBead P hx hy U) :=
  JTDecoratedIntervalCylinder.liftFromProjections_snd (Q hx hy) (labelIndex P hx hy)
    (cylinders P hx hy) (decoratedLeg P hx hy) (nativeLeg P hx hy) (sameRaw P hx hy) U

abbrev Resolution := BoundaryNecklaceComma.Presentation (cylinders P hx hy)

/-- Evaluate every internal necklace of each exact enlarged choice at the unchanged target. -/
def evaluation : Resolution P hx hy ⥤ TargetComma (Q hx hy) :=
  JTDecoratedIntervalCylinder.evaluateFromProjections (Q hx hy) (labelIndex P hx hy)
    (cylinders P hx hy) (decoratedLeg P hx hy) (nativeLeg P hx hy) (sameRaw P hx hy)

/-- The domain of the exact evaluation is weakly contractible. -/
theorem resolution_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (Resolution P hx hy))) := by
  let E := BoundaryNecklaceComma.fiberDiagram (cylinders P hx hy)
  let p := Grothendieck.forget E
  letI : WeakEquivalence (nerveMap p) :=
    GrothendieckContractibleFibers.projection_weak E (fun U ↦
      JTHomotopyTargetComma.fiber_point_GW_at (nativeCode P hx hy U) (timeDegree P hx hy U))
  letI : WeakEquivalence (pointMap (nerve (Index P hx hy))) :=
    (weakEquivalence_iff_GW _).mpr (index_point_GW P hx hy hW)
  rw [← pointIsTerminal.hom_ext (nerveMap p ≫ pointMap (nerve (Index P hx hy))) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTEndpointGraphCoefficientEvaluation
