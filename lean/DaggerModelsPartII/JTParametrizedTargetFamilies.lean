import DaggerModelsPartII.JTParametrizedTargetLiftTransport
import DaggerModelsPartII.JTBoundaryNecklacePresentationCone
import DaggerModelsPartII.JTTargetCommaExactEvaluation
import DaggerModelsPartII.JTHomotopyTargetComma

/-! Diagrams of original comparisons with varying native codes, time and coefficients. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTParametrizedTargetFamilies

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceEndpointCylinder
open JTGraphFactoredPresentation (TargetComma)
open DecoratedCylinderNecklacePresentation (underCocone underDiagram)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open JTParametrizedTargetLiftTransport (graph lift_square)
open BoundaryNecklaceComma (fiberDiagram necklaceUnder)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A]
variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev proj := OrderedLabelElements.projection W (boundaryPoint W x y)

/-- The projection retaining the varying native code of each decorated label. -/
abbrev codes (L : A ⥤ I W x y) :=
  L ⋙ proj ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory

private abbrev d (i : I W x y) := (proj.obj i).2
private abbrev c (i : I W x y) := (proj.obj i).1
private abbrev label (i : I W x y) := OrderedLabelElements.label W (boundaryPoint W x y) i

/-- A diagram of full groupoid parameters and native collapses over the
original fixed target. Its code, time and ordered label may all vary. -/
structure Family (L : A ⥤ I W x y) (time : A ⥤ SimplexCategory) where
  collapse : codes L ⟶ (Functor.const A).obj Q.code
  parameter : ∀ a, (c (L.obj a)).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (d (L.obj a))
  parameter_map : ∀ {a b : A} (f : a ⟶ b),
    (((proj.map (L.map f)).1).map ⊗ₘ J.map (time.map f)) ≫ parameter b =
      parameter a ≫ J.map (proj.map (L.map f)).2
  raw : ∀ a, (graph (parameter a)).right ≫ ((underCocone W x y).app (L.obj a)).right =
    augmentation (c (L.obj a)) (time.obj a) ≫ (collapse.app a).map ≫ Q.map

variable {Q} {L : A ⥤ I W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)


/-- Reindex the chosen family along every arrow of a different index. -/
def Family.precomp {B : Type} [SmallCategory B] (G : B ⥤ A) : Family Q (G ⋙ L) (G ⋙ time) where
  collapse := Functor.whiskerLeft G F.collapse
  parameter b := F.parameter (G.obj b)
  parameter_map f := F.parameter_map (G.map f)
  raw b := F.raw (G.obj b)

/-- Postcompose the unchanged diagram of native collapses into a new target. -/
def Family.postcomp {Q' : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    (g : Q ⟶ Q') : Family Q' L time where
  collapse := F.collapse ≫ (Functor.const A).map g.hom
  parameter := F.parameter
  parameter_map f := F.parameter_map f
  raw a := by
    change _ = augmentation _ (time.obj a) ≫ ((F.collapse.app a).map ≫ g.hom.map) ≫ Q'.map
    rw [Category.assoc (F.collapse.app a).map, g.w]
    exact F.raw a

/-- The original cylinder functor now varies in both code and time. -/
abbrev cylinders := ((codes L).prod' time) ⋙ NecklaceCylinderJointDiagram.cylinderUnder

set_option maxHeartbeats 400000 in
/-- The raw equality before imposing the two endpoint identifications. -/
theorem rawProduct (a : A) :
    JTBinaryPrismRealization.realizeProduct W (d (L.obj a)) (F.parameter a)
      (orderedLabel W x y (c (L.obj a)) (d (L.obj a)) (label (L.obj a))) =
    fst (c (L.obj a)).toSSet (J.obj (time.obj a)) ≫ (F.collapse.app a).map ≫ Q.map := by
  let T := c (L.obj a)
  let n := time.obj a
  let k := d (L.obj a)
  let z := label (L.obj a)
  let p := F.parameter a
  have h := F.raw a
  change JTInterpolatedReducedCylinder.cylinderMap T p ≫ descend W x y T k z =
    augmentation T n ≫ (F.collapse.app a).map ≫ Q.map at h
  have hh := congrArg (fun g ↦ (cylinder T).app n ≫ g) h
  dsimp only at hh
  rw [← Category.assoc ((cylinder T).app n) _ (descend W x y T k z),
    JTInterpolatedReducedCylinder.cylinderMap_cylinder, Category.assoc,
    descend_cylinder, ← Category.assoc ((cylinder T).app n),
    augmentation_cylinder] at hh
  exact hh

private theorem collapse_natural {a b : A} (f : a ⟶ b) :
    (proj.map (L.map f)).1 ≫ F.collapse.app b = F.collapse.app a := by
  have h := F.collapse.naturality f
  change (proj.map (L.map f)).1 ≫ F.collapse.app b = F.collapse.app a ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private abbrev D := JTTargetCommaPullback.diagram W x y Q

/-- The two legs of the actual pullback form one natural transformation
over the entire comparison diagram. -/
def liftNatural : cylinders (L := L) (time := time) ⟶ L ⋙ D (Q := Q) where
  app a := JTCylinderOverTarget.lift W x y Q (L.obj a) (c (L.obj a)) (time.obj a)
    (graph (F.parameter a)) (F.collapse.app a) (F.raw a)
  naturality {a b} f :=
    (lift_square Q (L.map f) (time.map f) (F.parameter a) (F.parameter b)
      (F.collapse.app a) (F.collapse.app b)
      (collapse_natural F f) (F.parameter_map f) (F.raw a) (F.raw b)).symm

/-- The whole original internal-necklace presentation of the family. -/
abbrev Presentation :=
  BoundaryNecklaceComma.Presentation (cylinders (L := L) (time := time))

/-- Evaluate the parametrized diagram into the original fixed-target comma. -/
def evaluate : Presentation (L := L) (time := time) ⥤ TargetComma Q :=
  JTBoundaryNecklacePresentationCone.mapPresentation (D (Q := Q))
    (cylinders (L := L) (time := time)) L (liftNatural F) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W x y Q

/-- The exact domain containing all internal necklaces has the weak
homotopy type of its parameter index. -/
theorem projection_weak : WeakEquivalence (nerveMap
    (Grothendieck.forget (fiberDiagram (cylinders (L := L) (time := time))))) :=
  GrothendieckContractibleFibers.projection_weak _
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at (c (L.obj a)) (time.obj a))

/-- Weak contractibility of the index passes to the whole original internal
necklace presentation, retaining the evaluation in the original comma. -/
theorem presentation_point_GW (hA : GW (pointMap (nerve A))) :
    GW (pointMap (nerve (Presentation (L := L) (time := time)))) := by
  let P := Grothendieck.forget (fiberDiagram (cylinders (L := L) (time := time)))
  letI : WeakEquivalence (nerveMap P) := projection_weak
  letI : WeakEquivalence (pointMap (nerve A)) := (weakEquivalence_iff_GW _).mpr hA
  have h : nerveMap P ≫ pointMap (nerve A) =
      pointMap (nerve (Presentation (L := L) (time := time))) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTParametrizedTargetFamilies
