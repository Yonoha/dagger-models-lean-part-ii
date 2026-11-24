import DaggerModelsPartII.JTExactGraphRelativeExtension
import DaggerModelsPartII.JTRigidOverlapDiagram
import DaggerModelsPartII.JTJointRelativeGraphFamily

/-!
# Relative covers of the two source intervals at an actual joint

The precise graph equations are kept in the original entire source
necklace's reduced cylinder, so they also preserve its fixed raw image.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels MonoidalCategory
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidJointGraphCover

open JTJointRelativeParameters (withTime withTimeMap overlapToLeft_vertices_injective
  overlapToRight_vertices_injective overlapToLeft_vertices_reflects
  overlapToRight_vertices_reflects)
open JTJointRelativeGraphFamily (native coefficient leftLeg rightLeg)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (left right overlap overlapToLeft overlapToRight)
open JTTargetJointMarks (Joint)
open JTNecklaceEndpointCylinder (cylinder)
open JTRigidOverlapDiagram (Data CommonCover stableAllowed stableAllowed_mapsTo
  allowed_left_at_rigid allowed_right_at_rigid)
open JTExactGraphRelativeExtension (sideCover sideProjection sideParameter
  sideProjection_trivialFibration sideCover_preserves_graph liftSharedTrace
  liftSharedTrace_projection liftSharedTrace_parameter)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj zero
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)

/-- The actual two relative intervals use their entire source necklace as
the target of each exact reduced-cylinder comparison. -/
def overlapData : Data I where
  overlap := withTime Q.map J time (native F) (overlap Q.code j)
  left := withTime Q.map J time (native F) (left Q.code j)
  right := withTime Q.map J time (native F) (right Q.code j)
  degree := coefficient (L := L)
  leftInclusion := withTimeMap Q.map J time (native F) (overlapToLeft Q.code j)
  rightInclusion := withTimeMap Q.map J time (native F) (overlapToRight Q.code j)
  leftReference := s
  rightReference := t
  leftCode p := (codes L).obj p
  rightCode p := (codes L).obj p
  leftNative p := (leftLeg F j).app p ≫ fst ((codes L).obj p).toSSet (J.obj (time.obj p))
  rightNative p := (rightLeg F j).app p ≫ fst ((codes L).obj p).toSSet (J.obj (time.obj p))

/-- A covered side carries the common trace and preserves its exact reference graph. -/
structure CoveredSide {D : Data I} (C : CommonCover D) (X : I ⥤ SSet.{0})
    (a : D.overlap ⟶ X) (reference : X ⟶ D.degree ⋙ J)
    (code : I → NecklaceCode) (f : ∀ p, X.obj p ⟶ (code p).toSSet) where
  source : I ⥤ SSet.{0}
  projection : source ⟶ X
  parameter : source ⟶ D.degree ⋙ J
  fromOverlap : C.source ⟶ source
  projectsOverlap : fromOverlap ≫ projection = C.projection ≫ a
  restrictsParameter : fromOverlap ≫ parameter = C.trace
  trivialFibration : ∀ p, trivialFibrations SSet.{0} (projection.app p)
  exactGraph : ∀ p, lift (projection.app p ≫ f p) (parameter.app p) ≫
      (cylinder (code p)).app (D.degree.obj p) =
    projection.app p ≫ lift (f p) (reference.app p) ≫ (cylinder (code p)).app (D.degree.obj p)

private def coveredSide {D : Data I} (C : CommonCover D) {X : I ⥤ SSet.{0}}
    (a : D.overlap ⟶ X) (reference : X ⟶ D.degree ⋙ J)
    (code : I → NecklaceCode) (f : ∀ p, X.obj p ⟶ (code p).toSSet)
    (injective : ∀ p, Function.Injective ((a.app p).app zero))
    (reflects : ∀ {p q : I} (g : p ⟶ q) (v : (X.obj p).obj zero),
      (X.map g).app zero v ∈ Set.range ((a.app q).app zero) →
        v ∈ Set.range ((a.app p).app zero))
    (rigid : ∀ p u c, c ∈ stableAllowed D p u →
      JTGraphParameterSourceRestriction.RigidVertex (code p) (f p) ((a.app p).app zero u) →
        c = JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
          ((reference.app p).app zero ((a.app p).app zero u)) 0) :
    CoveredSide C X a reference code f where
  source := sideCover a reference _ injective (@reflects) (stableAllowed_mapsTo D)
  projection := sideProjection a reference _ injective (@reflects) (stableAllowed_mapsTo D)
  parameter := sideParameter a reference _ injective (@reflects) (stableAllowed_mapsTo D)
  fromOverlap := liftSharedTrace a reference _ injective (@reflects) (stableAllowed_mapsTo D)
    C.projection C.trace C.forced
  projectsOverlap := liftSharedTrace_projection _ _ _ _ _ _ _ _ _
  restrictsParameter := liftSharedTrace_parameter _ _ _ _ _ _ _ _ _
  trivialFibration := sideProjection_trivialFibration _ _ _ _ _ _
    ((JTRigidOverlapDiagram.nonempty_iff_commonCover D).mpr ⟨C⟩)
  exactGraph p := sideCover_preserves_graph _ _ _ _ _ _ _ _ _ (rigid p)

variable (C : CommonCover (overlapData F j s t))

/-- Extend the common weak cover over the actual left interval, with its full native graph. -/
def coveredLeft :
    CoveredSide C (overlapData F j s t).left (overlapData F j s t).leftInclusion s
      (overlapData F j s t).leftCode (overlapData F j s t).leftNative :=
  coveredSide C _ s _ _
    (overlapToLeft_vertices_injective Q.map J time (native F) j)
    (fun {_ _} g v h ↦ overlapToLeft_vertices_reflects Q.map J time (native F) j g v h)
    (fun p u c hc hr ↦ allowed_left_at_rigid (overlapData F j s t) p u c hc hr)

/-- Extend the same common weak cover over the actual right interval. -/
def coveredRight :
    CoveredSide C (overlapData F j s t).right (overlapData F j s t).rightInclusion t
      (overlapData F j s t).rightCode (overlapData F j s t).rightNative :=
  coveredSide C _ t _ _
    (overlapToRight_vertices_injective Q.map J time (native F) j)
    (fun {_ _} g v h ↦ overlapToRight_vertices_reflects Q.map J time (native F) j g v h)
    (fun p u c hc hr ↦ allowed_right_at_rigid (overlapData F j s t) p u c hc hr)

/-- The two actual side graphs use precisely the same parameter on the full common cover. -/
theorem coveredSides_parameter_agree :
    (coveredLeft F j s t C).fromOverlap ≫ (coveredLeft F j s t C).parameter =
      (coveredRight F j s t C).fromOverlap ≫ (coveredRight F j s t C).parameter :=
  (coveredLeft F j s t C).restrictsParameter.trans
    (coveredRight F j s t C).restrictsParameter.symm

end

end DaggerModels.PartII.JTRigidJointGraphCover
