import ChosenNecklaceUnitCodeMaps
import DaggerModelsPartII.JTMarkedJoinJointInsertion
import DaggerModelsPartII.JTParametrizedTargetFamilyComparison
import DaggerModelsPartII.JTOrderedLabelJointInsertion
import DaggerModelsPartII.JTParametrizedTargetPullback
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! Exact evaluation comparison for a collapse of the complete constant middle. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelJointInsertion

open JTParametrizedTargetFamilies (Family evaluate)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x z y : Vertex W}
variable {L R : A ⥤ NecklaceCode} {degree : A ⥤ SimplexCategory}
variable (S : Sides (W := W) (x := x) (z := z) (y := y) L R degree)
variable {M N : A ⥤ NecklaceCode} (ρ : M ⟶ N)

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {t : A ⥤ SimplexCategory}
variable (G : Family Q (labels S N) t)

set_option maxHeartbeats 450000 in
/-- At every base object the complete decorated collapse compares the evaluations
of all internal necklaces in the original fixed target. -/
def pointwiseMiddleComparison (a : A) :=
  JTParametrizedTargetPullback.compare ((middleMap S ρ).app a) (t.obj a) (𝟙 (degree.obj a))
    (by
      change 𝟙 (degree.obj a) ≫
        ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
          ((middleMap S ρ).app a)).2 = 𝟙 (degree.obj a)
      rw [middleMap_coefficient, Category.id_comp])
    (G.parameter a) Q (G.collapse.app a) (G.raw a)

section AppendedMiddle

open NecklaceCode

/-- Append one fixed bead to the full middle. All original native operators
act unchanged on the middle and by the identity on the extra bead. -/
def appendMiddleBead : NecklaceCode ⥤ NecklaceCode where
  obj T := wedge T (single 1)
  map f := wedgeMap f (𝟙 (single 1))
  map_id T := wedgeMap_id (T := T) (U := single 1)
  map_comp f g := by
    change wedgeMap (Hom.comp f g) (Hom.id.{0} (single 1)) =
      Hom.comp (wedgeMap f (Hom.id.{0} (single 1))) (wedgeMap g (Hom.id.{0} (single 1)))
    rw [← wedgeMap_comp]
    rfl

private abbrev withBeadMap {T U : NecklaceCode} (f : T ⟶ U) :
    wedge T (single 1) ⟶ wedge U (single 1) :=
  wedgeMap f (𝟙 (single 1))

/-- The whole original middle can be collapsed functorially while keeping the
added identity bead, even when the original middle was already a point. -/
def retainMiddleBead : appendMiddleBead ⟶ (Functor.const NecklaceCode).obj (single 1) where
  app T := withBeadMap (toPoint T) ≫ wedgeLeftUnitCode (single 1)
  naturality {T U} f := by
    let e : wedge point (single 1) ⟶ single 1 := wedgeLeftUnitCode (single 1)
    have h : f ≫ toPoint U = toPoint T := Hom.ext (pointIsTerminal.hom_ext _ _)
    change withBeadMap f ≫ (withBeadMap (toPoint U) ≫ e) =
      (withBeadMap (toPoint T) ≫ e) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    have hw : withBeadMap f ≫ withBeadMap (toPoint U) = withBeadMap (toPoint T) := by
      change Hom.comp (wedgeMap f (Hom.id.{0} (single 1)))
          (wedgeMap (toPoint U) (Hom.id.{0} (single 1))) =
        wedgeMap (toPoint T) (Hom.id.{0} (single 1))
      rw [← wedgeMap_comp]
      exact congrArg (fun g ↦ wedgeMap g (Hom.id.{0} (single 1))) h
    rw [hw]

end AppendedMiddle

section FamilyComparison

open JTParametrizedTargetFamilyComparison

set_option maxHeartbeats 400000 in
/-- The two inserted-middle diagrams have literally the same coefficient
operators, giving a section of the coefficient change. -/
def middleSection : degrees (labels S N) ⟶ degrees (labels S M) where
  app a := 𝟙 (degree.obj a)
  naturality {a b} f := by
    change degree.map f ≫ 𝟙 (degree.obj b) = 𝟙 (degree.obj a) ≫ degree.map f
    rw [Category.id_comp, Category.comp_id]

set_option maxHeartbeats 400000 in
theorem middleSection_comp :
    middleSection S (M := M) (N := N) ≫ coefficient (middleMap S ρ) = 𝟙 _ := by
  apply NatTrans.ext
  funext a
  change 𝟙 (degree.obj a) ≫
      ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
        ((middleMap S ρ).app a)).2 = 𝟙 (degree.obj a)
  rw [middleMap_coefficient, Category.id_comp]

set_option maxHeartbeats 500000 in
/-- Pull back an exact fixed-target graph family along the whole middle change. -/
def expandedFamily : Family Q (labels S M) t :=
  pullback (middleMap S ρ) G (middleSection S) (middleSection_comp S ρ)

set_option maxHeartbeats 700000 in
/-- The original two projections on every internal necklace compare over the
literal fixed target, including when the entire middle is collapsed. -/
def expandedEvaluationComparison :
    evaluate (expandedFamily S ρ G) ⟶
      presentation (middleMap S ρ) (𝟙 t) ⋙ evaluate G :=
  pullback_compare (middleMap S ρ) G (middleSection S) (middleSection_comp S ρ)

set_option maxHeartbeats 700000 in
/-- The same comparison can be evaluated in a specified target of the two native collapses. -/
def expandedEvaluationComparisonAfterPostcomp
    {Q' : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)} (g : Q ⟶ Q') :
    evaluate ((expandedFamily S ρ G).postcomp g) ⟶
      presentation (middleMap S ρ) (𝟙 t) ⋙ evaluate (G.postcomp g) := by
  let E := expandedFamily S ρ G
  let r := middleMap S ρ
  have h : Compatible r (𝟙 t) E G :=
    pullback_compatible r G (middleSection S) (middleSection_comp S ρ)
  refine compare r (𝟙 t) (E.postcomp g) (G.postcomp g)
    { collapse := ?_, parameter := h.parameter }
  change native r ≫ (G.collapse ≫ (Functor.const A).map g.hom) =
    E.collapse ≫ (Functor.const A).map g.hom
  rw [← Category.assoc, h.collapse]

/-- The comparison of the full internal-necklace presentations is nerve weak. -/
theorem expandedPresentation_weak :
    WeakEquivalence (nerveMap (presentation (middleMap S ρ) (𝟙 t))) :=
  presentation_weak (middleMap S ρ) (𝟙 t)

end FamilyComparison

end

end DaggerModels.PartII.JTOrderedLabelJointInsertion

namespace DaggerModels.PartII.JTMarkedJoinJointInsertion

open JTOrderedLabelJointInsertion (labels)
open JTMarkedParametrizedTargetFamilyJoin (Mark UpperBound LowerBound)
open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x z y : Vertex W}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x z}
variable {R : A ⥤ DecoratedNecklaceHomDiagram.Index W z y}
variable {t : A ⥤ SimplexCategory}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (i : Mark L) (j : Mark R) (F : Family P L t) (G : Family Q R t)
variable (hi : UpperBound F i) (hj : LowerBound G j)

/-- The actual marked join gives a fixed-target family on the identical
insertion diagram with the identity bead as its middle. -/
def markedIdentityMiddleFamily : Family (NecklacesOver.wedge P Q)
    (labels (sides L R i j) ((Functor.const A).obj (NecklaceCode.single 1))) t :=
  (labels_eq L R i j).symm ▸ JTMarkedParametrizedTargetFamilyJoin.join L R i j F G hi hj

variable (M : A ⥤ NecklaceCode)

private abbrev toIdentityMiddle :=
  Functor.whiskerLeft M JTOrderedLabelJointInsertion.retainMiddleBead

/-- Insert an arbitrary full middle in the marked join, retaining the original
identity bead so the collapse is natural even for a point middle. -/
def expandedMarkedFamily : Family (NecklacesOver.wedge P Q)
    (labels (sides L R i j) (M ⋙ JTOrderedLabelJointInsertion.appendMiddleBead)) t :=
  JTOrderedLabelJointInsertion.expandedFamily (sides L R i j) (toIdentityMiddle M)
    (markedIdentityMiddleFamily i j F G hi hj)

/-- Every internal necklace in the expanded marked join compares to the
original marked evaluation in the original raw target. -/
def expandedMarkedComparison :
    JTParametrizedTargetFamilies.evaluate (expandedMarkedFamily i j F G hi hj M) ⟶
      JTParametrizedTargetFamilyComparison.presentation
        (JTOrderedLabelJointInsertion.middleMap (sides L R i j) (toIdentityMiddle M)) (𝟙 t) ⋙
      JTParametrizedTargetFamilies.evaluate (markedIdentityMiddleFamily i j F G hi hj) :=
  JTOrderedLabelJointInsertion.expandedEvaluationComparison (sides L R i j)
    (toIdentityMiddle M) (markedIdentityMiddleFamily i j F G hi hj)

/-- Compare the expanded marked join in the actual target of the native wedge. -/
def expandedMarkedComparisonAfterPostcomp
    {T : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    (g : NecklacesOver.wedge P Q ⟶ T) :
    JTParametrizedTargetFamilies.evaluate ((expandedMarkedFamily i j F G hi hj M).postcomp g) ⟶
      JTParametrizedTargetFamilyComparison.presentation
        (JTOrderedLabelJointInsertion.middleMap (sides L R i j) (toIdentityMiddle M)) (𝟙 t) ⋙
      JTParametrizedTargetFamilies.evaluate ((markedIdentityMiddleFamily i j F G hi hj).postcomp g) :=
  JTOrderedLabelJointInsertion.expandedEvaluationComparisonAfterPostcomp (sides L R i j)
    (toIdentityMiddle M) (markedIdentityMiddleFamily i j F G hi hj) g

end

end DaggerModels.PartII.JTMarkedJoinJointInsertion
