import DaggerModelsPartII.JTSharedInsertionSeamNative
import DaggerModelsPartII.JTPrismChainGraphCover
import DaggerModelsPartII.JTGraphCoveredProductInterface

/-!
# All original-time graph lifts for the actual corrected old split

The source is the corrected old P + point + R label, with both outer correction
pairs retained. Pull the original Family parameter along its actual oldAssembly
and the identity on old time, then keep ALL lifts through the shared coefficient
projection. No Family on a chain-degree time product or natural section is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionOldGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev toSSet := NecklaceCode.simplicialFunctor.{0}

private def mapWithTime {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t : C ⥤ SimplexCategory) :=
  Functor.whiskerRight
    (NatTrans.prod' (Functor.whiskerRight n toSSet) (𝟙 (t ⋙ J)))
    (MonoidalCategory.tensor SSet.{0})

private theorem mapWithTime_app {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t : C ⥤ SimplexCategory) (p : C) :
    (mapWithTime n t).app p = (n.app p).map ⊗ₘ 𝟙 (J.obj (t.obj p)) := rfl

private theorem timeMap_parameter {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t k : C ⥤ SimplexCategory)
    (r : JTGraphCoveredProductInterface.product M t ⟶ k ⋙ J) (p : C) :
    ((mapWithTime n t) ≫ r).app p =
      ((n.app p).map ⊗ₘ 𝟙 (J.obj (t.obj p))) ≫ r.app p := by
  rw [NatTrans.comp_app, mapWithTime_app]

private theorem cutPoint_left {P R T : NecklaceCode} (v : Fin (T.len + 1))
    (l : NecklaceCode.Hom.{0} P (cutLeft T v)) (r : R ⟶ cutRight T v) :
    tripleRightT P (single 0) R ≫
        ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)) ≫
          JTNativeCutPointAssembly.assembly T v).map = l.map ≫ cutLeftι T v := by
  change wedgeιLeft P (wedge (single 0) R) ≫
    ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)).map ≫
      (JTNativeCutPointAssembly.assembly T v).map) = _
  rw [← Category.assoc, wedgeMap_left, Category.assoc]
  exact congrArg (fun f ↦ l.map ≫ f) (JTNativeCutPointAssembly.assembly_left T v)

private theorem cutPoint_right {P R T : NecklaceCode} (v : Fin (T.len + 1))
    (l : NecklaceCode.Hom.{0} P (cutLeft T v)) (r : R ⟶ cutRight T v) :
    tripleRightV P (single 0) R ≫
        ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)) ≫
          JTNativeCutPointAssembly.assembly T v).map = r.map ≫ cutRightι T v := by
  change (wedgeιRight (single 0) R ≫ wedgeιRight P (wedge (single 0) R)) ≫
    ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)).map ≫
      (JTNativeCutPointAssembly.assembly T v).map) = _
  rw [Category.assoc, ← Category.assoc (wedgeιRight P _), wedgeMap_right,
    ← Category.assoc, ← Category.assoc, wedgeMap_right, Category.assoc, Category.assoc]
  exact congrArg (fun f ↦ r.map ≫ f) (JTNativeCutPointAssembly.assembly_right T v)

private theorem cutPoint_middle {P R T : NecklaceCode} (v : Fin (T.len + 1))
    (l : NecklaceCode.Hom.{0} P (cutLeft T v)) (r : R ⟶ cutRight T v) :
    tripleRightU P (single 0) R ≫
        ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)) ≫
          JTNativeCutPointAssembly.assembly T v).map =
      SSet.stdSimplex.isTerminalObj₀.from (single 0).toSSet ≫ pointAt T (ULift.up v) := by
  change (wedgeιLeft (single 0) R ≫ wedgeιRight P (wedge (single 0) R)) ≫
    ((wedgeMap l (wedgeMap (𝟙 (single 0)) r)).map ≫
      (JTNativeCutPointAssembly.assembly T v).map) = _
  rw [Category.assoc, ← Category.assoc (wedgeιRight P _), wedgeMap_right,
    ← Category.assoc, ← Category.assoc, wedgeMap_left]
  change ((𝟙 (single 0).toSSet) ≫ wedgeιLeft (single 0) (cutRight T v)) ≫
    (wedgeιRight (cutLeft T v) (wedge (single 0) (cutRight T v)) ≫
      (JTNativeCutPointAssembly.assembly T v).map) = _
  rw [Category.id_comp]
  exact JTNativeCutPointAssembly.assembly_middle T v

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The actual original shared chain, before adding any seam triangle filler. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The corrected old split family, with its two original outer correction pairs. -/
abbrev oldFamily := JTSharedInsertionNormalizedSeam.oldFamily F j

/-- The unchanged original source object and every original arrow. -/
abbrev originalBase := JTSharedInsertionChainSupport.originalBase F j

/-- Keep the complete original time, independently of the shared coefficient clock. -/
abbrev oldTime : Index F j ⥤ SimplexCategory := originalBase F j ⋙ time

/-- The coefficient degree of the original Family at that same original object. -/
abbrev oldDegrees := originalBase F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- The actual shared full-chain projection, retaining every original coefficient vertex. -/
abbrev coefficientProjection := JTSharedInsertionChoices.toOriginal F j

/-- The whole corrected old split, multiplied by the entire original time parameter. -/
abbrev X : Index F j ⥤ SSet.{0} :=
  JTGraphCoveredProductInterface.product (codes (oldFamily F j).labels) (oldTime F j)

private abbrev oldProduct : Index F j ⥤ SSet.{0} :=
  JTGraphCoveredProductInterface.product (originalBase F j ⋙ codes L) (oldTime F j)

private def originalParameter : oldProduct F j ⟶ oldDegrees F j ⋙ J where
  app p := F.parameter ((originalBase F j).obj p)
  naturality _ _ f := F.parameter_map ((originalBase F j).map f)

/-- The complete corrected old native assembly acts identically on original time. -/
def nativeTimeMap : X F j ⟶ oldProduct F j :=
  mapWithTime (JTSharedInsertionSeamNative.oldAssembly F j) (oldTime F j)

/-- The original parameter restricted along the WHOLE actual corrected old assembly. -/
def coarseParameter : X F j ⟶ oldDegrees F j ⋙ J :=
  nativeTimeMap F j ≫ originalParameter F j

/-- This is the literal original-time parameter, before any coefficient lift is chosen. -/
theorem coarseParameter_app (p : Index F j) :
    (coarseParameter F j).app p =
      (((JTSharedInsertionSeamNative.oldAssembly F j).app p).map ⊗ₘ
        𝟙 (J.obj ((oldTime F j).obj p))) ≫ F.parameter ((originalBase F j).obj p) :=
  timeMap_parameter (JTSharedInsertionSeamNative.oldAssembly F j)
    (oldTime F j) (oldDegrees F j) (originalParameter F j) p

/-- Every admissible full coefficient lift is retained, with all actual operators. -/
abbrev graph := JTPrismChainGraphCover.cover
  (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- Forget only the coefficient lift, retaining the whole corrected native-time product. -/
abbrev projection : graph F j ⟶ X F j := JTPrismChainGraphCover.projection
  (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The complete lifted coefficient parameter on that all-lifts graph. -/
abbrev parameter : graph F j ⟶ JTSharedInsertionChoices.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- Every lifted graph parameter projects to the exact old parameter. -/
theorem parameter_projection :
    parameter F j ≫ Functor.whiskerRight (coefficientProjection F j) J =
      projection F j ≫ coarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection
    (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The whole corrected product has a componentwise trivial-fibration graph cover. -/
theorem projection_trivialFibration (p : Index F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (X F j) (coarseParameter F j) (coefficientProjection F j)
    (JTSharedInsertionChoices.toOriginal_surjective F j) p

/-- The native coordinate is the whole corrected old P + point + R source. -/
abbrev native (p : Index F j) := (projection F j).app p ≫ fst _ _

/-- Its second coordinate is exactly the original independent time parameter. -/
abbrev clock (p : Index F j) := (projection F j).app p ≫ snd _ _

/-- The two coordinates retain the entire original-time graph projection. -/
theorem native_clock (p : Index F j) :
    lift (native F j p) (clock F j p) = (projection F j).app p :=
  lift_comp_fst_snd ((projection F j).app p)

/-- The actual graph equation for the whole corrected native source and old time. -/
theorem parameter_projection_app (p : Index F j) :
    (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
      (projection F j).app p ≫
        ((((JTSharedInsertionSeamNative.oldAssembly F j).app p).map ⊗ₘ
            𝟙 (J.obj ((oldTime F j).obj p))) ≫ F.parameter ((originalBase F j).obj p)) := by
  have h := congrArg (fun η : graph F j ⟶ oldDegrees F j ⋙ J ↦ η.app p)
    (parameter_projection F j)
  change (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
    (projection F j).app p ≫ (coarseParameter F j).app p at h
  rw [coarseParameter_app] at h
  exact h

/-- The actual corrected old family targets the SAME fixed original Q. -/
def target : codes (oldFamily F j).labels ⟶ (Functor.const (Index F j)).obj Q.code :=
  JTSharedInsertionSeamNative.oldAssembly F j ≫
    Functor.whiskerLeft (originalBase F j) F.collapse

private abbrev P (p : Index F j) := (JTSharedInsertionSeamSurroundings.leftNative F j).obj p
private abbrev R (p : Index F j) := (JTSharedInsertionSeamSurroundings.rightNative F j).obj p
private abbrev T (p : Index F j) := (codes L).obj ((originalBase F j).obj p)
private abbrev v (p : Index F j) := ((JTSharedInsertionChainSupport.marks F j 1).obj p).2.val

/-- The full corrected left piece retains its exact original native assembly. -/
theorem oldAssembly_left (p : Index F j) :
    tripleRightT (P F j p) (single 0) (R F j p) ≫
      ((JTSharedInsertionSeamNative.oldAssembly F j).app p).map =
        JTSharedInsertionNativeAssembly.leftToOriginal F j p := by
  exact (cutPoint_left (v F j p) ((JTSharedInsertionNativeAssembly.leftToCut F j).app p)
    ((JTSharedInsertionNativeAssembly.rightToCut F j).app p)).trans
      (JTSharedInsertionNativeAssembly.leftToCut_fac F j p)

/-- The full corrected right piece retains both original outside corrections. -/
theorem oldAssembly_right (p : Index F j) :
    tripleRightV (P F j p) (single 0) (R F j p) ≫
      ((JTSharedInsertionSeamNative.oldAssembly F j).app p).map =
        JTSharedInsertionNativeAssembly.rightToOriginal F j p := by
  exact (cutPoint_right (v F j p) ((JTSharedInsertionNativeAssembly.leftToCut F j).app p)
    ((JTSharedInsertionNativeAssembly.rightToCut F j).app p)).trans
      (JTSharedInsertionNativeAssembly.rightToCut_fac F j p)

/-- The old middle point is the ACTUAL varying source vertex b, before collapse to Q. -/
theorem oldAssembly_middle (p : Index F j) :
    tripleRightU (P F j p) (single 0) (R F j p) ≫
      ((JTSharedInsertionSeamNative.oldAssembly F j).app p).map =
        SSet.stdSimplex.isTerminalObj₀.from (single 0).toSSet ≫
          pointAt (T F j p) (ULift.up (v F j p)) :=
  cutPoint_middle (v F j p) ((JTSharedInsertionNativeAssembly.leftToCut F j).app p)
    ((JTSharedInsertionNativeAssembly.rightToCut F j).app p)

end
end DaggerModels.PartII.JTSharedInsertionOldGraph
