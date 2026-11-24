import DaggerModelsPartII.JTActualJointChainSeamSurroundings
import DaggerModelsPartII.JTNativeCutPointAssembly
import DaggerModelsPartII.JTChosenSeamOldComparison
import DaggerModelsPartII.JTWhiskeredSeamTarget

/-!
The actual full seam triangle maps to the original native code and fixed target.
The old two cuts are reassembled by the existing cut-wedge map. Coefficient
projections are composed strictly; no whole-time parameter lift is chosen.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSeamNative

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private theorem map_middle {P M R P' M' R' : NecklaceCode}
    (g : P ⟶ P') (h : M ⟶ M') (k : R ⟶ R') :
    tripleRightU P M R ≫ (wedgeMap g (wedgeMap h k)).map =
      h.map ≫ tripleRightU P' M' R' := by
  rw [tripleRightU, tripleRightU, Category.assoc, wedgeMap_right,
    ← Category.assoc, wedgeMap_left, Category.assoc]

private theorem map_right {P M R P' M' R' : NecklaceCode}
    (g : P ⟶ P') (h : M ⟶ M') (k : R ⟶ R') :
    tripleRightV P M R ≫ (wedgeMap g (wedgeMap h k)).map =
      k.map ≫ tripleRightV P' M' R' := by
  rw [tripleRightV, tripleRightV, Category.assoc, wedgeMap_right,
    ← Category.assoc, wedgeMap_right, Category.assoc]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev K := JTActualJointChoiceChainGraph.ordinals F j
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev U := JTActualJointChainSeamData.supportSSet F j
private abbrev incl := JTActualJointChainSeamData.supportIncl F j
private abbrev f := JTActualJointChainSeamData.endpointRows F j
private abbrev e := JTActualJointChoiceChainGraph.chainEnding F j
private abbrev s := JTActualJointChoiceChainGraph.chainStarting F j
private abbrev he := JTActualJointChainSeamData.ending_boundary F j
private abbrev hs := JTActualJointChainSeamData.starting_boundary F j
private abbrev hfU := JTActualJointChainSeamData.supported_endpoint F j
private abbrev heU := JTActualJointChainSeamData.ending_supported F j
private abbrev hsU := JTActualJointChainSeamData.starting_supported F j
private abbrev O := JTActualJointChainSeamSurroundings.surroundings F j
private abbrev base := JTActualJointChainSeamChoices.toOriginal F j

/-- The unchanged source object and arrow under the actual old choice chain. -/
abbrev chainOriginal : I F j ⥤ A :=
  JTActualJointChainSeamData.marked F j ⋙ JTExactlyMarkedSourceDiagram.base F j

/-- The unchanged original source under the full triangle-choice refinement. -/
abbrev original : JTActualJointChainSeamChoices.Index F j ⥤ A :=
  base F j ⋙ chainOriginal F j

/-- The literal old split coefficient family at the actual varying cut row. -/
abbrev oldFamily := JTChosenSeamOldComparison.oldFamily W (K F j) (f F j) (O F j)

/-- The complete actual seam family, with its literal old surrounding coefficients. -/
abbrev seamFamily :=
  JTChosenSeamChainDiagram.seamFamily W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) (O F j)

private abbrev marked (p : I F j) := (JTActualJointChainSeamData.marked F j).obj p
private abbrev T (p : I F j) := (codes L).obj ((chainOriginal F j).obj p)
private abbrev v (p : I F j) := (marked F j p).2.val

/-- Reassemble both literal old cuts and the middle point, naturally in every old arrow. -/
def oldAssembly : codes (oldFamily F j).labels ⟶ chainOriginal F j ⋙ codes L where
  app p := JTNativeCutPointAssembly.assembly (T F j p) (v F j p)
  naturality {p q} g := by
    have h := congrArg Prod.fst
      (JTWhiskeredSeamDiagram.Family.arrow_projection (oldFamily F j) g)
    change (codes (oldFamily F j).labels).map g =
      wedgeMap ((JTActualJointChainSeamSurroundings.leftNative F j).map g)
        (wedgeMap (𝟙 (single 0))
          ((JTActualJointChainSeamSurroundings.rightNative F j).map g)) at h
    change (codes (oldFamily F j).labels).map g ≫
        JTNativeCutPointAssembly.assembly (T F j q) (v F j q) =
      JTNativeCutPointAssembly.assembly (T F j p) (v F j p) ≫
        (codes L).map ((chainOriginal F j).map g)
    rw [h]
    exact JTNativeCutPointAssembly.assembly_natural
      ((codes L).map ((chainOriginal F j).map g)) (v F j p) (v F j q)
      (JTExactlyMarkedSourceDiagram.cut_map F j
        ((JTActualJointChainSeamData.marked F j).map g))

/-- The complete chosen collapsed phase has the original native code. -/
def collapsedNative :
    codes (JTWhiskeredSeamDiagram.collapsedFamily (seamFamily F j)).labels ⟶
      original F j ⋙ codes L :=
  JTWhiskeredSeamTarget.nativeOf
    (JTChosenSeamOldComparison.comparison W (z j) (U F j) (K F j) (incl F j)
      (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
      (O F j)) ≫ Functor.whiskerLeft (base F j) (oldAssembly F j)

/-- The entire triangle native coordinate returns to the literal original source. -/
def wholeNative : codes (seamFamily F j).triangle.labels ⟶ original F j ⋙ codes L :=
  JTWhiskeredSeamTarget.triangleToCollapsed (seamFamily F j) ≫ collapsedNative F j

/-- The whole actual seam triangle collapses to the SAME original fixed target Q. -/
def triangleTarget : codes (seamFamily F j).triangle.labels ⟶
    (Functor.const (JTActualJointChainSeamChoices.Index F j)).obj Q.code :=
  wholeNative F j ≫ Functor.whiskerLeft (original F j) F.collapse

/-- The exact original old coefficient degrees, without choosing lifts to new degrees. -/
abbrev oldDegrees : JTActualJointChainSeamChoices.Index F j ⥤ SimplexCategory :=
  original F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- Both actual coefficient projections are retained in one strict natural composite. -/
def coefficientProjection : JTActualJointChainSeamChoices.ordinals F j ⟶
    oldDegrees F j :=
  JTActualJointChainSeamChoices.toOld F j ≫ Functor.whiskerLeft (base F j)
    (JTActualJointChoiceChainGraph.toOriginal F j)

/-- Every original coefficient value occurs under the complete composite projection. -/
theorem coefficientProjection_surjective (p : JTActualJointChainSeamChoices.Index F j) :
    Function.Surjective ((coefficientProjection F j).app p).toOrderHom := by
  have hnew : Function.Surjective ((JTActualJointChainSeamChoices.toOld F j).app p).toOrderHom :=
    TimePrismChainDiagram.coeffProjection_surjective _ _ p
  exact (JTActualJointChoiceChainGraph.toOriginal_surjective F j ((base F j).obj p)).comp hnew

private abbrev a (p : JTActualJointChainSeamChoices.Index F j) := (base F j).obj p

private theorem collapsedNative_app (p : JTActualJointChainSeamChoices.Index F j) :
    (collapsedNative F j).app p =
      JTNativeCutPointAssembly.assembly (T F j (a F j p)) (v F j (a F j p)) := by
  have h := congrArg Prod.fst
    (JTChosenSeamOldComparison.component_projection W (z j) (U F j) (K F j) (incl F j)
      (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
      (O F j) p)
  change ((JTWhiskeredSeamTarget.nativeOf
    (JTChosenSeamOldComparison.comparison W (z j) (U F j) (K F j) (incl F j)
      (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
      (O F j))).app p) = 𝟙 _ at h
  change (JTWhiskeredSeamTarget.nativeOf
    (JTChosenSeamOldComparison.comparison W (z j) (U F j) (K F j) (incl F j)
      (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
      (O F j))).app p ≫ (oldAssembly F j).app (a F j p) = _
  rw [h, Category.id_comp]
  rfl

/-- Exact native triangle collapse followed by literal old cut reassembly. -/
theorem wholeNative_app (p : JTActualJointChainSeamChoices.Index F j) :
    (wholeNative F j).app p =
      wedgeMap (𝟙 (cutLeft (T F j (a F j p)) (v F j (a F j p))))
        (wedgeMap JTWhiskeredSeamTarget.collapseTriangle
          (𝟙 (cutRight (T F j (a F j p)) (v F j (a F j p))))) ≫
      JTNativeCutPointAssembly.assembly (T F j (a F j p)) (v F j (a F j p)) := by
  change (JTWhiskeredSeamTarget.triangleToCollapsed (seamFamily F j)).app p ≫
    (collapsedNative F j).app p = _
  rw [collapsedNative_app]
  rfl

/-- The full left inverse-image piece returns to the literal old left cut. -/
theorem wholeNative_left (p : JTActualJointChainSeamChoices.Index F j) :
    tripleRightT (cutLeft (T F j (a F j p)) (v F j (a F j p))) (single 2)
        (cutRight (T F j (a F j p)) (v F j (a F j p))) ≫
      ((wholeNative F j).app p).map =
        cutLeftι (T F j (a F j p)) (v F j (a F j p)) := by
  let C := T F j (a F j p)
  let v₀ := v F j (a F j p)
  let P := cutLeft C v₀
  let R := cutRight C v₀
  rw [wholeNative_app]
  change wedgeιLeft P (wedge (single 2) R) ≫
    ((wedgeMap (Hom.id.{0} P)
      (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (Hom.id.{0} R))).map ≫
        (JTNativeCutPointAssembly.assembly C v₀).map) = cutLeftι C v₀
  rw [← Category.assoc, wedgeMap_left]
  change (𝟙 P.toSSet ≫ wedgeιLeft P (wedge (single 0) R)) ≫
    (JTNativeCutPointAssembly.assembly C v₀).map = cutLeftι C v₀
  rw [Category.id_comp]
  exact JTNativeCutPointAssembly.assembly_left C v₀

/-- The full right inverse-image piece returns to the literal old right cut. -/
theorem wholeNative_right (p : JTActualJointChainSeamChoices.Index F j) :
    tripleRightV (cutLeft (T F j (a F j p)) (v F j (a F j p))) (single 2)
        (cutRight (T F j (a F j p)) (v F j (a F j p))) ≫
      ((wholeNative F j).app p).map =
        cutRightι (T F j (a F j p)) (v F j (a F j p)) := by
  let C := T F j (a F j p)
  let v₀ := v F j (a F j p)
  let P := cutLeft C v₀
  let R := cutRight C v₀
  rw [wholeNative_app]
  change tripleRightV P (single 2) R ≫
    ((wedgeMap (Hom.id.{0} P)
      (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (Hom.id.{0} R))).map ≫
        (JTNativeCutPointAssembly.assembly C v₀).map) = cutRightι C v₀
  rw [← Category.assoc, map_right]
  change (𝟙 R.toSSet ≫ tripleRightV P (single 0) R) ≫
    (JTNativeCutPointAssembly.assembly C v₀).map = cutRightι C v₀
  rw [Category.id_comp]
  exact JTNativeCutPointAssembly.assembly_right C v₀

/-- The entire middle triangle returns to the actual old selected source point. -/
theorem wholeNative_middle (p : JTActualJointChainSeamChoices.Index F j) :
    tripleRightU (cutLeft (T F j (a F j p)) (v F j (a F j p))) (single 2)
        (cutRight (T F j (a F j p)) (v F j (a F j p))) ≫
      ((wholeNative F j).app p).map =
        SSet.stdSimplex.isTerminalObj₀.from (single 2).toSSet ≫
          pointAt (T F j (a F j p)) (ULift.up (v F j (a F j p))) := by
  let C := T F j (a F j p)
  let v₀ := v F j (a F j p)
  let P := cutLeft C v₀
  let R := cutRight C v₀
  rw [wholeNative_app]
  change tripleRightU P (single 2) R ≫
    ((wedgeMap (Hom.id.{0} P)
      (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (Hom.id.{0} R))).map ≫
        (JTNativeCutPointAssembly.assembly C v₀).map) = _
  rw [← Category.assoc, map_middle, Category.assoc,
    JTNativeCutPointAssembly.assembly_middle, ← Category.assoc]
  congr 1

/-- The actual triangle left coefficient retains the full composite old degree. -/
theorem triangle_left (p : JTActualJointChainSeamChoices.Index F j) :
    ((seamFamily F j).triangle.data p).left =
      SSet.stdSimplex.map ((coefficientProjection F j).app p) ≫
        JTActualJointCutPrism.leftCoefficient (L := L)
          ((original F j).obj p) (v F j (a F j p)) := by
  change SSet.stdSimplex.map ((JTActualJointChainSeamChoices.toOld F j).app p) ≫
    (SSet.stdSimplex.map ((JTActualJointChoiceChainGraph.toOriginal F j).app (a F j p)) ≫
      JTActualJointCutPrism.leftCoefficient (L := L)
        ((original F j).obj p) (v F j (a F j p))) = _
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp]
  rfl

/-- The actual right coefficient retains the same full composite old degree. -/
theorem triangle_right (p : JTActualJointChainSeamChoices.Index F j) :
    ((seamFamily F j).triangle.data p).right =
      SSet.stdSimplex.map ((coefficientProjection F j).app p) ≫
        JTActualJointCutPrism.rightCoefficient (L := L)
          ((original F j).obj p) (v F j (a F j p)) := by
  change SSet.stdSimplex.map ((JTActualJointChainSeamChoices.toOld F j).app p) ≫
    (SSet.stdSimplex.map ((JTActualJointChoiceChainGraph.toOriginal F j).app (a F j p)) ≫
      JTActualJointCutPrism.rightCoefficient (L := L)
        ((original F j).obj p) (v F j (a F j p))) = _
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp]
  rfl

/-- The middle coefficient is the full actual row-two triangle label. -/
theorem triangle_middle (p : JTActualJointChainSeamChoices.Index F j) :
    ((seamFamily F j).triangle.data p).middle =
      (JTActualJointChainSeamChoices.triangle F j).app p ≫ JTNativeRowLabel.labelFromRow W 2 :=
  rfl

end
end DaggerModels.PartII.JTActualJointChainSeamNative
