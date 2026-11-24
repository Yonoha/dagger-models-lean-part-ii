import DaggerModelsPartII.JTSharedInsertionSeamNative
import DaggerModelsPartII.JTPrismChainGraphCover

/-!
The full original-time graph of the corrected shared insertion seam triangle. All lifts through
the composite coefficient projection are retained as a natural graph cover.
No natural section of an ordinal surjection or chain-degree Family is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionSeamGraph

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTSharedInsertionSeamNative (wholeNative)
open JTSharedInsertionNormalizedSeam (seamFamily original oldDegrees coefficientProjection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
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

private def firstCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ fst B T
private def secondCoordinate {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) := π ≫ snd B T
private theorem coordinate_pair {X B T : SSet.{0}} (π : X ⟶ B ⊗ T) :
    lift (firstCoordinate π) (secondCoordinate π) = π := lift_comp_fst_snd π

private theorem timeMap_parameter {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (n : N ⟶ M) (t k : C ⥤ SimplexCategory)
    (r : (((M ⋙ toSSet).prod' (t ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}) ⟶ k ⋙ J)
    (p : C) :
    ((mapWithTime n t) ≫ r).app p =
      ((n.app p).map ⊗ₘ 𝟙 (J.obj (t.obj p))) ≫ r.app p := by
  rw [NatTrans.comp_app, mapWithTime_app]


private theorem native_id_map (T : NecklaceCode) :
    (𝟙 T : T ⟶ T).map = 𝟙 T.toSSet := rfl

private theorem triple_map_middle {P M R P' M' R' : NecklaceCode}
    (g : P ⟶ P') (h : M ⟶ M') (k : R ⟶ R') :
    tripleRightU P M R ≫ (wedgeMap g (wedgeMap h k)).map =
      h.map ≫ tripleRightU P' M' R' := by
  rw [tripleRightU, tripleRightU, Category.assoc, wedgeMap_right,
    ← Category.assoc, wedgeMap_left, Category.assoc]

private theorem triple_map_right {P M R P' M' R' : NecklaceCode}
    (g : P ⟶ P') (h : M ⟶ M') (k : R ⟶ R') :
    tripleRightV P M R ≫ (wedgeMap g (wedgeMap h k)).map =
      k.map ≫ tripleRightV P' M' R' := by
  rw [tripleRightV, tripleRightV, Category.assoc, wedgeMap_right,
    ← Category.assoc, wedgeMap_right, Category.assoc]

private theorem triangle_collapse_app {C : Type} [SmallCategory C]
    {W : Source} {x y : Vertex W} {P R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (S : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K) (p : C) :
    (JTWhiskeredSeamTarget.triangleToCollapsed S).app p =
      wedgeMap (𝟙 (P.obj p)) (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (𝟙 (R.obj p))) :=
  rfl

private theorem comparison_native {C : Type} [SmallCategory C] (W : Source) (z : Vertex W)
    (U : C ⥤ SSet.{0}) (K : C ⥤ SimplexCategory) (incl : U ⟶ K ⋙ SSet.stdSimplex)
    (f : K ⋙ SSet.stdSimplex ⟶ (Functor.const C).obj (row W ⦋0⦌))
    (e s : K ⋙ SSet.stdSimplex ⟶ (Functor.const C).obj (row W ⦋1⦌))
    (he : ∀ a : C, e.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W (f.app a) z)
    (hs : ∀ a : C, s.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app a) z)
    (hf : ∀ a : C, incl.app a ≫ f.app a =
      SSet.stdSimplex.isTerminalObj₀.from (U.obj a) ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W z)
    (heU : ∀ a : C, incl.app a ≫ e.app a = JTJointSubcomplexRelativeLift.identityOnU W z)
    (hsU : ∀ a : C, incl.app a ≫ s.app a = JTJointSubcomplexRelativeLift.identityOnU W z)
    {x y : Vertex W} {P R : C ⥤ NecklaceCode}
    (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
    (p : JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hf heU hsU) :
    (JTWhiskeredSeamTarget.nativeOf
      (JTChosenSeamOldComparison.comparison W z U K incl f e s he hs hf heU hsU O)).app p =
        𝟙 _ :=
  congrArg Prod.fst
    (JTChosenSeamOldComparison.component_projection W z U K incl f e s he hs hf heU hsU O p)

private theorem chosen_triangle_collapse {C : Type} [SmallCategory C] (W : Source) (z : Vertex W)
    (U : C ⥤ SSet.{0}) (K : C ⥤ SimplexCategory) (incl : U ⟶ K ⋙ SSet.stdSimplex)
    (f : K ⋙ SSet.stdSimplex ⟶ (Functor.const C).obj (row W ⦋0⦌))
    (e s : K ⋙ SSet.stdSimplex ⟶ (Functor.const C).obj (row W ⦋1⦌))
    (he : ∀ a : C, e.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W (f.app a) z)
    (hs : ∀ a : C, s.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app a) z)
    (hf : ∀ a : C, incl.app a ≫ f.app a =
      SSet.stdSimplex.isTerminalObj₀.from (U.obj a) ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W z)
    (heU : ∀ a : C, incl.app a ≫ e.app a = JTJointSubcomplexRelativeLift.identityOnU W z)
    (hsU : ∀ a : C, incl.app a ≫ s.app a = JTJointSubcomplexRelativeLift.identityOnU W z)
    {x y : Vertex W} {P R : C ⥤ NecklaceCode}
    (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
    (p : JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hf heU hsU) :
    (JTWhiskeredSeamTarget.triangleToCollapsed
      (JTChosenSeamChainDiagram.seamFamily W z U K incl f e s he hs hf heU hsU O)).app p =
      wedgeMap (𝟙 (P.obj
        ((JTChosenSeamChainDiagram.toOriginal W z U K incl f e s he hs hf heU hsU).obj p)))
        (wedgeMap JTWhiskeredSeamTarget.collapseTriangle
          (𝟙 (R.obj
            ((JTChosenSeamChainDiagram.toOriginal W z U K incl f e s he hs hf heU hsU).obj p)))) :=
  rfl

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTSharedInsertionNormalizedSeam.Index F j
private abbrev natives := codes (seamFamily F j).triangle.labels

/-- The entire original time simplex and every original time operator are retained. -/
abbrev oldTime : I F j ⥤ SimplexCategory := original F j ⋙ time

/-- The whole triangle necklace paired with the complete original time parameter. -/
abbrev X : I F j ⥤ SSet.{0} :=
  (((natives F j) ⋙ toSSet).prod' ((oldTime F j) ⋙ J)) ⋙
    MonoidalCategory.tensor SSet.{0}

private abbrev oldProduct : I F j ⥤ SSet.{0} :=
  (((original F j ⋙ codes L) ⋙ toSSet).prod' ((oldTime F j) ⋙ J)) ⋙
    MonoidalCategory.tensor SSet.{0}

private def oldParameter : oldProduct F j ⟶ oldDegrees F j ⋙ J where
  app p := F.parameter ((original F j).obj p)
  naturality _ _ g := F.parameter_map ((original F j).map g)

/-- The actual whole native reassembly acts with identity on the entire old time. -/
def nativeTimeMap : X F j ⟶ oldProduct F j :=
  mapWithTime (wholeNative F j) (oldTime F j)

/-- The literal original Family parameter after whole native reassembly. -/
def coarseParameter : X F j ⟶ oldDegrees F j ⋙ J :=
  nativeTimeMap F j ≫ oldParameter F j

set_option maxHeartbeats 850000 in
/-- Every complete native/time prism uses exactly the original parameter. -/
theorem coarseParameter_app (p : I F j) :
    (coarseParameter F j).app p =
      (((wholeNative F j).app p).map ⊗ₘ 𝟙 (J.obj ((oldTime F j).obj p))) ≫
        F.parameter ((original F j).obj p) :=
  timeMap_parameter (wholeNative F j) (oldTime F j) (oldDegrees F j) (oldParameter F j) p

/-- Retain all coefficient lifts to the actual composite full-chain degree. -/
abbrev graph : I F j ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The full graph projection keeps the whole triangle and every old time simplex. -/
abbrev projection : graph F j ⟶ X F j :=
  JTPrismChainGraphCover.projection (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The complete lifted coefficient parameter, natural in all actual operators. -/
abbrev parameter : graph F j ⟶ JTSharedInsertionSeamTriangles.ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- The lifted parameter recovers the exact original whole-prism parameter. -/
theorem parameter_projection :
    parameter F j ≫ Functor.whiskerRight (coefficientProjection F j) J =
      projection F j ≫ coarseParameter F j :=
  JTPrismChainGraphCover.parameter_projection
    (X F j) (coarseParameter F j) (coefficientProjection F j)

/-- Each entire graph cover projects by a trivial fibration. -/
theorem projection_trivialFibration (p : I F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration (X F j) (coarseParameter F j)
    (coefficientProjection F j)
    (JTSharedInsertionNormalizedSeam.coefficientProjection_surjective F j) p

/-- The full triangle native coordinate of a lifted graph point. -/
abbrev native (p : I F j) :=
  firstCoordinate ((projection F j).app p)

/-- Its unchanged full original time coordinate. -/
abbrev clock (p : I F j) :=
  secondCoordinate ((projection F j).app p)

/-- The two coordinates recover the entire graph projection. -/
theorem native_clock (p : I F j) :
    lift (native F j p) (clock F j p) = (projection F j).app p :=
  coordinate_pair ((projection F j).app p)

set_option maxHeartbeats 850000 in
/-- The exact original parameter identity at every whole graph component. -/
theorem parameter_projection_app (p : I F j) :
    (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
      (projection F j).app p ≫
        ((((wholeNative F j).app p).map ⊗ₘ 𝟙 (J.obj ((oldTime F j).obj p))) ≫
          F.parameter ((original F j).obj p)) := by
  have h := congrArg (fun η : graph F j ⟶ oldDegrees F j ⋙ J ↦ η.app p)
    (parameter_projection F j)
  change (parameter F j).app p ≫ J.map ((coefficientProjection F j).app p) =
    (projection F j).app p ≫ (coarseParameter F j).app p at h
  exact h.trans (congrArg (fun q ↦ (projection F j).app p ≫ q)
    (coarseParameter_app F j p))

private abbrev base := JTSharedInsertionSeamTriangles.toOriginal F j
private abbrev shared (p : I F j) := (base F j).obj p
private abbrev P (p : I F j) :=
  (JTSharedInsertionSeamSurroundings.leftNative F j).obj (shared F j p)
private abbrev R (p : I F j) :=
  (JTSharedInsertionSeamSurroundings.rightNative F j).obj (shared F j p)
private abbrev marked (p : I F j) :=
  (JTSharedInsertionChainSupport.marks F j 1).obj (shared F j p)
private abbrev T (p : I F j) := (codes L).obj ((original F j).obj p)
private abbrev v (p : I F j) := (marked F j p).2.val
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev U := JTSharedInsertionChainSupport.diagram F j 1
private abbrev K := JTSharedInsertionChoices.ordinals F j
private abbrev incl := JTSharedInsertionChainSupport.inclusion F j 1
private abbrev f := JTSharedInsertionChainSupport.rows F j 1
private abbrev e := JTSharedInsertionIncidentEdges.ending F j 1
private abbrev s := JTSharedInsertionIncidentEdges.starting F j 1
private abbrev he := JTSharedInsertionIncidentEdges.ending_endpoints F j 1
private abbrev hs := JTSharedInsertionIncidentEdges.starting_endpoints F j 1
private abbrev hfU := JTSharedInsertionChainSupport.row_on_support F j 1
private abbrev heU := JTSharedInsertionIncidentEdges.ending_on_support F j 1
private abbrev hsU := JTSharedInsertionIncidentEdges.starting_on_support F j 1
private abbrev O := JTSharedInsertionSeamSurroundings.surroundings F j

private theorem collapsedNative_app (p : I F j) :
    (JTSharedInsertionSeamNative.collapsedNative F j).app p =
      (JTSharedInsertionSeamNative.oldAssembly F j).app (shared F j p) := by
  have h := comparison_native W (z j) (U F j) (K F j)
    (incl F j) (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j)
    (heU F j) (hsU F j) (O F j) p
  change (JTWhiskeredSeamTarget.nativeOf
    (JTSharedInsertionNormalizedSeam.collapsedToOld F j)).app p ≫ _ = _
  dsimp only [JTSharedInsertionNormalizedSeam.collapsedToOld]
  rw [h, Category.id_comp]
  rfl

set_option maxHeartbeats 850000 in
private theorem wholeNative_app (p : I F j) :
    (wholeNative F j).app p =
      wedgeMap (𝟙 (P F j p))
        (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (𝟙 (R F j p))) ≫
      (JTSharedInsertionSeamNative.oldAssembly F j).app (shared F j p) := by
  change (JTWhiskeredSeamTarget.triangleToCollapsed (seamFamily F j)).app p ≫
    (JTSharedInsertionSeamNative.collapsedNative F j).app p = _
  rw [collapsedNative_app]
  exact congrArg (fun g ↦ g ≫
    (JTSharedInsertionSeamNative.oldAssembly F j).app (shared F j p))
    (chosen_triangle_collapse W (z j) (U F j) (K F j) (incl F j) (f F j)
      (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) (O F j) p)

set_option maxHeartbeats 850000 in
/-- The complete corrected left side returns to its literal old native assembly. -/
theorem wholeNative_left (p : I F j) :
    tripleRightT (P F j p) (single 2) (R F j p) ≫
      ((wholeNative F j).app p).map =
        JTSharedInsertionNativeAssembly.leftToOriginal F j (shared F j p) := by
  rw [wholeNative_app]
  change wedgeιLeft (P F j p) (wedge (single 2) (R F j p)) ≫
    (_ ≫ ((wedgeMap
      ((JTSharedInsertionNativeAssembly.leftToCut F j).app (shared F j p))
      (wedgeMap (𝟙 (single 0))
        ((JTSharedInsertionNativeAssembly.rightToCut F j).app (shared F j p)))).map ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map)) = _
  rw [← Category.assoc, wedgeMap_left, native_id_map, Category.id_comp,
    ← Category.assoc, wedgeMap_left, Category.assoc]
  dsimp only [JTSharedInsertionNativeAssembly.leftCuts,
    JTSharedInsertionNativeAssembly.rightCuts, Functor.comp_obj,
    JTExactlyMarkedCutDiagrams.leftNative, JTExactlyMarkedCutDiagrams.rightNative]
  change _ ≫ (tripleRightT (cutLeft (T F j p) (v F j p)) (single 0)
    (cutRight (T F j p) (v F j p)) ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map) = _
  rw [JTNativeCutPointAssembly.assembly_left (T F j p) (v F j p)]
  exact JTSharedInsertionNativeAssembly.leftToCut_fac F j (shared F j p)

set_option maxHeartbeats 850000 in
/-- The complete corrected right side retains both outer correction edges. -/
theorem wholeNative_right (p : I F j) :
    tripleRightV (P F j p) (single 2) (R F j p) ≫
      ((wholeNative F j).app p).map =
        JTSharedInsertionNativeAssembly.rightToOriginal F j (shared F j p) := by
  rw [wholeNative_app]
  change tripleRightV (P F j p) (single 2) (R F j p) ≫
    (_ ≫ ((wedgeMap
      ((JTSharedInsertionNativeAssembly.leftToCut F j).app (shared F j p))
      (wedgeMap (𝟙 (single 0))
        ((JTSharedInsertionNativeAssembly.rightToCut F j).app (shared F j p)))).map ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map)) = _
  rw [← Category.assoc, triple_map_right, native_id_map, Category.id_comp,
    ← Category.assoc, triple_map_right, Category.assoc]
  dsimp only [JTSharedInsertionNativeAssembly.leftCuts,
    JTSharedInsertionNativeAssembly.rightCuts, Functor.comp_obj,
    JTExactlyMarkedCutDiagrams.leftNative, JTExactlyMarkedCutDiagrams.rightNative]
  change _ ≫ (tripleRightV (cutLeft (T F j p) (v F j p)) (single 0)
    (cutRight (T F j p) (v F j p)) ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map) = _
  rw [JTNativeCutPointAssembly.assembly_right (T F j p) (v F j p)]
  exact JTSharedInsertionNativeAssembly.rightToCut_fac F j (shared F j p)

/-- The entire middle triangle maps to the inserted old vertex, with full old time later. -/
theorem wholeNative_middle (p : I F j) :
    tripleRightU (P F j p) (single 2) (R F j p) ≫
      ((wholeNative F j).app p).map =
        SSet.stdSimplex.isTerminalObj₀.from (single 2).toSSet ≫
          pointAt (T F j p) (ULift.up (v F j p)) := by
  rw [wholeNative_app]
  change tripleRightU (P F j p) (single 2) (R F j p) ≫
    (_ ≫ ((wedgeMap
      ((JTSharedInsertionNativeAssembly.leftToCut F j).app (shared F j p))
      (wedgeMap (𝟙 (single 0))
        ((JTSharedInsertionNativeAssembly.rightToCut F j).app (shared F j p)))).map ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map)) = _
  rw [← Category.assoc, triple_map_middle, Category.assoc,
    ← Category.assoc (tripleRightU _ (single 0) _), triple_map_middle,
    native_id_map, Category.id_comp]
  dsimp only [JTSharedInsertionNativeAssembly.leftCuts,
    JTSharedInsertionNativeAssembly.rightCuts, Functor.comp_obj,
    JTExactlyMarkedCutDiagrams.leftNative, JTExactlyMarkedCutDiagrams.rightNative]
  change _ ≫ (tripleRightU (cutLeft (T F j p) (v F j p)) (single 0)
    (cutRight (T F j p) (v F j p)) ≫
      (JTNativeCutPointAssembly.assembly (T F j p) (v F j p)).map) = _
  rw [JTNativeCutPointAssembly.assembly_middle, ← Category.assoc]
  congr 1

end
end DaggerModels.PartII.JTSharedInsertionSeamGraph
