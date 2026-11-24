import DaggerModelsPartII.JTChosenSeamOuterRaw
import DaggerModelsPartII.JTChosenSeamSupportedParameterRaw
import DaggerModelsPartII.JTPrismJointCoefficient
import DaggerModelsPartII.JTThreePieceMiddleSupport

/-! Raw evaluation on the full chosen-seam middle inverse image. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChosenSeamMiddleRaw

open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem joint_raw (W : Source) {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (j : Joint Q.code) :
    pointAt Q.code (ULift.up j.val) ≫ Q.map =
      SSet.yonedaEquiv.symm
        (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) := by
  have h := JTParametrizedBeadGraph.pointGraph_jointCoefficient (Q := Q) j
  have hv := congrArg SSet.yonedaEquiv h
  rw [JTRowGraphPointCoefficient.pointGraph_vertex] at hv
  change rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) =
    SSet.yonedaEquiv (pointAt Q.code (ULift.up j.val) ≫ Q.map) at hv
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact hv.symm

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
variable (incl : U ⟶ K ⋙ std)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
  JTJointSubcomplexRelativeLift.boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
  JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a =
  term (U.obj a) ≫ JTProjectiveOrderedFiberComparison.vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a =
  JTJointSubcomplexRelativeLift.identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a =
  JTJointSubcomplexRelativeLift.identityOnU W z)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
variable (time : I ⥤ SimplexCategory)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (oldTimed : JTParametrizedTargetFamilies.Family Q
  (JTChosenSeamOldComparison.oldFamily W K f O).labels time)

private abbrev Chain := JTChosenSeamChainDiagram.Index
  W z U K incl f e s he hs hfU heU hsU
private abbrev base := JTChosenSeamChainDiagram.toOriginal
  W z U K incl f e s he hs hfU heU hsU
private abbrev degree := JTChosenSeamChainDiagram.ordinals
  W z U K incl f e s he hs hfU heU hsU
private abbrev α := JTChosenSeamChainDiagram.toOld
  W z U K incl f e s he hs hfU heU hsU
private abbrev graph := JTChosenSeamGraphCover.graph
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev π := JTChosenSeamGraphCover.projection
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev θ := JTChosenSeamGraphCover.parameter
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev triangleTarget := JTChosenSeamGraphCover.triangleTarget
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev wholeNative := JTChosenSeamGraphCover.wholeNative
  W z U K incl f e s he hs hfU heU hsU O

private abbrev a (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  (base W z U K incl f e s he hs hfU heU hsU).obj p
private abbrev newCode (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  wedge (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (wedge (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)))
private abbrev oldCode (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  wedge (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (wedge (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)))
private abbrev native (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    (graph W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).obj p ⟶
      (newCode (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p).toSSet :=
  (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
    fst (newCode (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p).toSSet
      (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))
private abbrev midNew (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightU (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))
private abbrev midOld (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightU (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))
private abbrev midFirst (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  pullback.fst
    (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
    (midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)
private abbrev midSecond (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  pullback.snd
    (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
    (midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)
private abbrev clock (p : Chain W z U K incl f e s he hs hfU heU hsU) :=
  (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
    snd (newCode (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p).toSSet
      (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))

private theorem lift_pre {X Y Z T : SSet.{0}} (u : X ⟶ Y)
    (h : Y ⟶ Z) (t : Y ⟶ T) :
    u ≫ lift h t = lift (u ≫ h) (u ≫ t) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]

private theorem lift_tensor {X B C T : SSet.{0}} (h : X ⟶ B)
    (t : X ⟶ T) (i : B ⟶ C) :
    lift h t ≫ (i ⊗ₘ 𝟙 T) = lift (h ≫ i) t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]

private theorem projection_lift
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    lift (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) =
      (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p := by
  apply CartesianMonoidalCategory.hom_ext
  · exact lift_fst _ _
  · exact lift_snd _ _

private theorem θ_projection
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
        J.map ((α W z U K incl f e s he hs hfU heU hsU).app p) =
      (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
        (JTChosenSeamGraphCover.coarseParameter
          W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p :=
  NatTrans.congr_app (JTChosenSeamGraphCover.parameter_projection
    W z U K incl f e s he hs hfU heU hsU O time Q oldTimed) p

private theorem wholeNative_component
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    (wholeNative W z U K incl f e s he hs hfU heU hsU O).app p =
      (JTWhiskeredSeamTarget.triangleToCollapsed
        (JTChosenSeamChainDiagram.seamFamily
          W z U K incl f e s he hs hfU heU hsU O)).app p := by
  have hc : (JTChosenSeamGraphCover.collapsedNative
      W z U K incl f e s he hs hfU heU hsU O).app p =
        𝟙 (oldCode (P := P) (R := R)
          W z U K incl f e s he hs hfU heU hsU p) := by
    change (JTWhiskeredSeamTarget.nativeOf
      (JTChosenSeamOldComparison.comparison
        W z U K incl f e s he hs hfU heU hsU O)).app p = _
    rw [JTWhiskeredSeamTarget.nativeOf_app]
    exact congrArg Prod.fst
      (JTChosenSeamOldComparison.component_projection
        W z U K incl f e s he hs hfU heU hsU O p)
  change (JTWhiskeredSeamTarget.triangleToCollapsed
      (JTChosenSeamChainDiagram.seamFamily
        W z U K incl f e s he hs hfU heU hsU O)).app p ≫
      (JTChosenSeamGraphCover.collapsedNative
        W z U K incl f e s he hs hfU heU hsU O).app p = _
  rw [hc]
  exact NecklaceCode.Hom.ext (Category.comp_id _)

private theorem native_middle_to_old
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map =
    JTWhiskeredSeamTarget.collapseTriangle.map ≫
      midOld (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p := by
  rw [wholeNative_component]
  let b := a W z U K incl f e s he hs hfU heU hsU p
  change tripleRightU (P.obj b) (single 2) (R.obj b) ≫
      (wedgeMap (𝟙 (P.obj b))
        (wedgeMap JTWhiskeredSeamTarget.collapseTriangle (𝟙 (R.obj b)))).map =
    JTWhiskeredSeamTarget.collapseTriangle.map ≫
      tripleRightU (P.obj b) (single 0) (R.obj b)
  unfold tripleRightU
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left, Category.assoc]

/-- If the old middle native code hits the actual target joint, then the
whole chosen triangle hits that same joint after native collapse. -/
theorem native_middle_target_of_old
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hOld : midOld (P := P) (R := R)
        W z U K incl f e s he hs hfU heU hsU p ≫
        (oldTimed.collapse.app (a W z U K incl f e s he hs hfU heU hsU p)).map =
      term (single 0).toSSet ≫ pointAt Q.code (ULift.up j.val)) :
    midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
      ((triangleTarget W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed).app p).map =
      term (single 2).toSSet ≫ pointAt Q.code (ULift.up j.val) := by
  have ht : JTWhiskeredSeamTarget.collapseTriangle.map ≫
      term (single 0).toSSet = term (single 2).toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change midNew (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p ≫
      (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ≫
        (oldTimed.collapse.app (a W z U K incl f e s he hs hfU heU hsU p)).map) = _
  rw [← Category.assoc, native_middle_to_old, Category.assoc, hOld,
    ← Category.assoc, ht]

/-- The canonical middle vertex of the original surrounding necklace maps
to the specified original target joint exactly when its vertex index does. -/
theorem old_middle_joint
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hv : orderMap (oldTimed.collapse.app
      (a W z U K incl f e s he hs hfU heU hsU p)).map
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) = j.val) :
    midOld (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
        (oldTimed.collapse.app (a W z U K incl f e s he hs hfU heU hsU p)).map =
      term (single 0).toSSet ≫ pointAt Q.code (ULift.up j.val) := by
  let b := a W z U K incl f e s he hs hfU heU hsU p
  have hm := JTThreePieceMiddleSupport.middlePoint P R b
  have hpt : pointAt (oldCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p)
      (ULift.up (JTThreePieceMiddleSupport.middleVertex P R b)) ≫
        (oldTimed.collapse.app b).map = pointAt Q.code (ULift.up j.val) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact hv
  have h0 : term (single 0).toSSet ≫ pointAt (single 0) (ULift.up 0) =
      𝟙 (single 0).toSSet := by
    have ht : IsTerminal ((single 0).toSSet : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.ofIso (singleIso 0).symm
    exact ht.hom_ext _ _
  have hh := congrArg (fun q : (Δ[0] : SSet.{0}) ⟶ Q.code.toSSet ↦
    term (single 0).toSSet ≫ q) hpt
  rw [hm] at hh
  simpa only [← Category.assoc, h0, Category.id_comp] using hh

private theorem collapsed_middle_point
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    JTWhiskeredSeamTarget.collapseTriangle.map ≫
        midOld (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p =
      term (single 2).toSSet ≫
        pointAt (oldCode (P := P) (R := R)
          W z U K incl f e s he hs hfU heU hsU p)
          (ULift.up (JTThreePieceMiddleSupport.middleVertex P R
            (a W z U K incl f e s he hs hfU heU hsU p))) := by
  have ht : IsTerminal ((single 0).toSSet : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.ofIso (singleIso 0).symm
  have hc : JTWhiskeredSeamTarget.collapseTriangle.map =
      term (single 2).toSSet ≫ pointAt (single 0) (ULift.up 0) :=
    ht.hom_ext _ _
  rw [hc, Category.assoc, JTThreePieceMiddleSupport.middlePoint]


/-- A full middle graph parameter factoring through the original support face
has the joint raw value. The target equation is stated as an exact native
collapse to the original joint, without assuming a middle raw equation. -/
theorem middle_raw_of_factors
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hz : z = JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (d : SimplexCategory) (u : d ⟶ K.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hu : Function.Injective u.toOrderHom)
    (v : std.obj d ⟶ U.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hv : std.map u = v ≫ incl.app (a W z U K incl f e s he hs hfU heU hsU p))
    (g : (pullback
      (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      (midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)) ⟶ J.obj d)
    (hg : (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
          J.map ((α W z U K incl f e s he hs hfU heU hsU).app p) = g ≫ J.map u)
    (hnative : midNew (P := P) (R := R)
        W z U K incl f e s he hs hfU heU hsU p ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map =
      term (single 2).toSSet ≫ pointAt Q.code (ULift.up j.val)) :
    lift (midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
          realizedLabel (single 2).toSSet W
            ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
            (SSet.yonedaEquiv
              ((JTChosenSeamChainDiagram.triangle
                W z U K incl f e s he hs hfU heU hsU).app p ≫
                  JTNativeRowLabel.labelFromRow W 2)) =
      midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map ≫ Q.map := by
  have hr := JTChosenSeamSupportedParameterRaw.graph_raw_of_old_factor
    W z U K incl f e s he hs hfU heU hsU p d u hu v hv
    (midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
    (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
      (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) g hg
  have hzraw : rawVertex W z =
      rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) :=
    congrArg (rawVertex W) hz
  have hr' := hr.trans (congrArg (fun w ↦
    midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
      term (single 2).toSSet ≫ SSet.yonedaEquiv.symm w) hzraw)
  calc
    _ = midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
          term (single 2).toSSet ≫
            SSet.yonedaEquiv.symm
              (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) := hr'
    _ = _ := by
      have hj := congrArg (fun q : (Δ[0] : SSet.{0}) ⟶ Raw W ↦
        term (single 2).toSSet ≫ q) (joint_raw W Q j)
      have hn := congrArg (fun q : (single 2).toSSet ⟶ Q.code.toSSet ↦
        q ≫ Q.map) hnative
      have ht : midNew (P := P) (R := R)
          W z U K incl f e s he hs hfU heU hsU p ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map ≫ Q.map =
          term (single 2).toSSet ≫ SSet.yonedaEquiv.symm
            (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) := by
        simpa only [Category.assoc] using hn.trans hj
      simpa only [Category.assoc] using congrArg
        (fun q ↦ midSecond W z U K incl f e s he hs hfU heU hsU
          O time Q oldTimed p ≫ q) ht.symm

/-- On the full middle inverse image, the lifted coefficient projects to the
original full-time parameter evaluated at the collapsed middle point. -/
theorem middle_parameter_projection
    (p : Chain W z U K incl f e s he hs hfU heU hsU) :
    (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
      (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        J.map ((α W z U K incl f e s he hs hfU heU hsU).app p) =
      lift (midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
          JTWhiskeredSeamTarget.collapseTriangle.map ≫
            midOld (P := P) (R := R)
              W z U K incl f e s he hs hfU heU hsU p)
        (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
          clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) ≫
            oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) := by
  let h := native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let i := midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p
  let t := clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let u := midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let v := midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  have hpb : u ≫ h = v ≫ i := pullback.condition
  have hπ := projection_lift W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p
  have hθ := θ_projection W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p
  have hn := native_middle_to_old W z U K incl f e s he hs hfU heU hsU O p
  calc
    _ = u ≫ (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
          (JTChosenSeamGraphCover.coarseParameter
            W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p := by
        rw [Category.assoc, hθ]
    _ = lift (u ≫ h) (u ≫ t) ≫
          (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ⊗ₘ
            𝟙 (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))) ≫
              oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) := by
        rw [← lift_pre, hπ]
        rfl
    _ = lift (v ≫ i) (u ≫ t) ≫
          (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ⊗ₘ
            𝟙 (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))) ≫
              oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) := by
        rw [hpb]
    _ = _ := by
        rw [← Category.assoc, lift_tensor, Category.assoc, hn]

/-- The original supported face and original native joint suffice for the
middle raw equation; neither triangle stationarity nor raw constancy is an
additional hypothesis. -/
theorem middle_raw_of_old_support
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hz : z = JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (d : SimplexCategory) (u : d ⟶ K.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hu : Function.Injective u.toOrderHom)
    (v : std.obj d ⟶ U.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hv : std.map u = v ≫ incl.app (a W z U K incl f e s he hs hfU heU hsU p))
    (jOld : midOld (P := P) (R := R)
        W z U K incl f e s he hs hfU heU hsU p ≫
        (oldTimed.collapse.app (a W z U K incl f e s he hs hfU heU hsU p)).map =
      term (single 0).toSSet ≫ pointAt Q.code (ULift.up j.val))
    (g : (pullback
      (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      (midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)) ⟶ J.obj d)
    (hfactor : lift (midSecond W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed p ≫ JTWhiskeredSeamTarget.collapseTriangle.map ≫
          midOld (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)
        (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
          clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) ≫
            oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) =
      g ≫ J.map u) :
    lift (midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
          realizedLabel (single 2).toSSet W
            ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
            (SSet.yonedaEquiv
              ((JTChosenSeamChainDiagram.triangle
                W z U K incl f e s he hs hfU heU hsU).app p ≫
                  JTNativeRowLabel.labelFromRow W 2)) =
      midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map ≫ Q.map :=
  middle_raw_of_factors W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
    p j hz d u hu v hv g
    ((middle_parameter_projection W z U K incl f e s he hs hfU heU hsU
      O time Q oldTimed p).trans hfactor)
    (native_middle_target_of_old W z U K incl f e s he hs hfU heU hsU
      O time Q oldTimed p j jOld)

/-- The canonical full timed support at the original middle vertex supplies
the entire inverse-image middle equation. The sole support datum is its
inclusion in the stated stationary subcomplex. -/
theorem middle_raw_used_face
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hz : z = JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (hv : orderMap (oldTimed.collapse.app
      (a W z U K incl f e s he hs hfU heU hsU p)).map
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) = j.val)
    (v : std.obj (JTActualSourceJointSupport.usedDegree oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) ⟶
      U.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hU : std.map (JTActualSourceJointSupport.usedInclusion oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) =
      v ≫ incl.app (a W z U K incl f e s he hs hfU heU hsU p)) :
    lift (midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      (midFirst W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
          realizedLabel (single 2).toSSet W
            ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
            (SSet.yonedaEquiv
              ((JTChosenSeamChainDiagram.triangle
                W z U K incl f e s he hs hfU heU hsU).app p ≫
                  JTNativeRowLabel.labelFromRow W 2)) =
      midSecond W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        midNew (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map ≫ Q.map := by
  let b := a W z U K incl f e s he hs hfU heU hsU p
  let m := JTThreePieceMiddleSupport.middleVertex P R b
  let d := JTActualSourceJointSupport.usedDegree oldTimed b j m hv
  let u := JTActualSourceJointSupport.usedInclusion oldTimed b j m hv
  let t := midFirst W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p ≫
      clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let g := lift (midSecond W z U K incl f e s he hs hfU heU hsU
      O time Q oldTimed p ≫ term (single 2).toSSet) t ≫
        JTJointTimedEndpointSupport.supportedTimedParameter oldTimed b j
          (JTActualSourceJointSupport.liftedOverlapVertex oldTimed b j m hv)
  have hu : Function.Injective u.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp
      (JTActualSourceJointSupport.usedInclusion_mono oldTimed b j m hv)
  have hfactor : lift (midSecond W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed p ≫ JTWhiskeredSeamTarget.collapseTriangle.map ≫
          midOld (P := P) (R := R) W z U K incl f e s he hs hfU heU hsU p)
      t ≫ oldTimed.parameter b = g ≫ J.map u := by
    have hf := JTThreePieceMiddleSupport.middleVertex_timeParameter_factor
      W P R K f O Q time oldTimed b j hv
    rw [collapsed_middle_point W z U K incl f e s he hs hfU heU hsU p]
    rw [← Category.assoc, ← lift_tensor]
    change lift (midSecond W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed p ≫ term (single 2).toSSet) t ≫
          JTActualSourceJointSupport.timeParameter oldTimed b m = _
    rw [← hf]
    rfl
  exact middle_raw_of_old_support W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p j hz d u hu v hU
    (old_middle_joint W z U K incl f e s he hs hfU heU hsU
      O time Q oldTimed p j hv) g hfactor

/-- The three full native inverse images satisfy the exact equations for the
same chosen label, graph parameter, and original fixed target. -/
theorem pieceEquations
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hz : z = JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (hv : orderMap (oldTimed.collapse.app
      (a W z U K incl f e s he hs hfU heU hsU p)).map
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) = j.val)
    (v : std.obj (JTActualSourceJointSupport.usedDegree oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) ⟶
      U.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hU : std.map (JTActualSourceJointSupport.usedInclusion oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) =
      v ≫ incl.app (a W z U K incl f e s he hs hfU heU hsU p)) :
    JTWhiskeredGraphRaw.PieceEquations W
      (JTChosenSeamChainDiagram.data
        W z U K incl f e s he hs hfU heU hsU O p)
      (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
      ((θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p)
      (((triangleTarget W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed).app p).map ≫ Q.map) := by
  refine ⟨?_, ?_, ?_⟩
  · exact JTChosenSeamOuterRaw.left_raw
      W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  · exact middle_raw_used_face W z U K incl f e s he hs hfU heU hsU
      O time Q oldTimed p j hz hv v hU
  · exact JTChosenSeamOuterRaw.right_raw
      W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p

/-- Consequently the entire chosen decorated triple has the original raw
evaluation, with no whole-graph raw premise. -/
theorem whole_raw
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (j : Joint Q.code)
    (hz : z = JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
    (hv : orderMap (oldTimed.collapse.app
      (a W z U K incl f e s he hs hfU heU hsU p)).map
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) = j.val)
    (v : std.obj (JTActualSourceJointSupport.usedDegree oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) ⟶
      U.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (hU : std.map (JTActualSourceJointSupport.usedInclusion oldTimed
        (a W z U K incl f e s he hs hfU heU hsU p) j
        (JTThreePieceMiddleSupport.middleVertex P R
          (a W z U K incl f e s he hs hfU heU hsU p)) hv) =
      v ≫ incl.app (a W z U K incl f e s he hs hfU heU hsU p)) :
    lift (native W z U K incl f e s he hs hfU heU hsU
        O time Q oldTimed p)
      ((θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        realizedLabel
          (newCode (P := P) (R := R)
            W z U K incl f e s he hs hfU heU hsU p).toSSet W
          ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
          (JTRealizedLabelEndpoints.orderedLabel W x y
            (newCode (P := P) (R := R)
              W z U K incl f e s he hs hfU heU hsU p)
            ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
            (JTComposedPrismLabels.orderedPoint
              (JTThreePieceLabelOperators.coefficients
                (JTChosenSeamChainDiagram.data
                  W z U K incl f e s he hs hfU heU hsU O p)))) =
      native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p ≫
        ((triangleTarget W z U K incl f e s he hs hfU heU hsU
          O time Q oldTimed).app p).map ≫ Q.map :=
  (pieceEquations W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
    p j hz hv v hU).ordered_raw

end
end DaggerModels.PartII.JTChosenSeamMiddleRaw
