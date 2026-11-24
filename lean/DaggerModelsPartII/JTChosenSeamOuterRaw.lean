import DaggerModelsPartII.JTChosenSeamGraphCover
import DaggerModelsPartII.JTWhiskeredGraphRaw

/-! Exact old-timed raw equations on both full outer graph inverse images. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChosenSeamOuterRaw

open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map i) W

private theorem lift_product_parameter {X B I K : SSet.{0}}
    (h : X ⟶ B) (t : X ⟶ I) (p : B ⊗ I ⟶ K) :
    lift h (lift h t ≫ p) = lift h t ≫ lift (fst B I) p := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]

private theorem lift_pre {X Y Z I : SSet.{0}} (u : X ⟶ Y)
    (h : Y ⟶ Z) (t : Y ⟶ I) :
    u ≫ lift h t = lift (u ≫ h) (u ≫ t) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]

private theorem lift_tensor {X B C I : SSet.{0}} (h : X ⟶ B)
    (t : X ⟶ I) (i : B ⟶ C) :
    lift h t ≫ (i ⊗ₘ 𝟙 I) = lift (h ≫ i) t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]

/-- Pull an exact old full-timed raw product to any graph simplex lying over
an old native subnecklace, while reindexing the coefficient degree. -/
private theorem outer_raw (W : Source) {X : SSet.{0}} {S T : NecklaceCode}
    {k l n : SimplexCategory} (α : k ⟶ l)
    (i : S.toSSet ⟶ T.toSSet) (h : X ⟶ S.toSSet)
    (q : X ⟶ J.obj k) (t : X ⟶ J.obj n)
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj l)
    (c : std.obj l ⟶ TripleBeadEndpointLabel.labels W T)
    (d : std.obj k ⟶ TripleBeadEndpointLabel.labels W S)
    (g : T.toSSet ⟶ Raw W)
    (hc : d = std.map α ≫ c ≫ pre W i)
    (hq : q ≫ J.map α = lift (h ≫ i) t ≫ p)
    (hr : JTComposedPrismLabels.rawProduct W p c = fst T.toSSet (J.obj n) ≫ g) :
    lift h q ≫ realizedLabel S.toSSet W k (SSet.yonedaEquiv d) = h ≫ i ≫ g := by
  rw [hc]
  rw [← JTWhiskerEdgeGraphRaw.coefficient_reindex W α h q (c ≫ pre W i)]
  rw [← JTWhiskerEdgeGraphRaw.native_restrict W i h (q ≫ J.map α) c]
  rw [hq, lift_product_parameter]
  change lift (h ≫ i) t ≫ JTComposedPrismLabels.rawProduct W p c = _
  rw [hr]
  simp only [Category.assoc, lift_fst_assoc]

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
  SSet.stdSimplex.isTerminalObj₀.from (U.obj a) ≫
    JTProjectiveOrderedFiberComparison.vertexPoint W z)
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

private abbrev C := JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hfU heU hsU
private abbrev base := JTChosenSeamChainDiagram.toOriginal
  W z U K incl f e s he hs hfU heU hsU
private abbrev degree := JTChosenSeamChainDiagram.ordinals
  W z U K incl f e s he hs hfU heU hsU
private abbrev α := JTChosenSeamChainDiagram.toOld
  W z U K incl f e s he hs hfU heU hsU
private abbrev old := JTChosenSeamOldComparison.oldFamily W K f O
private abbrev chosen := JTChosenSeamChainDiagram.seamFamily
  W z U K incl f e s he hs hfU heU hsU O
private abbrev G := JTChosenSeamGraphCover.graph
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev π := JTChosenSeamGraphCover.projection
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev θ := JTChosenSeamGraphCover.parameter
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed
private abbrev wholeNative := JTChosenSeamGraphCover.wholeNative
  W z U K incl f e s he hs hfU heU hsU O
private abbrev triangleTarget := JTChosenSeamGraphCover.triangleTarget
  W z U K incl f e s he hs hfU heU hsU O time Q oldTimed

private abbrev a (p : C W z U K incl f e s he hs hfU heU hsU) :=
  (base W z U K incl f e s he hs hfU heU hsU).obj p
private abbrev newCode (p : C W z U K incl f e s he hs hfU heU hsU) :=
  wedge (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (wedge (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)))
private abbrev newData (p : C W z U K incl f e s he hs hfU heU hsU) :=
  JTChosenSeamChainDiagram.data W z U K incl f e s he hs hfU heU hsU O p
private abbrev native (p : C W z U K incl f e s he hs hfU heU hsU) :
    (G W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).obj p ⟶
      (newCode (P := P) (R := R)
        W z U K incl f e s he hs hfU heU hsU p).toSSet :=
  (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
    fst (newCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p).toSSet
      (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))
private abbrev clock (p : C W z U K incl f e s he hs hfU heU hsU) :=
  (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
    snd (newCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p).toSSet
      (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))

private abbrev oldCode (a : I) :=
  (JTParametrizedTargetFamilies.codes (old W K f O).labels).obj a
private abbrev oldData (a : I) := JTChosenSeamOldComparison.oldData W K f O a
private abbrev oldCoefficient (a : I) :=
  JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients
    (oldData W K f O a))

/-- The original Family.rawProduct on the exact old three-piece coefficient. -/
private theorem old_raw (a : I) :
    JTComposedPrismLabels.rawProduct W (oldTimed.parameter a)
        (oldCoefficient W K f O a) =
      fst (oldCode W K f O a).toSSet (J.obj (time.obj a)) ≫
        (oldTimed.collapse.app a).map ≫ Q.map := by
  have hr := JTParametrizedTargetFamilies.rawProduct oldTimed a
  change JTBinaryPrismRealization.realizeProduct W (K.obj a)
      (oldTimed.parameter a)
      (JTRealizedLabelEndpoints.orderedLabel W x y
        (wedge (P.obj a) (wedge (single 0) (R.obj a)))
        (K.obj a) (JTComposedPrismLabels.orderedPoint
          (JTThreePieceLabelOperators.coefficients (oldData W K f O a)))) = _ at hr
  rw [JTComposedPrismLabels.orderedPoint_coefficient] at hr
  exact hr

private theorem collapsedNative_id
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    (JTChosenSeamGraphCover.collapsedNative
      W z U K incl f e s he hs hfU heU hsU O).app p =
        𝟙 (oldCode W K f O (a W z U K incl f e s he hs hfU heU hsU p)) := by
  change (JTWhiskeredSeamTarget.nativeOf
      (JTChosenSeamOldComparison.comparison
        W z U K incl f e s he hs hfU heU hsU O)).app p = _
  rw [JTWhiskeredSeamTarget.nativeOf_app]
  exact congrArg Prod.fst
    (JTChosenSeamOldComparison.component_projection
      W z U K incl f e s he hs hfU heU hsU O p)

private theorem wholeNative_component
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    (wholeNative W z U K incl f e s he hs hfU heU hsU O).app p =
      (JTWhiskeredSeamTarget.triangleToCollapsed
        (chosen W z U K incl f e s he hs hfU heU hsU O)).app p := by
  change (JTWhiskeredSeamTarget.triangleToCollapsed
      (chosen W z U K incl f e s he hs hfU heU hsU O)).app p ≫
      (JTChosenSeamGraphCover.collapsedNative
        W z U K incl f e s he hs hfU heU hsU O).app p = _
  rw [collapsedNative_id]
  exact NecklaceCode.Hom.ext (Category.comp_id _)

private theorem native_left
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    tripleRightT (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
        (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)) ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map =
    tripleRightT (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
      (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)) := by
  rw [wholeNative_component]
  let b := a W z U K incl f e s he hs hfU heU hsU p
  change tripleRightT (P.obj b) (single 2) (R.obj b) ≫
    (wedgeMap (𝟙 (P.obj b)) (wedgeMap JTWhiskeredSeamTarget.collapseTriangle
      (𝟙 (R.obj b)))).map = tripleRightT (P.obj b) (single 0) (R.obj b)
  rw [tripleRightT, wedgeMap_left]
  change (𝟙 (P.obj b).toSSet) ≫ wedgeιLeft (P.obj b)
    (wedge (single 0) (R.obj b)) = _
  exact Category.id_comp _

private theorem native_right
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    tripleRightV (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
        (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)) ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map =
    tripleRightV (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
      (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p)) := by
  rw [wholeNative_component]
  let b := a W z U K incl f e s he hs hfU heU hsU p
  change tripleRightV (P.obj b) (single 2) (R.obj b) ≫
    (wedgeMap (𝟙 (P.obj b)) (wedgeMap JTWhiskeredSeamTarget.collapseTriangle
      (𝟙 (R.obj b)))).map = tripleRightV (P.obj b) (single 0) (R.obj b)
  unfold tripleRightV
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_right]
  change ((𝟙 (R.obj b).toSSet) ≫ wedgeιRight (single 0) (R.obj b)) ≫
    wedgeιRight (P.obj b) (wedge (single 0) (R.obj b)) = _
  rw [Category.id_comp]

private theorem projection_lift
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    lift (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) =
      (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p := by
  apply CartesianMonoidalCategory.hom_ext
  · exact lift_fst _ _
  · exact lift_snd _ _

private theorem θ_projection
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
        J.map ((α W z U K incl f e s he hs hfU heU hsU).app p) =
      (π W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p ≫
        (JTChosenSeamGraphCover.coarseParameter
          W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p :=
  NatTrans.congr_app (JTChosenSeamGraphCover.parameter_projection
    W z U K incl f e s he hs hfU heU hsU O time Q oldTimed) p

private theorem piece_parameter {S : NecklaceCode}
    (p : C W z U K incl f e s he hs hfU heU hsU)
    (iNew : S.toSSet ⟶ (newCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode W K f O
      (a W z U K incl f e s he hs hfU heU hsU p)).toSSet)
    (hi : iNew ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map = iOld) :
    (pullback.fst
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew ≫
      (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        J.map ((α W z U K incl f e s he hs hfU heU hsU).app p) =
      lift (pullback.snd
          (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew ≫ iOld)
        (pullback.fst
          (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew ≫
            clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) ≫
          oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) := by
  let h := native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let t := clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let u := pullback.fst h iNew
  let v := pullback.snd h iNew
  have hpb : u ≫ h = v ≫ iNew := pullback.condition
  have hπ := projection_lift W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p
  have hθ := θ_projection W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p
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
    _ = lift (v ≫ iNew) (u ≫ t) ≫
          (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ⊗ₘ
            𝟙 (J.obj (time.obj (a W z U K incl f e s he hs hfU heU hsU p)))) ≫
              oldTimed.parameter (a W z U K incl f e s he hs hfU heU hsU p) := by
        rw [hpb]
    _ = _ := by
        rw [← Category.assoc, lift_tensor, Category.assoc, hi]

private theorem outer_target {S : NecklaceCode}
    (p : C W z U K incl f e s he hs hfU heU hsU)
    (iNew : S.toSSet ⟶ (newCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode W K f O
      (a W z U K incl f e s he hs hfU heU hsU p)).toSSet)
    (hi : iNew ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map = iOld) :
    iNew ≫
        ((triangleTarget W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p).map
          ≫ Q.map =
      iOld ≫ (oldTimed.collapse.app
        (a W z U K incl f e s he hs hfU heU hsU p)).map ≫ Q.map := by
  change iNew ≫
      (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ≫
        (oldTimed.collapse.app
          (a W z U K incl f e s he hs hfU heU hsU p)).map) ≫ Q.map = _
  have h := congrArg (fun v : S.toSSet ⟶
      (oldCode W K f O (a W z U K incl f e s he hs hfU heU hsU p)).toSSet ↦
        v ≫ (oldTimed.collapse.app
          (a W z U K incl f e s he hs hfU heU hsU p)).map ≫ Q.map) hi
  simpa only [Category.assoc] using h

private theorem piece_raw {S : NecklaceCode}
    (p : C W z U K incl f e s he hs hfU heU hsU)
    (iNew : S.toSSet ⟶ (newCode (P := P) (R := R)
      W z U K incl f e s he hs hfU heU hsU p).toSSet)
    (iOld : S.toSSet ⟶ (oldCode W K f O
      (a W z U K incl f e s he hs hfU heU hsU p)).toSSet)
    (hi : iNew ≫
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map = iOld)
    (d : std.obj ((degree W z U K incl f e s he hs hfU heU hsU).obj p) ⟶
      TripleBeadEndpointLabel.labels W S)
    (hc : d = std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫
      oldCoefficient W K f O (a W z U K incl f e s he hs hfU heU hsU p) ≫
        pre W iOld) :
    lift (pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew)
      (pullback.fst
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew ≫
          (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        realizedLabel S.toSSet W
          ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
          (SSet.yonedaEquiv d) =
      pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p) iNew ≫
          iNew ≫
            ((triangleTarget W z U K incl f e s he hs hfU heU hsU
              O time Q oldTimed).app p).map ≫ Q.map := by
  let b := a W z U K incl f e s he hs hfU heU hsU p
  let h := native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
  let v := pullback.snd h iNew
  let u := pullback.fst h iNew
  have hp := piece_parameter W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p iNew iOld hi
  have hr : JTComposedPrismLabels.rawProduct W (oldTimed.parameter b)
      (oldCoefficient W K f O b) =
      fst (oldCode W K f O b).toSSet (J.obj (time.obj b)) ≫
        ((oldTimed.collapse.app b).map ≫ Q.map) := by
    simpa only [Category.assoc] using old_raw W K f O time Q oldTimed b
  have hraw := outer_raw W ((α W z U K incl f e s he hs hfU heU hsU).app p)
    iOld v (u ≫ (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p)
    (u ≫ clock W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
    (oldTimed.parameter b) (oldCoefficient W K f O b) d
    ((oldTimed.collapse.app b).map ≫ Q.map) hc hp hr
  have ht := outer_target W z U K incl f e s he hs hfU heU hsU
    O time Q oldTimed p iNew iOld hi
  calc
    _ = v ≫ iOld ≫ (oldTimed.collapse.app b).map ≫ Q.map := hraw
    _ = v ≫ iNew ≫
          ((triangleTarget W z U K incl f e s he hs hfU heU hsU
            O time Q oldTimed).app p).map ≫ Q.map := by
      simpa only [Category.assoc] using congrArg (fun g ↦ v ≫ g) ht.symm

private theorem left_coefficient
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    (newData W z U K incl f e s he hs hfU heU hsU O p).left =
      std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫
        oldCoefficient W K f O (a W z U K incl f e s he hs hfU heU hsU p) ≫
          pre W (tripleRightT
            (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
            (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))) := by
  let b := a W z U K incl f e s he hs hfU heU hsU p
  have hc := JTWhiskeredGraphRaw.coefficient_left W (oldData W K f O b)
  change oldCoefficient W K f O b ≫
    pre W (tripleRightT (P.obj b) (single 0) (R.obj b)) = O.left b at hc
  change std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫ O.left b = _
  simpa only [Category.assoc] using congrArg
    (fun q ↦ std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫ q) hc.symm

private theorem right_coefficient
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    (newData W z U K incl f e s he hs hfU heU hsU O p).right =
      std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫
        oldCoefficient W K f O (a W z U K incl f e s he hs hfU heU hsU p) ≫
          pre W (tripleRightV
            (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
            (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))) := by
  let b := a W z U K incl f e s he hs hfU heU hsU p
  have hc := JTWhiskeredGraphRaw.coefficient_right W (oldData W K f O b)
  change oldCoefficient W K f O b ≫
    pre W (tripleRightV (P.obj b) (single 0) (R.obj b)) = O.right b at hc
  change std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫ O.right b = _
  simpa only [Category.assoc] using congrArg
    (fun q ↦ std.map ((α W z U K incl f e s he hs hfU heU hsU).app p) ≫ q) hc.symm

private abbrev leftNew (p : C W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightT (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))
private abbrev leftOld (p : C W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightT (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))
private abbrev rightNew (p : C W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightV (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 2) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))
private abbrev rightOld (p : C W z U K incl f e s he hs hfU heU hsU) :=
  tripleRightV (P.obj (a W z U K incl f e s he hs hfU heU hsU p))
    (single 0) (R.obj (a W z U K incl f e s he hs hfU heU hsU p))

/-- The exact raw equation on the full left native inverse image follows
from the original full-time `Family.rawProduct` equation. -/
theorem left_raw (p : C W z U K incl f e s he hs hfU heU hsU) :
    lift (pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (leftNew W z U K incl f e s he hs hfU heU hsU p))
      (pullback.fst
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (leftNew W z U K incl f e s he hs hfU heU hsU p) ≫
          (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        realizedLabel (P.obj (a W z U K incl f e s he hs hfU heU hsU p)).toSSet W
          ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
          (SSet.yonedaEquiv
            (newData W z U K incl f e s he hs hfU heU hsU O p).left) =
      pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (leftNew W z U K incl f e s he hs hfU heU hsU p) ≫
          leftNew W z U K incl f e s he hs hfU heU hsU p ≫
            ((triangleTarget W z U K incl f e s he hs hfU heU hsU
              O time Q oldTimed).app p).map ≫ Q.map :=
  piece_raw W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
    (leftNew W z U K incl f e s he hs hfU heU hsU p)
    (leftOld W z U K incl f e s he hs hfU heU hsU p)
    (native_left W z U K incl f e s he hs hfU heU hsU O p)
    (newData W z U K incl f e s he hs hfU heU hsU O p).left
    (left_coefficient W z U K incl f e s he hs hfU heU hsU O p)

/-- The exact raw equation on the full right native inverse image follows
from the same original full-time `Family.rawProduct` equation. -/
theorem right_raw (p : C W z U K incl f e s he hs hfU heU hsU) :
    lift (pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (rightNew W z U K incl f e s he hs hfU heU hsU p))
      (pullback.fst
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (rightNew W z U K incl f e s he hs hfU heU hsU p) ≫
          (θ W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) ≫
        realizedLabel (R.obj (a W z U K incl f e s he hs hfU heU hsU p)).toSSet W
          ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
          (SSet.yonedaEquiv
            (newData W z U K incl f e s he hs hfU heU hsU O p).right) =
      pullback.snd
        (native W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p)
        (rightNew W z U K incl f e s he hs hfU heU hsU p) ≫
          rightNew W z U K incl f e s he hs hfU heU hsU p ≫
            ((triangleTarget W z U K incl f e s he hs hfU heU hsU
              O time Q oldTimed).app p).map ≫ Q.map :=
  piece_raw W z U K incl f e s he hs hfU heU hsU O time Q oldTimed p
    (rightNew W z U K incl f e s he hs hfU heU hsU p)
    (rightOld W z U K incl f e s he hs hfU heU hsU p)
    (native_right W z U K incl f e s he hs hfU heU hsU O p)
    (newData W z U K incl f e s he hs hfU heU hsU O p).right
    (right_coefficient W z U K incl f e s he hs hfU heU hsU O p)

end
end DaggerModels.PartII.JTChosenSeamOuterRaw
