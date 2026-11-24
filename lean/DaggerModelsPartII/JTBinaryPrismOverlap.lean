import DaggerModelsPartII.JTBinaryPrismRealization
import DaggerModelsPartII.JTTargetIntervalOverMapping
import DaggerModelsPartII.JTBinaryPrismParameter
import OriginalWedgeCutFlags

/-!
# The native joint overlap contains the whole binary connector
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismOverlap

open JTTargetJointMarks JTTargetIntervalPullback JTTargetIntervalGluing
open JTBinaryPrismRealization JTProjectiveOrderedFiberComparison
open DaggerOriginalProductGadget

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev A := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- The literal joint of the wedge, using the native cut construction. -/
def joint (V Z : NecklaceCode) : Joint (wedge V Z) :=
  ⟨wedgeCutJoint V Z, wedgeCutJoint_mem V Z⟩

private theorem joint_point (V Z : NecklaceCode) :
    JTGraphBinaryTraversal.joint V Z = pointAt (wedge V Z) (ULift.up (joint V Z).val) := by
  rw [JTGraphBinaryTraversal.joint, pointAt_comp, wedgeιLeft_vertices]
  rfl

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)

private abbrev cut := joint P.code Q.code
private abbrev f := collapse c e

/-- The original left side factors into the full left preimage interval. -/
def leftFactor :
    T.toSSet ⟶ (sourceInterval (f c e) ⟨0, (wedge P.code Q.code).first_mem⟩
      (cut (P := P) (Q := Q)) (Fin.zero_le _)).toSSet :=
  (JTTargetIntervalPullback.isPullback (f c e) _ (cut (P := P) (Q := Q)) (Fin.zero_le _)).lift
    (tripleRightT T A U) (c.map ≫ (wedgeLeftCutHom P.code Q.code).map) (by
      rw [collapse_left_map, Category.assoc]
      exact congrArg (fun h ↦ c.map ≫ h) (wedgeLeftCutHom_fac P.code Q.code).symm)

/-- The original right side factors into the full right preimage interval. -/
def rightFactor :
    U.toSSet ⟶ (sourceInterval (f c e) (cut (P := P) (Q := Q))
      ⟨Fin.last (wedge P.code Q.code).len, (wedge P.code Q.code).last_mem⟩
      (Fin.le_last _)).toSSet :=
  (JTTargetIntervalPullback.isPullback (f c e) (cut (P := P) (Q := Q)) _ (Fin.le_last _)).lift
    (tripleRightV T A U) (e.map ≫ (wedgeRightCutHom P.code Q.code).map) (by
      rw [collapse_right_map, Category.assoc]
      exact congrArg (fun h ↦ e.map ≫ h) (wedgeRightCutHom_fac P.code Q.code).symm)

theorem leftFactor_fac :
    leftFactor c e ≫ leftInclusion (f c e) (cut (P := P) (Q := Q)) =
      tripleRightT T A U :=
  (JTTargetIntervalPullback.isPullback (f c e) _ _ (Fin.zero_le _)).lift_fst _ _ _

theorem rightFactor_fac :
    rightFactor c e ≫ rightInclusion (f c e) (cut (P := P) (Q := Q)) =
      tripleRightV T A U :=
  (JTTargetIntervalPullback.isPullback (f c e) _ _ (Fin.le_last _)).lift_fst _ _ _

private abbrev jointCode (V Z : NecklaceCode) :=
  intervalCode (wedge V Z) (joint V Z).val (joint V Z).val le_rfl

/-- The whole one-bead connector lies inside the overlap of the two
actual inverse-image intervals, including when those intervals have
other collapsed source beads at the joint. -/
def connectorFactor :
    A.toSSet ⟶ (sourceInterval (f c e) (cut (P := P) (Q := Q))
      (cut (P := P) (Q := Q)) le_rfl).toSSet :=
  (JTTargetIntervalPullback.isPullback (f c e)
      (cut (P := P) (Q := Q)) (cut (P := P) (Q := Q)) le_rfl).lift
    (tripleRightU T A U) (term A.toSSet ≫ pointAt (jointCode P.code Q.code) (ULift.up 0)) (by
      rw [collapse_middle_map, joint_point, Category.assoc]
      exact congrArg (fun h ↦ term A.toSSet ≫ h)
        (intervalPoint_first (wedge P.code Q.code) _ _ le_rfl).symm)

theorem connectorFactor_fac :
    connectorFactor c e ≫ middleInclusion (f c e) (cut (P := P) (Q := Q)) =
      tripleRightU T A U :=
  (JTTargetIntervalPullback.isPullback (f c e) _ _ le_rfl).lift_fst _ _ _

/-- The connector is embedded monomorphically in the full overlap. -/
theorem connectorFactor_mono : Mono (connectorFactor c e) := by
  have h : Mono (tripleRightU.{0} T A U) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        apply (mono_iff_injective _).mpr
        exact (wedgeRight_injective T (wedge A U)).comp (wedgeLeft_injective A U)
  exact mono_of_mono_fac (connectorFactor_fac c e)


/-- The full common interval of the joined collapse over the original target joint. -/
abbrev commonInterval :=
  sourceInterval (f c e) (cut (P := P) (Q := Q)) (cut (P := P) (Q := Q)) le_rfl

private abbrev lastJoint (V : NecklaceCode) : Joint V := ⟨Fin.last V.len, V.last_mem⟩
private abbrev firstJoint (V : NecklaceCode) : Joint V := ⟨0, V.first_mem⟩

private abbrev leftEnd := lastJoint P.code
private abbrev rightEnd := firstJoint Q.code

private theorem leftEndpoint :
    pointAt.{0} P.code (ULift.up (Fin.last P.code.len)) ≫ wedgeιLeft P.code Q.code =
      pointAt (NecklacesOver.wedge P Q).code (ULift.up (cut (P := P) (Q := Q)).val) :=
  joint_point P.code Q.code

private theorem rightEndpoint :
    pointAt.{0} Q.code (ULift.up 0) ≫ wedgeιRight P.code Q.code =
      pointAt (NecklacesOver.wedge P Q).code (ULift.up (cut (P := P) (Q := Q)).val) :=
  (wedge_comm P.code Q.code).symm.trans (leftEndpoint (P := P) (Q := Q))

/-- The entire final plateau of the left collapse lies in the joined overlap. -/
def leftPlateauFactor :
    (sourceInterval c (leftEnd (P := P)) (leftEnd (P := P)) le_rfl).toSSet ⟶
      (commonInterval c e).toSSet :=
  (middlePB (f c e) (cut (P := P) (Q := Q))).lift
    (middleInclusion c (leftEnd (P := P)) ≫ tripleRightT T A U)
    (middlePoint c (leftEnd (P := P))) (by
      rw [Category.assoc, collapse_left_map, ← Category.assoc,
        (middlePB c (leftEnd (P := P))).w, Category.assoc, leftEndpoint (P := P) (Q := Q)])

/-- The entire initial plateau of the right collapse lies in the joined overlap. -/
def rightPlateauFactor :
    (sourceInterval e (rightEnd (Q := Q)) (rightEnd (Q := Q)) le_rfl).toSSet ⟶
      (commonInterval c e).toSSet :=
  (middlePB (f c e) (cut (P := P) (Q := Q))).lift
    (middleInclusion e (rightEnd (Q := Q)) ≫ tripleRightV T A U)
    (middlePoint e (rightEnd (Q := Q))) (by
      rw [Category.assoc, collapse_right_map, ← Category.assoc,
        (middlePB e (rightEnd (Q := Q))).w, Category.assoc, rightEndpoint (P := P) (Q := Q)])

private theorem leftPlateauFactor_fac :
    leftPlateauFactor c e ≫ middleInclusion (f c e) (cut (P := P) (Q := Q)) =
      middleInclusion c (leftEnd (P := P)) ≫ tripleRightT T A U :=
  (middlePB (f c e) (cut (P := P) (Q := Q))).lift_fst _ _ _

private theorem rightPlateauFactor_fac :
    rightPlateauFactor c e ≫ middleInclusion (f c e) (cut (P := P) (Q := Q)) =
      middleInclusion e (rightEnd (Q := Q)) ≫ tripleRightV T A U :=
  (middlePB (f c e) (cut (P := P) (Q := Q))).lift_fst _ _ _

private theorem plateauDegree
    {S V : NecklaceCode} (g : S ⟶ V) (j : Joint V) {n : ℕ}
    (u : S.toSSet.obj (op ⦋n⦌)) (v : (Δ[0] : SSet.{0}).obj (op ⦋n⦌))
    (h : g.map.app _ u = (pointAt V (ULift.up j.val)).app _ v) :
    ∃ a, (middleInclusion g j).app (op ⦋n⦌) a = u := by
  have hp := (middlePB g j).map ((evaluation _ _).obj (op ⦋n⦌))
  obtain ⟨a, ha, _⟩ := Types.exists_of_isPullback hp u v h
  exact ⟨a, ha⟩

private theorem include_injective (g : NecklaceCode.Hom.{0} T U) (j : Joint U) (n : ℕ) :
    Function.Injective ((middleInclusion g j).app (op ⦋n⦌)) :=
  intervalι_injective T _ _ _

/-- Every simplex of the actual overlap comes from one of the two side
plateaus or the full connector. This holds also for collapsed side beads. -/
theorem commonInterval_degree_cover (n : ℕ)
    (z : (commonInterval c e).toSSet.obj (op ⦋n⦌)) :
    (∃ x, (leftPlateauFactor c e).app (op ⦋n⦌) x = z) ∨
      (∃ x, (connectorFactor c e).app (op ⦋n⦌) x = z) ∨
      (∃ x, (rightPlateauFactor c e).app (op ⦋n⦌) x = z) := by
  let j := cut (P := P) (Q := Q)
  let incl := middleInclusion (f c e) j
  let pt := (middlePoint (f c e) j).app (op ⦋n⦌) z
  have hz : (f c e).map.app (op ⦋n⦌) (incl.app _ z) =
      (pointAt (NecklacesOver.wedge P Q).code (ULift.up j.val)).app _ pt :=
    congrFun (NatTrans.congr_app (middlePB (f c e) j).w (op ⦋n⦌)) z
  rcases wedge_degree_cover T (wedge A U) (incl.app _ z) with ⟨u, hu⟩ | ⟨u, hu⟩
  · have h : (tripleRightT T A U).app (op ⦋n⦌) u = incl.app _ z := hu
    have h' := (congrFun (NatTrans.congr_app (collapse_left_map c e) (op ⦋n⦌)) u).symm
    change (wedgeιLeft P.code Q.code).app (op ⦋n⦌) (c.map.app _ u) =
      (f c e).map.app _ ((tripleRightT T A U).app _ u) at h'
    rw [h, hz, ← leftEndpoint (P := P) (Q := Q)] at h'
    obtain ⟨u', hu'⟩ := plateauDegree c (leftEnd (P := P)) u pt
      (wedgeLeft_injective P.code Q.code h')
    refine Or.inl ⟨u', include_injective (f c e) j n ?_⟩
    have hfac := congrFun (NatTrans.congr_app (leftPlateauFactor_fac c e) (op ⦋n⦌)) u'
    exact hfac.trans ((congrArg ((tripleRightT T A U).app (op ⦋n⦌)) hu').trans h)
  · rcases wedge_degree_cover A U u with ⟨u', hu'⟩ | ⟨u', hu'⟩
    · refine Or.inr (Or.inl ⟨u', include_injective (f c e) j n ?_⟩)
      have hfac := congrFun (NatTrans.congr_app (connectorFactor_fac c e) (op ⦋n⦌)) u'
      exact hfac.trans ((congrArg ((wedgeιRight T (wedge A U)).app (op ⦋n⦌)) hu').trans hu)
    · have h : (tripleRightV T A U).app (op ⦋n⦌) u' = incl.app _ z :=
        (congrArg ((wedgeιRight T (wedge A U)).app (op ⦋n⦌)) hu').trans hu
      have h' := (congrFun (NatTrans.congr_app (collapse_right_map c e) (op ⦋n⦌)) u').symm
      change (wedgeιRight P.code Q.code).app (op ⦋n⦌) (e.map.app _ u') =
        (f c e).map.app _ ((tripleRightV T A U).app _ u') at h'
      rw [h, hz, ← rightEndpoint (P := P) (Q := Q)] at h'
      obtain ⟨u'', hu''⟩ := plateauDegree e (rightEnd (Q := Q)) u' pt
        (wedgeRight_injective P.code Q.code h')
      refine Or.inr (Or.inr ⟨u'', include_injective (f c e) j n ?_⟩)
      have hfac := congrFun (NatTrans.congr_app (rightPlateauFactor_fac c e) (op ⦋n⦌)) u''
      exact hfac.trans ((congrArg ((tripleRightV T A U).app (op ⦋n⦌)) hu'').trans h)

/-- The three original pieces detect equality of maps out of the full overlap. -/
theorem commonInterval_hom_ext {X : SSet.{0}}
    {g h : (commonInterval c e).toSSet ⟶ X}
    (hl : leftPlateauFactor c e ≫ g = leftPlateauFactor c e ≫ h)
    (hm : connectorFactor c e ≫ g = connectorFactor c e ≫ h)
    (hr : rightPlateauFactor c e ≫ g = rightPlateauFactor c e ≫ h) : g = h := by
  apply NatTrans.ext
  funext n z
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  rcases commonInterval_degree_cover c e n z with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact congrFun (NatTrans.congr_app hl _) x
  · exact congrFun (NatTrans.congr_app hm _) x
  · exact congrFun (NatTrans.congr_app hr _) x


/-- The same three restrictions detect equality for the complete time
parameter, in every simplicial degree. -/
theorem commonInterval_tensor_hom_ext {K X : SSet.{0}}
    {g h : (commonInterval c e).toSSet ⊗ K ⟶ X}
    (hl : (leftPlateauFactor c e ⊗ₘ 𝟙 K) ≫ g =
      (leftPlateauFactor c e ⊗ₘ 𝟙 K) ≫ h)
    (hm : (connectorFactor c e ⊗ₘ 𝟙 K) ≫ g =
      (connectorFactor c e ⊗ₘ 𝟙 K) ≫ h)
    (hr : (rightPlateauFactor c e ⊗ₘ 𝟙 K) ≫ g =
      (rightPlateauFactor c e ⊗ₘ 𝟙 K) ≫ h) : g = h := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  funext zt
  rcases zt with ⟨z, t⟩
  rcases commonInterval_degree_cover c e n z with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hl (op ⦋n⦌)) (a, t)
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hm (op ⦋n⦌)) (a, t)
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hr (op ⦋n⦌)) (a, t)


section Parameter

open CartesianMonoidalCategory
open JTBinaryPrismParameter (parameter parameter_left parameter_middle parameter_right
  connector leftBoundary rightBoundary connector_eq_of_boundary)

variable (K : SimplexCategory) (I : SSet.{0})
variable (s : T.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K)
variable (t : U.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K)

/-- The actual joined groupoid parameter on the full native overlap. -/
def overlapParameter : (commonInterval c e).toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K :=
  (middleInclusion (f c e) (cut (P := P) (Q := Q)) ⊗ₘ 𝟙 I) ≫ parameter T U K I s t

private theorem tensor_restrict {X Y Z L M : SSet.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (k : Z ⊗ L ⟶ M) :
    (a ⊗ₘ 𝟙 L) ≫ (b ⊗ₘ 𝟙 L) ≫ k = ((a ≫ b) ⊗ₘ 𝟙 L) ≫ k := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem overlapParameter_left :
    (leftPlateauFactor c e ⊗ₘ 𝟙 I) ≫ overlapParameter c e K I s t =
      (middleInclusion c (leftEnd (P := P)) ⊗ₘ 𝟙 I) ≫ s := by
  rw [overlapParameter, tensor_restrict, leftPlateauFactor_fac, ← tensor_restrict, parameter_left]

theorem overlapParameter_middle :
    (connectorFactor c e ⊗ₘ 𝟙 I) ≫ overlapParameter c e K I s t =
      connector T U K I s t := by
  rw [overlapParameter, tensor_restrict, connectorFactor_fac, parameter_middle]

theorem overlapParameter_right :
    (rightPlateauFactor c e ⊗ₘ 𝟙 I) ≫ overlapParameter c e K I s t =
      (middleInclusion e (rightEnd (Q := Q)) ⊗ₘ 𝟙 I) ≫ t := by
  rw [overlapParameter, tensor_restrict, rightPlateauFactor_fac, ← tensor_restrict, parameter_right]

private theorem leftBoundary_eq_of_plateau {s' : T.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K}
    (hs : (middleInclusion c (leftEnd (P := P)) ⊗ₘ 𝟙 I) ≫ s =
      (middleInclusion c (leftEnd (P := P)) ⊗ₘ 𝟙 I) ≫ s') :
    leftBoundary T K I s = leftBoundary T K I s' := by
  let j := leftEnd (P := P)
  let V := sourceInterval c j j le_rfl
  let p : Δ[0] ⟶ V.toSSet := pointAt V (ULift.up (Fin.last V.len))
  have hp : p ≫ middleInclusion c j = pointAt T (ULift.up (Fin.last T.len)) :=
    JTTargetIntervalOverMapping.right_last P.code j (Over.mk c)
  unfold leftBoundary
  rw [← hp, ← tensor_restrict, ← tensor_restrict, hs]

private theorem rightBoundary_eq_of_plateau {t' : U.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K}
    (ht : (middleInclusion e (rightEnd (Q := Q)) ⊗ₘ 𝟙 I) ≫ t =
      (middleInclusion e (rightEnd (Q := Q)) ⊗ₘ 𝟙 I) ≫ t') :
    rightBoundary U K I t = rightBoundary U K I t' := by
  let j := rightEnd (Q := Q)
  let V := sourceInterval e j j le_rfl
  let p : Δ[0] ⟶ V.toSSet := pointAt V (ULift.up 0)
  have hp : p ≫ middleInclusion e j = pointAt U (ULift.up 0) :=
    JTTargetIntervalOverMapping.left_first Q.code j (Over.mk e)
  unfold rightBoundary
  rw [← hp, ← tensor_restrict, ← tensor_restrict, ht]

/-- Agreement of the two complete side parameters on their actual plateaus
implies agreement on the entire joined overlap, including the connector. -/
theorem overlapParameter_eq_of_plateaus
    {s' : T.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K}
    {t' : U.toSSet ⊗ I ⟶ GroupoidSimplex.parameter.obj K}
    (hs : (middleInclusion c (leftEnd (P := P)) ⊗ₘ 𝟙 I) ≫ s =
      (middleInclusion c (leftEnd (P := P)) ⊗ₘ 𝟙 I) ≫ s')
    (ht : (middleInclusion e (rightEnd (Q := Q)) ⊗ₘ 𝟙 I) ≫ t =
      (middleInclusion e (rightEnd (Q := Q)) ⊗ₘ 𝟙 I) ≫ t') :
    overlapParameter c e K I s t = overlapParameter c e K I s' t' := by
  apply commonInterval_tensor_hom_ext c e
  · rw [overlapParameter_left, overlapParameter_left]
    exact hs
  · rw [overlapParameter_middle, overlapParameter_middle]
    exact connector_eq_of_boundary T U K I s t
      (leftBoundary_eq_of_plateau c K I s hs) (rightBoundary_eq_of_plateau e K I t ht)
  · rw [overlapParameter_right, overlapParameter_right]
    exact ht

end Parameter

end

end DaggerModels.PartII.JTBinaryPrismOverlap
