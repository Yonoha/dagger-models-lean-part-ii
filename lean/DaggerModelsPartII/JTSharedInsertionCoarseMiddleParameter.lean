import DaggerModelsPartII.JTSharedInsertionCoarseMiddleSupport
import DaggerModelsPartII.JTSharedInsertionCoarseGraph
import DaggerModelsPartII.JTJointSubdivisionBeadNormalization
import DaggerModelsPartII.JTNativeEndpointPadding
import DaggerModelsPartII.JTJointBeadOverlapDiagram
import DaggerModelsPartII.JTOrdinalInverseFaceParameterDiagram

/-!
# The given actual coarse-middle parameter factors through its full chart support

Collapse only the two middle correction edges, retain the entire old chart and
original time, and use the existing whole timed chart support. The final factor
must recover the GIVEN graph parameter; no new parameter section is chosen.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseMiddleParameter

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev E := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem over_first {X : SSet.{0}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    pointAt P.code (ULift.up 0) ≫ P.map = SSet.yonedaEquiv.symm a := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    SSet.yonedaEquiv.apply_symm_apply] using P.first

private theorem over_last {X : SSet.{0}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    pointAt P.code (ULift.up (Fin.last P.code.len)) ≫ P.map =
      SSet.yonedaEquiv.symm b := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    SSet.yonedaEquiv.apply_symm_apply] using P.last

private theorem padded_factor {X : SSet.{0}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    (NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver E a)
      (NecklacesOver.wedge P (JTCorrectedIntervalAssembly.constantOver E b))).map =
      (NecklaceCode.collapse E P.code E).map ≫ P.map := by
  dsimp only [NecklacesOver.wedge, JTCorrectedIntervalAssembly.constantOver]
  apply tripleRight_hom_ext (T := E) (U := P.code) (V := E)
  · change wedgeιLeft E (wedge P.code E) ≫ _ = _
    rw [wedgeDesc_left, ← Category.assoc, NecklaceCode.collapse_left,
      Category.assoc, over_first]
    congr 1
  · change (wedgeιLeft P.code E ≫ wedgeιRight E (wedge P.code E)) ≫ _ = _
    rw [Category.assoc, wedgeDesc_right, wedgeDesc_left,
      ← Category.assoc, NecklaceCode.collapse_middle, Category.id_comp]
  · change (wedgeιRight P.code E ≫ wedgeιRight E (wedge P.code E)) ≫ _ = _
    rw [Category.assoc, wedgeDesc_right, wedgeDesc_right,
      ← Category.assoc, NecklaceCode.collapse_right, Category.assoc, over_last]
    congr 1

private theorem corrected_middle (T : NecklaceCode) (a c : Fin (T.len + 1))
    (hac : a ≤ c) :
    tripleRightU
        (wedge (intervalOver.{0} T 0 a (Fin.zero_le a)).code E)
        (wedge E (wedge (intervalOver.{0} T a c hac).code E))
        (wedge E (intervalOver.{0} T c (Fin.last T.len) (Fin.le_last c)).code) ≫
      (JTCorrectedCoarseIntervalComparison.assembly T a c hac).map =
        (NecklaceCode.collapse E (intervalOver.{0} T a c hac).code E).map ≫
          (intervalOver.{0} T a c hac).map := by
  change _ ≫ (JTCorrectedCoarseIntervalComparison.coarseOver T a c hac).map = _
  dsimp only [JTCorrectedCoarseIntervalComparison.coarseOver, NecklacesOver.wedge,
    JTCorrectedIntervalAssembly.constantOver]
  unfold tripleRightU
  rw [Category.assoc, wedgeDesc_right, wedgeDesc_left]
  exact padded_factor (intervalOver.{0} T a c hac)

private theorem cast_restrict {X : SSet.{0}} {N C T : NecklaceCode}
    (e : N = C) (i : X ⟶ N.toSSet) (i' : X ⟶ C.toSSet) (hi : HEq i i') (g : C ⟶ T) :
    i ≫ (eqToHom e ≫ g).map = i' ≫ g.map := by
  subst C
  have he : i = i' := eq_of_heq hi
  subst i'
  change i ≫ (𝟙 _ ≫ g.map) = i ≫ g.map
  rw [Category.id_comp]

private def familyMiddleInclusion {C : Type} [SmallCategory C]
    {W : SegalLocalizers.ReverseDaggerSpace.{0}}
    {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}
    {P M R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
    (G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K) :
    M ⋙ NecklaceCode.simplicialFunctor ⟶
      JTParametrizedTargetFamilies.codes G.labels ⋙ NecklaceCode.simplicialFunctor where
  app p := tripleRightU (P.obj p) (M.obj p) (R.obj p)
  naturality {p q} f := by
    have hn : (JTParametrizedTargetFamilies.codes G.labels).map f =
        wedgeMap (P.map f) (wedgeMap (M.map f) (R.map f)) :=
      congrArg Prod.fst (JTVariableMiddleWhiskeredDiagram.Family.arrow_projection G f)
    change (M.map f).map ≫ tripleRightU _ _ _ =
      tripleRightU _ _ _ ≫ ((JTParametrizedTargetFamilies.codes G.labels).map f).map
    rw [hn]
    symm
    unfold tripleRightU
    rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left, Category.assoc]

section Pullback

variable {C : Type} [SmallCategory C] {X Y Z : C ⥤ SSet.{0}}
variable (h : X ⟶ Z) (i : Y ⟶ Z)

private def pointwisePullback : C ⥤ SSet.{0} where
  obj p := pullback (h.app p) (i.app p)
  map {p q} f := pullback.map (h.app p) (i.app p) (h.app q) (i.app q)
    (X.map f) (Y.map f) (Z.map f) (h.naturality f).symm (i.naturality f).symm
  map_id p := by
    simp only [X.map_id, Y.map_id, Z.map_id]
    exact pullback.map_id
  map_comp f g := by
    rw [pullback.map_comp]
    simp only [X.map_comp, Y.map_comp, Z.map_comp]

private def pullbackFirst : pointwisePullback h i ⟶ X where
  app p := pullback.fst (h.app p) (i.app p)
  naturality _ _ _ := pullback.lift_fst _ _ _

private def pullbackSecond : pointwisePullback h i ⟶ Y where
  app p := pullback.snd (h.app p) (i.app p)
  naturality _ _ _ := pullback.lift_snd _ _ _

private theorem pullback_factor_app {K S : C ⥤ SimplexCategory}
    (θ : X ⟶ K ⋙ J) (q : pointwisePullback h i ⟶ S ⋙ J) (u : S ⟶ K)
    (hq : q ≫ Functor.whiskerRight u J = pullbackFirst h i ≫ θ) (p : C) :
    pullback.fst (h.app p) (i.app p) ≫ θ.app p = q.app p ≫ J.map (u.app p) :=
  (NatTrans.congr_app hq p).symm

end Pullback

private theorem single_std_natural {m n : ℕ} (f : single m ⟶ single n) :
    f.map ≫ (singleIso n).hom = (singleIso m).hom ≫
      std.map (SimplexCategory.Hom.mk (orderMap f.map) : ⦋m⦌ ⟶ ⦋n⦌) := by
  have h := map_inclusion f.map
  rw [← singleIso_hom m, ← singleIso_hom n] at h
  exact h

private theorem iso_native_factor {B S : NecklaceCode} {X : SSet.{0}}
    (e : B ≅ S) (n : B.toSSet ⟶ X) : e.hom.map ≫ (e.inv.map ≫ n) = n := by
  have he : e.hom.map ≫ e.inv.map = 𝟙 B.toSSet :=
    congrArg NecklaceCode.Hom.map e.hom_inv_id
  rw [← Category.assoc, he, Category.id_comp]

private def firstProjection {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) :
    JTGraphCoveredProductInterface.product N t ⟶ N ⋙ NecklaceCode.simplicialFunctor where
  app p := fst (N.obj p).toSSet (J.obj (t.obj p))
  naturality _ _ _ := tensorHom_fst _ _

private def secondProjection {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) :
    JTGraphCoveredProductInterface.product N t ⟶ t ⋙ J where
  app p := snd (N.obj p).toSSet (J.obj (t.obj p))
  naturality _ _ _ := tensorHom_snd _ _

private def tensorPair {C : Type} [SmallCategory C] {X B T : C ⥤ SSet.{0}}
    (h : X ⟶ B) (q : X ⟶ T) : X ⟶ B.prod' T ⋙ MonoidalCategory.tensor SSet.{0} where
  app p := lift (h.app p) (q.app p)
  naturality {p r} f := by
    change X.map f ≫ lift (h.app r) (q.app r) =
      lift (h.app p) (q.app p) ≫ (B.map f ⊗ₘ T.map f)
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc] using h.naturality f
    · simpa only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc] using q.naturality f

private theorem inverseImage_pair {X B C T : SSet.{0}}
    (π : X ⟶ B ⊗ T) (i : C ⟶ B) :
    pullback.fst (π ≫ fst B T) i ≫ π =
      lift (pullback.snd (π ≫ fst B T) i ≫ i)
        (pullback.fst (π ≫ fst B T) i ≫ π ≫ snd B T) := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using
      (pullback.condition : pullback.fst (π ≫ fst B T) i ≫ (π ≫ fst B T) =
        pullback.snd (π ≫ fst B T) i ≫ i)
  · simp only [Category.assoc, lift_snd]

private theorem piece_parameter {X B C S : SSet.{0}} {k l t : SimplexCategory}
    (π : X ⟶ B ⊗ J.obj t) (θ : X ⟶ J.obj k) (n : B ⟶ C)
    (oldθ : C ⊗ J.obj t ⟶ J.obj l) (α : k ⟶ l)
    (hθ : θ ≫ J.map α = π ≫ ((n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ))
    (i : S ⟶ B) (iOld : S ⟶ C) (hi : i ≫ n = iOld) :
    (pullback.fst (π ≫ fst B (J.obj t)) i ≫ θ) ≫ J.map α =
      lift (pullback.snd (π ≫ fst B (J.obj t)) i ≫ iOld)
        (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π ≫ snd B (J.obj t)) ≫ oldθ := by
  calc
    _ = (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π) ≫
          (n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ := by
      rw [Category.assoc, hθ]
      simp only [Category.assoc]
    _ = lift (pullback.snd (π ≫ fst B (J.obj t)) i ≫ i)
          (pullback.fst (π ≫ fst B (J.obj t)) i ≫ π ≫ snd B (J.obj t)) ≫
            (n ⊗ₘ 𝟙 (J.obj t)) ≫ oldθ := by rw [inverseImage_pair]
    _ = _ := by
      rw [← Category.assoc, lift_map]
      simp only [Category.assoc, hi, Category.comp_id]

private theorem chart_parameter_value {X N T : SSet.{0}} {d : ℕ}
    {t s k : SimplexCategory} (m : N ⟶ (single d).toSSet)
    (i : (single d).toSSet ⟶ T) (h : X ⟶ N) (clock : X ⟶ J.obj t)
    (ψ : std.obj ⦋d⦌ ⊗ J.obj t ⟶ J.obj s) (u : s ⟶ k)
    (τ : T ⊗ J.obj t ⟶ J.obj k)
    (hψ : ψ ≫ J.map u = (((singleIso d).inv ≫ i) ⊗ₘ 𝟙 (J.obj t)) ≫ τ) :
    (lift (h ≫ m ≫ (singleIso d).hom) clock ≫ ψ) ≫ J.map u =
      lift (h ≫ m ≫ i) clock ≫ τ := by
  rw [Category.assoc, hψ, ← Category.assoc, lift_map]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]

private theorem componentwise_eq {C : Type} [SmallCategory C]
    {X Y : C ⥤ SSet.{0}} (f g : X ⟶ Y) (h : ∀ p, f.app p = g.app p) : f = g := by
  apply NatTrans.ext
  exact funext h

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The unchanged actual shared insertion source. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The actual adjacent chart, retaining every original source operator. -/
abbrev charts := JTSharedInsertionChoices.base F j ⋙
  JTSharedInsertionChoices.projection F j ⋙ JTJointSubdivisionInsertion.toCharts F j

/-- The actual padded coarse middle with both endpoint correction edges. -/
abbrev middleLabels := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairGapChainLabels.labels F j

/-- The complete native middle diagram. -/
abbrev middleNative := JTParametrizedTargetFamilies.codes (middleLabels F j)

/-- Collapse ONLY the two correction edges, naturally to the same original chart. -/
def middleCollapse : middleNative F j ⟶ charts F j ⋙ JTJointSubdivisionBeadCharts.native F j :=
  Functor.whiskerLeft (charts F j ⋙ JTJointSubdivisionBeadCharts.native F j)
    JTNativeEndpointPadding.collapse

/-- Identify that unchanged whole interval with the actual single-simplex chart. -/
def middleToChart : middleNative F j ⟶
    charts F j ⋙ JTJointSubdivisionBeadCharts.singleNative F j :=
  middleCollapse F j ≫
    Functor.whiskerLeft (charts F j) (JTJointSubdivisionBeadCharts.nativeIso F j).hom

/-- The whole native middle inclusion, natural under every original operator. -/
def middleInclusion : middleNative F j ⋙ NecklaceCode.simplicialFunctor ⟶
    JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j) ⋙
      NecklaceCode.simplicialFunctor :=
  familyMiddleInclusion (JTSharedInsertionCoarseLabels.family F j)

private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev T (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes L).obj ((pairs F j).obj p).1
private abbrev a (p : Index F j) := ((pairs F j).obj p).2.left.val
private abbrev c (p : Index F j) := ((pairs F j).obj p).2.right.val
private abbrev hac (p : Index F j) := ((pairs F j).obj p).2.le

private theorem code_eq (p : Index F j) :
    (JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)).obj p =
      (JTCorrectedCoarseIntervalComparison.coarseOver
        (T F j p) (a F j p) (c F j p) (hac F j p)).code :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

set_option maxHeartbeats 400000 in
private theorem middle_view (p : Index F j) : HEq ((middleInclusion F j).app p)
    (tripleRightU
      (wedge (intervalOver.{0} (T F j p) 0 (a F j p) (Fin.zero_le _)).code E)
      (wedge E (wedge (intervalOver.{0} (T F j p) (a F j p) (c F j p) (hac F j p)).code E))
      (wedge E (intervalOver.{0} (T F j p) (c F j p)
        (Fin.last (T F j p).len) (Fin.le_last _)).code)) := by
  rfl

set_option maxHeartbeats 400000 in
/-- The complete middle restriction agrees in ORIGINAL T, BEFORE any map to Q. -/
theorem middle_original_factor (p : Index F j) :
    (middleInclusion F j).app p ≫ ((JTSharedInsertionCoarseNative.assembly F j).app p).map =
      ((middleCollapse F j).app p).map ≫
        (JTJointSubdivisionBeadCharts.inclusions F j).app ((charts F j).obj p) := by
  rw [JTSharedInsertionCoarseNative.assembly_app]
  have h := cast_restrict (code_eq F j p) ((middleInclusion F j).app p) _
    (middle_view F j p) (JTCorrectedCoarseIntervalComparison.assembly
      (T F j p) (a F j p) (c F j p) (hac F j p))
  exact h.trans (corrected_middle (T F j p) (a F j p) (c F j p) (hac F j p))

private abbrev D := charts F j ⋙ JTJointSubdivisionBeadNormalization.degrees F j
private abbrev oldTime := JTSharedInsertionCoarseGraph.oldTime F j
private abbrev original := JTSharedInsertionCoarseGraph.original F j

/-- The complete natural chart simplex, including width zero. -/
def chartToSimplex : (charts F j ⋙ JTJointSubdivisionBeadCharts.singleNative F j) ⋙
    NecklaceCode.simplicialFunctor ⟶ D F j ⋙ std where
  app p := (singleIso ((D F j).obj p).len).hom
  naturality _ _ f := single_std_natural
    ((JTJointSubdivisionBeadCharts.singleNative F j).map ((charts F j).map f))

/-- The same complete middle assembly factor, expressed through the actual single chart. -/
theorem middle_native_factor (p : Index F j) :
    (middleInclusion F j).app p ≫ ((JTSharedInsertionCoarseNative.assembly F j).app p).map =
      ((middleToChart F j).app p).map ≫
        (JTJointSubdivisionBeadCharts.singleInclusions F j).app ((charts F j).obj p) := by
  rw [middle_original_factor]
  change ((middleCollapse F j).app p).map ≫ _ =
    (((middleCollapse F j).app p).map ≫
      ((JTJointSubdivisionBeadCharts.simplexIso F j ((charts F j).obj p)).hom).map) ≫
      (((JTJointSubdivisionBeadCharts.simplexIso F j ((charts F j).obj p)).inv).map ≫ _)
  rw [Category.assoc, iso_native_factor]

private abbrev vertexD := JTJointSubdivisionVertexSupport.toCharts F j ⋙
  JTJointSubdivisionBeadNormalization.degrees F j
private abbrev vertexO := JTJointSubdivisionVertexSupport.toCharts F j ⋙
  JTJointSubdivisionBeadCharts.base F j

private def vertexChartParameter : JTFullPrismSupportedDiagram.prisms (vertexD F j)
    (vertexO F j ⋙ time) ⟶ JTIncidentChartSupport.chartSupports F j ⋙ J where
  app p := JTJointSubdivisionVertexSupport.beadParameter F j p.1
  naturality {p q} f := by
    have h := JTJointSubdivisionBeadNormalization.native_natural F j f.val
    have h' : (singleIso ((vertexD F j).obj p).len).inv ≫
        JTJointSubdivisionBeadNormalization.inclusion F j p.1 ≫
        ((JTParametrizedTargetFamilies.codes L).map ((vertexO F j).map f)).map =
      std.map ((vertexD F j).map f) ≫ (singleIso ((vertexD F j).obj q).len).inv ≫
        JTJointSubdivisionBeadNormalization.inclusion F j q.1 := by
      simpa only [JTJointSubdivisionBeadNormalization.toJointInterval_fac] using h
    have hn := JTParametrizedBeadGraph.supportedFullBeadParameter_map
      (i := JTJointSubdivisionBeadNormalization.inclusion F j p.1)
      (i' := JTJointSubdivisionBeadNormalization.inclusion F j q.1) F
      ((vertexO F j).map f) ((vertexD F j).map f)
      ((Category.assoc _ _ _).trans h')
    exact hn

private theorem vertexChartParameter_factor
    (p : JTJointSubdivisionVertexSupport.VertexIndex F j) :
    (vertexChartParameter F j).app p ≫
        J.map ((JTIncidentChartSupport.chartInclusion F j).app p) =
      JTParametrizedBeadGraph.fullBeadParameter F ((vertexO F j).obj p)
        ((vertexD F j).obj p).len (JTJointSubdivisionBeadNormalization.inclusion F j p.1) :=
  JTPrismRectangle.supportedParameter_factor _

/-- The existing WHOLE timed overlap-chart parameter, typed on the same old support. -/
def chartParameter : JTFullPrismSupportedDiagram.prisms (D F j) (oldTime F j) ⟶
    JTSharedInsertionCoarseMiddleSupport.oldSupports F j ⋙ J :=
  Functor.whiskerLeft (JTSharedInsertionCoarseMiddleSupport.firstVertex F j)
    (vertexChartParameter F j)

/-- It recovers the actual original parameter on the ENTIRE native-chart time prism. -/
theorem chartParameter_factor (p : Index F j) :
    (chartParameter F j).app p ≫
        J.map ((JTSharedInsertionCoarseMiddleSupport.oldInclusion F j).app p) =
      JTParametrizedBeadGraph.fullBeadParameter F ((original F j).obj p)
        ((D F j).obj p).len
        (JTJointSubdivisionBeadNormalization.inclusion F j ((charts F j).obj p)) :=
  vertexChartParameter_factor F j ((JTSharedInsertionCoarseMiddleSupport.firstVertex F j).obj p)

private abbrev N := JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)

/-- Retain the GIVEN whole native coordinate of every original-time graph point. -/
def nativeProjection := JTSharedInsertionCoarseGraph.projection F j ≫
  firstProjection (N F j) (oldTime F j)

/-- Retain the ENTIRE original time, separately from the tuple/choice clock. -/
def clock := JTSharedInsertionCoarseGraph.projection F j ≫
  secondProjection (N F j) (oldTime F j)

/-- Each object is literally the complete middle inverse image, with all original arrows. -/
def middlePB := pointwisePullback (nativeProjection F j) (middleInclusion F j)

/-- Its original graph projection, not a chosen section. -/
def middleFirst := pullbackFirst (nativeProjection F j) (middleInclusion F j)

/-- Its complete native middle coordinate. -/
def middleSecond := pullbackSecond (nativeProjection F j) (middleInclusion F j)

/-- The GIVEN restricted graph parameter, with every coefficient value retained. -/
def givenParameter := middleFirst F j ≫ JTSharedInsertionCoarseGraph.parameter F j

/-- The complete middle maps naturally into the literal chart simplex. -/
def middleToSimplex := Functor.whiskerRight (middleToChart F j)
  NecklaceCode.simplicialFunctor ≫ chartToSimplex F j

/-- The literal chart coordinate together with the ENTIRE unchanged original time. -/
def middleChartTime := tensorPair (middleSecond F j ≫ middleToSimplex F j)
  (middleFirst F j ≫ clock F j)

/-- The existing full chart-support parameter on the complete middle inverse image. -/
def oldParameter := middleChartTime F j ≫ chartParameter F j

private def ambient_square (p : Index F j) :=
  (NatTrans.congr_app (JTSharedInsertionCoarseGraph.parameter_projection F j) p).trans
    (congrArg ((JTSharedInsertionCoarseGraph.projection F j).app p ≫ ·)
      (JTSharedInsertionCoarseGraph.coarseParameter_app F j p))

private def old_piece_equation (p : Index F j) :=
  piece_parameter (JTSharedInsertionCoarseGraph.projection F j |>.app p)
    (JTSharedInsertionCoarseGraph.parameter F j |>.app p)
    ((JTSharedInsertionCoarseNative.assembly F j).app p).map
    (F.parameter ((original F j).obj p))
    ((JTSharedInsertionChoices.toOriginal F j).app p) (ambient_square F j p)
    ((middleInclusion F j).app p)
    (((middleToChart F j).app p).map ≫
      (JTJointSubdivisionBeadCharts.singleInclusions F j).app ((charts F j).obj p))
    (middle_native_factor F j p)

private theorem oldParameter_value (p : Index F j) :
    (oldParameter F j).app p ≫
        J.map ((JTSharedInsertionCoarseMiddleSupport.oldInclusion F j).app p) =
      lift ((middleSecond F j).app p ≫ ((middleToChart F j).app p).map ≫
          (JTJointSubdivisionBeadCharts.singleInclusions F j).app ((charts F j).obj p))
        ((middleFirst F j).app p ≫ (clock F j).app p) ≫
        F.parameter ((original F j).obj p) :=
  chart_parameter_value ((middleToChart F j).app p).map
    ((JTJointSubdivisionBeadCharts.singleInclusions F j).app ((charts F j).obj p))
    ((middleSecond F j).app p) ((middleFirst F j).app p ≫ (clock F j).app p)
    ((chartParameter F j).app p)
    ((JTSharedInsertionCoarseMiddleSupport.oldInclusion F j).app p)
    (F.parameter ((original F j).obj p)) (chartParameter_factor F j p)

private def oldSquareComponent (p : Index F j) :=
  (old_piece_equation F j p).trans (oldParameter_value F j p).symm

set_option maxHeartbeats 400000 in
/-- The GIVEN coefficient parameter and the old support parameter agree through alpha. -/
def oldParameter_square := componentwise_eq
  (givenParameter F j ≫ Functor.whiskerRight (JTSharedInsertionChoices.toOriginal F j) J)
  (oldParameter F j ≫
    Functor.whiskerRight (JTSharedInsertionCoarseMiddleSupport.oldInclusion F j) J)
  (oldSquareComponent F j)

/-- Canonically factor the GIVEN middle parameter through the FULL inverse-image face. -/
def factor := JTOrdinalInverseFaceParameterDiagram.factor
  (JTSharedInsertionCoarseMiddleSupport.oldSupports F j)
  (JTSharedInsertionCoarseMiddleSupport.oldDegrees F j)
  (JTSharedInsertionCoarseMiddleSupport.degrees F j)
  (JTSharedInsertionCoarseMiddleSupport.oldInclusion F j)
  (JTSharedInsertionCoarseMiddleSupport.coefficientProjection F j)
  (JTSharedInsertionCoarseMiddleSupport.oldInclusion_mono F j)
  (JTSharedInsertionChoices.toOriginal_surjective F j)
  (middlePB F j) (givenParameter F j) (oldParameter F j) (oldParameter_square F j)

/-- Its exact component has the literal middle pullback as domain. -/
abbrev factor_app (p : Index F j) := (factor F j).app p

/-- Inclusion recovers the ENTIRE GIVEN parameter, naturally in every original arrow. -/
def factor_incl := JTOrdinalInverseFaceParameterDiagram.factor_incl
  (JTSharedInsertionCoarseMiddleSupport.oldSupports F j)
  (JTSharedInsertionCoarseMiddleSupport.oldDegrees F j)
  (JTSharedInsertionCoarseMiddleSupport.degrees F j)
  (JTSharedInsertionCoarseMiddleSupport.oldInclusion F j)
  (JTSharedInsertionCoarseMiddleSupport.coefficientProjection F j)
  (JTSharedInsertionCoarseMiddleSupport.oldInclusion_mono F j)
  (JTSharedInsertionChoices.toOriginal_surjective F j)
  (middlePB F j) (givenParameter F j) (oldParameter F j) (oldParameter_square F j)

/-- The exact component equation, in the direction required by whiskered path evaluation. -/
def factor_incl_app (p : Index F j) :=
  pullback_factor_app (nativeProjection F j) (middleInclusion F j)
    (JTSharedInsertionCoarseGraph.parameter F j) (factor F j)
    (JTSharedInsertionCoarseMiddleSupport.inclusion F j) (factor_incl F j) p

/-- Every original native/coefficient/choice operator transports the same parameter. -/
def factor_natural {p q : Index F j} (f : p ⟶ q) := (factor F j).naturality f

end
end DaggerModels.PartII.JTSharedInsertionCoarseMiddleParameter
