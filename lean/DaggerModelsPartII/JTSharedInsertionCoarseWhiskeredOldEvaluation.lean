import DaggerModelsPartII.JTSharedInsertionCoarseWhiskeredGraph
import DaggerModelsPartII.JTSharedInsertionCoarseEvaluation
import DaggerModelsPartII.JTSupportedPathWhiskeredZeroEvaluation

/-!
# Identify the old supported-whiskered endpoint with the actual coarse evaluation

Both evaluators retain the SAME original-time graph, complete inverse images
of both endpoint lines, all internal necklaces and the original fixed Q.
Only the old degree-cast presentation of the parameter differs. No supported
parameter factor or contraction hypothesis is needed at this old endpoint.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredOldEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private abbrev J := GroupoidSimplex.parameter

private theorem evaluation_parameter_eq {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : I ⥤ SimplexCategory)
    (c : codes N ⟶ (Functor.const I).obj Q.code) {Y : I ⥤ SSet.{0}}
    (pi : Y ⟶ JTJointRelativeParameters.withTime Q.map J t (Over.lift (codes N) c)
      (JTTargetIntervalOverMapping.whole Q.code))
    (theta theta' : Y ⟶ degrees N ⋙ J) (h : theta = theta')
    (nr : JTGraphCoveredLiftComparison.RawEquation Q N t c pi theta)
    (mr : JTGraphCoveredLiftComparison.RawEquation Q N t c pi theta') :
    JTGraphCoveredLabelEvaluation.evaluation Q N t c pi theta nr =
      JTGraphCoveredLabelEvaluation.evaluation Q N t c pi theta' mr := by
  cases h
  exact congrArg
    (fun raw : JTGraphCoveredLiftComparison.RawEquation Q N t c pi theta ↦
      JTGraphCoveredLabelEvaluation.evaluation Q N t c pi theta raw)
    (Subsingleton.elim nr mr)

private theorem cast_app_heq {I : Type} [SmallCategory I]
    {Y D E : I ⥤ SSet.{0}} (h : D = E) (theta : Y ⟶ D) (a : I) :
    HEq ((theta ≫ eqToHom h).app a) (theta.app a) := by
  cases h
  change HEq (theta.app a ≫ 𝟙 (D.obj a)) (theta.app a)
  exact heq_of_eq (Category.comp_id _)

private def castDegreeFull {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
    {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory} {Y : I ⥤ SSet.{0}}
    (C : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K)
    (theta : Y ⟶ K ⋙ J) : Y ⟶ degrees C.labels ⋙ J :=
  theta ≫ eqToHom (congrArg (· ⋙ J)
    (JTGraphCoveredProductInterface.degrees_labels C).symm)

private theorem castDegreeFull_app_heq {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W}
    {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory} {Y : I ⥤ SSet.{0}}
    (C : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K)
    (theta : Y ⟶ K ⋙ J) (a : I) : HEq ((castDegreeFull C theta).app a) (theta.app a) :=
  cast_app_heq (congrArg (· ⋙ J) (JTGraphCoveredProductInterface.degrees_labels C).symm)
    theta a

private def parameterForFamily {B : Type} [SmallCategory B]
    {V : Source} {a b : Vertex V} {P M R : B ⥤ NecklaceCode}
    {K : B ⥤ SimplexCategory} {Y : B ⥤ SSet.{0}}
    (C : JTVariableMiddleWhiskeredDiagram.Family (W := V) (x := a) (y := b) P M R K)
    (theta : Y ⟶ K ⋙ J) : Y ⟶ degrees C.labels ⋙ J := theta

private theorem parameterForFamily_app_heq {B : Type} [SmallCategory B]
    {V : Source} {a b : Vertex V} {P M R : B ⥤ NecklaceCode}
    {K : B ⥤ SimplexCategory} {Y : B ⥤ SSet.{0}}
    (C : JTVariableMiddleWhiskeredDiagram.Family (W := V) (x := a) (y := b) P M R K)
    (theta : Y ⟶ K ⋙ J) (p : B) :
    HEq ((parameterForFamily C theta).app p) (theta.app p) := HEq.rfl

section Generic

variable {I : Type} [SmallCategory I] {W : Source} (x z y : Vertex W)
variable (N : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (P R : I ⥤ NecklaceCode)
variable (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y N P R)
variable (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
variable (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y N P R O t)
variable (theta : Y ⟶ degrees N ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : codes (JTSupportedPathWhiskeredGraph.oldLabels W x z y N P R O) ⟶
  (Functor.const I).obj Q.code)

private abbrev genericFamily := JTSupportedPathWhiskeredGraph.oldFamily W x z y N P R O
private abbrev genericLabels := JTSupportedPathWhiskeredGraph.oldLabels W x z y N P R O
private abbrev genericProduct := pi ≫ (JTGraphCoveredProductInterface.iso
  (codes (genericLabels x z y N P R O)) t Q.code Q.map c).hom

private theorem genericProduct_app_heq (a : I) :
    HEq ((genericProduct x z y N P R O t pi Q c).app a) (pi.app a) := by
  exact heq_of_eq (by simp only [genericProduct, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id])

private def castParameter := castDegreeFull (genericFamily x z y N P R O) theta

private theorem castParameter_eq
    (thetaNew : Y ⟶ degrees (genericLabels x z y N P R O) ⋙ J)
    (he : ∀ a : I, HEq (theta.app a) (thetaNew.app a)) :
    castParameter x z y N P R O theta = thetaNew := by
  apply NatTrans.ext
  funext a
  exact eq_of_heq ((castDegreeFull_app_heq
    (genericFamily x z y N P R O) theta a).trans (he a))

variable (oldRaw : ∀ a : I,
  lift (pi.app a ≫ fst (NecklaceCode.wedge (P.obj a)
    (NecklaceCode.wedge ((codes N).obj a) (R.obj a))).toSSet (J.obj (t.obj a)))
      (theta.app a) ≫ JTNecklaceLabelRealization.realizedLabel
        (NecklaceCode.wedge (P.obj a)
          (NecklaceCode.wedge ((codes N).obj a) (R.obj a))).toSSet W ((degrees N).obj a)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients
            ((genericFamily x z y N P R O).data a)))) =
    (pi.app a ≫ fst (NecklaceCode.wedge (P.obj a)
      (NecklaceCode.wedge ((codes N).obj a) (R.obj a))).toSSet (J.obj (t.obj a))) ≫
        (c.app a).map ≫ Q.map)

private def sourceOfLift {B : Type} [SmallCategory B]
    {C : Type 1} [Category.{0} C] {D E : B ⥤ C} (_p : D ⟶ E) : B ⥤ C := D

private def oldDiagram := sourceOfLift
  (JTSupportedPathWhiskeredZeroEvaluation.oldLift W x z y N P R O t pi theta Q c oldRaw)

private def oldCylinder : Y ⟶ oldDiagram x z y N P R O t pi theta Q c oldRaw ⋙
    Under.forget JTXiEndpointCollapse.boundary :=
  JTGraphCoveredCylinderEquations.inc Q (genericLabels x z y N P R O) t c
    (genericProduct x z y N P R O t pi Q c)

variable (T : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (cC : codes T ⟶ (Functor.const I).obj Q.code)
variable (piC : Y ⟶ JTJointRelativeParameters.withTime Q.map J t
  (Over.lift (codes T) cC) (JTTargetIntervalOverMapping.whole Q.code))
variable (thetaC : Y ⟶ degrees T ⋙ J)
variable (hT : genericLabels x z y N P R O = T)
variable (hcC : ∀ a : I, HEq (c.app a) (cC.app a))
variable (hpC : ∀ a : I,
  HEq ((genericProduct x z y N P R O t pi Q c).app a) (piC.app a))
variable (heC : ∀ a : I, HEq (theta.app a) (thetaC.app a))

private abbrev newDiagram := JTGraphCoveredLabelEvaluation.reduced Q T t cC piC

include hT hcC hpC in
private theorem diagrams_eq : oldDiagram x z y N P R O t pi theta Q c oldRaw =
    newDiagram x y t Q T cC piC := by
  cases hT
  have hc : c = cC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hcC a)
  subst cC
  have hp : genericProduct x z y N P R O t pi Q c = piC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hpC a)
  subst piC
  rfl

private def sourceChangeGeneric := eqToHom
  (diagrams_eq x z y N P R O t pi theta Q c oldRaw T cC piC hT hcC hpC)

include hT hcC hpC in
private theorem sourceChange_cylinder_generic (a : I) :
    (oldCylinder x z y N P R O t pi theta Q c oldRaw).app a ≫
        ((sourceChangeGeneric x z y N P R O t pi theta Q c oldRaw T cC piC
          hT hcC hpC).app a).right =
      (JTGraphCoveredCylinderEquations.inc Q T t cC piC).app a := by
  cases hT
  have hc : c = cC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hcC a)
  subst cC
  have hp : genericProduct x z y N P R O t pi Q c = piC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hpC a)
  subst piC
  simp only [oldCylinder, sourceChangeGeneric, eqToHom_refl, NatTrans.id_app]
  exact Category.comp_id _

private def presentationGeneric := Grothendieck.map (Functor.whiskerRight
  (sourceChangeGeneric x z y N P R O t pi theta Q c oldRaw T cC piC hT hcC hpC)
  BoundaryNecklaceComma.diagram)

variable (q : newDiagram x y t Q T cC piC ⟶ T ⋙ JTTargetCommaPullback.diagram W x y Q)
variable (qfst : ∀ a : I, q.app a ≫ JTTargetCommaPullback.fst W x y Q (T.obj a) =
  (JTGraphCoveredLabelEvaluation.decorated Q T t cC piC thetaC).app a)
variable (qsnd : ∀ a : I, q.app a ≫ JTTargetCommaPullback.snd W x y Q (T.obj a) =
  (JTGraphCoveredLabelEvaluation.nativeLeg Q T t cC piC).app a)

include oldRaw heC qfst qsnd in
private theorem lift_square_generic (a : I) :
    (JTSupportedPathWhiskeredZeroEvaluation.oldLift W x z y N P R O t pi theta Q c
      oldRaw).app a ≫ (JTTargetCommaPullback.diagram W x y Q).map
        ((eqToHom hT).app a) =
      (sourceChangeGeneric x z y N P R O t pi theta Q c oldRaw T cC piC hT hcC hpC).app a ≫
        q.app a := by
  cases hT
  have hc : c = cC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hcC a)
  subst cC
  have hp : genericProduct x z y N P R O t pi Q c = piC := by
    apply NatTrans.ext
    funext a
    exact eq_of_heq (hpC a)
  subst piC
  simp only [sourceChangeGeneric, eqToHom_refl, NatTrans.id_app, Category.id_comp]
  rw [(JTTargetCommaPullback.diagram W x y Q).map_id]
  apply Eq.trans (Category.comp_id
    ((JTSupportedPathWhiskeredZeroEvaluation.oldLift W x z y N P R O t pi theta Q c
      oldRaw).app a))
  have hcast := castParameter_eq x z y N P R O theta thetaC heC
  have hcmp : ∀ a : I,
      (JTGraphCoveredLabelEvaluation.decorated Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)
        (castParameter x z y N P R O theta)).app a ≫
          (DecoratedCylinderNecklacePresentation.underCocone W x y).app
            ((genericLabels x z y N P R O).obj a) =
      (JTGraphCoveredLabelEvaluation.nativeLeg Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)).app a ≫
          JTTargetCommaPullback.targetMap W x y Q := by
    intro b
    rw [hcast, ← qfst b, ← qsnd b, Category.assoc,
      JTTargetCommaPullback.condition, ← Category.assoc]
  apply pullback.hom_ext
    (f := (DecoratedCylinderNecklacePresentation.underCocone W x y).app
      ((genericLabels x z y N P R O).obj a))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change _ ≫ JTTargetCommaPullback.fst W x y Q
      ((genericLabels x z y N P R O).obj a) =
        _ ≫ JTTargetCommaPullback.fst W x y Q
          ((genericLabels x z y N P R O).obj a)
    have h0 := JTDecoratedIntervalCylinder.liftFromProjections_fst Q
      (genericLabels x z y N P R O) (oldDiagram x z y N P R O t pi theta Q c oldRaw)
      (JTGraphCoveredLabelEvaluation.decorated Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)
        (castParameter x z y N P R O theta))
      (JTGraphCoveredLabelEvaluation.nativeLeg Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)) hcmp a
    exact h0.trans
      ((congrArg (fun v ↦ (JTGraphCoveredLabelEvaluation.decorated Q
        (genericLabels x z y N P R O) t c (genericProduct x z y N P R O t pi Q c)
        v).app a) hcast).trans (qfst a).symm)
  · change _ ≫ JTTargetCommaPullback.snd W x y Q
      ((genericLabels x z y N P R O).obj a) =
        _ ≫ JTTargetCommaPullback.snd W x y Q
          ((genericLabels x z y N P R O).obj a)
    have h0 := JTDecoratedIntervalCylinder.liftFromProjections_snd Q
      (genericLabels x z y N P R O) (oldDiagram x z y N P R O t pi theta Q c oldRaw)
      (JTGraphCoveredLabelEvaluation.decorated Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)
        (castParameter x z y N P R O theta))
      (JTGraphCoveredLabelEvaluation.nativeLeg Q (genericLabels x z y N P R O) t c
        (genericProduct x z y N P R O t pi Q c)) hcmp a
    exact h0.trans (qsnd a).symm

include oldRaw heC qfst qsnd in
private def comparisonGeneric :=
  eqToHom (JTSupportedPathWhiskeredZeroEvaluation.oldEvaluation_eq_mapPresentation
    W x z y N P R O t pi theta Q c oldRaw) ≫
  JTBoundaryNecklacePresentationTransport.comparisonWithSourceChange
    (JTTargetCommaPullback.diagram W x y Q)
    (JTSupportedPathWhiskeredZeroEvaluation.oldLift W x z y N P R O t pi theta Q c oldRaw)
    q (sourceChangeGeneric x z y N P R O t pi theta Q c oldRaw T cC piC hT hcC hpC)
    (eqToHom hT)
    (lift_square_generic x z y N P R O t pi theta Q c oldRaw T cC piC thetaC
      hT hcC hpC heC q qfst qsnd)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

private theorem oldForget_weak
    (hpi : ∀ a : I, trivialFibrations SSet.{0} (pi.app a)) :
    WeakEquivalence (nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
      (oldDiagram x z y N P R O t pi theta Q c oldRaw)))) := by
  apply JTGraphCoveredPresentationWeak.forget_weak Q (genericLabels x z y N P R O) t c
    (genericProduct x z y N P R O t pi Q c)
  intro a
  have hp : (genericProduct x z y N P R O t pi Q c).app a = pi.app a :=
    eq_of_heq (genericProduct_app_heq x z y N P R O t pi Q c a)
  rw [hp]
  exact hpi a

private theorem presentationWeak {B : Type} [SmallCategory B]
    {D D' : B ⥤ Under JTXiEndpointCollapse.boundary} (s : D ⟶ D')
    (hd : WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram D))))
    (hd' : WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram D')))) :
    WeakEquivalence (nerveMap (Grothendieck.map
      (Functor.whiskerRight s BoundaryNecklaceComma.diagram))) := by
  letI := hd
  letI := hd'
  have he : nerveMap (Grothendieck.map
      (Functor.whiskerRight s BoundaryNecklaceComma.diagram)) ≫
        nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram D')) =
      nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram D)) :=
    (nerveFunctor.map_comp
      (Grothendieck.map (Functor.whiskerRight s BoundaryNecklaceComma.diagram)).toCatHom
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram D')).toCatHom).symm.trans
      (congrArg nerveMap (Grothendieck.functor_comp_forget
        (α := Functor.whiskerRight s BoundaryNecklaceComma.diagram)))
  exact weakEquivalence_of_postcomp_of_fac he

end Generic

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j

/-- The unchanged actual shared insertion-choice source. -/
abbrev Index := JTSharedInsertionCoarseWhiskeredGraph.Index F j

/-- BOTH complete endpoint inverse images, in the exact existing Zero old frame. -/
def reduced := oldDiagram x (z j) y (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)

/-- The entire original-time cylinder summand in the old full endpoint quotient. -/
def cylinderInclusion := oldCylinder x (z j) y
  (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)

/-- The existing Zero.oldEvaluation on its entire unchanged old presentation. -/
def evaluation :=
  JTSupportedPathWhiskeredZeroEvaluation.oldEvaluation W x (z j) y
    (M F j) (P F j) (R F j) (O F j)
    (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
    (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
    (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
    (JTSharedInsertionCoarseWhiskeredGraph.target F j)
    (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)

/-- Forget every internal necklace to the SAME shared insertion choices. -/
def oldToChoices := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j))

private def actualProjection_app_heq (p : Index F j) :=
  (heq_of_eq (JTSharedInsertionCoarseWhiskeredGraph.projection_app F j p)).trans
    (heq_of_eq (JTSharedInsertionCoarseEvaluation.projection_app F j p).symm)

private def actualProduct_app_heq (p : Index F j) :=
  (genericProduct_app_heq x (z j) y (M F j) (P F j) (R F j) (O F j)
    (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
    (JTSharedInsertionCoarseWhiskeredGraph.projection F j) Q
    (JTSharedInsertionCoarseWhiskeredGraph.target F j) p).trans
      (actualProjection_app_heq F j p)

private def actualTarget_app_heq (p : Index F j) :=
  heq_of_eq (JTSharedInsertionCoarseWhiskeredGraph.target_app F j p)

private def actualParameter_app_heq (p : Index F j) :=
  (heq_of_eq (JTSharedInsertionCoarseWhiskeredGraph.parameter_app F j p)).trans
    (parameterForFamily_app_heq (JTSharedInsertionCoarseLabels.family F j)
      (JTSharedInsertionCoarseGraph.parameter F j) p).symm

/-- Compare the ENTIRE old reduced graph with the EXISTING actual coarse reduced graph.
Both complete endpoint inverse images, every original operator and all time are retained. -/
def sourceChange := sourceChangeGeneric x (z j) y
  (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (JTSharedInsertionCoarseEvaluation.labels F j)
  (JTSharedInsertionCoarseEvaluation.target F j)
  (JTSharedInsertionCoarseEvaluation.projection F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)
  (actualTarget_app_heq F j) (actualProduct_app_heq F j)

/-- The source change is the strict identity on the entire given graph-cylinder summand. -/
def sourceChange_cylinder (p : Index F j) := sourceChange_cylinder_generic x (z j) y
  (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (JTSharedInsertionCoarseEvaluation.labels F j)
  (JTSharedInsertionCoarseEvaluation.target F j)
  (JTSharedInsertionCoarseEvaluation.projection F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)
  (actualTarget_app_heq F j) (actualProduct_app_heq F j) p

/-- Transport ALL internal necklaces to the existing coarse presentation. -/
def presentation := Grothendieck.map (Functor.whiskerRight
  (sourceChange F j) BoundaryNecklaceComma.diagram)

private def actualComparison := comparisonGeneric x (z j) y
  (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (JTSharedInsertionCoarseEvaluation.labels F j)
  (JTSharedInsertionCoarseEvaluation.target F j)
  (JTSharedInsertionCoarseEvaluation.projection F j)
  (JTSharedInsertionCoarseEvaluation.parameter F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)
  (actualTarget_app_heq F j) (actualProduct_app_heq F j) (actualParameter_app_heq F j)
  (JTSharedInsertionCoarseEvaluation.pullbackLift F j)
  (JTSharedInsertionCoarseEvaluation.pullbackLift_fst F j)
  (JTSharedInsertionCoarseEvaluation.pullbackLift_snd F j)

/-- A full natural comparison into the EXISTING coarse evaluator in the SAME fixed Q.
No raw, support, parameter factor or compatibility hypothesis is added for callers. -/
def comparison := actualComparison F j ≫ Functor.whiskerLeft (presentation F j)
  (eqToHom (JTSharedInsertionCoarseEvaluation.evaluation_eq_mapPresentation F j).symm)

/-- The full presentation comparison strictly retains the shared insertion-choice base. -/
def presentation_toChoices := Grothendieck.functor_comp_forget
  (α := Functor.whiskerRight (sourceChange F j) BoundaryNecklaceComma.diagram)

/-- The existing old full presentation weakly covers ONLY the same shared choice source. -/
def oldToChoices_weak := oldForget_weak x (z j) y
  (M F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldTime F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection F j)
  (JTSharedInsertionCoarseWhiskeredGraph.parameter F j) Q
  (JTSharedInsertionCoarseWhiskeredGraph.target F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection_trivialFibration F j)

/-- Weakness follows from the TWO checked full covers and their strict shared-base triangle. -/
def presentation_weak := presentationWeak (sourceChange F j)
  (oldToChoices_weak F j) (JTSharedInsertionCoarseEvaluation.toChoices_weak F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredOldEvaluation
