import DaggerModelsPartII.JTSharedInsertionCoarseSupportedComparisonLabels
import DaggerModelsPartII.JTSharedInsertionSupportedComparisonGraph
import DaggerModelsPartII.JTSharedInsertionCoarseMiddleParameter
import DaggerModelsPartII.JTNativeTimeProductTransport
import DaggerModelsPartII.JTGraphCoveredRawTransport
import DaggerModelsPartII.JTGraphCoveredLiftComparison

/-!
# Whole raw input for the actual old-native restricted supported path

All graph assignments and original-time coordinates are retained. Raw is derived from
actual coarse-path pieces and transported along the decorated comparison, without a section.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionSupportedComparisonRaw

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def projectionTransport {B : Type} [SmallCategory B]
    {X Y Z : B ⥤ SSet.{0}} (pi : X ⟶ Y) (e : Z ≅ Y) : X ⟶ Z := pi ≫ e.inv

private def projectionForIso {B : Type} [SmallCategory B]
    {Y Z : B ⥤ SSet.{0}} (e : Z ≅ Y) {X : B ⥤ SSet.{0}} (pi : X ⟶ Y) : X ⟶ Z :=
  pi ≫ e.inv

private def targetCompose {B : Type} [SmallCategory B]
    {N M : B ⥤ NecklaceCode} (n : N ⟶ M) (T : NecklaceCode)
    (c : M ⟶ (Functor.const B).obj T) := n ≫ c

private def codeProductIso {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) (N : I ⥤ NecklaceCode) (NP : B ⥤ NecklaceCode)
    (e : NP = b ⋙ N) (t : I ⥤ SimplexCategory) :
    JTGraphCoveredProductInterface.product NP (b ⋙ t) ≅
      b ⋙ JTGraphCoveredProductInterface.product N t :=
  JTNativeTimeProductTransport.iso (eqToIso e) (b ⋙ t)

private def labelProductIso {B I : Type} [SmallCategory B] [SmallCategory I]
    {W : Source} {x y : Vertex W} (b : B ⥤ I)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (NP : B ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (e : JTParametrizedTargetFamilies.codes NP = b ⋙ JTParametrizedTargetFamilies.codes N)
    (t : I ⥤ SimplexCategory) :=
  codeProductIso b (JTParametrizedTargetFamilies.codes N)
    (JTParametrizedTargetFamilies.codes NP) e t

private def labelDegreeParameter {B : Type} [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (N C : B ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (e : JTParametrizedTargetFamilyComparison.degrees N =
      JTParametrizedTargetFamilyComparison.degrees C)
    {X : B ⥤ SSet.{0}} (q : X ⟶ JTParametrizedTargetFamilyComparison.degrees C ⋙ J) :=
  q ≫ Functor.whiskerRight (eqToHom e.symm) J

private def labelTarget {B : Type} [SmallCategory B]
    {W : Source} {x y : Vertex W}
    (N C : B ⥤ DecoratedNecklaceHomDiagram.Index W x y) (r : N ⟶ C)
    (T : NecklaceCode)
    (c : JTParametrizedTargetFamilies.codes C ⟶ (Functor.const B).obj T) :=
  JTWhiskeredSeamTarget.nativeOf r ≫ c

private def productForArrow {B : Type} [SmallCategory B]
    {W : Source} {x y : Vertex W}
    {NP CP : B ⥤ DecoratedNecklaceHomDiagram.Index W x y} (_r : NP ⟶ CP)
    {I : Type} [SmallCategory I] (b : B ⥤ I)
    (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (e : JTParametrizedTargetFamilies.codes NP = b ⋙ JTParametrizedTargetFamilies.codes N)
    (t : I ⥤ SimplexCategory) := labelProductIso b N NP e t

private def parameterForArrow {B : Type} [SmallCategory B]
    {W : Source} {x y : Vertex W}
    {NP CP : B ⥤ DecoratedNecklaceHomDiagram.Index W x y} (_r : NP ⟶ CP)
    (e : JTParametrizedTargetFamilyComparison.degrees NP =
      JTParametrizedTargetFamilyComparison.degrees CP)
    {X : B ⥤ SSet.{0}} (q : X ⟶ JTParametrizedTargetFamilyComparison.degrees CP ⋙ J) :=
  labelDegreeParameter NP CP e q

private def targetForArrow {B : Type} [SmallCategory B]
    {W : Source} {x y : Vertex W}
    {NP CP : B ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : NP ⟶ CP)
    (T : NecklaceCode)
    (c : JTParametrizedTargetFamilies.codes CP ⟶ (Functor.const B).obj T) :=
  labelTarget NP CP r T c

private def productOfCodeEquality {B I : Type} [SmallCategory B] [SmallCategory I]
    {b : B ⥤ I} {N : I ⥤ NecklaceCode} {NP : B ⥤ NecklaceCode}
    (e : NP = b ⋙ N) (t : I ⥤ SimplexCategory) := codeProductIso b N NP e t


private theorem codeProductIso_square {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) (N C : I ⥤ NecklaceCode) (NP CP : B ⥤ NecklaceCode)
    (en : NP = b ⋙ N) (ec : CP = b ⋙ C) (t : I ⥤ SimplexCategory)
    (n : N ⟶ C) (nB : NP ⟶ CP)
    (hn : nB = eqToHom en ≫ Functor.whiskerLeft b n ≫ eqToHom ec.symm) :
    (codeProductIso b N NP en t).inv ≫
        JTSharedInsertionPhaseGraph.mapWithTime nB (b ⋙ t) =
      Functor.whiskerLeft b (JTSharedInsertionPhaseGraph.mapWithTime n t) ≫
        (codeProductIso b C CP ec t).inv := by
  subst NP
  subst CP
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hn
  subst nB
  apply NatTrans.ext
  funext p
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ ((n.app (b.obj p)).map ⊗ₘ 𝟙 _) =
    ((n.app (b.obj p)).map ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ 𝟙 _)
  simp

private theorem productGraph_square {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) (N C : I ⥤ NecklaceCode) (NP CP : B ⥤ NecklaceCode)
    (en : NP = b ⋙ N) (ec : CP = b ⋙ C) (t : I ⥤ SimplexCategory)
    (n : N ⟶ C) (nB : NP ⟶ CP)
    (hn : nB = eqToHom en ≫ Functor.whiskerLeft b n ≫ eqToHom ec.symm)
    {X Y : B ⥤ SSet.{0}}
    (piN : X ⟶ b ⋙ JTGraphCoveredProductInterface.product N t)
    (piC : Y ⟶ b ⋙ JTGraphCoveredProductInterface.product C t) (eta : X ⟶ Y)
    (hp : eta ≫ piC = piN ≫
      Functor.whiskerLeft b (JTSharedInsertionPhaseGraph.mapWithTime n t)) :
    eta ≫ (piC ≫ (codeProductIso b C CP ec t).inv) =
      (piN ≫ (codeProductIso b N NP en t).inv) ≫
        JTSharedInsertionPhaseGraph.mapWithTime nB (b ⋙ t) := by
  rw [← Category.assoc, hp, Category.assoc,
    ← codeProductIso_square b N C NP CP en ec t n nB hn, ← Category.assoc]

private def degreeParameter {B : Type} [SmallCategory B]
    (K D : B ⥤ SimplexCategory) (e : D = K) {X : B ⥤ SSet.{0}}
    (q : X ⟶ K ⋙ J) : X ⟶ D ⋙ J :=
  q ≫ Functor.whiskerRight (eqToHom e.symm) J

private def parameterOfDegreeEquality {B : Type} [SmallCategory B]
    {K D : B ⥤ SimplexCategory} (e : D = K) {X : B ⥤ SSet.{0}}
    (q : X ⟶ K ⋙ J) := degreeParameter K D e q

private theorem degreeParameter_square {B : Type} [SmallCategory B]
    (K D : B ⥤ SimplexCategory) (e : D = K) {X Y : B ⥤ SSet.{0}}
    (q : X ⟶ K ⋙ J) (r : Y ⟶ K ⋙ J) (eta : X ⟶ Y)
    (hq : eta ≫ r = q) :
    degreeParameter K D e q ≫ Functor.whiskerRight (eqToHom e) J = eta ≫ r := by
  subst D
  have hi : Functor.whiskerRight (𝟙 K) J = 𝟙 (K ⋙ J) := by
    apply NatTrans.ext
    funext p
    exact J.map_id _
  simpa only [degreeParameter, eqToHom_refl, hi, Category.comp_id] using hq.symm

private theorem collapse_square {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) (N C : I ⥤ NecklaceCode) (NP CP : B ⥤ NecklaceCode)
    (en : NP = b ⋙ N) (ec : CP = b ⋙ C)
    (n : N ⟶ C) (nB : NP ⟶ CP)
    (hn : nB = eqToHom en ≫ Functor.whiskerLeft b n ≫ eqToHom ec.symm)
    (T : NecklaceCode) (cn : N ⟶ (Functor.const I).obj T)
    (cc : C ⟶ (Functor.const I).obj T) (hc : n ≫ cc = cn) :
    nB ≫ (eqToHom ec ≫ Functor.whiskerLeft b cc) =
      eqToHom en ≫ Functor.whiskerLeft b cn := by
  subst NP
  subst CP
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hn ⊢
  rw [hn, ← Functor.whiskerLeft_comp, hc]

section CoveredTransport

variable {B : Type} [SmallCategory B] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (N : B ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : B ⥤ SimplexCategory)
variable (c : JTParametrizedTargetFamilies.codes N ⟶ (Functor.const B).obj Q.code)
variable {X : B ⥤ SSet.{0}}
variable (pi : X ⟶ JTGraphCoveredProductInterface.product
  (JTParametrizedTargetFamilies.codes N) t)

private def framedProjection := pi ≫ (JTGraphCoveredProductInterface.iso
  (JTParametrizedTargetFamilies.codes N) t Q.code Q.map c).hom

private theorem framedProjection_app (p : B) :
    (framedProjection Q N t c pi).app p = pi.app p := by
  change pi.app p ≫ 𝟙 _ = pi.app p
  exact Category.comp_id _

variable (C : B ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (cc : JTParametrizedTargetFamilies.codes C ⟶ (Functor.const B).obj Q.code)
variable {Y : B ⥤ SSet.{0}}
variable (pj : Y ⟶ JTGraphCoveredProductInterface.product
  (JTParametrizedTargetFamilies.codes C) t)
variable (qn : X ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J)
variable (qc : Y ⟶ JTParametrizedTargetFamilyComparison.degrees C ⋙ J)
variable (r : N ⟶ C) (eta : X ⟶ Y)
variable (hn : ∀ p, (pi.app p ≫ fst _ _) ≫
    ((JTWhiskeredSeamTarget.nativeOf r).app p).map = eta.app p ≫ pj.app p ≫ fst _ _)
variable (hq : ∀ p, qn.app p ≫
    J.map ((JTParametrizedTargetFamilyComparison.coefficient r).app p) = eta.app p ≫ qc.app p)
variable (hr : JTGraphCoveredLiftComparison.RawEquation Q C t cc
  (framedProjection Q C t cc pj) qc)

private def rawOverComparison : JTGraphCoveredLiftComparison.RawEquation Q N t
    (JTWhiskeredSeamTarget.nativeOf r ≫ cc)
    (framedProjection Q N t (JTWhiskeredSeamTarget.nativeOf r ≫ cc) pi) qn := by
  intro p
  have hc := hr p
  simp only [framedProjection_app] at hc
  have h := JTGraphCoveredRawTransport.ordered_raw (r.app p)
    (pi.app p ≫ fst _ _) (qn.app p) (pj.app p ≫ fst _ _) (qc.app p) (eta.app p)
    ((cc.app p).map ≫ Q.map) (hn p) (hq p) hc
  simpa only [framedProjection_app, NatTrans.comp_app, Category.assoc] using h

end CoveredTransport

private def MiddleFactorEquation {I : Type} [SmallCategory I]
    (W : Source) (x z y : Vertex W)
    (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (P R : I ⥤ NecklaceCode)
    (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
    (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y M P R O t)
    (theta : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
    (S : I ⥤ SimplexCategory) (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
    (q : ∀ a : I, pullback
      (pi.app a ≫ fst (wedge (P.obj a) (wedge
        ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a))).toSSet (J.obj (t.obj a)))
      (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ⟶
        J.obj (S.obj a)) : Prop :=
  ∀ a : I, pullback.fst
    (pi.app a ≫ fst (wedge (P.obj a) (wedge
      ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a))).toSSet (J.obj (t.obj a)))
    (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ≫
      theta.app a = q a ≫ J.map (u.app a)


section PathRawFactory

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (S : I ⥤ SimplexCategory)
variable (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
variable (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
  JTSupportedOrderedCoefficientChoices.old W z M p =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)
variable (P R : I ⥤ NecklaceCode)
variable (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
variable (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
variable (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y M P R O t)
variable (theta : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : JTParametrizedTargetFamilies.codes
  (JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O) ⟶
    (Functor.const I).obj Q.code)

private def pathTimeFactory := JTSupportedPathChainLabels.toOriginal W z M S u hs ⋙ t

private def pathRawFactory := fun oldRaw q hq hu ↦
  JTVariableMiddleGraphEvaluation.raw Q
    (JTSupportedPathWhiskeredDiagram.variableMiddleFamily W x z y M S u hs P R O)
    (JTSupportedPathChainLabels.toOriginal W z M S u hs ⋙ t)
    (JTSupportedPathWhiskeredRaw.collapse W x z y M S u hs P R O Q c)
    (JTSupportedPathWhiskeredGraph.projectionNew W x z y M S u hs P R O t pi theta)
    (JTSupportedPathWhiskeredGraph.parameter W z M S u hs theta)
    (JTSupportedPathWhiskeredRaw.pieceEquations W x z y M S u hs P R O
      t pi theta Q c oldRaw q hq hu)

end PathRawFactory

private def reindexedTime {B I : Type} [SmallCategory B] [SmallCategory I]
    (b : B ⥤ I) (t : I ⥤ SimplexCategory) : B ⥤ SimplexCategory := b ⋙ t

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j
private abbrev oldTime := JTSharedInsertionCoarseWhiskeredGraph.oldTime F j
private abbrev oldPi := JTSharedInsertionCoarseWhiskeredGraph.projection F j
private abbrev oldTheta := JTSharedInsertionCoarseWhiskeredGraph.parameter F j
private abbrev oldTarget := JTSharedInsertionCoarseWhiskeredGraph.target F j

/-- The canonical factor of the GIVEN parameter on the whole old middle inverse image. -/
abbrev middleFactor (p : JTSharedInsertionChoices.Index F j) :=
  (JTSharedInsertionCoarseMiddleParameter.factor F j).app p

set_option maxHeartbeats 400000 in
private def actualMiddleFactor : MiddleFactorEquation W x (z j) y
    (M F j) (P F j) (R F j) (O F j) (oldTime F j) (oldPi F j) (oldTheta F j)
    (S F j) (u F j) (middleFactor F j) :=
  JTSharedInsertionCoarseMiddleParameter.factor_incl_app F j

/-- The exact literal middle-PB equation, derived from the public GIVEN-factor API. -/
def middleFactor_equation := actualMiddleFactor F j

/-- The unchanged entire original time at each supported path choice. -/
def oldTimeAtPath := pathTimeFactory W (z j) (M F j) (S F j) (u F j) (hs F j)
  (oldTime F j)

/-- The complete coarse path target in the SAME original Q. -/
def coarsePathTarget := JTSupportedPathWhiskeredRaw.collapse W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j) Q (oldTarget F j)

/-- All three FULL native inverse-image equations are derived from original F,j. -/
def coarsePath_pieces := JTSupportedPathWhiskeredRaw.pieceEquations W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldPi F j) (oldTheta F j) Q (oldTarget F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (middleFactor F j) (actualMiddleFactor F j)
  (JTSharedInsertionCoarseMiddleSupport.inclusion_mono F j)

/-- The entire actual coarse supported-path coefficient has its original raw value. -/
def coarsePath_raw := pathRawFactory W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldPi F j) (oldTheta F j) Q (oldTarget F j)
  (JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j)
  (middleFactor F j) (actualMiddleFactor F j)
  (JTSharedInsertionCoarseMiddleSupport.inclusion_mono F j)

/-- The actual supported path and both complete chain choices. -/
abbrev Index := JTSharedInsertionSupportedComparisonGraph.Index F j

/-- All original-old-native coefficients restricted from the actual coarse supported path. -/
abbrev labels := JTSharedInsertionCoarseSupportedComparisonLabels.labels F j

/-- The existing decorated native restriction, retaining the whole coefficient degree. -/
abbrev comparison := JTSharedInsertionCoarseSupportedComparisonLabels.comparison F j

/-- Every original old assignment and every compatible supported coefficient lift. -/
abbrev graph := JTSharedInsertionSupportedComparisonGraph.graph F j

/-- The exact public code equality, with every original old native operator retained. -/
def codes_reindex := JTSharedInsertionCoarseSupportedComparisonLabels.codes_reindex F j

/-- The exact public source/target degree equality. -/
def degrees_eq := JTSharedInsertionCoarseSupportedComparisonLabels.degrees_eq F j

set_option maxHeartbeats 400000 in
private def actualProductIso := productOfCodeEquality (codes_reindex F j)
  (JTSharedInsertionOldGraph.oldTime F j)

/-- The strict native transport acts identically on the ENTIRE original time. -/
def productIso := actualProductIso F j

set_option maxHeartbeats 400000 in
private def actualProjection := projectionForIso (productIso F j)
  (JTSharedInsertionSupportedComparisonGraph.projection F j)

/-- The whole original-time graph projection, now typed on the literal NP native code. -/
def projection := actualProjection F j

set_option maxHeartbeats 400000 in
private def actualParameter := parameterOfDegreeEquality (degrees_eq F j)
  (JTSharedInsertionSupportedComparisonGraph.parameter F j)

/-- Retain the GIVEN full lifted parameter with its exact NP degree transport. -/
def parameter := actualParameter F j

set_option maxHeartbeats 400000 in
private def actualTarget := targetForArrow (comparison F j) Q.code (coarsePathTarget F j)

/-- Collapse through the exact native restriction to the SAME original Q code. -/
def target := actualTarget F j

end
end DaggerModels.PartII.JTSharedInsertionSupportedComparisonRaw
