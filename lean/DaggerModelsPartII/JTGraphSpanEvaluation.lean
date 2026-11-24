import DaggerModelsPartII.JTGraphSpanLift
import DaggerModelsPartII.JTVariablePresentationCone

/-! The exact fixed-target evaluation on the original span cylinders. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSpanEvaluation

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphSpanFamily (tail)
open JTGraphSpanParameterMap (parameter)
open JTGraphVariableTimeComparison (collapse_square)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphCylinderSimplexSpan (SpanIndex)
open JTGraphSpanLift (originalCylinders spanLabels spanFamily cylinders_eq
  spanLabelCollapse spanNativeCollapse spanNativeCollapse_app spanLift_app)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev C := TargetComma Q
private abbrev S := SpanIndex (C Q)

private abbrev pullbackDiagram := JTTargetCommaPullback.diagram W x y Q

/-- The lift on the original cylinders pairs the entire decorated traversal
with the actual native map into the fixed target. -/
def spanLift : originalCylinders Q ⟶ spanLabels Q ⋙ pullbackDiagram Q :=
  eqToHom (cylinders_eq Q).symm ≫ JTParametrizedTargetFamilies.liftNatural (spanFamily Q)

private abbrev fullFibers := JTGraphCylinderSimplexSpan.fibers (C Q) (nativeCode Q)

private abbrev mapPresentation :=
  JTBoundaryNecklacePresentationCone.mapPresentation (pullbackDiagram Q)
    (originalCylinders Q) (spanLabels Q) (spanLift Q)

private abbrev actualFibers := BoundaryNecklaceComma.fiberDiagram (originalCylinders Q)

private def evaluation :
    Grothendieck (actualFibers Q) ⥤ C Q :=
  mapPresentation Q ⋙ JTTargetCommaExactEvaluation.fromPresentation W x y Q

private def transportEvaluation {I C : Type} [SmallCategory I] [SmallCategory C]
    {D E : I ⥤ Cat.{0, 0}} (h : D = E) (F : Grothendieck D ⥤ C) :
    Grothendieck E ⥤ C := by
  subst E
  exact F

private theorem fibers_eq : actualFibers Q = fullFibers Q := by
  unfold actualFibers fullFibers BoundaryNecklaceComma.fiberDiagram
    JTGraphCylinderSimplexSpan.fibers JTGraphCylinderFiberDiagram.diagram originalCylinders
  apply CategoryTheory.Functor.assoc

/-- Evaluate the actual span cylinders with all original internal necklace operators. -/
def fullEvaluation : Grothendieck (fullFibers Q) ⥤ C Q :=
  transportEvaluation (D := actualFibers Q) (E := fullFibers Q) (fibers_eq Q) (evaluation Q)

private theorem transportEvaluation_eq_comp {I Z : Type} [SmallCategory I] [SmallCategory Z]
    {D E : I ⥤ Cat.{0, 0}} (h : D = E) (G : Grothendieck D ⥤ Z) :
    transportEvaluation h G = Grothendieck.map (eqToHom h.symm) ⋙ G := by
  subst E
  simp only [eqToHom_refl, Grothendieck.map_id_eq, Functor.id_comp]
  rfl

private theorem mapPresentation_of_eq {I J : Type} [SmallCategory I] [SmallCategory J]
    {D E : I ⥤ Under JTXiEndpointCollapse.boundary}
    (V : J ⥤ Under JTXiEndpointCollapse.boundary) (L : I ⥤ J)
    (h : D = E) (a : E ⟶ L ⋙ V) :
    Grothendieck.map (eqToHom (congrArg BoundaryNecklaceComma.fiberDiagram h)) ⋙
        JTBoundaryNecklacePresentationCone.mapPresentation V E L a =
      JTBoundaryNecklacePresentationCone.mapPresentation V D L (eqToHom h ≫ a) := by
  subst E
  simp only [congrArg, eqToHom_refl, Grothendieck.map_id_eq, Functor.id_comp, Category.id_comp]

private abbrev parametrizedCylinders :=
  JTParametrizedTargetFamilies.cylinders (L := spanLabels Q) (time := JTGraphSpanLift.time Q)

private def toActualCylinders : Grothendieck (fullFibers Q) ⥤ Grothendieck (actualFibers Q) :=
  Grothendieck.map (eqToHom (fibers_eq Q).symm)

private def toParametrizedCylinders : Grothendieck (actualFibers Q) ⥤
    BoundaryNecklaceComma.Presentation (parametrizedCylinders Q) :=
  Grothendieck.map (eqToHom (congrArg BoundaryNecklaceComma.fiberDiagram (cylinders_eq Q).symm))

/-- Identify the exact original span presentation with the parametrized
presentation while retaining all internal necklaces. -/
def parametrizedPresentationMap : Grothendieck (fullFibers Q) ⥤
    BoundaryNecklaceComma.Presentation (parametrizedCylinders Q) :=
  toActualCylinders Q ⋙ toParametrizedCylinders Q

/-- Following this identification by the parametrized evaluation gives the
original full-span evaluation as an equality of functors. -/
theorem evaluate_parametrizedPresentationMap :
    parametrizedPresentationMap Q ⋙
        JTParametrizedTargetFamilies.evaluate (spanFamily Q) = fullEvaluation Q := by
  unfold fullEvaluation
  rw [transportEvaluation_eq_comp]
  let f := toActualCylinders Q
  let g := toParametrizedCylinders Q
  let m := JTBoundaryNecklacePresentationCone.mapPresentation (pullbackDiagram Q)
    (parametrizedCylinders Q) (spanLabels Q)
    (JTParametrizedTargetFamilies.liftNatural (spanFamily Q))
  let r := JTTargetCommaExactEvaluation.fromPresentation W x y Q
  change (f ⋙ g) ⋙ (m ⋙ r) = f ⋙ (mapPresentation Q ⋙ r)
  have hm : g ⋙ m = mapPresentation Q :=
    mapPresentation_of_eq (pullbackDiagram Q) (spanLabels Q) (cylinders_eq Q).symm
      (JTParametrizedTargetFamilies.liftNatural (spanFamily Q))
  rw [Functor.assoc f g (m ⋙ r), ← Functor.assoc g m r, hm]

private abbrev toP := JTTargetCommaPullback.toPullback W x y Q
private abbrev e := JTTargetCommaPullback.equivalence W x y Q

private def natTransWithApp {I X : Type*} [Category* I] [Category* X]
    {F G H : I ⥤ X} (h : F = G) (η : G ⟶ H)
    (app : ∀ i, F.obj i ⟶ H.obj i) (hApp : ∀ i, HEq (app i) (η.app i)) : F ⟶ H where
  app := app
  naturality {i j} f := by
    subst G
    rw [eq_of_heq (hApp i), eq_of_heq (hApp j)]
    exact η.naturality f

private theorem natTransWithApp_eq {I X : Type*} [Category* I] [Category* X]
    {F G H : I ⥤ X} (h : F = G) (η : G ⟶ H)
    (app : ∀ i, F.obj i ⟶ H.obj i) (hApp : ∀ i, HEq (app i) (η.app i)) :
    natTransWithApp h η app hApp = eqToHom h ≫ η := by
  subst G
  rw [eqToHom_refl, Category.id_comp]
  apply NatTrans.ext
  funext i
  exact eq_of_heq (hApp i)

private abbrev paramLift := JTParametrizedTargetFamilies.liftNatural (spanFamily Q)

private def liftApp (P : S Q) : (originalCylinders Q).obj P ⟶
    (spanLabels Q ⋙ pullbackDiagram Q).obj P :=
  (paramLift Q).app P

private def pointwiseLift : originalCylinders Q ⟶ spanLabels Q ⋙ pullbackDiagram Q :=
  natTransWithApp (cylinders_eq Q).symm (paramLift Q) (liftApp Q) (fun _ ↦ HEq.rfl)

private theorem pointwiseLift_eq : pointwiseLift Q = spanLift Q :=
  natTransWithApp_eq (cylinders_eq Q).symm (paramLift Q) (liftApp Q) (fun _ ↦ HEq.rfl)

set_option maxHeartbeats 500000 in
private theorem pointwiseCollapse_right (P : S Q) :
    ((pointwiseLift Q).app P).right ≫
      ((pullbackDiagram Q).map ((spanLabelCollapse Q).app P)).right =
      ((spanNativeCollapse Q).app P).right ≫
        ((toP Q).obj ((tail (C Q)).obj P)).fiber.hom.right := by
  let U := (tail (C Q)).obj P
  let p : JTGraphVariableTimeIndex.Index U := parameter (Q := Q) P
  let a := ((pullbackDiagram Q).map ((spanLabelCollapse Q).app P)).right
  let b := ((toP Q).obj U).fiber.hom.right
  let f := ((JTGraphVariableTimeComparison.liftNatural U).app p).right
  let g := ((JTGraphVariableTimeComparison.nativeCollapse U).app p).right
  have h₀ : ((pointwiseLift Q).app P).right = ((paramLift Q).app P).right := rfl
  have h₁ : ((paramLift Q).app P).right = f :=
    congrArg (fun k ↦ k.right) (spanLift_app Q P)
  have h₂ : ((spanNativeCollapse Q).app P).right = g :=
    congrArg (fun k ↦ k.right) (spanNativeCollapse_app Q P)
  have h₃ : f ≫ a = g ≫ b := congrArg (fun k ↦ k.right) (collapse_square U p)
  exact (congrArg (· ≫ a) (h₀.trans h₁)).trans (h₃.trans (congrArg (· ≫ b) h₂.symm))

private theorem squareCongr {I X : Type*} [Category* I] [Category* X]
    {F G : I ⥤ X} {η η' : F ⟶ G} (h : η = η') (i : I) {Z : X}
    (a : G.obj i ⟶ Z) (b : F.obj i ⟶ Z) (hs : η.app i ≫ a = b) :
    η'.app i ≫ a = b := by
  subst η'
  exact hs

/-- The decorated and native collapses commute over the exact fixed target. -/
theorem spanCollapse_square (P : S Q) :
    (spanLift Q).app P ≫ (pullbackDiagram Q).map ((spanLabelCollapse Q).app P) =
      (spanNativeCollapse Q).app P ≫ ((toP Q).obj ((tail (C Q)).obj P)).fiber.hom :=
  squareCongr (pointwiseLift_eq Q) P
    ((pullbackDiagram Q).map ((spanLabelCollapse Q).app P))
    ((spanNativeCollapse Q).app P ≫ ((toP Q).obj ((tail (C Q)).obj P)).fiber.hom)
    (Under.UnderMorphism.ext (pointwiseCollapse_right Q P))

private abbrev pairedTail := tail (C Q) ⋙ toP Q

private abbrev nativeTail :=
  (pairedTail Q ⋙ BoundaryNecklaceComma.sourceCode (pullbackDiagram Q)) ⋙
    BoundaryNecklaceComma.necklaceUnder

set_option maxHeartbeats 1000000 in
/-- Collapse the parametrized cylinders to the varying native necklace. -/
def parametrizedNativeCollapse : parametrizedCylinders Q ⟶ nativeTail Q :=
  natTransWithApp (F := parametrizedCylinders Q) (G := originalCylinders Q)
    (H := nativeTail Q) (cylinders_eq Q) (spanNativeCollapse Q)
    (fun P ↦ (spanNativeCollapse Q).app P) (fun _ ↦ HEq.rfl)

/-- Collapse the parametrized labels to the varying tail presentation. -/
def parametrizedLabelCollapse :
    spanLabels Q ⟶ pairedTail Q ⋙ Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram (pullbackDiagram Q)) :=
  spanLabelCollapse Q

/-- The parametrized lift respects both legs of the collapse to the original span tail. -/
theorem parametrizedCollapse_square (P : S Q) :
    (paramLift Q).app P ≫ (pullbackDiagram Q).map ((parametrizedLabelCollapse Q).app P) =
      (parametrizedNativeCollapse Q).app P ≫ ((pairedTail Q).obj P).fiber.hom := by
  apply Under.UnderMorphism.ext
  exact pointwiseCollapse_right Q P

set_option maxHeartbeats 850000 in
private def presentationCone
    (h : ∀ P, (spanLift Q).app P ≫
      (pullbackDiagram Q).map ((JTGraphSpanLift.spanLabelCollapse Q).app P) =
      (JTGraphSpanLift.spanNativeCollapse Q).app P ≫
        ((toP Q).obj ((tail (C Q)).obj P)).fiber.hom) :=
  JTVariablePresentationCone.cone (pullbackDiagram Q) (originalCylinders Q)
    (spanLabels Q) (spanLift Q) (tail (C Q) ⋙ toP Q)
    (JTGraphSpanLift.spanLabelCollapse Q)
    (JTGraphSpanLift.spanNativeCollapse Q) h

private def actualComparison
    (h : ∀ P, (spanLift Q).app P ≫
      (pullbackDiagram Q).map ((JTGraphSpanLift.spanLabelCollapse Q).app P) =
      (JTGraphSpanLift.spanNativeCollapse Q).app P ≫
        ((toP Q).obj ((tail (C Q)).obj P)).fiber.hom) :
    evaluation Q ⟶ Grothendieck.forget (actualFibers Q) ⋙ tail (C Q) := by
  let outer := Grothendieck.forget (actualFibers Q) ⋙ tail (C Q)
  let f := JTTargetCommaExactEvaluation.fromPresentation W x y Q
  let t₀ : evaluation Q ⟶ (outer ⋙ toP Q) ⋙ f := by
    let h₀ :
        (Grothendieck.forget (actualFibers Q) ⋙ (tail (C Q) ⋙ toP Q)) ⋙ f =
          (outer ⋙ toP Q) ⋙ f :=
      congrArg (· ⋙ f)
        (Functor.assoc (Grothendieck.forget (actualFibers Q)) (tail (C Q)) (toP Q)).symm
    exact (Functor.whiskerRight (presentationCone Q h) f) ≫ eqToHom h₀
  let t₁ : (outer ⋙ toP Q) ⋙ f ⟶ (outer ⋙ toP Q) ⋙ (e Q).inverse :=
    Functor.whiskerLeft (outer ⋙ toP Q)
      (JTTargetCommaExactEvaluation.inverseIso W x y Q).inv
  let t₂ : (outer ⋙ toP Q) ⋙ (e Q).inverse ⟶ outer := by
    exact eqToHom (Functor.assoc outer (toP Q) (e Q).inverse) ≫
      (Functor.whiskerLeft outer (e Q).unitIso.inv) ≫
        eqToHom (Functor.comp_id outer)
  exact t₀ ≫ t₁ ≫ t₂

private def transportComparison {I C : Type} [SmallCategory I] [SmallCategory C]
    {D E : I ⥤ Cat.{0, 0}} (h : D = E) (F : Grothendieck D ⥤ C)
    (T : I ⥤ C)
    (t : F ⟶ Grothendieck.forget D ⋙ T) :
    transportEvaluation h F ⟶ Grothendieck.forget E ⋙ T := by
  subst E
  exact t

/-- The exact evaluation compares naturally to the original final vertex. -/
def fullComparison :
    fullEvaluation Q ⟶ Grothendieck.forget (fullFibers Q) ⋙ tail (C Q) :=
  transportComparison (fibers_eq Q) (evaluation Q) (tail (C Q))
    (actualComparison Q (spanCollapse_square Q))

end
end DaggerModels.PartII.JTGraphSpanEvaluation
