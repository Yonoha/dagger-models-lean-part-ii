import DaggerModelsPartII.JTCoveredJointCylinder
import DaggerModelsPartII.JTGraphSpanEvaluation
import DaggerModelsPartII.JTSemisimplicialSpanEvaluation

/-! The covered exact evaluation on the span resolution used in Theorem C. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

namespace DaggerModels.PartII.JTCoveredSpanEvaluation

open JTGraphFactoredPresentation (TargetComma)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphSpanLift (spanFamily)
open JTJointRelativeGraphFamily (leftLeg rightLeg originalLeft originalRight original_rawOn)
open JTTargetJointMarks (Joint)

noncomputable section

private theorem precomp_support_nullhomotopies {U V Z : Type}
    [SmallCategory U] [SmallCategory V] [SmallCategory Z]
    (i : U ⥤ V) (G : V ⥤ Z) (h : FiniteLastVertexSupport.SupportNullhomotopies G) :
    FiniteLastVertexSupport.SupportNullhomotopies (i ⋙ G) := by
  intro S hS
  let f := S.ι ≫ nerveMap i
  let K := SSet.Subcomplex.range f
  let r := SSet.Subcomplex.toRange f
  letI : S.toSSet.IsFinite := hS
  have hK : K.toSSet.IsFinite := SSet.isFinite_range f
  obtain ⟨v, ⟨H⟩⟩ := h K hK
  have he : nerveMap i ≫ nerveMap G = nerveMap (i ⋙ G) :=
    (nerveFunctor.map_comp i.toCatHom G.toCatHom).symm
  refine ⟨v, ⟨(H.precomp (R.map r)).congr ?_ ?_⟩⟩
  · change R.map r ≫ R.map (K.ι ≫ nerveMap G) = R.map (S.ι ≫ nerveMap (i ⋙ G))
    have hr : r ≫ K.ι = f := SSet.Subcomplex.toRange_ι f
    rw [← R.map_comp, ← Category.assoc, hr]
    simp only [f, Category.assoc, he]
  · let point (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X
    have hp : r ≫ point K.toSSet = point S.toSSet :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change R.map r ≫ R.map (point K.toSSet ≫ v) = R.map (point S.toSSet ≫ v)
    rw [← R.map_comp, ← Category.assoc, hp]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (j : Joint Q.code) (hfirst : j.val ≠ 0) (hlast : j.val ≠ Fin.last Q.code.len)

private abbrev fibers := JTGraphCylinderSimplexSpan.fibers (TargetComma Q) (nativeCode Q)

/-- The covered presentation of the whole original span family. -/
abbrev Presentation :=
  BoundaryNecklaceComma.Presentation
    (JTCoveredJointCylinder.reduced (spanFamily Q) j
      (originalLeft (spanFamily Q) j) (originalRight (spanFamily Q) j) hfirst hlast)

/-- Evaluate the exact original span labels on the covered cylinders. -/
abbrev evaluate : Presentation Q j hfirst hlast ⥤ TargetComma Q :=
  JTCoveredJointCylinder.evaluate (spanFamily Q) j
    (originalLeft (spanFamily Q) j) (originalRight (spanFamily Q) j) hfirst hlast
    (original_rawOn (spanFamily Q) (leftLeg (spanFamily Q) j))
    (original_rawOn (spanFamily Q) (rightLeg (spanFamily Q) j))

/-- Embed every original span and internal necklace via its original graph. -/
def lift : Grothendieck (fibers Q) ⥤ Presentation Q j hfirst hlast :=
  JTGraphSpanEvaluation.parametrizedPresentationMap Q ⋙
    JTCoveredJointCylinder.originalPresentationSection (spanFamily Q) j hfirst hlast

/-- The lifted evaluation is the full-span evaluation used in Theorem C. -/
theorem evaluate_lift :
    lift Q j hfirst hlast ⋙ evaluate Q j hfirst hlast = JTGraphSpanEvaluation.fullEvaluation Q := by
  let f := JTGraphSpanEvaluation.parametrizedPresentationMap Q
  let g := JTCoveredJointCylinder.originalPresentationSection (spanFamily Q) j hfirst hlast
  let e := evaluate Q j hfirst hlast
  have he : g ⋙ e = JTParametrizedTargetFamilies.evaluate (spanFamily Q) :=
    JTCoveredJointCylinder.evaluate_originalSection (spanFamily Q) j hfirst hlast
  exact (Functor.assoc f g e).trans
    ((congrArg (fun a ↦ f ⋙ a) he).trans
      (JTGraphSpanEvaluation.evaluate_parametrizedPresentationMap Q))

variable (A : (nerve (TargetComma Q)).Subcomplex)

/-- Lift the exact injective-phase resolution to the covered original spans. -/
def liftSemisimplicial : JTSemisimplicialSpanEvaluation.Presentation Q A ⥤
    Presentation Q j hfirst hlast :=
  JTGraphSpanSemisimplicial.cover A (nativeCode Q) ⋙
    Grothendieck.pre (fibers Q) (HomSpanRestriction.map ((CategoryOfElements.map A.ι).op)) ⋙
    lift Q j hfirst hlast

set_option maxHeartbeats 1000000 in
/-- The original injective-phase evaluation agrees on all finite supports
with the covered evaluation restricted along its natural lift. -/
theorem evaluate_liftSemisimplicial :
    liftSemisimplicial Q j hfirst hlast A ⋙ evaluate Q j hfirst hlast =
      JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q) := by
  let f := JTGraphSpanSemisimplicial.cover A (nativeCode Q)
  let g := Grothendieck.pre (fibers Q) (HomSpanRestriction.map ((CategoryOfElements.map A.ι).op))
  let h := lift Q j hfirst hlast
  let e := evaluate Q j hfirst hlast
  let m := JTGraphSpanEvaluation.fullEvaluation Q
  change (f ⋙ g ⋙ h) ⋙ e = f ⋙ g ⋙ m
  exact (Functor.assoc f (g ⋙ h) e).trans
    (congrArg (fun a ↦ f ⋙ a) ((Functor.assoc g h e).trans
      (congrArg (fun a ↦ g ⋙ a) (evaluate_lift Q j hfirst hlast))))

set_option maxHeartbeats 1000000 in
/-- Finite supports of the original evaluation map into finite supports
of the covered evaluation, and inherit their contractions. -/
theorem support_nullhomotopies
    (h : FiniteLastVertexSupport.SupportNullhomotopies (evaluate Q j hfirst hlast)) :
    FiniteLastVertexSupport.SupportNullhomotopies
      (JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)) := by
  have he := evaluate_liftSemisimplicial Q j hfirst hlast A
  exact he ▸ precomp_support_nullhomotopies (liftSemisimplicial Q j hfirst hlast A) _ h

set_option maxHeartbeats 1000000 in
/-- Contract the actual inclusion of an arbitrary finite subcomplex of the
fixed-target comma by contracting finite supports of the covered evaluation. -/
theorem inclusion_nullhomotopic (hA : A.toSSet.IsFinite)
    (h : FiniteLastVertexSupport.SupportNullhomotopies (evaluate Q j hfirst hlast)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
      Nonempty (SSet.Homotopy (R.map A.ι)
        (R.map (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v))) :=
  JTSemisimplicialSpanEvaluation.inclusion_nullhomotopic Q A hA
    (JTGraphSpanEvaluation.fullComparison Q) (support_nullhomotopies Q j hfirst hlast A h)

end

end DaggerModels.PartII.JTCoveredSpanEvaluation
