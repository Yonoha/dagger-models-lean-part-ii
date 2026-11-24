import DaggerModelsPartII.JTGraphSpanFamily
import DaggerModelsPartII.HomSpanRestriction
import DaggerModelsPartII.JTFiniteCylinderSupport
import DaggerModelsPartII.BoundaryNecklaceFiniteHom

/-! A finite diagram of explicit original cylinders over each finite subcomplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTBoundedSpanEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphCylinderSimplexSpan (fibers)
open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex) (n : ℕ)

private abbrev B := (BoundedSimplex.bounded A.toSSet n).FullSubcategory
private abbrev I := BoundedSimplex.inclusion A.toSSet n
private abbrev A₀ := A.toSSet.Elementsᵒᵖ
private abbrev originalSimplices : A₀ Q A ⥤ JTGraphCylinderSimplexSpan.Simplices (TargetComma Q) :=
  (CategoryOfElements.map A.ι).op

/-- The actual factorizations between the finitely many bounded simplices. -/
abbrev Index := HomSpanRestriction.Spans (B Q A n)

theorem finite_objects (hA : A.toSSet.IsFinite) : Finite (Index Q A n) := by
  letI := hA
  letI := BoundedSimplex.finite_objects A.toSSet n
  exact HomSpanRestriction.finite_objects _ (BoundedSimplex.finite_hom A.toSSet n)

theorem finite_hom (s t : Index Q A n) : Finite (s ⟶ t) :=
  HomSpanRestriction.finite_hom (BoundedSimplex.finite_hom A.toSSet n) s t

private abbrev includeSpans :
    Index Q A n ⥤ JTGraphCylinderSimplexSpan.SpanIndex (TargetComma Q) :=
  HomSpanRestriction.map (I Q A n ⋙ originalSimplices Q A)

/-- The cylinder time degree is the dimension of the smaller bounded simplex. -/
theorem time_degree_le (P : Index Q A n) :
    (((JTGraphCylinderSimplexSpan.index (TargetComma Q) (nativeCode Q)).obj
      ((includeSpans Q A n).obj P)).2).len ≤ n :=
  P.unop.fst.1.unop.property

private abbrev fullFibers := fibers (TargetComma Q) (nativeCode Q)

/-- Each object of the finite index carries its one explicit source and time
cylinder, keeping all internal neckaces in that cylinder. -/
abbrev diagram : Index Q A n ⥤ Cat.{0, 0} :=
  includeSpans Q A n ⋙ fullFibers Q

/-- Two fixed objects of the full bounded cylinder have only finitely many
actual arrows, including all their admissible internal necklace operators. -/
theorem resolution_finite_hom (P P' : Grothendieck (diagram Q A n)) : Finite (P ⟶ P') :=
  BoundaryNecklaceComma.finite_hom
    (includeSpans Q A n ⋙ JTGraphCylinderSimplexSpan.index (TargetComma Q) (nativeCode Q) ⋙
      NecklaceCylinderJointDiagram.cylinderUnder)
    (finite_hom Q A n) P P'

private abbrev p : Grothendieck (diagram Q A n) ⥤ A₀ Q A :=
  Grothendieck.forget (diagram Q A n) ⋙ HomSpanRestriction.smaller (B Q A n) ⋙ I Q A n

/-- Restrict the whole evaluation along the original bounded spans. -/
def evaluation (E : Grothendieck (fullFibers Q) ⥤ TargetComma Q) :
    Grothendieck (diagram Q A n) ⥤ TargetComma Q :=
  Grothendieck.pre (fullFibers Q) (includeSpans Q A n) ⋙ E

private theorem projection_weak (hn : ∀ s : A.toSSet.N, s.dim ≤ n) :
    WeakEquivalence (nerveMap (p Q A n)) := by
  let G := diagram Q A n
  let k := JTGraphCylinderSimplexSpan.index (TargetComma Q) (nativeCode Q)
  letI : WeakEquivalence (nerveMap (Grothendieck.forget G)) :=
    GrothendieckContractibleFibers.projection_weak G
      (fun s ↦ JTHomotopyTargetComma.fiber_point_GW_at
        (k.obj ((includeSpans Q A n).obj s)).1 (k.obj ((includeSpans Q A n).obj s)).2)
  letI := HomSpanRestriction.smaller_weak (B Q A n)
  letI := BoundedSimplex.inclusion_weak hn
  change WeakEquivalence (nerveMap (Grothendieck.forget G) ≫
    nerveMap (HomSpanRestriction.smaller (B Q A n)) ≫ nerveMap (I Q A n))
  infer_instance

/-- The restricted evaluation compares naturally to the original last vertex. -/
def comparison {E : Grothendieck (fullFibers Q) ⥤ TargetComma Q}
    (t : E ⟶ Grothendieck.forget (fullFibers Q) ⋙ JTGraphSpanFamily.tail (TargetComma Q)) :
    evaluation Q A n E ⟶ p Q A n ⋙ lastVertexOnSubcomplex (TargetComma Q) A :=
  Functor.whiskerLeft (Grothendieck.pre (fullFibers Q) (includeSpans Q A n)) t

/-- Descend nullhomotopies of the finite supports of a bounded span evaluation. -/
theorem inclusion_nullhomotopic (hA : A.toSSet.IsFinite) (hn : ∀ s : A.toSSet.N, s.dim ≤ n)
    {E : Grothendieck (fullFibers Q) ⥤ TargetComma Q}
    (t : E ⟶ Grothendieck.forget (fullFibers Q) ⋙ JTGraphSpanFamily.tail (TargetComma Q))
    (hS : FiniteLastVertexSupport.SupportNullhomotopies (evaluation Q A n E)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
      Nonempty (SSet.Homotopy (R.map A.ι)
        (R.map (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v))) := by
  letI := projection_weak Q A n hn
  exact FiniteLastVertexSupport.inclusion_nullhomotopic A (p Q A n) (evaluation Q A n E)
    hA (comparison Q A n t) hS

end
end DaggerModels.PartII.JTBoundedSpanEvaluation

