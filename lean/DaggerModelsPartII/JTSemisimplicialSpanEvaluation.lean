import DaggerModelsPartII.JTGraphSpanSemisimplicial
import DaggerModelsPartII.FiniteLastVertexSupport
import DaggerModelsPartII.JTGraphSpanFamily
import DaggerModelsPartII.BoundaryNecklaceFiniteHom

/-! Descent of finite-support contractions along the original injective-phase span cover. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSemisimplicialSpanEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)

private abbrev C := TargetComma Q
private abbrev L := JTGraphCylinderSpanProjection.nativeCode Q
private abbrev F := JTGraphCylinderSimplexSpan.fibers (C Q) (L Q)
private abbrev original :=
  HomSpanRestriction.map ((CategoryOfElements.map A.ι).op)
private abbrev FA := original Q A ⋙ F Q
private abbrev FI := JTGraphSpanSemisimplicial.intoFull A.toSSet ⋙ FA Q A
private abbrev cover := JTGraphSpanSemisimplicial.cover A (L Q)

/-- The original injective-phase cylinder resolution with all internal necklaces. -/
abbrev Presentation := Grothendieck (FI Q A)

/-- The exact injective-phase cylinder resolution projects to the original simplices. -/
def projection : Grothendieck (FI Q A) ⥤ A.toSSet.Elementsᵒᵖ :=
  cover Q A ⋙ Grothendieck.forget (FA Q A) ⋙
    HomSpanRestriction.smaller A.toSSet.Elementsᵒᵖ

/-- The injective-phase resolution remains a weak cover of the subcomplex. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection Q A)) := by
  let i := JTGraphCylinderSimplexSpan.index (C Q) (L Q)
  letI : WeakEquivalence (nerveMap (cover Q A)) :=
    JTGraphSpanSemisimplicial.cover_weak A (L Q)
  letI : WeakEquivalence (nerveMap (Grothendieck.forget (FA Q A))) :=
    GrothendieckContractibleFibers.projection_weak (FA Q A)
      (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at
        ((i.obj ((original Q A).obj a))).1 ((i.obj ((original Q A).obj a))).2)
  letI : WeakEquivalence
      (nerveMap (HomSpanRestriction.smaller A.toSSet.Elementsᵒᵖ)) :=
    HomSpanRestriction.smaller_weak _
  change WeakEquivalence (nerveMap (cover Q A) ≫
    nerveMap (Grothendieck.forget (FA Q A)) ≫
      nerveMap (HomSpanRestriction.smaller A.toSSet.Elementsᵒᵖ))
  infer_instance

/-- Restrict any original full-span evaluation along the injective-phase cover. -/
def evaluation (E : Grothendieck (F Q) ⥤ C Q) :
    Grothendieck (FI Q A) ⥤ C Q :=
  cover Q A ⋙ Grothendieck.pre (F Q) (original Q A) ⋙ E

/-- Restrict its natural comparison to the final original target. -/
def comparison {E : Grothendieck (F Q) ⥤ C Q}
    (t : E ⟶ Grothendieck.forget (F Q) ⋙ JTGraphSpanFamily.tail (C Q)) :
    evaluation Q A E ⟶ projection Q A ⋙
      NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex (C Q) A :=
  Functor.whiskerLeft (cover Q A ⋙ Grothendieck.pre (F Q) (original Q A)) t

/-- Finite-support contractions on the injective-phase cover contract the original inclusion. -/
theorem inclusion_nullhomotopic (hA : A.toSSet.IsFinite)
    {E : Grothendieck (F Q) ⥤ C Q}
    (t : E ⟶ Grothendieck.forget (F Q) ⋙ JTGraphSpanFamily.tail (C Q))
    (hS : FiniteLastVertexSupport.SupportNullhomotopies (evaluation Q A E)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (C Q),
      Nonempty (SSet.Homotopy (R.map A.ι)
        (R.map (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v))) := by
  letI := projection_weak Q A
  exact FiniteLastVertexSupport.inclusion_nullhomotopic A
    (projection Q A) (evaluation Q A E) hA (comparison Q A t) hS

private abbrev B :=
  (SemiSimplexCategory.toSimplexCategory.op ⋙ A.toSSet).Elementsᵒᵖ

private theorem semi_finite_hom (n m : SemiSimplexCategory) : Finite (n ⟶ m) := by
  letI : Finite (SemiSimplexCategory.toSimplexCategory.obj n ⟶
    SemiSimplexCategory.toSimplexCategory.obj m) := inferInstance
  exact Finite.of_injective (fun f : n ⟶ m ↦
    SemiSimplexCategory.toSimplexCategory.map f)
      (fun _ _ h ↦ SemiSimplexCategory.toSimplexCategory.map_injective h)

/-- Between two fixed injective-phase simplices there are finitely many operators. -/
private theorem simplex_finite_hom (s t : B Q A) : Finite (s ⟶ t) := by
  letI : Finite (s.unop.fst.unop ⟶ t.unop.fst.unop) := semi_finite_hom _ _
  apply Finite.of_injective (f := fun (f : s ⟶ t) ↦ f.unop.val.unop)
  intro f g h
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact Quiver.Hom.unop_inj h

/-- The exact injective-phase span index has finite hom sets. -/
private theorem span_finite_hom (s t : JTGraphSpanSemisimplicial.Index A.toSSet) : Finite (s ⟶ t) :=
  HomSpanRestriction.finite_hom (simplex_finite_hom Q A) s t

private abbrev cylinderDiagram := JTGraphSpanSemisimplicial.intoOriginal A ⋙
  JTGraphCylinderSimplexSpan.index (C Q) (L Q) ⋙
    NecklaceCylinderJointDiagram.cylinderUnder

private theorem cylinder_finite_hom
    (P P' : BoundaryNecklaceComma.Presentation (cylinderDiagram Q A)) : Finite (P ⟶ P') :=
  BoundaryNecklaceComma.finite_hom (cylinderDiagram Q A) (span_finite_hom Q A) P P'

private theorem finite_hom_of_diagram_eq {I : Type} [SmallCategory I]
    (D E : I ⥤ Cat.{0, 0}) (h : D = E)
    (hE : ∀ P P' : Grothendieck E, Finite (P ⟶ P'))
    (P P' : Grothendieck D) : Finite (P ⟶ P') := by
  subst E
  exact hE P P'

/-- Internal necklace arrows remain finite between fixed resolution objects. -/
theorem resolution_finite_hom (P P' : Grothendieck (FI Q A)) : Finite (P ⟶ P') :=
  finite_hom_of_diagram_eq (FI Q A)
    (BoundaryNecklaceComma.fiberDiagram (cylinderDiagram Q A)) rfl
    (cylinder_finite_hom Q A) P P'

end
end DaggerModels.PartII.JTSemisimplicialSpanEvaluation
