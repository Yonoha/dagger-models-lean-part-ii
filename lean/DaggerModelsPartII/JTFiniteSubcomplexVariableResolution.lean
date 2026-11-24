import DaggerModelsPartII.JTGraphVariableTotalComparison
import DaggerModelsPartII.JTRezkRecognitionLastVertex
import DaggerModelsPartII.FiniteLastVertexFactor
import DaggerModelsPartII.BoundedSimplex

/-! Pull the checked exact chain-parameter diagram back to a finite subcomplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteSubcomplexVariableResolution

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeTransport (resolutionDiagram)
open JTGraphVariableResolutionCategory (toPresentation totalComparison)
open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex)
open JTRezkRecognitionLastVertex (theoremC_of_last_vertex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)

/-- Resolve every original last vertex by all native sources, time parameters,
and internal cylinder necklaces, transported along the original suffix maps. -/
abbrev diagram : A.toSSet.Elementsᵒᵖ ⥤ Cat.{0, 0} :=
  lastVertexOnSubcomplex (TargetComma Q) A ⋙ resolutionDiagram Q

/-- The comparison retains every original last vertex and suffix. -/
abbrev toOriginal : Grothendieck (diagram Q A) ⥤ TargetComma Q :=
  Grothendieck.forget (diagram Q A) ⋙ lastVertexOnSubcomplex (TargetComma Q) A

/-- Evaluate the full resolved diagram on the last vertices of a subcomplex. -/
abbrev toCylinder (C : Grothendieck (resolutionDiagram Q) ⥤ TargetComma Q) :
    Grothendieck (diagram Q A) ⥤ TargetComma Q :=
  Grothendieck.pre (resolutionDiagram Q) (lastVertexOnSubcomplex (TargetComma Q) A) ⋙ C

/-- Restrict a comparison of the full cylinder to the exact last vertices of a subcomplex. -/
def restrictComparison
    {C : Grothendieck (resolutionDiagram Q) ⥤ TargetComma Q}
    (p : C ⟶ Grothendieck.forget (resolutionDiagram Q)) :
    toCylinder Q A C ⟶ toOriginal Q A :=
  Functor.whiskerLeft
    (Grothendieck.pre (resolutionDiagram Q) (lastVertexOnSubcomplex (TargetComma Q) A)) p

/-- The original fixed-target cylinder evaluation on the resolution of a subcomplex. -/
abbrev cylinderEvaluation : Grothendieck (diagram Q A) ⥤ TargetComma Q :=
  toCylinder Q A (toPresentation Q ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse)

/-- The original cylinder evaluation compares to the last-vertex projection. -/
def cylinderComparison : cylinderEvaluation Q A ⟶ toOriginal Q A :=
  restrictComparison Q A (totalComparison Q)

theorem projection_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (diagram Q A))) :=
  JTGraphVariableResolutionCategory.projection_weak_of (lastVertexOnSubcomplex (TargetComma Q) A)

/-- The original Theorem C follows from weakly contractible factorizations
on the full variable-source resolution of each finite subcomplex. -/
theorem theoremC_of_factors
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ (E : Cat.{0, 0}) (F : Grothendieck (diagram Q A) ⥤ E) (G : E ⥤ TargetComma Q),
          GW (DaggerOriginalProductGadget.pointMap (nerve E)) ∧
            NatTransZigzag (toOriginal Q A) (F ⋙ G)) :
    TheoremCStatement.statement := by
  apply theoremC_of_last_vertex
  intro W hW x y Q A hA
  obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA
  let P := Grothendieck.forget (diagram Q A)
  letI : WeakEquivalence (nerveMap P) := projection_weak Q A
  exact FiniteLastVertexFactor.last_vertex_nullhomotopic A P F G hE H

/-- A weakly contractible factor of the cylinder comparison supplies the
nullhomotopy of the original last-vertex diagram. -/
theorem lastVertex_nullhomotopic_of_cylinder_factor {E : Type} [SmallCategory E]
    {C : Grothendieck (resolutionDiagram Q) ⥤ TargetComma Q}
    (p : C ⟶ Grothendieck.forget (resolutionDiagram Q))
    (F : Grothendieck (diagram Q A) ⥤ E) (G : E ⥤ TargetComma Q)
    (hE : GW (DaggerOriginalProductGadget.pointMap (nerve E)))
    (h : NatTransZigzag (toCylinder Q A C) (F ⋙ G)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap (lastVertexOnSubcomplex (TargetComma Q) A)))
        (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve A.toSSet.Elementsᵒᵖ) ≫ v))) := by
  let P := Grothendieck.forget (diagram Q A)
  letI : WeakEquivalence (nerveMap P) := projection_weak Q A
  have hp : NatTransZigzag (toCylinder Q A C) (toOriginal Q A) :=
    .rel _ _ ⟨restrictComparison Q A p⟩
  exact FiniteLastVertexFactor.last_vertex_nullhomotopic A P F G hE
    (.trans _ _ _ (.symm _ _ hp) h)

/-- Factoring the actual cylinder evaluation on every finite subcomplex
through a category with weakly contractible nerve suffices for Theorem C. -/
theorem theoremC_of_cylinder_factors
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ (E : Cat.{0, 0}) (F : Grothendieck (diagram Q A) ⥤ E) (G : E ⥤ TargetComma Q),
          GW (DaggerOriginalProductGadget.pointMap (nerve E)) ∧
            NatTransZigzag (cylinderEvaluation Q A) (F ⋙ G)) :
    TheoremCStatement.statement := by
  apply theoremC_of_last_vertex
  intro W hW x y Q A hA
  obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA
  exact lastVertex_nullhomotopic_of_cylinder_factor Q A (totalComparison Q) F G hE H

variable (n : ℕ)

/-- Use the original resolution on the finite-object category of bounded simplices. -/
abbrev boundedDiagram : (BoundedSimplex.bounded A.toSSet n).FullSubcategory ⥤ Cat.{0, 0} :=
  BoundedSimplex.inclusion A.toSSet n ⋙ diagram Q A

/-- The restriction keeps the actual cylinder evaluation and its comparison. -/
abbrev boundedEvaluation : Grothendieck (boundedDiagram Q A n) ⥤ TargetComma Q :=
  Grothendieck.pre (diagram Q A) (BoundedSimplex.inclusion A.toSSet n) ⋙ cylinderEvaluation Q A

/-- A factorization over the bounded simplex category gives the nullhomotopy
of the original last-vertex map, including all degeneracies of the subcomplex. -/
theorem lastVertex_nullhomotopic_of_bounded_factor {E : Type} [SmallCategory E]
    (hn : ∀ s : A.toSSet.N, s.dim ≤ n)
    (F : Grothendieck (boundedDiagram Q A n) ⥤ E) (G : E ⥤ TargetComma Q)
    (hE : GW (DaggerOriginalProductGadget.pointMap (nerve E)))
    (h : NatTransZigzag (boundedEvaluation Q A n) (F ⋙ G)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap (lastVertexOnSubcomplex (TargetComma Q) A)))
        (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve A.toSSet.Elementsᵒᵖ) ≫ v))) := by
  let I := BoundedSimplex.inclusion A.toSSet n
  let L := lastVertexOnSubcomplex (TargetComma Q) A
  let P := Grothendieck.forget (boundedDiagram Q A n) ⋙ I
  haveI : WeakEquivalence (nerveMap I) := BoundedSimplex.inclusion_weak hn
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget (boundedDiagram Q A n))) :=
    JTGraphVariableResolutionCategory.projection_weak_of (I ⋙ L)
  haveI : WeakEquivalence (nerveMap P) := by
    change WeakEquivalence (nerveMap (Grothendieck.forget (boundedDiagram Q A n)) ≫ nerveMap I)
    infer_instance
  have p : boundedEvaluation Q A n ⟶ P ⋙ L :=
    Functor.whiskerLeft (Grothendieck.pre (diagram Q A) I) (cylinderComparison Q A)
  exact FiniteLastVertexFactor.last_vertex_nullhomotopic A P F G hE
    (.trans _ _ _ (.symm _ _ (.rel _ _ ⟨p⟩)) h)

/-- The original Theorem C follows from factorizations of the actual
cylinder evaluation over bounded simplex diagrams. -/
theorem theoremC_of_bounded_factors
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ (n : ℕ) (_ : ∀ s : A.toSSet.N, s.dim ≤ n)
          (E : Cat.{0, 0}) (F : Grothendieck (boundedDiagram Q A n) ⥤ E) (G : E ⥤ TargetComma Q),
          GW (DaggerOriginalProductGadget.pointMap (nerve E)) ∧
            NatTransZigzag (boundedEvaluation Q A n) (F ⋙ G)) :
    TheoremCStatement.statement := by
  apply theoremC_of_last_vertex
  intro W hW x y Q A hA
  obtain ⟨n, hn, E, F, G, hE, H⟩ := h W hW x y Q A hA
  exact lastVertex_nullhomotopic_of_bounded_factor Q A n hn F G hE H

end
end DaggerModels.PartII.JTFiniteSubcomplexVariableResolution
