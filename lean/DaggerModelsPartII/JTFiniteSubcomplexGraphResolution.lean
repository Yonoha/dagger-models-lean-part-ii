import DaggerModelsPartII.JTGraphChainParameterSection
import DaggerModelsPartII.JTRezkRecognitionLastVertex
import DaggerModelsPartII.FiniteLastVertexFactor

/-! Pull the checked exact chain-parameter diagram back to a finite subcomplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteSubcomplexGraphResolution

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphChainParameterSection (diagram)
open JTGraphCylinderSimplexSpan (Simplices)
open JTGraphSimplexLastVertex (lastVertex)
open JTRezkRecognitionLastVertex (theoremC_of_last_vertex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)

private abbrev K := A.toSSet.Elementsᵒᵖ

private abbrev includeSimplices : K Q A ⥤ Simplices (TargetComma Q) :=
  (CategoryOfElements.map A.ι).op

/-- All actual finite-chain parameters over the simplices in the prescribed subcomplex. -/
abbrev fibers : K Q A ⥤ Cat.{0, 0} :=
  includeSimplices Q A ⋙ diagram Q ⋙ SimplicialResolutionFunctor.elementsOpposite

/-- Forgetting the exact time choices is weak on the entire subcomplex's simplex category. -/
theorem projection_weak : WeakEquivalence (nerveMap (Grothendieck.forget (fibers Q A))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun P ↦
    JTGraphArrowParameterDiagram.timeSimplices_point_GW Q
      ((JTGraphChainArrowIndex.chainIndex (TargetComma Q)).obj ((includeSimplices Q A).obj P)))

/-- The original last object, with the original suffix along each simplex operator. -/
def toOriginal : Grothendieck (fibers Q A) ⥤ TargetComma Q :=
  Grothendieck.forget (fibers Q A) ⋙ includeSimplices Q A ⋙ lastVertex (TargetComma Q)

/-- A contraction on the original restricted chain-parameter resolution suffices
for the last-vertex nullhomotopy of this finite diagram. -/
theorem last_vertex_nullhomotopic (v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q))
    (h : SSet.Homotopy (R.map (nerveMap (toOriginal Q A)))
      (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve (Grothendieck (fibers Q A))) ≫ v))) :
    Nonempty (SSet.Homotopy
      (R.map (nerveMap (NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex (TargetComma Q) A)))
      (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve (K Q A)) ≫ v))) := by
  let p := nerveMap (Grothendieck.forget (fibers Q A))
  have hp : WeakEquivalence p := projection_weak Q A
  have hRp : WeakEquivalence (R.map p) := FiniteWeakCover.weak_singular p
  refine ⟨FiniteWeakCover.homotopyOfPrecomp (R.map p) ?_⟩
  rw [← R.map_comp, ← R.map_comp, ← Category.assoc]
  have he : p ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve (K Q A)) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (Grothendieck (fibers Q A))) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact h

/-- The original Theorem C follows from contracting the last-vertex map
on the exact graph resolution of each finite subcomplex. -/
theorem theoremC_of_resolved_finite_nullhomotopies
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
          Nonempty (SSet.Homotopy (R.map (nerveMap (toOriginal Q A)))
            (R.map (SSet.stdSimplex.isTerminalObj₀.from
              (nerve (Grothendieck (fibers Q A))) ≫ v)))) :
    TheoremCStatement.statement := by
  apply theoremC_of_last_vertex
  intro W hW x y Q A hA
  obtain ⟨v, ⟨H⟩⟩ := h W hW x y Q A hA
  exact ⟨v, last_vertex_nullhomotopic Q A v H⟩


/-- If the exact resolved last-vertex maps can be deformed to maps through
weakly contractible categories over their original target commas, the
original four Quillen equivalences follow. -/
theorem theoremC_of_resolved_finite_factors
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
        (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
        ∃ (E : Cat.{0, 0}) (F : Grothendieck (fibers Q A) ⥤ E) (G : E ⥤ TargetComma Q),
          GW (DaggerOriginalProductGadget.pointMap (nerve E)) ∧
            NatTransZigzag (toOriginal Q A) (F ⋙ G)) :
    TheoremCStatement.statement := by
  apply theoremC_of_last_vertex
  intro W hW x y Q A hA
  obtain ⟨E, F, G, hE, H⟩ := h W hW x y Q A hA
  let P := Grothendieck.forget (fibers Q A)
  letI : WeakEquivalence (nerveMap P) := projection_weak Q A
  exact FiniteLastVertexFactor.last_vertex_nullhomotopic A P F G hE H

end
end DaggerModels.PartII.JTFiniteSubcomplexGraphResolution
