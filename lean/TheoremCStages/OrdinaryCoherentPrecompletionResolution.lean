import OrdinaryCoherentCompletenessCriterion
import OrdinarySegalCotensorSegal
import OrdinarySegalVerticalPrecompletion
import OrdinarySegalResolutionMappingFibers
import NativeBisimplicialDiagonalWeak

/-!
# The full coherent-arrow resolution of the corrected precompletion

The original groupoid-simplex cotensors act on their entire coherent-arrow
component images. Walking evaluation is weak in each row and on the literal
vertical diagonal. The endpoint map on this diagonal is kept explicitly;
its comparison with the coherent image after fibrant replacement is separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentPrecompletionResolution

open OrdinaryCSSLocalization (Space walkingSpace)
open OrdinaryCoherentArrowNaturality
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex coherentEvaluation)
open OrdinaryCoherentCompletenessCriterion (endpoint)

noncomputable section

/-- The actual component-saturated coherent-arrow image, functorial in the target. -/
def coherentArrowFunctor : Space ⥤ SSet.{0} where
  obj W := (coherentArrowSubcomplex W).toSSet
  map f := coherentArrowMap f
  map_id W := by
    apply (cancel_mono (coherentArrowSubcomplex W).ι).mp
    rw [coherentArrowMap_inclusion]
    simp only [NatTrans.id_app, Category.comp_id, Category.id_comp]
  map_comp {W X Y} f g := by
    apply (cancel_mono (coherentArrowSubcomplex Y).ι).mp
    calc
      coherentArrowMap (f ≫ g) ≫ (coherentArrowSubcomplex Y).ι =
          (coherentArrowSubcomplex W).ι ≫ (f ≫ g).app (op ⦋1⦌) :=
        coherentArrowMap_inclusion (f ≫ g)
      _ = ((coherentArrowSubcomplex W).ι ≫ f.app (op ⦋1⦌)) ≫
          g.app (op ⦋1⦌) := by rw [NatTrans.comp_app, Category.assoc]
      _ = (coherentArrowMap f ≫ (coherentArrowSubcomplex X).ι) ≫
          g.app (op ⦋1⦌) := by rw [coherentArrowMap_inclusion]
      _ = (coherentArrowMap f ≫ coherentArrowMap g) ≫
          (coherentArrowSubcomplex Y).ι := by
        simpa only [Category.assoc] using
          (congrArg (fun m ↦ coherentArrowMap f ≫ m)
            (coherentArrowMap_inclusion g)).symm

/-- Walking evaluation maps into exactly the original coherent component image. -/
def evaluationNatural : diagramMappingTarget walkingSpace ⟶ coherentArrowFunctor where
  app W := coherentEvaluation W
  naturality {_ _} f := coherentEvaluation_post f

/-- Retain the original selected endpoint as a natural transformation. -/
def endpointNatural : coherentArrowFunctor ⟶
    (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋0⦌) where
  app W := endpoint W
  naturality {_ _} f := OrdinaryCoherentCompletenessCriterion.endpoint_natural f

/-- The original outer parameter and all coherent-arrow simplices are retained. -/
def coherentResolution (W : Space) : BiSSet.{0} :=
  OrdinarySegalPrecompletion.resolution W ⋙ coherentArrowFunctor

/-- The whole walking resolution maps to its exact coherent-arrow resolution. -/
def evaluationResolution (W : Space) :
    OrdinarySegalPrecompletion.resolution W ⋙ diagramMappingTarget walkingSpace ⟶
      coherentResolution W :=
  Functor.whiskerLeft (OrdinarySegalPrecompletion.resolution W) evaluationNatural

/-- The original selected endpoint in every outer parameter. -/
def endpointResolution (W : Space) : coherentResolution W ⟶
    OrdinarySegalResolutionMappingFibers.rowResolution W 0 :=
  Functor.whiskerLeft (OrdinarySegalPrecompletion.resolution W) endpointNatural

/-- Its actual diagonal targets the object row of the corrected precompletion. -/
def diagonalEndpoint (W : Space) :
    diagonalFunctor.obj (coherentResolution W) ⟶
      (OrdinarySegalVerticalPrecompletion.precompletion W).obj (op ⦋0⦌) :=
  diagonalFunctor.map (endpointResolution W)

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The whole evaluation is weak in every original groupoid-simplex row. -/
theorem evaluationResolution_row_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((evaluationResolution W).app q) := by
  have : IsFibrant ((OrdinarySegalPrecompletion.resolution W).obj q) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant
      (GroupoidSimplex.parameter.obj q.unop) W inferInstance
  exact ((mem_trivialFibrations_iff _).mp
    (OrdinarySegalCoherentEvaluationTrivialFibration.coherentEvaluation_trivialFibration
      ((OrdinarySegalPrecompletion.resolution W).obj q)
      (OrdinarySegalCotensorSegal.cotensor_segalCondition
        (GroupoidSimplex.parameter.obj q.unop) W hSegal))).2

/-- Taking the literal vertical diagonal preserves this complete evaluation comparison. -/
theorem evaluationResolution_diagonal_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (diagonalFunctor.map (evaluationResolution W)) :=
  DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak _
    (evaluationResolution_row_weak W hSegal)

#print axioms coherentArrowFunctor
#print axioms endpointResolution
#print axioms evaluationResolution_row_weak
#print axioms evaluationResolution_diagonal_weak

end

end DaggerModels.PartII.OrdinaryCoherentPrecompletionResolution
