import OrdinaryDiscreteMapping
import DaggerModelsPartII.InjectiveKanModel
import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.JTSimplexUnitKan

/-!
# Actual evaluation of a coherent ordinary isomorphism

The parameter is the original groupoid-completed one-simplex, and evaluation
restricts along the original simplex-to-groupoid unit. For an injectively Kan
fibrant simplicial space this evaluation is a Kan fibration. Its two endpoint
maps are literally the original selected parameter vertices. No assertion that
its fibers are contractible, or that it detects equivalence arrows, is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalWalkingEvaluation

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The ordinary representable mapping space is its actual horizontal row. -/
def simplexMappingIso (W : Space) (n : ℕ) :
    diagramMappingSpace (discrete.obj (Δ[n] : SSet.{0})) W ≅ W.obj (op ⦋n⦌) :=
  OrdinaryDiscreteMapping.mappingIso (Δ[n] : SSet.{0}) W ≪≫
    DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso W n

/-- This identification retains the given horizontal simplex operator. -/
theorem simplexMappingIso_natural (W : Space) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    diagramMappingPrecomp (discrete.map (SSet.stdSimplex.map θ)) W ≫
        (simplexMappingIso W m).hom =
      (simplexMappingIso W n).hom ≫ W.map θ.op := by
  have h : DaggerNativeBisimplicialHorizontalMapping.horizontalPre
        (SSet.stdSimplex.map θ) W ≫
        (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso W m).hom =
      (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso W n).hom ≫
        W.map θ.op := by
    apply NatTrans.ext
    funext q η
    exact SSet.yonedaEquiv_map_comp θ η
  dsimp only [simplexMappingIso, Iso.trans_hom]
  rw [← Category.assoc, OrdinaryDiscreteMapping.mappingIso_natural, Category.assoc, h]
  simp only [Category.assoc]

/-- The space of maps from the actual horizontal walking isomorphism. -/
def walkingMapping (W : Space) : SSet.{0} :=
  diagramMappingSpace
    (discrete.obj (GroupoidSimplex.parameter.obj ⦋1⦌)) W

/-- Evaluation retains the actual original directed edge in the walking isomorphism. -/
def edgeEvaluation (W : Space) : walkingMapping W ⟶ W.obj (op ⦋1⦌) :=
  diagramMappingPrecomp
      (discrete.map (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) W ≫
    (simplexMappingIso W 1).hom

/-- Maps from the walking isomorphism form a Kan complex on a Kan-injective target. -/
theorem walkingMapping_isFibrant (W : Space) [IsFibrant W] :
    IsFibrant (walkingMapping W) :=
  InjectiveKanDiagram.model_mappingSpace_isFibrant SimplexCategoryᵒᵖ _ W

/-- Each actual horizontal row of a Kan-injective target is Kan. -/
theorem row_isFibrant (W : Space) [IsFibrant W] (n : ℕ) :
    IsFibrant (W.obj (op ⦋n⦌)) := by
  have : IsFibrant (diagramMappingSpace (discrete.obj (Δ[n] : SSet.{0})) W) :=
    InjectiveKanDiagram.model_mappingSpace_isFibrant SimplexCategoryᵒᵖ _ W
  exact isFibrant_of_iso (simplexMappingIso W n)

/-- Coherent-isomorphism evaluation is a fibration; no Segal hypothesis is required. -/
theorem edgeEvaluation_fibration (W : Space) [IsFibrant W] :
    Fibration (edgeEvaluation W) := by
  have : Mono (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) :=
    JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  have : Mono (discrete.map (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  have : Fibration (diagramMappingPrecomp
      (discrete.map (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration SimplexCategoryᵒᵖ _ W
  dsimp only [edgeEvaluation]
  infer_instance

/-- Both specified ordered vertices are the original vertices of the groupoid parameter. -/
theorem edgeEvaluation_vertex (W : Space) (i : Fin 2) :
    edgeEvaluation W ≫ W.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op =
      diagramMappingPrecomp
          (discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)) W ≫
        (simplexMappingIso W 0).hom := by
  rw [edgeEvaluation, Category.assoc, ← simplexMappingIso_natural]
  rw [← Category.assoc, ← diagramMappingPrecomp_comp, ← discrete.map_comp,
    JTParameterVertexKan.simplexUnit_vertex]

#print axioms simplexMappingIso_natural
#print axioms walkingMapping_isFibrant
#print axioms row_isFibrant
#print axioms edgeEvaluation_fibration
#print axioms edgeEvaluation_vertex

end

end DaggerModels.PartII.OrdinarySegalWalkingEvaluation
