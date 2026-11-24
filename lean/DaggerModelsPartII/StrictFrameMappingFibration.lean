import DaggerModelsPartII.StrictFrameMappingWeak
import DaggerModelsPartII.DiagramHomKanFibration

/-!
# Kan fibrations on strict Hom from relative cosimplicial frames

The retained horn-restriction theorem applies to a Reedy fibration between
homotopically constant opposite diagrams. The original native/plain-Hom
isomorphism transfers it to the literal strict mapping simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.StrictFrameMappingFibration

open StrictFrameMappingWeak

noncomputable section

variable {C : Type u} [Category.{0} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- Relative cofibrant frames with weak structure maps give a Kan
fibration on the actual strict Hom simplicial sets into a fibrant target. -/
theorem strictMapping_map_fibration (Z : C) [IsFibrant Z]
    {D E : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} [IsFibrant D] [IsFibrant E]
    (hD : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences Cᵒᵖ (D.map g))
    (hE : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences Cᵒᵖ (E.map g))
    (g : D ⟶ E) (hg : reedyMatchingProperty (fibrations Cᵒᵖ) g) :
    Fibration ((strictMapping Z).map g) := by
  haveI : IsCofibrant (op Z) := by
    apply (cofibration_iff _).mpr
    rw [cofibrations_op]
    exact (fibration_iff _).mp
      ((isFibrant_iff_of_isTerminal (initial.to (op Z)).unop
        (terminalUnopOfInitial initialIsInitial)).mp inferInstance)
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  have h : Fibration (F.map g) := by
    change Fibration (diagramHomPostcomp (op Z) g)
    exact diagramHomPostcomp_kan_fibration (op Z) hD hE g hg
  let e := nativeStrictIso Z
  let ea : Arrow.mk (F.map g) ≅ Arrow.mk ((strictMapping Z).map g) :=
    Arrow.isoMk (e.app D) (e.app E) (e.hom.naturality g).symm
  exact (fibration_iff _).mpr
    (((fibrations SSet.{0}).arrow_mk_iso_iff ea).mp ((fibration_iff _).mp h))

end

end DaggerModels.PartII.StrictFrameMappingFibration
