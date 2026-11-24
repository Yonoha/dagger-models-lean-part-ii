import DaggerModelsPartII.ResolutionAdjunction

/-!
# Local finite presentability of the resolution diagram category

Mathlib's free representable generators for a presheaf category take the
Part I finitely presentable strong generator to a finitely presentable
strong generator in the outer simplicial direction.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace DaggerModels.PartII

noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0
local instance : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- The underlying category in `cs.lem.reedy` is locally finitely presentable. -/
theorem resolutionDiagramLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} ResolutionDiagram.{u} := by
  obtain ⟨P, hsmall, hstrong, hp⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
      DaggerSSet.{u} Cardinal.aleph0.{u}).mp daggerSSetLocallyFinitelyPresentable
  let G := ObjectProperty.ofObj
    (fun T : SimplexCategory × Subtype P ↦ Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    ResolutionDiagram.{u} Cardinal.aleph0.{u}).mpr
  refine ⟨G, inferInstance, Presheaf.isStrongGenerator hstrong SimplexCategory, ?_⟩
  rintro _ ⟨⟨n, M, hM⟩⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0.{u} := by
    rw [← isCardinalPresentable_iff]
    exact hp M hM
  rw [isCardinalPresentable_iff]
  change IsCardinalPresentable (Presheaf.freeYoneda n M) Cardinal.aleph0.{u}
  infer_instance

/-- Local presentability for the combinatoriality clause. -/
theorem resolutionDiagramLocallyPresentable :
    IsLocallyPresentable.{u} ResolutionDiagram.{u} :=
  ⟨Cardinal.aleph0.{u}, inferInstance, resolutionDiagramLocallyFinitelyPresentable⟩

end

end DaggerModels.PartII
