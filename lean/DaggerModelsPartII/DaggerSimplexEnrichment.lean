import DaggerModelsPartII.DaggerSimplexIndex
import DaggerModelsPartII.DiscreteDaggerEnrichment

/-! The path model of the free dagger simplices embeds fully faithfully
in simplicial dagger categories. -/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex DaggerUnitaryDiscrete

namespace DaggerModels.PartII

noncomputable section

/-- The constant enrichment of the ordinary free dagger simplex. -/
def enrichedDaggerSimplex (n : DaggerSimplex) : DaggerSimplicialCat.{0, 0} :=
  ordinaryEnrichment (FreeDaggerSimplex n.len)

/-- The path-model Hom includes exactly all enriched dagger functors
between the corresponding constant enrichments. -/
def enrichedDaggerSimplexHomEquiv (m n : DaggerSimplex) :
    (m ⟶ n) ≃ (enrichedDaggerSimplex m ⟶ enrichedDaggerSimplex n) :=
  (show (m ⟶ n) ≃ {F : FreeDaggerSimplex m.len ⥤ FreeDaggerSimplex n.len // DaggerFunctor F}
   from
    ⟨fun f ↦ ⟨f.toFunctor, f.map_dagger⟩, fun f ↦ ⟨f.1, f.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩).trans discreteDaggerFunctorEquiv

/-- Enrichment presents the path-model index as a full subcategory of dagger
simplicial categories on the constant enrichments of the path objects. -/
def enrichedDaggerSimplexInclusion : DaggerSimplex ⥤ DaggerSimplicialCat.{0, 0} where
  obj := enrichedDaggerSimplex
  map {m n} := enrichedDaggerSimplexHomEquiv m n
  map_id n := by
    apply (enrichedDaggerSimplexHomEquiv n n).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  map_comp {m n p} f g := by
    apply (enrichedDaggerSimplexHomEquiv m p).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl

instance : enrichedDaggerSimplexInclusion.Full where
  map_surjective {m n} := (enrichedDaggerSimplexHomEquiv m n).surjective

instance : enrichedDaggerSimplexInclusion.Faithful where
  map_injective {m n} := (enrichedDaggerSimplexHomEquiv m n).injective

end

end DaggerModels.PartII
