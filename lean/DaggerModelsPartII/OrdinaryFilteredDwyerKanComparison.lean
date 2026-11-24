import DaggerModelsPartII.OrdinaryFilteredLocalComparison
import DaggerModelsPartII.OrdinaryDwyerKanCore
import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Full ordinary DK comparison at a filtered colimit

The original object functor preserves the supplied colimit. A target object
therefore comes from a stage; stagewise component essential surjectivity and
the literal cocone-leg equation give essential surjectivity of the supplied
colimit comparison. The existing endpoint-sensitive filtered Hom theorem gives
its local geometric part when both diagrams have Hom-monic transitions.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels
open DaggerOriginalSimplicialPiZeroCategory

universe u

namespace DaggerModels.OrdinaryFilteredDwyerKanComparison

noncomputable section

variable {J : Type u} [SmallCategory J]
variable {F G : J ⥤ SimplicialCat.{u, u}}
variable (η : F ⟶ G)

/-- Stagewise essential surjectivity descends to the actual supplied comparison
of ordinary enriched colimits, retaining its cocone-leg equation. -/
theorem componentEss_of_colimits
    {c : Cocone F} {d : Cocone G}
    (hd : IsColimit d) (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (hstage : ∀ j : J, (componentFunctor (η.app j)).EssSurj) :
    (componentFunctor g).EssSurj := by
  letI : PreservesColimitsOfSize.{u, u} SimplicialCat.objects.{u, u} :=
    SimplicialCat.objectsPreservesColimitsOfSize
  have hdObj : IsColimit (SimplicialCat.objects.mapCocone d) :=
    isColimitOfPreserves SimplicialCat.objects hd
  constructor
  intro z
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hdObj z
  obtain ⟨a, ⟨e⟩⟩ := (hstage j).mem_essImage b
  have hcomm : g.obj ((c.ι.app j).obj a) =
      (d.ι.app j).obj ((η.app j).obj a) := by
    have h := congrArg (fun T : F.obj j ⟶ d.pt ↦ T.obj a) (hlegs j)
    exact h
  exact ⟨(c.ι.app j).obj a,
    ⟨eqToIso hcomm ≪≫ (componentFunctor (d.ι.app j)).mapIso e ≪≫ eqToIso hb⟩⟩

/-- A filtered supplied comparison is a full ordinary DK weak equivalence
when the stage maps are DK weak and both diagrams have Hom-monic transitions. -/
theorem filtered_W_of_colimits [IsFiltered J]
    {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d)
    (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (hmonoF : ∀ {j k : J} (α : j ⟶ k) (a b : (F.obj j).Obj),
      Mono ((F.map α).map a b))
    (hmonoG : ∀ {j k : J} (α : j ⟶ k) (a b : (G.obj j).Obj),
      Mono ((G.map α).map a b))
    (hstage : ∀ j : J, OrdinaryDwyerKanCore.W (η.app j)) :
    OrdinaryDwyerKanCore.W g := by
  constructor
  · intro x y
    exact OrdinaryFilteredLocalComparison.filtered_local_of_colimits
      η hc hd g hlegs hmonoF hmonoG (fun j a b ↦ (hstage j).1 a b) x y
  · exact componentEss_of_colimits η hd g hlegs (fun j ↦ (hstage j).2)

end

end DaggerModels.OrdinaryFilteredDwyerKanComparison
