import DaggerModelsPartII.OrdinaryDwyerKanCore
import OriginalUnitaryCoherentAlgebraRecovered
import OriginalActualGlobalWeakDefinitionsRecovered

/-!
# The actual dagger DK condition implies the retained ordinary DK condition

Compare the existing full component category used by coherent unitaries with
its native ordinary enrichment transport. Both objects and Hom components are
unchanged. Check composition on original vertex representatives, then map the
actual coherent-unitary isomorphism. No new component quotient is introduced.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerOriginalSimplicialPiZeroCategory

universe u

namespace DaggerModels.DaggerOrdinaryDwyerKan

noncomputable section

local instance (C : DaggerSimplicialCat.{u, u}) :
    Category (DaggerUnitarySubgroupoid.hC C) := DaggerUnitarySubgroupoid.hC_category C

/-- The retained dagger component category maps to the native ordinary component
category by the identity on all original objects and full Hom components. -/
def hCToOrdinaryComponent (C : DaggerSimplicialCat.{u, u}) :
    DaggerUnitarySubgroupoid.hC C ⥤ componentObjects (DaggerSimplicialCat.forget.obj C) where
  obj x := x
  map f := f
  map_id x := (DaggerUnitarySubgroupoid.hC_id_mk C x).trans
    (componentId_eq (DaggerSimplicialCat.forget.obj C) x).symm
  map_comp {x y z} f g := by
    obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective f
    obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective g
    exact (DaggerUnitarySubgroupoid.hC_comp_mk C f g).trans
      (componentComp_mk (DaggerSimplicialCat.forget.obj C) f g).symm

/-- The component comparison retains the original action of every dagger functor. -/
theorem hCToOrdinaryComponent_naturality {C D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ D) :
    DaggerUnitarySubgroupoid.hFunctor F ⋙ hCToOrdinaryComponent D =
      hCToOrdinaryComponent C ⋙ componentFunctor (DaggerSimplicialCat.forget.map F) := by
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro x y a
  exact heq_of_eq rfl

/-- Coherent unitary essential surjectivity implies essential surjectivity of the
literal ordinary component functor, for the same fibrant replacement and map. -/
theorem componentEss_of_coherent
    (R : DaggerUnitaryInvariance.FunctorialFibrantReplacement.{u})
    {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : DaggerGlobalDK.CoherentlyEssentiallySurjective R F) :
    (componentFunctor (DaggerSimplicialCat.forget.map F)).EssSurj := by
  constructor
  intro y
  obtain ⟨x, a, ha⟩ := hF y
  exact ⟨x, ⟨(hCToOrdinaryComponent D).mapIso
    (DaggerUnitarySubgroupoid.coherentlyUnitaryIso R D (F.obj x) y a ha)⟩⟩

/-- Forgetting the actual dagger DK condition gives the original ordinary DK
condition, keeping its Hom maps and both component endpoints unchanged. -/
theorem daggerDK_forget_W
    (R : DaggerUnitaryInvariance.FunctorialFibrantReplacement.{u})
    {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : DaggerGlobalDK.daggerDK R F) :
    OrdinaryDwyerKanCore.W (DaggerSimplicialCat.forget.map F) := by
  refine ⟨?_, componentEss_of_coherent R F hF.2⟩
  intro x y
  exact hF.1 x y

end

end DaggerModels.DaggerOrdinaryDwyerKan
