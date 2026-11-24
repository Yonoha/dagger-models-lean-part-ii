import DaggerModelsPartII.JTProjectiveGeneratorRealization
import DaggerModelsPartII.JTWeightedFrameMonomorphisms

/-!
# Actual free projective maps and ordinary local cobase

The two actual free-weight realizations send every simplicial-set mono,
after forgetting dagger, into the completed universal ordinary local
cobase class. The canonical all-weight normalization transports the
existing result for literal Gamma and Xi weighted realizations.
This does not assert the Lambda local weak-equivalence comparison.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryUniversalLocalCobase

namespace DaggerModels.PartII.JTProjectiveGeneratorLocalCobase

open JTProjectiveGeneratorRealization

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The canonical all-weight Gamma isomorphism identifies each actual
free coefficient arrow with the literal weighted Gamma arrow. -/
def gammaFreeArrowIso (m : ReverseSimplex) {K L : SSet.{0}} (i : K ⟶ L) :
    Arrow.mk (DaggerSimplicialCat.forget.map
      (JTFrameAdjunction.frameRealization.map ((outerFree m).map i))) ≅
    Arrow.mk (DaggerSimplicialCat.forget.map ((gammaWeighted m).map i)) :=
  Arrow.isoMk
    (DaggerSimplicialCat.forget.mapIso ((gammaFreeWeightedIso m).app K))
    (DaggerSimplicialCat.forget.mapIso ((gammaFreeWeightedIso m).app L))
    (by
      have h := (gammaFreeWeightedIso m).hom.naturality i
      exact (by
        simpa only [Functor.map_comp] using
          (congrArg DaggerSimplicialCat.forget.map h).symm))

/-- The same actual arrow identification for the original Xi realization. -/
def xiFreeArrowIso (m : ReverseSimplex) {K L : SSet.{0}} (i : K ⟶ L) :
    Arrow.mk (DaggerSimplicialCat.forget.map
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map ((outerFree m).map i)))) ≅
    Arrow.mk (DaggerSimplicialCat.forget.map ((xiWeighted m).map i)) :=
  Arrow.isoMk
    (DaggerSimplicialCat.forget.mapIso ((xiFreeWeightedIso m).app K))
    (DaggerSimplicialCat.forget.mapIso ((xiFreeWeightedIso m).app L))
    (by
      have h := (xiFreeWeightedIso m).hom.naturality i
      simpa only [Functor.map_comp] using
        (congrArg DaggerSimplicialCat.forget.map h).symm)

/-- Every actual free outer coefficient mono maps into U under Gamma. -/
theorem gamma_free_mono_in_U (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    U (DaggerSimplicialCat.forget.map
      (JTFrameAdjunction.frameRealization.map ((outerFree m).map i))) := by
  apply (U.arrow_mk_iso_iff (gammaFreeArrowIso m i)).2
  exact JTWeightedFrameMonomorphisms.gamma_weighted_mono_in_U m i

/-- Every actual free outer coefficient mono maps into U under Xi. -/
theorem xi_free_mono_in_U (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    U (DaggerSimplicialCat.forget.map
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map ((outerFree m).map i)))) := by
  apply (U.arrow_mk_iso_iff (xiFreeArrowIso m i)).2
  change U (DaggerSimplicialCat.forget.map
    ((JTWeightedBoundaryLatching.weighted
      (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi)).map i))
  exact JTWeightedFrameMonomorphisms.xi_weighted_mono_in_U m i

end

end DaggerModels.PartII.JTProjectiveGeneratorLocalCobase
