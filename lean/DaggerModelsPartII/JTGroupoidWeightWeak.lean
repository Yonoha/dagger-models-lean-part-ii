import DaggerModelsPartII.JTWeightedWeakPreservation
import DaggerModelsPartII.JTXiOrdinaryLatching
import OriginalTaggedFreeZeroNativeWitness
import DaggerModels.FreeDagger
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# The actual completed-simplex vertical weight

At the outer zero object, the forgotten Xi frame is the original ordinary
rigidification of `J^k`. Uniqueness of colimit-preserving Yoneda extensions
identifies its actual weighted realization with rigidification after the
left Kan extension of the completed-simplex parameter. The installed
all-weight Xi theorem then gives full ordinary DK weakness for the map
induced by any scalar Kan weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryDwyerKanCore

namespace DaggerModels.PartII.JTGroupoidWeightWeak

open GroupoidSimplex DaggerJTFrameUnderlying JTProjectiveGeneratorRealization
open JTXiOrdinaryLatching

noncomputable section

private abbrev zeroIndex : ReverseSimplex :=
  ReverseSimplex.inclusion.obj ⦋0⦌

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : HasColimits SimplicialCat.{0, 0} :=
  simplicialCatHasColimits

/-- The vertical `J^k` realization with the literal groupoid-completed
simplex parameter. -/
def jRealization : SSet.{0} ⥤ SSet.{0} :=
  uliftYoneda.{0}.leftKanExtension GroupoidSimplex.parameter

private def jRealizationAdjunction :
    jRealization ⊣ Presheaf.restrictedULiftYoneda.{0} GroupoidSimplex.parameter := by
  letI : jRealization.IsLeftKanExtension
      (uliftYoneda.{0}.leftKanExtensionUnit GroupoidSimplex.parameter) := by
    dsimp [jRealization]
    infer_instance
  exact Presheaf.uliftYonedaAdjunction jRealization
    (uliftYoneda.{0}.leftKanExtensionUnit GroupoidSimplex.parameter)

/-- The actual represented reversal zero-simplex becomes the tensor unit
after forgetting dagger. -/
private def underlyingZeroIso :
    underlyingSimplex.obj zeroIndex ≅ (𝟙_ SSet.{0}) := by
  letI : PreservesLimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesLimits
  let e : underlyingSimplex.obj zeroIndex ≅ DaggerSSet.point.{0}.toSSet :=
    DaggerSSet.forget.mapIso
      ((reversalSimplexFreeIso.app ⦋0⦌) ≪≫
        DaggerOriginalTaggedFreeZeroNativeWitness.pointFreeZeroIso.symm)
  have hp : IsTerminal DaggerSSet.point.{0}.toSSet :=
    DaggerSSet.pointIsTerminal.isTerminalObj DaggerSSet.forget DaggerSSet.point
  exact e ≪≫ hp.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{0}))

/-- Tensoring by the underlying zero reversal simplex is naturally the
identity scalar functor. -/
private def tensorLeftZeroIso :
    tensorLeft (underlyingSimplex.obj zeroIndex) ≅ 𝟭 SSet.{0} :=
  (curriedTensor SSet.{0}).mapIso underlyingZeroIso ≪≫
    leftUnitorNatIso SSet.{0}

/-- The original Xi frame at outer zero is exactly rigidification of the
actual groupoid-completed simplex, naturally in its vertical index. -/
private def xiZeroFrameIso :
    xiVertical zeroIndex ⋙ DaggerSimplicialCat.forget ≅
      GroupoidSimplex.parameter ⋙ rigidification :=
  (actualOrdinaryXiIso zeroIndex) ≪≫
    Functor.isoWhiskerLeft GroupoidSimplex.parameter
      ((Functor.isoWhiskerRight tensorLeftZeroIso rigidification) ≪≫
        rigidification.leftUnitor)

private local instance : PreservesColimitsOfSize.{0, 0, 0, 0, 1, 1}
    (xiWeighted zeroIndex ⋙ DaggerSimplicialCat.forget) := by
  letI : PreservesColimitsOfSize.{0, 0} (xiWeighted zeroIndex) :=
    (xiWeightedAdjunction zeroIndex).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  infer_instance

private local instance : PreservesColimitsOfSize.{0, 0, 0, 0, 1, 1}
    (jRealization ⋙ rigidification) := by
  letI : PreservesColimitsOfSize.{0, 0} jRealization := by
    exact jRealizationAdjunction.leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} rigidification.{0} :=
    rigidificationCoherentNerveAdjunction.leftAdjoint_preservesColimits
  infer_instance

/-- Canonical all-weight extension of the actual outer-zero frame iso.
Both sides preserve the original scalar colimits and have the same
represented Yoneda normalization. -/
def xiZeroWeightedUnderlyingIso :
    xiWeighted zeroIndex ⋙ DaggerSimplicialCat.forget ≅
      jRealization ⋙ rigidification := by
  letI : PreservesColimitsOfSize.{0, 0, 0, 0, 1, 1}
      (xiWeighted zeroIndex ⋙ DaggerSimplicialCat.forget) := inferInstance
  letI : PreservesColimitsOfSize.{0, 0, 0, 0, 1, 1}
      (jRealization ⋙ rigidification) := inferInstance
  let eF : GroupoidSimplex.parameter ⋙ rigidification ≅
      uliftYoneda.{0} ⋙
        (xiWeighted zeroIndex ⋙ DaggerSimplicialCat.forget) :=
    xiZeroFrameIso.symm ≪≫
      Functor.isoWhiskerRight
        (Presheaf.isExtensionAlongULiftYoneda (xiVertical zeroIndex)).symm
        DaggerSimplicialCat.forget ≪≫
      Functor.associator uliftYoneda (xiWeighted zeroIndex)
        DaggerSimplicialCat.forget
  let eH : GroupoidSimplex.parameter ⋙ rigidification ≅
      uliftYoneda.{0} ⋙ (jRealization ⋙ rigidification) :=
    Functor.isoWhiskerRight
      (Presheaf.isExtensionAlongULiftYoneda GroupoidSimplex.parameter).symm
      rigidification ≪≫
      Functor.associator uliftYoneda jRealization rigidification
  exact (Presheaf.uniqueExtensionAlongULiftYoneda
      (xiWeighted zeroIndex ⋙ DaggerSimplicialCat.forget) eF) ≪≫
    (Presheaf.uniqueExtensionAlongULiftYoneda
      (jRealization ⋙ rigidification) eH).symm

/-- For every scalar Kan weak map, the original ordinary rigidification
of its literal `J^k`-realization image is full ordinary DK. -/
theorem rigidification_jRealization_map_W {K L : SSet.{0}}
    (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    W (rigidification.map (jRealization.map f)) := by
  let e := xiZeroWeightedUnderlyingIso
  let ea : Arrow.mk
      (DaggerSimplicialCat.forget.map ((xiWeighted zeroIndex).map f)) ≅
        Arrow.mk (rigidification.map (jRealization.map f)) :=
    Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm
  exact (W.arrow_mk_iso_iff ea).1
    (JTWeightedWeakPreservation.xiWeighted_map_W zeroIndex f hf)

end

end DaggerModels.PartII.JTGroupoidWeightWeak
