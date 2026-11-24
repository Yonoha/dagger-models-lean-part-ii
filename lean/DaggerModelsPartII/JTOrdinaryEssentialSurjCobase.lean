import DaggerModelsPartII.OrdinaryDwyerKanCore
import DaggerModelsPartII.OrdinaryCofibrationLocalComparison
import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Essential surjectivity under ordinary enriched cobase change

The original object functor preserves pushouts. Every target object of an
ordinary enriched pushout is therefore in one of the two object-map images.
An object from the weak-equivalence side is component-isomorphic to an image
from the common source, and this isomorphism survives under the other leg.
No cofibration premise is needed for essential surjectivity itself.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels
open DaggerOriginalSimplicialPiZeroCategory

universe u

namespace DaggerModels.OrdinaryEssentialSurjCobase

noncomputable section

theorem essSurj_of_isPushout
    {C D B P : SimplicialCat.{u, u}}
    (F : C ⟶ D) (i : C ⟶ B) (j : D ⟶ P) (Fplus : B ⟶ P)
    (sq : IsPushout F i j Fplus)
    (hF : (componentFunctor F).EssSurj) :
    (componentFunctor Fplus).EssSurj := by
  letI : PreservesColimitsOfSize.{0, 0} SimplicialCat.objects.{u, u} :=
    SimplicialCat.objectsPreservesColimitsOfSize
  have hsq : IsPushout
      (SimplicialCat.objects.map F) (SimplicialCat.objects.map i)
      (SimplicialCat.objects.map j) (SimplicialCat.objects.map Fplus) :=
    sq.map SimplicialCat.objects
  constructor
  intro z
  obtain ⟨y, hy⟩ | ⟨b, hb⟩ := Types.eq_or_eq_of_isPushout hsq z
  · obtain ⟨x, ⟨e⟩⟩ := hF.mem_essImage y
    have hcomm : Fplus.obj (i.obj x) = j.obj (F.obj x) :=
      (congrArg (fun T : C ⟶ P ↦ T.obj x) sq.w).symm
    exact ⟨i.obj x,
      ⟨eqToIso hcomm ≪≫ (componentFunctor j).mapIso e ≪≫ eqToIso hy⟩⟩
  · exact ⟨b, ⟨eqToIso hb⟩⟩

theorem weak_of_isPushout_along_cofibration
    {C D B P : SimplicialCat.{u, u}}
    (F : C ⟶ D) (i : C ⟶ B) (j : D ⟶ P) (Fplus : B ⟶ P)
    (sq : IsPushout F i j Fplus)
    (hi : DaggerOrdinaryRigidificationCof.ordinaryCofibrations i)
    (hF : OrdinaryDwyerKanCore.W F) :
    OrdinaryDwyerKanCore.W Fplus := by
  exact ⟨OrdinaryCofibrationLocalComparison.local_geometric_of_isPushout
      F i hi hF.1 j Fplus sq,
    essSurj_of_isPushout F i j Fplus sq hF.2⟩

end

end DaggerModels.OrdinaryEssentialSurjCobase
