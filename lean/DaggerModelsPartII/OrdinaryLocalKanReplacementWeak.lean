import DaggerModelsPartII.OrdinaryDwyerKanCore
import OriginalOrdinaryLocalKanReplacementHomReconciled

/-!
# The original ordinary local Kan replacement unit is DK weak

The existing functorial horn-cell factorization defines the literal unit. Its
already proved object bijection and anodyne Hom maps give the ordinary DK
condition on every original simplicial category, without a local Kan premise.
The replacement construction and its unit are not redefined here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModels.OrdinaryUniversalLocalCobase
open DaggerOriginalSimplicialPiZeroCategory

universe u

namespace DaggerModels.OrdinaryLocalKanReplacementWeak

open OriginalOrdinaryHornGenerators
open OriginalOrdinaryLocalKanReplacement
open OriginalOrdinaryLocalKanReplacementHom
open OriginalOrdinaryHornLeftClassAnodyne
open OriginalOrdinaryHornObjectBijections
open OrdinaryDwyerKanCore

noncomputable section

/-- The original ordinary horn-cell left class is geometrically weak on all
ordered original Hom simplicial sets. -/
theorem hornLeft_localGeometric {C D : SimplicialCat.{u, u}}
    (f : C ⟶ D) (hf : generators.rlp.llp f) : LocalGeometric f := by
  intro x y
  exact hornLeft_hom_geometric f hf x y

/-- The original horn-cell left class is essentially surjective on the
retained native component categories, using its actual object bijection. -/
theorem hornLeft_componentEss {C D : SimplicialCat.{u, u}}
    (f : C ⟶ D) (hf : generators.rlp.llp f) :
    (componentFunctor f).EssSurj := by
  apply Functor.essSurj_of_surj
  exact (object_bijective_of_generators_rlp_llp f hf).2

/-- The literal horn-cell left class lies in the ordinary DK weak class. -/
theorem hornLeft_W {C D : SimplicialCat.{u, u}}
    (f : C ⟶ D) (hf : generators.rlp.llp f) : W f :=
  ⟨hornLeft_localGeometric f hf, hornLeft_componentEss f hf⟩

/-- The original functorial local Kan replacement unit is locally geometric
on every ordered original Hom, without a Kan hypothesis on its source. -/
theorem unit_localGeometric (C : SimplicialCat.{u, u}) :
    LocalGeometric (unit.app C) := by
  intro x y
  exact unit_hom_geometric C x y

/-- The unchanged unit is essentially surjective on the native component
category, witnessed by its already proved bijection on original objects. -/
theorem unit_componentEss (C : SimplicialCat.{u, u}) :
    (componentFunctor (unit.app C)).EssSurj := by
  apply Functor.essSurj_of_surj
  exact (unit_obj_bijective C).2

/-- The literal functorial local Kan replacement unit satisfies the full
ordinary DK weak condition for every original simplicial category. -/
theorem unit_W (C : SimplicialCat.{u, u}) : W (unit.app C) :=
  ⟨unit_localGeometric C, unit_componentEss C⟩

/-- The checked weak unit retains the original object bijection and the
locally Kan output on the very same chosen replacement functor. -/
theorem unit_W_and_replacement_locallyKan (C : SimplicialCat.{u, u}) :
    W (unit.app C) ∧ Function.Bijective (unit.app C).obj ∧
      ∀ x y : (replacement.obj C).Obj, SSet.KanComplex (x ⟶[SSet.{u}] y) :=
  ⟨unit_W C, unit_obj_bijective C, replacement_locallyKan C⟩

end

end DaggerModels.OrdinaryLocalKanReplacementWeak
