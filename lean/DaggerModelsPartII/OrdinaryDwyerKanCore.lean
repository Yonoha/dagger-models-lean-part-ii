import DaggerModelsPartII.OrdinaryUniversalLocalCobase
import OriginalSimplicialPiZeroFunctor
import SimplicialIsoHoms
import SSetGluingPushouts
import Mathlib.CategoryTheory.EssentialImage

/-!
# The original ordinary DK condition and basic closure

Use the retained geometric condition on every original Hom and essential
surjectivity of the retained native component functor. The native component
category and its monoidal construction are not reconstructed here.
This is a weak-equivalence predicate and basic closure, not a model structure.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryDwyerKanCore

open OrdinaryUniversalLocalCobase DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialPiZeroFunctor

noncomputable section

/-- The standard ordinary DK condition on the retained simplicial categories. -/
def W : MorphismProperty SimplicialCat.{u, u} :=
  fun _ _ F ↦ LocalGeometric F ∧ (componentFunctor F).EssSurj

/-- The existing geometric Hom predicate is precisely the native scalar weak class. -/
theorem localGeometric_iff_native {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    LocalGeometric F ↔ ∀ x y : C.Obj, WeakEquivalence (F.map x y) := by
  constructor
  · intro h x y
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2 (h x y)
  · intro h x y
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1 (h x y)

/-- Local weakness gives full faithfulness of the original component functor. -/
def componentFullyFaithful {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : LocalGeometric F) : (componentFunctor F).FullyFaithful :=
  componentFunctorFullyFaithful F ((localGeometric_iff_native F).1 hF)

/-- The ordinary DK condition induces equivalence of the retained component categories. -/
theorem componentIsEquivalence {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : W F) : (componentFunctor F).IsEquivalence := by
  let h := componentFullyFaithful F hF.1
  exact ⟨h.faithful, h.full, hF.2⟩

/-- The literal ordinary identity functor satisfies the DK condition. -/
theorem id_mem (C : SimplicialCat.{u, u}) : W (𝟙 C) := by
  constructor
  · apply (localGeometric_iff_native _).2
    intro x y
    change WeakEquivalence (𝟙 (C.enriched.Hom x y))
    infer_instance
  · rw [componentFunctor_id]
    infer_instance

/-- Original composition preserves the full ordinary DK condition. -/
theorem comp_mem {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E)
    (hF : W F) (hG : W G) : W (F ≫ G) := by
  constructor
  · apply (localGeometric_iff_native _).2
    intro x y
    have : WeakEquivalence (F.map x y) := (localGeometric_iff_native F).1 hF.1 x y
    have : WeakEquivalence (G.map (F.obj x) (F.obj y)) :=
      (localGeometric_iff_native G).1 hG.1 (F.obj x) (F.obj y)
    change WeakEquivalence (F.map x y ≫ G.map (F.obj x) (F.obj y))
    infer_instance
  · rw [componentFunctor_comp]
    have : (componentFunctor F).EssSurj := hF.2
    have : (componentFunctor G).EssSurj := hG.2
    infer_instance

/-- A DK functor can be cancelled from the second position of a composite. -/
theorem of_postcomp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E)
    (hG : W G) (hFG : W (F ≫ G)) : W F := by
  constructor
  · apply (localGeometric_iff_native _).2
    intro x y
    have : WeakEquivalence (G.map (F.obj x) (F.obj y)) :=
      (localGeometric_iff_native G).1 hG.1 (F.obj x) (F.obj y)
    have : WeakEquivalence (F.map x y ≫ G.map (F.obj x) (F.obj y)) :=
      (localGeometric_iff_native (F ≫ G)).1 hFG.1 x y
    exact weakEquivalence_of_postcomp (F.map x y) (G.map (F.obj x) (F.obj y))
  · let h := componentFullyFaithful G hG.1
    have : (componentFunctor G).Faithful := h.faithful
    have : (componentFunctor G).Full := h.full
    have : (componentFunctor F ⋙ componentFunctor G).EssSurj := by
      rw [← componentFunctor_comp]
      exact hFG.2
    exact Functor.essSurj_of_comp_fully_faithful (componentFunctor F) (componentFunctor G)

/-- Actual bundled isomorphisms satisfy the ordinary DK condition. -/
theorem of_isIso {C D : SimplicialCat.{u, u}} (F : C ⟶ D) [IsIso F] : W F := by
  constructor
  · apply (localGeometric_iff_native _).2
    intro x y
    have : IsIso (F.map x y) := DaggerSimplicialIsoHoms.mapIsIso (asIso F) x y
    infer_instance
  · apply Functor.essSurj_of_surj
    have : IsIso (SimplicialCat.objects.map F) := inferInstance
    exact ((isIso_iff_bijective (SimplicialCat.objects.map F)).1 inferInstance).2

instance W_containsIdentities : W.{u}.ContainsIdentities where
  id_mem C := id_mem C

instance W_stableComposition : W.{u}.IsStableUnderComposition where
  comp_mem F G hF hG := comp_mem F G hF hG

instance W_respectsIso : W.{u}.RespectsIso := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro C D F hF
  have : IsIso F := hF
  exact of_isIso F

end

end DaggerModels.OrdinaryDwyerKanCore
