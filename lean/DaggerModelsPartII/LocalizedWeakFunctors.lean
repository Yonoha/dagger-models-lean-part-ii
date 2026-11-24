import DaggerModelsPartII.CosimplicialMappingInvariance
import TopCatModelCategory.QuillenAdjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Localization.Predicate

/-! Localization of weak-preserving functors and objectwise weak comparisons. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.LocalizedWeakFunctors

noncomputable section

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
variable {WA : MorphismProperty A} {WB : MorphismProperty B} {WC : MorphismProperty C}
variable {F F' : A ⥤ B} {G : B ⥤ C}

private theorem inverts (h : WA ≤ WB.inverseImage F) : WA.IsInvertedBy (F ⋙ WB.Q) :=
  fun _ _ f hf ↦ CategoryTheory.Localization.inverts WB.Q WB (F.map f) (h f hf)

/-- Localize a functor that carries one specified weak class to the other. -/
def lift (h : WA ≤ WB.inverseImage F) : WA.Localization ⥤ WB.Localization :=
  CategoryTheory.Localization.lift (F ⋙ WB.Q) (inverts h) WA.Q

/-- The canonical factorization isomorphism for the localized functor. -/
def fac (h : WA ≤ WB.inverseImage F) : WA.Q ⋙ lift h ≅ F ⋙ WB.Q :=
  CategoryTheory.Localization.fac (F ⋙ WB.Q) (inverts h) WA.Q

private instance lifting (h : WA ≤ WB.inverseImage F) :
    CategoryTheory.Localization.Lifting WA.Q WA (F ⋙ WB.Q) (lift h) := ⟨fac h⟩

/-- Pointwise weak natural transformations give natural isomorphisms on localizations. -/
def mapIso (h : WA ≤ WB.inverseImage F) (h' : WA ≤ WB.inverseImage F')
    (t : F ⟶ F') (ht : ∀ X, WB (t.app X)) : lift h ≅ lift h' := by
  let t' := Functor.whiskerRight t WB.Q
  letI : IsIso t' := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ CategoryTheory.Localization.inverts WB.Q WB (t.app X) (ht X)
  exact CategoryTheory.Localization.liftNatIso WA.Q WA _ _ _ _ (asIso t')

/-- Localization preserves composition up to the canonical comparison. -/
def compIso (hF : WA ≤ WB.inverseImage F) (hG : WB ≤ WC.inverseImage G)
    (hFG : WA ≤ WC.inverseImage (F ⋙ G)) :
    lift hF ⋙ lift hG ≅ lift hFG := by
  letI : CategoryTheory.Localization.Lifting WA.Q WA ((F ⋙ G) ⋙ WC.Q) (lift hF ⋙ lift hG) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (fac hF) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (fac hG) ≪≫
      (Functor.associator _ _ _).symm⟩
  exact CategoryTheory.Localization.liftNatIso WA.Q WA
    ((F ⋙ G) ⋙ WC.Q) ((F ⋙ G) ⋙ WC.Q) _ _ (Iso.refl _)

/-- Localization of the identity functor is canonically the identity. -/
def idIso (h : WA ≤ WA.inverseImage (𝟭 A)) : lift h ≅ 𝟭 WA.Localization := by
  letI : CategoryTheory.Localization.Lifting WA.Q WA WA.Q (𝟭 WA.Localization) :=
    ⟨Functor.rightUnitor WA.Q⟩
  exact CategoryTheory.Localization.liftNatIso WA.Q WA _ _ _ _ (Functor.leftUnitor WA.Q)

end

section

variable {A B : Type*} [Category* A] [Category* B] [ModelCategory A] [ModelCategory B]
variable {L : A ⥤ B} {G : B ⥤ A} (adj : L ⊣ G)

/-- The right adjoint after a functorial weak fibrant replacement preserves all weak maps. -/
theorem rightAfterReplacement_map_weak [adj.IsQuillenAdjunction]
    (R : B ⥤ B) (r : 𝟭 B ⟶ R)
    (hFib : ∀ X, IsFibrant (R.obj X)) (hr : ∀ X, weakEquivalences B (r.app X)) :
    weakEquivalences B ≤ (weakEquivalences A).inverseImage (R ⋙ G) := by
  intro X Y f hf
  letI := hFib X
  letI := hFib Y
  letI := Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adj
  have h : weakEquivalences B (R.map f) := by
    apply (weakEquivalences B).of_precomp _ _ (hr X)
    rw [← r.naturality f]
    exact (weakEquivalences B).comp_mem _ _ hf (hr Y)
  apply map_weak_of_trivialFibration G _ (R.map f) h
  intro U V p hp
  exact (Functor.PreservesTrivialFibrations.trivialFibrations_le G p hp).2

end

end DaggerModels.PartII.LocalizedWeakFunctors
