import DaggerModelsPartII.InjectiveKanDiagramGenerators
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-! Kernel-pair relations realize every regular-epi quotient of a free simplex diagram. -/

set_option autoImplicit false
open CategoryTheory Limits MorphismProperty
open scoped Simplicial
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

/-- Every regular-epi quotient of a free simplex diagram is represented by a
relation quotient in the small family. -/
theorem relationQuotient_iso_of_regularEpi (c : C) (n : ℕ)
    (Q : C ⥤ SSet.{u}) (q : freeSimplexDiagram C c n ⟶ Q) [IsRegularEpi q] :
    ∃ r : RelationIndex C c n, Nonempty (relationQuotient C c n r ≅ Q) := by
  let R := freeSimplexDiagram C c n
  let k : pullback q q ⟶ R ⨯ R := prod.lift (pullback.fst q q) (pullback.snd q q)
  haveI : Mono k := inferInstance
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  let r : RelationIndex C c n := equivShrink _ (Subobject.mk k)
  have hrel : relation C c n r = Subobject.mk k := by
    simp [relation, r]
  let a := (Subobject.mk k).arrow ≫ prod.fst
  let b := (Subobject.mk k).arrow ≫ prod.snd
  let e₀ := (Subobject.underlyingIso k).symm
  have ha : e₀.hom ≫ a = pullback.fst q q := by
    dsimp [e₀, a]
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_fst _ _
  have hb : e₀.hom ≫ b = pullback.snd q q := by
    dsimp [e₀, b]
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_snd _ _
  have w : a ≫ q = b ≫ q := by
    apply (cancel_epi e₀.hom).mp
    change (e₀.hom ≫ a) ≫ q = (e₀.hom ≫ b) ≫ q
    rw [ha, hb]
    exact pullback.condition
  let c₀ : Cofork (pullback.fst q q) (pullback.snd q q) :=
    Cofork.ofπ q pullback.condition
  let c₁ : Cofork a b := Cofork.ofπ q w
  have hc₀ : IsColimit c₀ := (IsKernelPair.of_hasPullback q).toCoequalizer'
  have hc₁ : IsColimit c₁ := by
    apply Cofork.isColimitOfIsos c₀ hc₀ c₁ e₀ (Iso.refl R) (Iso.refl Q)
  refine ⟨r, ⟨?_⟩⟩
  change coequalizer ((relation C c n r).arrow ≫ prod.fst)
    ((relation C c n r).arrow ≫ prod.snd) ≅ Q
  rw [hrel]
  exact (coequalizerIsCoequalizer a b).coconePointUniqueUpToIso hc₁


/-- Every subobject of a regular-epi quotient of a free simplex diagram occurs,
up to isomorphism of arrows, in the small quotient-subobject family. -/
theorem quotientSubobjectArrow_iso_of_regularEpi (c : C) (n : ℕ)
    (Q : C ⥤ SSet.{u}) (q : freeSimplexDiagram C c n ⟶ Q) [IsRegularEpi q]
    (S : Subobject Q) :
    ∃ i : QuotientSubobjectIndex C,
      Nonempty (Arrow.mk S.arrow ≅ quotientSubobjectArrow C i) := by
  obtain ⟨r, ⟨e⟩⟩ := relationQuotient_iso_of_regularEpi C c n Q q
  letI : WellPowered.{u} (C ⥤ SSet.{u}) := wellPowered C
  let T : Subobject (relationQuotient C c n r) := Subobject.mk (S.arrow ≫ e.inv)
  let i : QuotientSubobjectIndex C := ⟨c, n, r, equivShrink _ T⟩
  have hT : ((equivShrink _).symm i.2.2.2 :
      Subobject (relationQuotient C c n r)) = T := by simp [i]
  let d : (S : C ⥤ SSet.{u}) ≅
      (((equivShrink _).symm i.2.2.2 :
        Subobject (relationQuotient C c n r)) : C ⥤ SSet.{u}) :=
    (Subobject.underlyingIso (S.arrow ≫ e.inv)).symm ≪≫
      Subobject.isoOfEq T _ hT.symm
  refine ⟨i, ⟨Arrow.isoMk d e.symm ?_⟩⟩
  change d.hom ≫
    ((equivShrink _).symm i.2.2.2 :
      Subobject (relationQuotient C c n r)).arrow = S.arrow ≫ e.inv
  simp [d, T]


/-- Right lifting against the small family gives lifting against every
subobject of a regular-epi quotient of a free simplex diagram. -/
theorem quotientSubobjectGenerators_rlp_regularEpi_subobject
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : (quotientSubobjectGenerators C).rlp p)
    (c : C) (n : ℕ) (Q : C ⥤ SSet.{u})
    (q : freeSimplexDiagram C c n ⟶ Q) [IsRegularEpi q]
    (S : Subobject Q) : HasLiftingProperty S.arrow p := by
  obtain ⟨i, ⟨e⟩⟩ := quotientSubobjectArrow_iso_of_regularEpi C c n Q q S
  have hi : HasLiftingProperty (quotientSubobjectArrow C i).hom p :=
    hp _ ⟨i⟩
  exact (HasLiftingProperty.iff_of_arrow_iso_left e p).mpr hi

end
end DaggerModels.PartII.InjectiveKanDiagram
