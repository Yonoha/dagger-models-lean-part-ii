import DaggerModelsPartII.LocalEquivalencePushouts

/-!
# Left properness of a local weak-equivalence class

In a left proper model category, local equivalences for any specified family
remain local equivalences after pushout along an original cofibration. The
proof factors a local equivalence into an original cofibration and trivial
fibration, then applies the local pushout theorem to the former and original
left properness to the latter.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C : Type u} [Category.{v} C] [baseModel : ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, v} C]

/-- Local equivalences are preserved by pushout along original cofibrations
in a left proper base model category, for any localizing family. -/
theorem localEquivalences_leftProper
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P}, IsPushout i k l r →
        cofibrations C i → weakEquivalences C k → weakEquivalences C l)
    (S : MorphismProperty C)
    {X Y X' Y' : C} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : localEquivalences S f) (hi : cofibrations C i) :
    localEquivalences S f' := by
  letI : (cofibrations C ⊓ localEquivalences S).IsStableUnderCobaseChange :=
    localTrivialCofibrations_cobaseChange leftProper S
  let d := factorizationData (cofibrations C) (trivialFibrations C) f
  have hp : localEquivalences S d.p :=
    weakEquivalences_le_localEquivalences S d.p d.hp.2
  have hd : (cofibrations C ⊓ localEquivalences S) d.i :=
    ⟨d.hi, (localEquivalences S).of_postcomp _ _ hp (d.fac.symm ▸ hf)⟩
  let sq₁ := IsPushout.of_hasPushout d.i i
  have hc : d.i ≫ d.p ≫ j = i ≫ f' := by
    rw [← Category.assoc, d.fac]
    exact sq.w
  let g := pushout.desc (d.p ≫ j) f' hc
  have hfac : pushout.inr d.i i ≫ g = f' := pushout.inr_desc _ _ _
  have comm : d.p ≫ j = pushout.inl d.i i ≫ g := (pushout.inl_desc _ _ _).symm
  have sq₂ : IsPushout d.p (pushout.inl d.i i) j g :=
    (sq₁.paste_horiz_iff comm).mp (by rw [d.fac, hfac]; exact sq)
  have h₁ := (cofibrations C ⊓ localEquivalences S).of_isPushout sq₁.flip hd
  have hcof : cofibrations C (pushout.inl d.i i) :=
    (cofibrations C).of_isPushout sq₁ hi
  have h₂ := leftProper sq₂.flip hcof d.hp.2
  rw [← hfac]
  exact (localEquivalences S).comp_mem _ _ h₁.2
    (weakEquivalences_le_localEquivalences S g h₂)

/-- Any model structure with the original cofibrations and the exact local
weak-equivalence class inherits left properness. -/
theorem localizedModel_leftProper
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P}, IsPushout i k l r →
        cofibrations C i → weakEquivalences C k → weakEquivalences C l)
    (S : MorphismProperty C) (N : ModelCategory C)
    (hc : N.categoryWithCofibrations.cofibrations =
      baseModel.categoryWithCofibrations.cofibrations)
    (hw : N.categoryWithWeakEquivalences.weakEquivalences =
      @localEquivalences C _ baseModel _ _ S)
    {X Y X' Y' : C} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : N.categoryWithWeakEquivalences.weakEquivalences f)
    (hi : N.categoryWithCofibrations.cofibrations i) :
    N.categoryWithWeakEquivalences.weakEquivalences f' := by
  have hf' : (@localEquivalences C _ baseModel _ _ S) f := by
    rw [← hw]
    exact hf
  have hi' : baseModel.categoryWithCofibrations.cofibrations i := by
    rw [← hc]
    exact hi
  have h' : (@localEquivalences C _ baseModel _ _ S) f' := by
    letI : ModelCategory C := baseModel
    exact localEquivalences_leftProper leftProper S sq hf' hi'
  rw [hw]
  exact h'

end

end DaggerModels.PartII.Localization
