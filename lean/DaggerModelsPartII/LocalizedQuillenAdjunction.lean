import DaggerModelsPartII.LocalizationModelFibrancy
import DaggerModelsPartII.CosimplicialQuillenComparison
import TopCatModelCategory.QuillenAdjunction

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u
namespace DaggerModels.PartII.Localization
noncomputable section
variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [N : ModelCategory C] (M : ModelCategory C) (S : MorphismProperty C)
  (hc : N.categoryWithCofibrations.cofibrations = M.categoryWithCofibrations.cofibrations)
  (hw : N.categoryWithWeakEquivalences.weakEquivalences = @localEquivalences C _ M _ _ S)

include hc hw in
/-- A base fibration between local fibrant objects is a fibration in the exact
left localization. -/
theorem baseFibration_betweenLocal_isLocalizedFibration
    {X Y : C} (p : X ⟶ Y)
    (hp : M.categoryWithFibrations.fibrations p)
    (hX : @localObject C _ M _ _ S X)
    (hY : @localObject C _ M _ _ S Y) :
    N.categoryWithFibrations.fibrations p := by
  letI : ModelCategory C := N
  let d := factorizationData (trivialCofibrations C) (fibrations C) p
  have hYN : @IsFibrant C _ N.categoryWithFibrations _ Y :=
    (localized_isFibrant_iff M S hc hw Y).mpr hY
  letI : IsFibrant Y := hYN
  have hZN : @IsFibrant C _ N.categoryWithFibrations _ d.Z :=
    isFibrant_of_fibration d.p
  have hZ : @localObject C _ M _ _ S d.Z :=
    (localized_isFibrant_iff M S hc hw d.Z).mp hZN
  have hdM : M.categoryWithCofibrations.cofibrations d.i ∧
      M.categoryWithWeakEquivalences.weakEquivalences d.i := by
    refine ⟨hc ▸ d.hi.1, ?_⟩
    letI := M
    exact (localEquivalence_iff_weak_of_local S d.i hX hZ).mp (hw ▸ d.hi.2)
  have hl : HasLiftingProperty d.i p := by
    letI : ModelCategory C := M
    haveI : Cofibration d.i := (cofibration_iff _).mpr hdM.1
    haveI : WeakEquivalence d.i := (weakEquivalence_iff _).mpr hdM.2
    haveI : Fibration p := (fibration_iff _).mpr hp
    infer_instance
  let sq : CommSq (𝟙 X) d.i p d.p := ⟨by simp [d.fac]⟩
  letI := hl
  let r : d.Z ⟶ X := sq.lift
  have hr₁ : d.i ≫ r = 𝟙 X := sq.fac_left
  have hr₂ : r ≫ p = d.p := sq.fac_right
  let e : RetractArrow p d.p := {
    i := Arrow.homMk d.i (𝟙 _) (by simp [d.fac])
    r := Arrow.homMk r (𝟙 _) (by simpa using hr₂)
    retract := by ext <;> simp [hr₁] }
  have hRetr : (N.categoryWithFibrations.fibrations).IsStableUnderRetracts := N.cm3b
  exact hRetr.of_retract e d.hp

end
end DaggerModels.PartII.Localization

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [ModelCategory C] [ModelCategory D]
  (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)

/-- Dugger's criterion: a right adjoint that preserves trivial fibrations
and fibrations between fibrant objects is right Quillen. -/
theorem quillen_of_trivialFibrations_and_fibrantFibrations
    (htriv : G.PreservesTrivialFibrations)
    (hfib : ∀ ⦃X Y : D⦄ (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
      fibrations D p → fibrations C (G.map p)) :
    adj.IsQuillenAdjunction := by
  have hcof : F.PreservesCofibrations :=
    (adj.preservesTrivialFibrations_iff_preservesCofibrations).mp htriv
  have htrivcof : F.PreservesTrivialCofibrations := by
    apply F.preservesTrivialCofibrations_iff.mpr
    intro A B i hi
    have hiCof : cofibrations C i := hi.1
    have hiW : weakEquivalences C i := hi.2
    let kData := factorizationData (trivialCofibrations D) (fibrations D)
      (terminal.from (F.obj B))
    let d := factorizationData (trivialCofibrations D) (fibrations D)
      (F.map i ≫ kData.i)
    have hY : IsFibrant kData.Z := by
      letI : IsFibrant (⊤_ D) := by
        change Fibration (terminal.from (⊤_ D))
        have h : terminal.from (⊤_ D) = 𝟙 (⊤_ D) := terminal.hom_ext _ _
        rw [h]
        infer_instance
      letI : Fibration kData.p := (fibration_iff _).mpr kData.hp
      exact isFibrant_of_fibration kData.p
    have hX : IsFibrant d.Z := by
      letI : IsFibrant kData.Z := hY
      letI : Fibration d.p := (fibration_iff _).mpr d.hp
      exact isFibrant_of_fibration d.p
    have hpG : fibrations C (G.map d.p) := hfib d.p hX hY d.hp
    have hlG : HasLiftingProperty i (G.map d.p) := by
      letI : Cofibration i := (cofibration_iff _).mpr hiCof
      letI : WeakEquivalence i := (weakEquivalence_iff _).mpr hiW
      letI : Fibration (G.map d.p) := (fibration_iff _).mpr hpG
      infer_instance
    have hl : HasLiftingProperty (F.map i) d.p :=
      (adj.hasLiftingProperty_iff i d.p).mpr hlG
    let sq₁ : CommSq d.i (F.map i) d.p kData.i := ⟨d.fac⟩
    letI : HasLiftingProperty (F.map i) d.p := hl
    let g : F.obj B ⟶ d.Z := sq₁.lift
    have hg₁ : F.map i ≫ g = d.i := sq₁.fac_left
    have hg₂ : g ≫ d.p = kData.i := sq₁.fac_right
    let sq₂ : CommSq g kData.i d.p (𝟙 kData.Z) := ⟨by simp [hg₂]⟩
    have hl₂ : HasLiftingProperty kData.i d.p := by
      letI : Cofibration kData.i := (cofibration_iff _).mpr kData.hi.1
      letI : WeakEquivalence kData.i := (weakEquivalence_iff _).mpr kData.hi.2
      letI : Fibration d.p := (fibration_iff _).mpr d.hp
      infer_instance
    letI : HasLiftingProperty kData.i d.p := hl₂
    let s : kData.Z ⟶ d.Z := sq₂.lift
    have hs₁ : kData.i ≫ s = g := sq₂.fac_left
    have hs₂ : s ≫ d.p = 𝟙 kData.Z := sq₂.fac_right
    have heq : d.i ≫ (d.p ≫ s) = d.i := by
      calc
        d.i ≫ (d.p ≫ s) = (F.map i ≫ kData.i) ≫ s := by rw [← Category.assoc, d.fac]
        _ = F.map i ≫ g := by rw [Category.assoc, hs₁]
        _ = d.i := hg₁
    have heW : weakEquivalences D (d.p ≫ s) := by
      apply (weakEquivalences D).of_precomp d.i (d.p ≫ s) d.hi.2
      rw [heq]
      exact d.hi.2
    have hpW : weakEquivalences D d.p := by
      let e : RetractArrow d.p (d.p ≫ s) := {
        i := Arrow.homMk (𝟙 _) s (by simp)
        r := Arrow.homMk (𝟙 _) d.p (by simp [Category.assoc, hs₂])
        retract := by ext <;> simp [hs₂] }
      exact (inferInstance : (weakEquivalences D).IsStableUnderRetracts).of_retract e heW
    have hcomp : weakEquivalences D (F.map i ≫ kData.i) := by
      rw [← d.fac]
      exact (weakEquivalences D).comp_mem d.i d.p d.hi.2 hpW
    have hFiW : weakEquivalences D (F.map i) :=
      (weakEquivalences D).of_postcomp (F.map i) kData.i kData.hi.2 hcomp
    haveI : Cofibration i := (cofibration_iff _).mpr hiCof
    exact ⟨(cofibration_iff _).mp (inferInstance : Cofibration (F.map i)), hFiW⟩
  have hpresfib : G.PreservesFibrations :=
    (adj.preservesTrivialCofibrations_iff_preservesFibrations).mp htrivcof
  exact { toPreservesCofibrations := hcof, toPreservesFibrations := hpresfib }

end

end DaggerModels.PartII.Localization
