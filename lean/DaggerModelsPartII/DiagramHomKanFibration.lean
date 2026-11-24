import DaggerModelsPartII.ReedyHornRestriction

/-! Kan fibration tests for the mapping simplicial sets of target resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C]

/-- A coefficient lift against the relative restriction supplies the corresponding
lift in the relative mapping simplicial set. -/
theorem diagramHomCorner_lifting_of_restriction [HasPullbacks C]
    {A B : C} (i : A ⟶ B) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)
    {K L : SSet.{v}} (j : K ⟶ L)
    (h : HasLiftingProperty i (diagramRestrictionRelative j f)) :
    HasLiftingProperty j (diagramHomCorner i f) := by
  constructor
  intro a b sq
  let P := pullback (diagramHomPostcomp A f) (diagramHomPrecomp i V)
  let b₀ : L ⟶ diagramHomSSet A W := b ≫ pullback.fst _ _
  let b₁ : L ⟶ diagramHomSSet B V := b ≫ pullback.snd _ _
  let a' := diagramRestrictionHomEquiv K B W a
  let b₀' := diagramRestrictionHomEquiv L A W b₀
  let b₁' := diagramRestrictionHomEquiv L B V b₁
  have h₀ : a ≫ diagramHomPrecomp i W = j ≫ b₀ := by
    have w := congrArg (fun k : K ⟶ P ↦ k ≫ pullback.fst _ _) sq.w
    simpa only [Category.assoc, diagramHomCorner, pullback.lift_fst, b₀] using w
  have h₁ : a ≫ diagramHomPostcomp B f = j ≫ b₁ := by
    have w := congrArg (fun k : K ⟶ P ↦ k ≫ pullback.snd _ _) sq.w
    simpa only [Category.assoc, diagramHomCorner, pullback.lift_snd, b₁] using w
  have h₁' : a' ≫ diagramRestrictionPost K f = b₁' ≫ diagramRestrictionPre j V := by
    dsimp only [a', b₁']
    rw [← diagramRestrictionHomEquiv_post, h₁, diagramRestrictionHomEquiv_pre]
  let b' := pullback.lift a' b₁' h₁'
  have sq' : CommSq b₀' i (diagramRestrictionRelative j f) b' := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, diagramRestrictionRelative, b', pullback.lift_fst]
      dsimp only [b₀', a']
      rw [← diagramRestrictionHomEquiv_pre, ← diagramRestrictionHomEquiv_coeff, h₀]
    · simp only [Category.assoc, diagramRestrictionRelative, b', pullback.lift_snd]
      dsimp only [b₀', b₁']
      rw [← diagramRestrictionHomEquiv_post, ← diagramRestrictionHomEquiv_coeff]
      simp only [b₀, b₁, Category.assoc, pullback.condition]
  letI := h
  let e := diagramRestrictionHomEquiv L B W
  refine CommSq.HasLift.mk' ⟨e.symm sq'.lift, ?_, ?_⟩
  · apply (diagramRestrictionHomEquiv K B W).injective
    rw [diagramRestrictionHomEquiv_pre, Equiv.apply_symm_apply]
    have w : (sq'.lift ≫ diagramRestrictionRelative j f) ≫ pullback.fst _ _ =
        b' ≫ pullback.fst _ _ := by rw [sq'.fac_right]
    simpa only [Category.assoc, diagramRestrictionRelative, b', pullback.lift_fst] using w
  · apply pullback.hom_ext
    · simp only [Category.assoc, diagramHomCorner, pullback.lift_fst]
      apply (diagramRestrictionHomEquiv L A W).injective
      rw [diagramRestrictionHomEquiv_coeff, Equiv.apply_symm_apply]
      exact sq'.fac_left
    · simp only [Category.assoc, diagramHomCorner, pullback.lift_snd]
      apply (diagramRestrictionHomEquiv L B V).injective
      rw [diagramRestrictionHomEquiv_post, Equiv.apply_symm_apply]
      have w : (sq'.lift ≫ diagramRestrictionRelative j f) ≫ pullback.snd _ _ =
          b' ≫ pullback.snd _ _ := by rw [sq'.fac_right]
      simpa only [Category.assoc, diagramRestrictionRelative, b', pullback.lift_snd] using w

variable [ModelCategory C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance mappingReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  simplicialReedyModelCategory C

/-- A coefficient cofibration and a Reedy fibration of homotopically constant
Reedy fibrant diagrams induce a Kan fibration on the relative mapping space. -/
theorem diagramHomCorner_kan_fibration {A B : C} (i : A ⟶ B) [Cofibration i]
    {W V : SimplexCategoryᵒᵖ ⥤ C} [IsFibrant W] [IsFibrant V]
    (hW : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t), weakEquivalences C (W.map g))
    (hV : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t), weakEquivalences C (V.map g))
    (f : W ⟶ V) (hf : reedyMatchingProperty (fibrations C) f) :
    Fibration (diagramHomCorner i f) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  exact diagramHomCorner_lifting_of_restriction i f _
    (hasLiftingProperty_of_wfs i (diagramRestrictionRelative _ f)
      (mem_cofibrations i) (diagramRestrictionRelative_horn_trivial W hW hV f hf n k))

/-- A Reedy fibration between homotopically constant Reedy fibrant diagrams
induces a Kan fibration on mapping simplicial sets out of a cofibrant object. -/
theorem diagramHomPostcomp_kan_fibration (A : C) [IsCofibrant A]
    {W V : SimplexCategoryᵒᵖ ⥤ C} [IsFibrant W] [IsFibrant V]
    (hW : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t), weakEquivalences C (W.map g))
    (hV : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t), weakEquivalences C (V.map g))
    (f : W ⟶ V) (hf : reedyMatchingProperty (fibrations C) f) :
    Fibration (diagramHomPostcomp A f) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  constructor
  intro a b sq
  let j := (SSet.horn.{v} (n + 1) k).ι
  let e := diagramRestrictionHomEquiv (Δ[n + 1] : SSet.{v}) A W
  let a' := diagramRestrictionHomEquiv _ A W a
  let b' := diagramRestrictionHomEquiv _ A V b
  have comm : a' ≫ diagramRestrictionPost _ f = b' ≫ diagramRestrictionPre j V := by
    dsimp only [a', b']
    rw [← diagramRestrictionHomEquiv_post, ← diagramRestrictionHomEquiv_pre, sq.w]
  let d := pullback.lift a' b' comm
  let i := initial.to A
  have sq' : CommSq (initial.to _) i (diagramRestrictionRelative j f) d :=
    ⟨initial.hom_ext _ _⟩
  letI := hasLiftingProperty_of_wfs i (diagramRestrictionRelative j f)
    (mem_cofibrations i) (diagramRestrictionRelative_horn_trivial W hW hV f hf n k)
  refine CommSq.HasLift.mk' ⟨e.symm sq'.lift, ?_, ?_⟩
  · apply (diagramRestrictionHomEquiv _ A W).injective
    rw [diagramRestrictionHomEquiv_pre, Equiv.apply_symm_apply]
    have w := congrArg (fun g ↦ g ≫ pullback.fst _ _) sq'.fac_right
    simpa only [Category.assoc, diagramRestrictionRelative, d, pullback.lift_fst] using w
  · apply (diagramRestrictionHomEquiv _ A V).injective
    rw [diagramRestrictionHomEquiv_post, Equiv.apply_symm_apply]
    have w := congrArg (fun g ↦ g ≫ pullback.snd _ _) sq'.fac_right
    simpa only [Category.assoc, diagramRestrictionRelative, d, pullback.lift_snd] using w

end

end DaggerModels.PartII
