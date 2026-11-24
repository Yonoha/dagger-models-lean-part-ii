import DaggerModelsPartII.DiagramRestriction
import DaggerModelsPartII.SimplicialReedyModel

/-! Relative restrictions of Reedy fibrations along monomorphisms. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C] [HasPullbacks C]
  {K L : SSet.{v}} (j : K ⟶ L) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)

omit [HasPullbacks C] in
/-- Restriction and a map of diagrams give a commutative square. -/
theorem diagramRestriction_comm :
    diagramRestrictionPre j W ≫ diagramRestrictionPost K f =
      diagramRestrictionPost L f ≫ diagramRestrictionPre j V := by
  apply limit.hom_ext
  intro d
  simp only [Category.assoc, diagramRestrictionPost, limMap_π,
    diagramRestrictionPre_π, diagramRestrictionPre_π_assoc]
  rfl

/-- The relative restriction associated to a test map and a map of diagrams. -/
def diagramRestrictionRelative :
    diagramRestriction L W ⟶ pullback (diagramRestrictionPost K f) (diagramRestrictionPre j V) :=
  pullback.lift (diagramRestrictionPre j W) (diagramRestrictionPost L f)
    (diagramRestriction_comm j f)

variable [HasLimitsOfSize.{0, 0} C]

/-- Boundary lifts in the coefficient category give relative restriction lifts along
any monomorphism of test simplicial sets. -/
theorem diagramRestrictionRelative_lifting [Mono j] {A B : C} (i : A ⟶ B)
    (h : ∀ n, HasLiftingProperty i (relativeMatchingMap n f)) :
    HasLiftingProperty i (diagramRestrictionRelative j f) := by
  constructor
  intro a b sq
  let eKW := diagramRestrictionHomEquiv K B W
  let eAW := diagramRestrictionHomEquiv L A W
  let eBV := diagramRestrictionHomEquiv L B V
  let a' := eKW.symm (b ≫ pullback.fst _ _)
  let b₀ := eAW.symm a
  let b₁ := eBV.symm (b ≫ pullback.snd _ _)
  have h₀ : j ≫ b₀ = a' ≫ diagramHomPrecomp i W := by
    apply (diagramRestrictionHomEquiv K A W).injective
    rw [diagramRestrictionHomEquiv_pre, diagramRestrictionHomEquiv_coeff]
    change eAW b₀ ≫ diagramRestrictionPre j W = i ≫ eKW a'
    simp only [a', b₀, Equiv.apply_symm_apply]
    rw [← pullback.lift_fst _ (diagramRestrictionPost L f) (diagramRestriction_comm j f),
      ← Category.assoc, ← Category.assoc, ← diagramRestrictionRelative, sq.w]
  have h₁ : a' ≫ diagramHomPostcomp B f = j ≫ b₁ := by
    apply (diagramRestrictionHomEquiv K B V).injective
    rw [diagramRestrictionHomEquiv_post, diagramRestrictionHomEquiv_pre]
    change eKW a' ≫ diagramRestrictionPost K f = eBV b₁ ≫ diagramRestrictionPre j V
    simp only [a', b₁, Equiv.apply_symm_apply, Category.assoc, pullback.condition]
  have h₂ : b₀ ≫ diagramHomPostcomp A f = b₁ ≫ diagramHomPrecomp i V := by
    apply (diagramRestrictionHomEquiv L A V).injective
    rw [diagramRestrictionHomEquiv_post, diagramRestrictionHomEquiv_coeff]
    change eAW b₀ ≫ diagramRestrictionPost L f = i ≫ eBV b₁
    simp only [b₀, b₁, Equiv.apply_symm_apply]
    rw [← pullback.lift_snd (diagramRestrictionPre j W) _ (diagramRestriction_comm j f),
      ← Category.assoc, ← Category.assoc, ← diagramRestrictionRelative, sq.w]
  let b' := pullback.lift b₀ b₁ h₂
  have sq' : CommSq a' j (diagramHomCorner i f) b' := by
    constructor
    apply pullback.hom_ext
    · simpa only [Category.assoc, b', diagramHomCorner, pullback.lift_fst] using h₀.symm
    · simpa only [Category.assoc, b', diagramHomCorner, pullback.lift_snd] using h₁
  letI := diagramHomCorner_mono_lifting i f h j
  let eBW := diagramRestrictionHomEquiv L B W
  have hl : eBW sq'.lift ≫ diagramRestrictionPre j W = b ≫ pullback.fst _ _ := by
    rw [← diagramRestrictionHomEquiv_pre, sq'.fac_left]
    exact Equiv.apply_symm_apply eKW _
  refine CommSq.HasLift.mk' ⟨eBW sq'.lift, ?_, ?_⟩
  · rw [← diagramRestrictionHomEquiv_coeff]
    have hq : (sq'.lift ≫ diagramHomCorner i f) ≫ pullback.fst _ _ =
        b' ≫ pullback.fst _ _ := by rw [sq'.fac_right]
    simp only [Category.assoc, diagramHomCorner, b', pullback.lift_fst] at hq
    rw [hq]
    exact Equiv.apply_symm_apply eAW _
  · apply pullback.hom_ext
    · simpa only [Category.assoc, diagramRestrictionRelative, pullback.lift_fst] using hl
    · simp only [Category.assoc, diagramRestrictionRelative, pullback.lift_snd]
      rw [← diagramRestrictionHomEquiv_post]
      have hq : (sq'.lift ≫ diagramHomCorner i f) ≫ pullback.snd _ _ =
          b' ≫ pullback.snd _ _ := by rw [sq'.fac_right]
      simp only [Category.assoc, diagramHomCorner, b', pullback.lift_snd] at hq
      rw [hq]
      exact Equiv.apply_symm_apply eBV _

variable [ModelCategory C]

/-- Every relative restriction of a Reedy fibration along a monomorphism is a fibration. -/
theorem diagramRestrictionRelative_fibration [Mono j]
    (hf : reedyMatchingProperty (fibrations C) f) :
    fibrations C (diagramRestrictionRelative j f) := by
  rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
  intro A B i hi
  exact diagramRestrictionRelative_lifting j f i
    (fun n ↦ hasLiftingProperty_of_wfs _ _ hi (hf n))

end

end DaggerModels.PartII
