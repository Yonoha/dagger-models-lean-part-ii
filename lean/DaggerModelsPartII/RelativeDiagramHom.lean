import DaggerModelsPartII.DiagramHomBoundaryLifting
import TopCatModelCategory.ModelCategorySSet

/-! The relative mapping-space square and its boundary lifting test. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] {A B : C} (i : A ⟶ B)
  {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)

/-- The map imposing agreement under restriction along the coefficient map and the diagram map. -/
def diagramHomCorner :
    diagramHomSSet B W ⟶ pullback (diagramHomPostcomp A f) (diagramHomPrecomp i V) :=
  pullback.lift (diagramHomPrecomp i W) (diagramHomPostcomp B f) (by
    ext n x : 2
    exact Category.assoc i x (f.app n))

/-- A degree-zero lift of the mapping-space corner gives the original coefficient lift. -/
theorem hasLiftingProperty_evalZero_of_diagramHomCorner
    (h : HasLiftingProperty (SSet.boundary.{v} 0).ι (diagramHomCorner i f)) :
    HasLiftingProperty i (f.app (op ⦋0⦌)) := by
  constructor
  intro a b sq
  let a₀ : (Δ[0] : SSet.{v}) ⟶ diagramHomSSet A W := SSet.yonedaEquiv.symm a
  let b₀ : (Δ[0] : SSet.{v}) ⟶ diagramHomSSet B V := SSet.yonedaEquiv.symm b
  have comm : a₀ ≫ diagramHomPostcomp A f = b₀ ≫ diagramHomPrecomp i V := by
    apply SSet.yonedaEquiv.injective
    dsimp only [a₀, b₀]
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact sq.w
  let k := pullback.lift a₀ b₀ comm
  let j := (SSet.boundary.{v} 0).ι
  have sq' : CommSq (SSet.boundary.isInitial.to _) j (diagramHomCorner i f) k :=
    ⟨SSet.boundary.isInitial.hom_ext _ _⟩
  letI := h
  refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv sq'.lift, ?_, ?_⟩
  · have w : (sq'.lift ≫ diagramHomCorner i f) ≫ pullback.fst _ _ =
        k ≫ pullback.fst _ _ := by rw [sq'.fac_right]
    simp only [Category.assoc, diagramHomCorner, k, pullback.lift_fst] at w
    have h' := congrArg SSet.yonedaEquiv w
    rw [SSet.yonedaEquiv_comp] at h'
    simpa only [a₀, Equiv.apply_symm_apply] using h'
  · have w : (sq'.lift ≫ diagramHomCorner i f) ≫ pullback.snd _ _ =
        k ≫ pullback.snd _ _ := by rw [sq'.fac_right]
    simp only [Category.assoc, diagramHomCorner, k, pullback.lift_snd] at w
    have h' := congrArg SSet.yonedaEquiv w
    rw [SSet.yonedaEquiv_comp] at h'
    simpa only [b₀, Equiv.apply_symm_apply] using h'

/-- Kan fibration of the corner and weak equivalence on both mapping spaces give strict
lifting at degree zero. -/
theorem hasLiftingProperty_evalZero_of_mappingTests
    (hA : trivialFibrations SSet.{v} (diagramHomPostcomp A f))
    (hB : weakEquivalences SSet.{v} (diagramHomPostcomp B f))
    (hc : fibrations SSet.{v} (diagramHomCorner i f)) :
    HasLiftingProperty i (f.app (op ⦋0⦌)) := by
  letI : (trivialFibrations SSet.{v}).IsStableUnderBaseChange := by
    rw [← rlp_eq_of_wfs (cofibrations SSet.{v}) (trivialFibrations SSet.{v})]
    infer_instance
  have hπ := (trivialFibrations SSet.{v}).pullback_snd
    (diagramHomPostcomp A f) (diagramHomPrecomp i V) hA
  have w : diagramHomCorner i f ≫
      pullback.snd (diagramHomPostcomp A f) (diagramHomPrecomp i V) = diagramHomPostcomp B f :=
    pullback.lift_snd _ _ _
  have h : weakEquivalences SSet.{v} (diagramHomCorner i f) :=
    (weakEquivalences SSet.{v}).of_postcomp _ _ hπ.2 (w.symm ▸ hB)
  apply hasLiftingProperty_evalZero_of_diagramHomCorner
  have w : SSet.modelCategoryQuillen.I.rlp (diagramHomCorner i f) := by
    rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    exact ⟨hc, h⟩
  exact w _ ⟨0⟩

variable [HasLimitsOfSize.{0, 0} C]

/-- A coefficient lift against the relative matching map gives the relative boundary lift. -/
theorem diagramHomCorner_boundary_lifting (n : ℕ)
    (h : HasLiftingProperty i (relativeMatchingMap n f)) :
    HasLiftingProperty (SSet.boundary.{v} n).ι (diagramHomCorner i f) := by
  constructor
  intro a b sq
  let P := pullback (diagramHomPostcomp A f) (diagramHomPrecomp i V)
  let b₀ : (Δ[n] : SSet.{v}) ⟶ diagramHomSSet A W := b ≫ pullback.fst _ _
  let b₁ : (Δ[n] : SSet.{v}) ⟶ diagramHomSSet B V := b ≫ pullback.snd _ _
  let a' := boundaryDiagramHomEquiv n B W a
  let b₀' : A ⟶ W.obj (op ⦋n⦌) := SSet.yonedaEquiv b₀
  let b₁' : B ⟶ V.obj (op ⦋n⦌) := SSet.yonedaEquiv b₁
  have h₀ : a ≫ diagramHomPrecomp i W = (SSet.boundary n).ι ≫ b₀ := by
    have w := congrArg (fun k : (SSet.boundary n).toSSet ⟶ P ↦
      k ≫ pullback.fst (diagramHomPostcomp A f) (diagramHomPrecomp i V)) sq.w
    simpa only [Category.assoc, diagramHomCorner, pullback.lift_fst, b₀] using w
  have h₁ : a ≫ diagramHomPostcomp B f = (SSet.boundary n).ι ≫ b₁ := by
    have w := congrArg (fun k : (SSet.boundary n).toSSet ⟶ P ↦
      k ≫ pullback.snd (diagramHomPostcomp A f) (diagramHomPrecomp i V)) sq.w
    simpa only [Category.assoc, diagramHomCorner, pullback.lift_snd, b₁] using w
  have h₁' : a' ≫ (matchingFunctor n).map f = b₁' ≫ (matchingComparison n).app V := by
    change boundaryDiagramHomEquiv n B W a ≫ (matchingFunctor n).map f =
      SSet.yonedaEquiv b₁ ≫ (matchingComparison n).app V
    rw [← boundaryDiagramHomEquiv_postcomp, h₁, boundaryDiagramHomEquiv_restrict]
  let b' := pullback.lift a' b₁' h₁'
  have sq' : CommSq b₀' i (relativeMatchingMap n f) b' := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeMatchingMap, b', pullback.lift_fst]
      change SSet.yonedaEquiv b₀ ≫ (matchingComparison n).app W =
        i ≫ boundaryDiagramHomEquiv n B W a
      rw [← boundaryDiagramHomEquiv_restrict, ← boundaryDiagramHomEquiv_precomp, h₀]
    · simp only [Category.assoc, relativeMatchingMap, b', pullback.lift_snd]
      have w : b₀ ≫ diagramHomPostcomp A f = b₁ ≫ diagramHomPrecomp i V :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k ↦ b ≫ k) pullback.condition).trans (Category.assoc _ _ _).symm)
      exact congrArg SSet.yonedaEquiv w
  letI := h
  refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv.symm sq'.lift, ?_, ?_⟩
  · apply (boundaryDiagramHomEquiv n B W).injective
    rw [boundaryDiagramHomEquiv_restrict, Equiv.apply_symm_apply]
    have w : (sq'.lift ≫ relativeMatchingMap n f) ≫ pullback.fst _ _ =
        b' ≫ pullback.fst _ _ := by rw [sq'.fac_right]
    simpa only [Category.assoc, relativeMatchingMap, b', pullback.lift_fst] using w
  · apply pullback.hom_ext
    · simp only [Category.assoc, diagramHomCorner, pullback.lift_fst]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact sq'.fac_left
    · simp only [Category.assoc, diagramHomCorner, pullback.lift_snd]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      have w : (sq'.lift ≫ relativeMatchingMap n f) ≫ pullback.snd _ _ =
          b' ≫ pullback.snd _ _ := by rw [sq'.fac_right]
      simpa only [Category.assoc, relativeMatchingMap, b', pullback.lift_snd] using w

/-- If the coefficient map lifts against each relative matching map, its relative
Hom map lifts against every monomorphism of simplicial sets. -/
theorem diagramHomCorner_mono_lifting (h : ∀ n, HasLiftingProperty i (relativeMatchingMap n f))
    {K L : SSet.{v}} (j : K ⟶ L) [Mono j] :
    HasLiftingProperty j (diagramHomCorner i f) := by
  have hI : SSet.modelCategoryQuillen.I.rlp (diagramHomCorner i f) := by
    intro X Y k hk
    obtain ⟨n⟩ := hk
    exact diagramHomCorner_boundary_lifting i f n (h n)
  rw [SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp] at hI
  exact hI j (show Mono j from inferInstance)

end

end DaggerModels.PartII
