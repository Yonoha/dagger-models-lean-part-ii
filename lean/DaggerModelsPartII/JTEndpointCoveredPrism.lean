import DaggerModelsPartII.JTRelativeEndpointPrism
import OriginalCounitRightConeRelativeHomotopyEndpoints
import NativeSimplicialPushoutTensorMono

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTEndpointCoveredPrism

noncomputable section

open JTRelativeEndpointPrism

private theorem actual_timeSlice_eq (X : SSet.{u}) (t : Fin 2) :
    DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice X t =
      JTRelativeEndpointPrism.timeSlice X t := by
  fin_cases t <;> rfl

theorem exists_relative_prism {A X X' : SSet.{u}}
    (u : A ⟶ X') (d : A ⟶ X) (π : X' ⟶ X) (σ : X ⟶ X')
    [Mono d] [Fibration π] [WeakEquivalence π]
    (huπ : u ≫ π = d) (hdσ : d ≫ σ = u) (hσπ : σ ≫ π = 𝟙 X) :
    ∃ H : X' ⊗ (Δ[1] : SSet.{u}) ⟶ X',
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice X' 0 ≫ H = 𝟙 X' ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice X' 1 ≫ H = π ≫ σ ∧
      (u ▷ (Δ[1] : SSet.{u})) ≫ H = fst A (Δ[1] : SSet.{u}) ≫ u ∧
      H ≫ π = fst X' (Δ[1] : SSet.{u}) ≫ π := by
  haveI : Mono u := mono_of_mono_fac huπ
  let sq := JTRelativeEndpointPrism.relativeCylinderSquare u
  haveI : Mono sq.ι :=
    DaggerNativeSimplicialPushoutTensorMono.mono_ι u (SSet.boundary 1).ι sq
  haveI : Cofibration sq.ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono sq.ι
  let gB := JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ)
  let gA := fst A (Δ[1] : SSet.{u}) ≫ u
  let bottom := fst X' (Δ[1] : SSet.{u}) ≫ π
  have hcompat :
      (u ▷ (SSet.boundary 1 : SSet.{u})) ≫ gB =
        (A ◁ (SSet.boundary 1).ι) ≫ gA := by
    apply SSet.boundary₁.hom_ext_leftTensor
    · rw [MonoidalCategory.whisker_exchange_assoc,
        JTRelativeEndpointPrism.endpointBoundary_zero]
      apply NatTrans.ext
      funext q x
      rfl
    · rw [MonoidalCategory.whisker_exchange_assoc,
        JTRelativeEndpointPrism.endpointBoundary_one]
      apply NatTrans.ext
      funext q x
      exact congrFun (NatTrans.congr_app (by simpa [Category.assoc] using
        (huπ ▸ hdσ)) q) x.1
  have hB : gB ≫ π = (X' ◁ (SSet.boundary 1).ι) ≫ bottom := by
    apply SSet.boundary₁.hom_ext_leftTensor
    · change (X' ◁ SSet.boundary₁.ι₀) ≫
        JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ) ≫ π = _
      rw [← Category.assoc, JTRelativeEndpointPrism.endpointBoundary_zero]
      apply NatTrans.ext
      rfl
    · change (X' ◁ SSet.boundary₁.ι₁) ≫
        JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ) ≫ π = _
      rw [← Category.assoc, JTRelativeEndpointPrism.endpointBoundary_one]
      simp only [Category.assoc, hσπ, Category.comp_id]
      apply NatTrans.ext
      rfl
  have hA : gA ≫ π = (u ▷ (Δ[1] : SSet.{u})) ≫ bottom := by
    dsimp [gA, bottom]
    apply NatTrans.ext
    funext q x
    rfl
  let top : sq.pt ⟶ X' := sq.isPushout.desc gB gA hcompat
  have htop : top ≫ π = sq.ι ≫ bottom := by
    apply sq.isPushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc,
        ← Category.assoc, sq.inl_ι]
      exact hB
    · rw [← Category.assoc, IsPushout.inr_desc,
        ← Category.assoc, sq.inr_ι]
      exact hA
  let c : CommSq top sq.ι π bottom := ⟨htop⟩
  let H := c.lift
  have hHB : (X' ◁ (SSet.boundary 1).ι) ≫ H = gB := by
    calc
      _ = (sq.inl ≫ sq.ι) ≫ H :=
        (congrArg (fun f ↦ f ≫ H) sq.inl_ι).symm
      _ = sq.inl ≫ (sq.ι ≫ H) := Category.assoc _ _ _
      _ = sq.inl ≫ top := by rw [c.fac_left]
      _ = gB := sq.isPushout.inl_desc gB gA hcompat
  have hHA : (u ▷ (Δ[1] : SSet.{u})) ≫ H = gA := by
    calc
      _ = (sq.inr ≫ sq.ι) ≫ H :=
        (congrArg (fun f ↦ f ≫ H) sq.inr_ι).symm
      _ = sq.inr ≫ (sq.ι ≫ H) := Category.assoc _ _ _
      _ = sq.inr ≫ top := by rw [c.fac_left]
      _ = gA := sq.isPushout.inr_desc gB gA hcompat
  refine ⟨H, ?_, ?_, hHA, c.fac_right⟩
  · rw [actual_timeSlice_eq]
    change (SSet.stdSimplex.rightUnitor X').inv ≫
      (X' ◁ SSet.boundary₁.ι₀) ≫
        (X' ◁ (SSet.boundary 1).ι) ≫ H = 𝟙 X'
    rw [hHB]
    change _ ≫ (X' ◁ SSet.boundary₁.ι₀) ≫
      JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ) = _
    rw [JTRelativeEndpointPrism.endpointBoundary_zero, ← Category.assoc,
      SSet.stdSimplex.rightUnitor_inv_fst, Category.id_comp]
  · rw [actual_timeSlice_eq]
    change (SSet.stdSimplex.rightUnitor X').inv ≫
      (X' ◁ SSet.boundary₁.ι₁) ≫
        (X' ◁ (SSet.boundary 1).ι) ≫ H = π ≫ σ
    rw [hHB]
    change _ ≫ (X' ◁ SSet.boundary₁.ι₁) ≫
      JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ) = _
    rw [JTRelativeEndpointPrism.endpointBoundary_one, ← Category.assoc,
      SSet.stdSimplex.rightUnitor_inv_fst, Category.id_comp]

theorem exists_collapsed_prism {A B X X' P : SSet.{u}}
    (u : A ⟶ X') (d : A ⟶ X) (π : X' ⟶ X) (σ : X ⟶ X')
    [Mono d] [Fibration π] [WeakEquivalence π]
    (huπ : u ≫ π = d) (hdσ : d ≫ σ = u) (hσπ : σ ≫ π = 𝟙 X)
    (e : A ⟶ B) (l : X' ⟶ P) (b : B ⟶ P)
    (sq : IsPushout u e l b) (v : P ⟶ P)
    (hlv : l ≫ v = (π ≫ σ) ≫ l) (hbv : b ≫ v = b) :
    ∃ K : P ⊗ (Δ[1] : SSet.{u}) ⟶ P,
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 0 ≫ K = 𝟙 P ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 1 ≫ K = v ∧
      (b ▷ (Δ[1] : SSet.{u})) ≫ K = fst B (Δ[1] : SSet.{u}) ≫ b := by
  obtain ⟨H, hH0, hH1, hHu, _⟩ :=
    exists_relative_prism u d π σ huπ hdσ hσπ
  letI : BraidedCategory SSet.{u} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfShape WalkingSpan (tensorLeft (Δ[1] : SSet.{u})) :=
    inferInstance
  letI : PreservesColimitsOfShape WalkingSpan (tensorRight (Δ[1] : SSet.{u})) :=
    preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (Δ[1] : SSet.{u}))
  let tsq := sq.map (tensorRight (Δ[1] : SSet.{u}))
  have hc : (u ▷ (Δ[1] : SSet.{u})) ≫ H ≫ l =
      (e ▷ (Δ[1] : SSet.{u})) ≫ fst B (Δ[1] : SSet.{u}) ≫ b := by
    rw [← Category.assoc, hHu]
    apply NatTrans.ext
    funext q z
    exact congrFun (NatTrans.congr_app sq.w q) z.1
  let K := tsq.desc (H ≫ l) (fst B (Δ[1] : SSet.{u}) ≫ b) hc
  have hKl : (l ▷ (Δ[1] : SSet.{u})) ≫ K = H ≫ l :=
    tsq.inl_desc _ _ _
  have hKb : (b ▷ (Δ[1] : SSet.{u})) ≫ K =
      fst B (Δ[1] : SSet.{u}) ≫ b := tsq.inr_desc _ _ _
  refine ⟨K, ?_, ?_, hKb⟩
  · apply sq.hom_ext
    · rw [← Category.assoc,
        DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice_naturality,
        Category.assoc, hKl, ← Category.assoc, hH0]
      simp
    · rw [← Category.assoc,
        DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice_naturality,
        Category.assoc, hKb]
      apply NatTrans.ext
      rfl
  · apply sq.hom_ext
    · rw [← Category.assoc,
        DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice_naturality,
        Category.assoc, hKl, ← Category.assoc, hH1, hlv]
    · rw [← Category.assoc,
        DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice_naturality,
        Category.assoc, hKb, hbv]
      apply NatTrans.ext
      rfl

end

end DaggerModels.PartII.JTEndpointCoveredPrism
