import DaggerModelsPartII.JTEndpointReducedPullbackCover
import DaggerModelsPartII.JTEndpointCoveredPrism
import DaggerModelsPartII.JTEndpointCoverRigidification
import DaggerModelsPartII.GrothendieckContractibleFibers
import DaggerModelsPartII.JTBoundaryNecklacePresentationCone
import NativeIhomRelativeSectionsWeak

/-! Relative deformation after collapsing the full inverse image of a boundary. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits MonoidalCategory EnrichedCategory
  CartesianMonoidalCategory HomotopicalAlgebra Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FullInverseImagePrism

noncomputable section

/-- A trivial fibration contracts each fiber toward a chosen section. -/
theorem exists_fiber_prism {X X' : SSet.{0}}
    (π : X' ⟶ X) (σ : X ⟶ X')
    [Fibration π] [WeakEquivalence π]
    (hσπ : σ ≫ π = 𝟙 X) :
    ∃ H : X' ⊗ (Δ[1] : SSet.{0}) ⟶ X',
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice X' 0 ≫ H = 𝟙 X' ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice X' 1 ≫ H = π ≫ σ ∧
      H ≫ π = fst X' (Δ[1] : SSet.{0}) ≫ π := by
  let g := DaggerModels.PartII.JTRelativeEndpointPrism.endpointBoundary (𝟙 X') (π ≫ σ)
  let b := fst X' (Δ[1] : SSet.{0}) ≫ π
  have hb : g ≫ π = (X' ◁ (SSet.boundary 1).ι) ≫ b := by
    apply SSet.boundary₁.hom_ext_leftTensor
    · change (X' ◁ SSet.boundary₁.ι₀) ≫ g ≫ π = _
      rw [← Category.assoc,
        DaggerModels.PartII.JTRelativeEndpointPrism.endpointBoundary_zero]
      apply NatTrans.ext
      rfl
    · change (X' ◁ SSet.boundary₁.ι₁) ≫ g ≫ π = _
      rw [← Category.assoc,
        DaggerModels.PartII.JTRelativeEndpointPrism.endpointBoundary_one]
      simp only [Category.assoc, hσπ, Category.comp_id]
      apply NatTrans.ext
      rfl
  letI : Mono (X' ◁ (SSet.boundary 1).ι) :=
    DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono X' (SSet.boundary 1).ι
  letI : Cofibration (X' ◁ (SSet.boundary 1).ι) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  let c : CommSq g (X' ◁ (SSet.boundary 1).ι) π b := ⟨hb⟩
  let H := c.lift
  have hH : (X' ◁ (SSet.boundary 1).ι) ≫ H = g := c.fac_left
  refine ⟨H, ?_, ?_, c.fac_right⟩
  · change (SSet.stdSimplex.rightUnitor X').inv ≫
      (X' ◁ SSet.boundary₁.ι₀) ≫
        (X' ◁ (SSet.boundary 1).ι) ≫ H = 𝟙 X'
    rw [hH]
    rw [DaggerModels.PartII.JTRelativeEndpointPrism.endpointBoundary_zero,
      ← Category.assoc, SSet.stdSimplex.rightUnitor_inv_fst, Category.id_comp]
  · change (SSet.stdSimplex.rightUnitor X').inv ≫
      (X' ◁ SSet.boundary₁.ι₁) ≫
        (X' ◁ (SSet.boundary 1).ι) ≫ H = π ≫ σ
    rw [hH]
    rw [DaggerModels.PartII.JTRelativeEndpointPrism.endpointBoundary_one,
      ← Category.assoc, SSet.stdSimplex.rightUnitor_inv_fst, Category.id_comp]

/-- A fiberwise prism restricts to the entire inverse-image boundary and
preserves its projection to the old boundary. -/
def pullbackPrism {A A' X X' : SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (u : A' ⟶ X') (v : A' ⟶ A) (sqA : IsPullback u v π d)
    (H : X' ⊗ (Δ[1] : SSet.{0}) ⟶ X')
    (hH : H ≫ π = fst X' (Δ[1] : SSet.{0}) ≫ π) :
    A' ⊗ (Δ[1] : SSet.{0}) ⟶ A' := by
  let hu : (u ▷ (Δ[1] : SSet.{0})) ≫ H ≫ π =
      (fst (A') (Δ[1] : SSet.{0}) ≫ v) ≫ d := by
    rw [Category.assoc, hH]
    apply NatTrans.ext
    funext q z
    exact congrFun (NatTrans.congr_app (sqA.w) q) z.1
  exact sqA.lift ((u ▷ (Δ[1] : SSet.{0})) ≫ H)
    (fst (A') (Δ[1] : SSet.{0}) ≫ v) hu

theorem pullbackPrism_fst {A A' X X' : SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (u : A' ⟶ X') (v : A' ⟶ A) (sqA : IsPullback u v π d)
    (H : X' ⊗ (Δ[1] : SSet.{0}) ⟶ X')
    (hH : H ≫ π = fst X' (Δ[1] : SSet.{0}) ≫ π) :
    pullbackPrism π d u v sqA H hH ≫ u =
      (u ▷ (Δ[1] : SSet.{0})) ≫ H :=
  sqA.lift_fst _ _ _

theorem pullbackPrism_snd {A A' X X' : SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (u : A' ⟶ X') (v : A' ⟶ A) (sqA : IsPullback u v π d)
    (H : X' ⊗ (Δ[1] : SSet.{0}) ⟶ X')
    (hH : H ≫ π = fst X' (Δ[1] : SSet.{0}) ≫ π) :
    pullbackPrism π d u v sqA H hH ≫ v =
      fst (A') (Δ[1] : SSet.{0}) ≫ v :=
  sqA.lift_snd _ _ _

/-- The full inverse-image boundary can move during the contraction because
its projection to the old boundary remains fixed. -/
theorem exists_collapsed_prism {A A' B X X' P : SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (u : A' ⟶ X') (v : A' ⟶ A) (sqA : IsPullback u v π d) (σ : X ⟶ X')
    [Fibration π] [WeakEquivalence π] (hσπ : σ ≫ π = 𝟙 X)
    (e : A ⟶ B)
    (l : X' ⟶ P) (b : B ⟶ P)
    (sq : IsPushout (u) (v ≫ e) l b)
    (m : P ⟶ P)
    (hlm : l ≫ m = (π ≫ σ) ≫ l) (hbm : b ≫ m = b) :
    ∃ K : P ⊗ (Δ[1] : SSet.{0}) ⟶ P,
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 0 ≫ K = 𝟙 P ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 1 ≫ K = m ∧
      (b ▷ (Δ[1] : SSet.{0})) ≫ K = fst B (Δ[1] : SSet.{0}) ≫ b := by
  obtain ⟨H, hH0, hH1, hHπ⟩ := exists_fiber_prism π σ hσπ
  let HA := pullbackPrism π d u v sqA H hHπ
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfShape WalkingSpan (tensorLeft (Δ[1] : SSet.{0})) :=
    inferInstance
  letI : PreservesColimitsOfShape WalkingSpan (tensorRight (Δ[1] : SSet.{0})) :=
    preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (Δ[1] : SSet.{0}))
  let tsq := sq.map (tensorRight (Δ[1] : SSet.{0}))
  have hc : (u ▷ (Δ[1] : SSet.{0})) ≫ H ≫ l =
      ((v ≫ e) ▷ (Δ[1] : SSet.{0})) ≫
        fst B (Δ[1] : SSet.{0}) ≫ b := by
    rw [← Category.assoc, ← pullbackPrism_fst π d u v sqA H hHπ, Category.assoc,
      sq.w, ← Category.assoc,
      ← Category.assoc (pullbackPrism π d u v sqA H hHπ) (v) e,
      pullbackPrism_snd π d u v sqA H hHπ]
    apply NatTrans.ext
    funext q z
    rfl
  let K := tsq.desc (H ≫ l) (fst B (Δ[1] : SSet.{0}) ≫ b) hc
  have hKl : (l ▷ (Δ[1] : SSet.{0})) ≫ K = H ≫ l :=
    tsq.inl_desc _ _ _
  have hKb : (b ▷ (Δ[1] : SSet.{0})) ≫ K =
      fst B (Δ[1] : SSet.{0}) ≫ b := tsq.inr_desc _ _ _
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
        Category.assoc, hKl, ← Category.assoc, hH1, hlm]
    · rw [← Category.assoc,
        DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice_naturality,
        Category.assoc, hKb, hbm]
      apply NatTrans.ext
      rfl

/-- The original pushout has a section through the full inverse-image
pushout, and the latter contracts over the ordered boundary. -/
theorem exists_relative_deformation {A A' B X X' P Y : SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (u : A' ⟶ X') (v : A' ⟶ A) (sqA : IsPullback u v π d) (e : A ⟶ B)
    [Fibration π] [WeakEquivalence π]
    (l : X' ⟶ P) (b : B ⟶ P)
    (sqP : IsPushout (u) (v ≫ e) l b)
    (i : X ⟶ Y) (b₀ : B ⟶ Y)
    (sqY : IsPushout d e i b₀)
    (ρ : P ⟶ Y)
    (hρl : l ≫ ρ = π ≫ i) (hρb : b ≫ ρ = b₀) :
    ∃ (r : Y ⟶ P) (K : P ⊗ (Δ[1] : SSet.{0}) ⟶ P),
      r ≫ ρ = 𝟙 Y ∧
      b₀ ≫ r = b ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 0 ≫ K = 𝟙 P ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice P 1 ≫ K = ρ ≫ r ∧
      (b ▷ (Δ[1] : SSet.{0})) ≫ K = fst B (Δ[1] : SSet.{0}) ≫ b := by
  letI : Mono (initial.to X) := inferInstance
  letI : Cofibration (initial.to X) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  let cs : CommSq (initial.to X') (initial.to X) π (𝟙 X) :=
    ⟨initialIsInitial.hom_ext _ _⟩
  let σ := cs.lift
  have hσπ : σ ≫ π = 𝟙 X := cs.fac_right
  let τ : A ⟶ A' :=
    sqA.lift (d ≫ σ) (𝟙 A) (by rw [Category.assoc, hσπ]; simp)
  have hτu : τ ≫ u = d ≫ σ :=
    sqA.lift_fst _ _ _
  have hτv : τ ≫ v = 𝟙 A :=
    sqA.lift_snd _ _ _
  have hc : d ≫ (σ ≫ l) = e ≫ b := by
    rw [← Category.assoc, ← hτu, Category.assoc, sqP.w,
      ← Category.assoc, ← Category.assoc, hτv, Category.id_comp]
  let r := sqY.desc (σ ≫ l) b hc
  have hri : i ≫ r = σ ≫ l := sqY.inl_desc _ _ _
  have hrb : b₀ ≫ r = b := sqY.inr_desc _ _ _
  have hrρ : r ≫ ρ = 𝟙 Y := by
    apply sqY.hom_ext
    · rw [← Category.assoc, hri, Category.assoc, hρl,
        ← Category.assoc, hσπ]
      simp
    · rw [← Category.assoc, hrb, hρb]
      simp
  have hlm : l ≫ (ρ ≫ r) = (π ≫ σ) ≫ l := by
    rw [← Category.assoc, hρl, Category.assoc, hri, ← Category.assoc]
  have hbm : b ≫ (ρ ≫ r) = b := by
    rw [← Category.assoc, hρb, hrb]
  obtain ⟨K, hK0, hK1, hKb⟩ :=
    exists_collapsed_prism π d u v sqA σ hσπ e l b sqP (ρ ≫ r) hlm hbm
  exact ⟨r, K, hrρ, hrb, hK0, hK1, hKb⟩

/-- Pointwise deformation for a reduced diagram built from a complete
inverse-image boundary. The old boundary need not be monic. -/
theorem exists_diagram_relative_deformation
    {I : Type} [SmallCategory I] {B : SSet.{0}}
    {A X X' : I ⥤ SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (e : A ⟶ (Functor.const I).obj B)
    (Y : I ⥤ Under B) (i : X ⟶ Y ⋙ Under.forget B)
    (hi : d ≫ i = e ≫ JTEndpointReducedCover.boundary Y)
    (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    (hπ : trivialFibrations SSet.{0} (π.app p)) :
    let c := (JTEndpointReducedPullbackCover.reduced π d e).obj p
    let y := Y.obj p
    let ρ := (JTEndpointReducedPullbackCover.projection π d e Y i hi).app p
    ∃ (r : y ⟶ c) (K : c.right ⊗ (Δ[1] : SSet.{0}) ⟶ c.right),
      r ≫ ρ = 𝟙 y ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice c.right 0 ≫ K =
        𝟙 c.right ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice c.right 1 ≫ K =
        ρ.right ≫ r.right ∧
      (c.hom ▷ (Δ[1] : SSet.{0})) ≫ K =
        fst B (Δ[1] : SSet.{0}) ≫ c.hom := by
  letI : Fibration (π.app p) := ((mem_trivialFibrations_iff _).mp hπ).1
  letI : WeakEquivalence (π.app p) := ((mem_trivialFibrations_iff _).mp hπ).2
  let u := (JTEndpointReducedPullbackCover.u π d).app p
  let v := (JTEndpointReducedPullbackCover.v π d).app p
  let l := (pushout.inl (JTEndpointReducedPullbackCover.u π d)
    (JTEndpointReducedPullbackCover.collapse π d e)).app p
  let b := (pushout.inr (JTEndpointReducedPullbackCover.u π d)
    (JTEndpointReducedPullbackCover.collapse π d e)).app p
  let ρ := (JTEndpointReducedPullbackCover.projection π d e Y i hi).app p
  let sqP : IsPushout u (v ≫ e.app p) l b := by
    convert (IsPushout.of_hasPushout (JTEndpointReducedPullbackCover.u π d)
      (JTEndpointReducedPullbackCover.collapse π d e)).map
      ((evaluation I SSet.{0}).obj p) using 1
  let sqA : IsPullback u v (π.app p) (d.app p) :=
    (IsPullback.of_hasPullback π d).map ((evaluation I SSet.{0}).obj p)
  have hρl : l ≫ ρ.right = π.app p ≫ i.app p :=
    JTEndpointReducedPullbackCover.projection_cylinder π d e Y i hi p
  have hρb : b ≫ ρ.right = (JTEndpointReducedCover.boundary Y).app p :=
    Under.w ρ
  obtain ⟨r, K, hrρ, hrb, hK0, hK1, hKb⟩ :=
    exists_relative_deformation (π.app p) (d.app p) u v sqA (e.app p)
      l b sqP (i.app p) ((JTEndpointReducedCover.boundary Y).app p)
      sq ρ.right hρl hρb
  let rU : Y.obj p ⟶ (JTEndpointReducedPullbackCover.reduced π d e).obj p :=
    Under.homMk r hrb
  have hrU : rU ≫ ρ = 𝟙 (Y.obj p) := by
    apply Under.UnderMorphism.ext
    exact hrρ
  exact ⟨rU, K, hrU, hK0, hK1, hKb⟩

/-- The complete inverse-image presentation fiber is contractible when
the original cylinder Hom is weakly contractible. -/
theorem diagram_fiber_point_GW
    {I : Type} [SmallCategory I]
    {A X X' : I ⥤ SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (e : A ⟶ (Functor.const I).obj JTXiEndpointCollapse.boundary)
    (Y : I ⥤ Under JTXiEndpointCollapse.boundary)
    (i : X ⟶ Y ⋙ Under.forget JTXiEndpointCollapse.boundary)
    (hi : d ≫ i = e ≫ JTEndpointReducedCover.boundary Y)
    (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    (hπ : trivialFibrations SSet.{0} (π.app p))
    (hHom : DaggerSSetGluing.GW (pointMap
      (RV (Y.obj p).right (BoundaryNecklaceComma.first (Y.obj p)) ⟶[SSet.{0}]
        RV (Y.obj p).right (BoundaryNecklaceComma.last (Y.obj p))))) :
    DaggerSSetGluing.GW (pointMap
      (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder
        ((JTEndpointReducedPullbackCover.reduced π d e).obj p)))) := by
  obtain ⟨r, K, hr, hK0, hK1, hKB⟩ :=
    exists_diagram_relative_deformation π d e Y i hi p sq hπ
  exact JTEndpointCoverRigidification.fiber_point_GW
    ((JTEndpointReducedPullbackCover.projection π d e Y i hi).app p)
    r hr K hK0 hK1 hKB hHom

theorem diagram_forget_weak
    {I : Type} [SmallCategory I]
    {A X X' : I ⥤ SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (e : A ⟶ (Functor.const I).obj JTXiEndpointCollapse.boundary)
    (Y : I ⥤ Under JTXiEndpointCollapse.boundary)
    (i : X ⟶ Y ⋙ Under.forget JTXiEndpointCollapse.boundary)
    (hi : d ≫ i = e ≫ JTEndpointReducedCover.boundary Y)
    (sq : ∀ p, IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    (hπ : ∀ p, trivialFibrations SSet.{0} (π.app p))
    (hHom : ∀ p, DaggerSSetGluing.GW (pointMap
      (RV (Y.obj p).right (BoundaryNecklaceComma.first (Y.obj p)) ⟶[SSet.{0}]
        RV (Y.obj p).right (BoundaryNecklaceComma.last (Y.obj p))))) :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (JTEndpointReducedPullbackCover.reduced π d e)))) := by
  apply GrothendieckContractibleFibers.projection_weak
  intro p
  exact diagram_fiber_point_GW π d e Y i hi p (sq p) (hπ p) (hHom p)

theorem diagram_presentationProjection_weak
    {I : Type} [SmallCategory I]
    {A X X' : I ⥤ SSet.{0}}
    (π : X' ⟶ X) (d : A ⟶ X)
    (e : A ⟶ (Functor.const I).obj JTXiEndpointCollapse.boundary)
    (Y : I ⥤ Under JTXiEndpointCollapse.boundary)
    (i : X ⟶ Y ⋙ Under.forget JTXiEndpointCollapse.boundary)
    (hi : d ≫ i = e ≫ JTEndpointReducedCover.boundary Y)
    (sq : ∀ p, IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    (hπ : ∀ p, trivialFibrations SSet.{0} (π.app p))
    (hHom : ∀ p, DaggerSSetGluing.GW (pointMap
      (RV (Y.obj p).right (BoundaryNecklaceComma.first (Y.obj p)) ⟶[SSet.{0}]
        RV (Y.obj p).right (BoundaryNecklaceComma.last (Y.obj p)))))
    (hY : WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram Y)))) :
    WeakEquivalence (nerveMap
      (JTBoundaryNecklacePresentationCone.mapPresentation Y
        (JTEndpointReducedPullbackCover.reduced π d e) (𝟭 I)
        (JTEndpointReducedPullbackCover.projection π d e Y i hi))) := by
  let p := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram Y)
  let q := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (JTEndpointReducedPullbackCover.reduced π d e))
  let f := JTBoundaryNecklacePresentationCone.mapPresentation Y
    (JTEndpointReducedPullbackCover.reduced π d e) (𝟭 I)
    (JTEndpointReducedPullbackCover.projection π d e Y i hi)
  have hb : f ⋙ p = q := rfl
  have he : nerveMap f ≫ nerveMap p = nerveMap q :=
    (nerveFunctor.map_comp f.toCatHom p.toCatHom).symm.trans (congrArg nerveMap hb)
  letI : WeakEquivalence (nerveMap q) :=
    diagram_forget_weak π d e Y i hi sq hπ hHom
  letI : WeakEquivalence (nerveMap p) := hY
  letI : WeakEquivalence (nerveMap f ≫ nerveMap p) := by
    rw [he]
    infer_instance
  exact weakEquivalence_of_postcomp (nerveMap f) (nerveMap p)

end
end DaggerModels.PartII.FullInverseImagePrism
