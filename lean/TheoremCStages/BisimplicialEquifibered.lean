import SSetWeakPullbackComparison
import NativeReedyRelativeReplacement
import NativeReedyRowFibrations

/-!
# Equifibered endpoint diagrams and their relative Reedy replacements

Equifibered means that each actual transition comparison into the strict
pullback is weak. When the row projections are Kan fibrations, this is the
homotopy-cartesian transition condition. The actual relative Reedy units
preserve it, by weak comparison of the corresponding pullbacks.
No diagonal fibration or homotopy-colimit descent is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.BisimplicialEquifibered

noncomputable section

def transitionComparison (f : Arrow BiSSet.{u})
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    f.left.obj q ⟶ pullback (f.hom.app r) (f.right.map θ) :=
  pullback.lift (f.left.map θ) (f.hom.app q) (f.hom.naturality θ)

theorem transitionComparison_fst (f : Arrow BiSSet.{u})
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    transitionComparison f θ ≫ pullback.fst (f.hom.app r) (f.right.map θ) =
      f.left.map θ := by
  simp only [transitionComparison, pullback.lift_fst]

theorem transitionComparison_snd (f : Arrow BiSSet.{u})
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    transitionComparison f θ ≫ pullback.snd (f.hom.app r) (f.right.map θ) =
      f.hom.app q := by
  simp only [transitionComparison, pullback.lift_snd]

/-- Each transition has a weak comparison to its literal pullback. -/
def Equifibered (f : Arrow BiSSet.{u}) : Prop :=
  ∀ ⦃q r : SimplexCategoryᵒᵖ⦄ (θ : q ⟶ r),
    WeakEquivalence (transitionComparison f θ)

def comparisonMap {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    pullback (f.hom.app r) (f.right.map θ) ⟶
      pullback (g.hom.app r) (g.right.map θ) :=
  SSetWeakPullbackComparison.comparison
    (f.hom.app r) (g.hom.app r) (s.left.app r) (s.right.app r)
    (NatTrans.congr_app s.w r).symm
    (f.right.map θ) (g.right.map θ) (s.right.app q) (s.right.naturality θ)

theorem comparisonMap_fst {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    comparisonMap s θ ≫ pullback.fst (g.hom.app r) (g.right.map θ) =
      pullback.fst (f.hom.app r) (f.right.map θ) ≫ s.left.app r :=
  SSetWeakPullbackComparison.comparison_fst _ _ _ _ _ _ _ _ _

theorem comparisonMap_snd {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    comparisonMap s θ ≫ pullback.snd (g.hom.app r) (g.right.map θ) =
      pullback.snd (f.hom.app r) (f.right.map θ) ≫ s.right.app q :=
  SSetWeakPullbackComparison.comparison_snd _ _ _ _ _ _ _ _ _

theorem transitionComparison_natural {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    s.left.app q ≫ transitionComparison g θ =
      transitionComparison f θ ≫ comparisonMap s θ := by
  apply pullback.hom_ext
  · have hR : (transitionComparison f θ ≫ comparisonMap s θ) ≫
        pullback.fst (g.hom.app r) (g.right.map θ) =
          f.left.map θ ≫ s.left.app r := by
      calc
        _ = (transitionComparison f θ ≫
            pullback.fst (f.hom.app r) (f.right.map θ)) ≫ s.left.app r := by
          simpa only [Category.assoc] using congrArg
            (fun k ↦ transitionComparison f θ ≫ k) (comparisonMap_fst s θ)
        _ = _ := congrArg (fun k ↦ k ≫ s.left.app r) (transitionComparison_fst f θ)
    calc
      _ = s.left.app q ≫ g.left.map θ := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ s.left.app q ≫ k) (transitionComparison_fst g θ)
      _ = f.left.map θ ≫ s.left.app r := (s.left.naturality θ).symm
      _ = _ := hR.symm
  · have hR : (transitionComparison f θ ≫ comparisonMap s θ) ≫
        pullback.snd (g.hom.app r) (g.right.map θ) =
          f.hom.app q ≫ s.right.app q := by
      calc
        _ = (transitionComparison f θ ≫
            pullback.snd (f.hom.app r) (f.right.map θ)) ≫ s.right.app q := by
          simpa only [Category.assoc] using congrArg
            (fun k ↦ transitionComparison f θ ≫ k) (comparisonMap_snd s θ)
        _ = _ := congrArg (fun k ↦ k ≫ s.right.app q) (transitionComparison_snd f θ)
    calc
      _ = s.left.app q ≫ g.hom.app q := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ s.left.app q ≫ k) (transitionComparison_snd g θ)
      _ = f.hom.app q ≫ s.right.app q := NatTrans.congr_app s.w q
      _ = _ := hR.symm

/-- A rowwise weak square between row fibrations transfers every actual
homotopy-cartesian transition square to its new endpoints. -/
theorem transfer_equifibered {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    (hF : ∀ q, Fibration (f.hom.app q)) (hG : ∀ q, Fibration (g.hom.app q))
    (hL : ∀ q, WeakEquivalence (s.left.app q))
    (hR : ∀ q, WeakEquivalence (s.right.app q))
    (hf : Equifibered f) : Equifibered g := by
  intro q r θ
  have : Fibration (f.hom.app r) := hF r
  have : Fibration (g.hom.app r) := hG r
  have : WeakEquivalence (s.left.app r) := hL r
  have : WeakEquivalence (s.right.app r) := hR r
  have : WeakEquivalence (s.right.app q) := hR q
  have : WeakEquivalence (comparisonMap s θ) :=
    SSetWeakPullbackComparison.comparison_weak _ _ _ _ _ _ _ _ _
  have : WeakEquivalence (transitionComparison f θ) := hf θ
  have : WeakEquivalence (transitionComparison f θ ≫ comparisonMap s θ) := inferInstance
  have : WeakEquivalence (s.left.app q) := hL q
  exact weakEquivalence_of_precomp_of_fac (transitionComparison_natural s θ)

/-- The specified relative Reedy replacement preserves equifiberedness.
Its units and row fibrations are the existing actual constructions. -/
theorem relative_replacement_equifibered (f : Arrow BiSSet.{u})
    (hF : ∀ q, Fibration (f.hom.app q)) (hf : Equifibered f) :
    Equifibered (DaggerNativeReedyRelativeReplacement.relativeReplacement.obj f) := by
  let s : f ⟶ DaggerNativeReedyRelativeReplacement.relativeReplacement.obj f :=
    Arrow.homMk (DaggerNativeReedyRelativeReplacement.totalUnit f)
      (DaggerNativeReedyRelativeReplacement.baseUnit f)
      (DaggerNativeReedyRelativeReplacement.unit_square f)
  apply transfer_equifibered s hF
  · exact fun q ↦ DaggerNativeReedyRowFibrations.row_fibration _
      (DaggerNativeReedyRelativeReplacement.projection_reedy f) q
  · exact fun q ↦ ((mem_trivialCofibrations_iff _).mp
      (DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial f q)).2
  · exact fun q ↦ ((mem_trivialCofibrations_iff _).mp
      (DaggerNativeReedyRelativeReplacement.baseUnit_row_trivial f q)).2
  · exact hf

#print axioms transitionComparison_natural
#print axioms transfer_equifibered
#print axioms relative_replacement_equifibered

end
end DaggerModels.PartII.BisimplicialEquifibered
