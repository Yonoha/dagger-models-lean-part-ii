import NativeSimplicialReplacementReindex
import NativeSimplicialReplacementWeightsChange
import NerveNatTrans
import TopCatModelCategory.SSet.Homotopy

/-!
The native simplicial replacement reindexing map varies simplicially under a
natural transformation. The cylinder keeps every simplex operator and transports
the coefficient along the first vertex of the mixed chain. This is a homotopy
between weighted reindexing maps; it makes no claim about the original dagger
comparison map or the still-open Theorem C statement.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementReindex
open DaggerNativeSimplicialReplacementWeightsChange

universe u

namespace DaggerModels.PartII.WeightedReplacementHomotopy

noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ SSet.{u})

private theorem family_map_apply {J : Type u} (X : J → SSet.{u})
    {q r : SimplexCategoryᵒᵖ} (β : q ⟶ r) (j : J) (z : (X j).obj q) :
    (DaggerOriginalProductGadget.familySSet X).map β ⟨j, z⟩ =
      (⟨j, (X j).map β z⟩ : (DaggerOriginalProductGadget.familySSet X).obj r) := rfl

private def P : Fin 2 × C ⥤ D :=
  Functor.uncurry.obj (ComposableArrows.mk₁ α)

def timeFunctor (q : SimplexCategoryᵒᵖ)
    (s : (Δ[1] : SSet.{u}).obj q) : Fin (q.unop.len + 1) ⥤ Fin 2 :=
  (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor

def mixedChain (q : SimplexCategoryᵒᵖ)
    (c : Chain (C := C) q) (s : (Δ[1] : SSet.{u}).obj q) :
    Chain (C := D) q :=
  ((timeFunctor q s).prod' c) ⋙ P α

/-- The map from the zero-time coefficient to the coefficient at time `i`. -/
private def transition (i : Fin 2) (c : C) :
    F.obj c ⟶ ((ComposableArrows.mk₁ α).obj i).obj c :=
  ((ComposableArrows.mk₁ α).map (homOfLE (Fin.zero_le i))).app c

private theorem transition_comp (i j : Fin 2) (h : i ⟶ j) (c : C) :
    transition α i c ≫ ((ComposableArrows.mk₁ α).map h).app c =
      transition α j c := by
  change ((ComposableArrows.mk₁ α).map (homOfLE (Fin.zero_le i))).app c ≫
    ((ComposableArrows.mk₁ α).map h).app c = _
  rw [← NatTrans.comp_app, ← Functor.map_comp]
  congr 1

private theorem transition_square (i j : Fin 2) (h : i ⟶ j)
    {c d : C} (f : c ⟶ d) :
    F.map f ≫ transition α j d =
      (transition α i c ≫ ((ComposableArrows.mk₁ α).map h).app c) ≫
        ((ComposableArrows.mk₁ α).obj j).map f := by
  rw [transition_comp]
  exact ((ComposableArrows.mk₁ α).map (homOfLE (Fin.zero_le j))).naturality f

/-- The original source coefficient moves along the first time vertex. -/
def firstTransport (q : SimplexCategoryᵒᵖ)
    (c : Chain (C := C) q) (s : (Δ[1] : SSet.{u}).obj q) :
    F.obj (first c) ⟶ first (mixedChain α q c s) :=
  transition α ((timeFunctor q s).obj 0) (first c)

/-- The coefficient transport commutes with every diagonal simplex operator. -/
private theorem firstTransport_natural {q r : SimplexCategoryᵒᵖ}
    (β : q ⟶ r) (c : Chain (C := C) q)
    (s : (Δ[1] : SSet.{u}).obj q) :
    F.map (initialArrow β c) ≫
        firstTransport α r ((nerve C).map β c) ((Δ[1] : SSet.{u}).map β s) =
      firstTransport α q c s ≫ initialArrow β (mixedChain α q c s) := by
  let σ := (SimplexCategory.toCat.map β.unop).toFunctor
  let j := σ.obj (0 : Fin (r.unop.len + 1))
  let τ := timeFunctor q s
  have h := transition_square α (τ.obj 0) (τ.obj j)
    (τ.map (homOfLE (Fin.zero_le j))) (initialArrow β c)
  have htime :
      (timeFunctor r ((Δ[1] : SSet.{u}).map β s)).obj 0 = τ.obj j := by
    dsimp only [timeFunctor, τ, j, σ]
    rw [SSet.stdSimplex.map_apply]
    simp only [Equiv.apply_symm_apply]
    rfl
  have hchain :
      initialArrow β (mixedChain α q c s) =
        ((ComposableArrows.mk₁ α).map
          (τ.map (homOfLE (Fin.zero_le j)))).app (first c) ≫
          ((ComposableArrows.mk₁ α).obj (τ.obj j)).map (initialArrow β c) := rfl
  unfold firstTransport
  cases htime
  rw [hchain]
  simpa only [τ, Category.assoc] using h

/-- The same horizontal square after applying the simplicial-set weight. -/
private theorem firstTransport_map_natural {q r : SimplexCategoryᵒᵖ}
    (β : q ⟶ r) (c : Chain (C := C) q)
    (s : (Δ[1] : SSet.{u}).obj q) :
    (F ⋙ H).map (initialArrow β c) ≫
        H.map (firstTransport α r ((nerve C).map β c) ((Δ[1] : SSet.{u}).map β s)) =
      H.map (firstTransport α q c s) ≫
        H.map (initialArrow β (mixedChain α q c s)) := by
  change H.map (F.map (initialArrow β c)) ≫ _ = _
  rw [← H.map_comp, ← H.map_comp, firstTransport_natural]

/-- The full chain and entire parameter simplex at one diagonal time. -/
private def cylinderCell (q : SimplexCategoryᵒᵖ)
    (x : Cell (F ⋙ H) q q) (s : (Δ[1] : SSet.{u}).obj q) :
    Cell H q q :=
  ⟨mixedChain α q x.1 s, (H.map (firstTransport α q x.1 s)).app q x.2⟩

/-- The actual mixed-chain cylinder, retaining the whole parameter simplex. -/
def weightedCylinderMap :
    DaggerBisimplicialDiagonal.diag (replacement (F ⋙ H)) ⊗ Δ[1] ⟶
      DaggerBisimplicialDiagonal.diag (replacement H) where
  app q p := cylinderCell α H q p.1 p.2
  naturality {q r} β := by
    funext p
    rcases p with ⟨⟨c, z⟩, s⟩
    change cylinderCell α H r
      ((DaggerBisimplicialDiagonal.diag (replacement (F ⋙ H))).map β ⟨c, z⟩)
      ((Δ[1] : SSet.{u}).map β s) =
        (DaggerBisimplicialDiagonal.diag (replacement H)).map β
          (cylinderCell α H q ⟨c, z⟩ s)
    rw [DaggerBisimplicialDiagonal.diag_map_other_order (replacement (F ⋙ H)) β,
      DaggerBisimplicialDiagonal.diag_map_other_order (replacement H) β]
    dsimp only [cylinderCell, types_comp_apply, replacement, horizontal, vertical]
    simp only [family_map_apply]
    have hchain : mixedChain α r ((nerve C).map β c) ((Δ[1] : SSet.{u}).map β s) =
        (nerve D).map β (mixedChain α q c s) := by
      have h := congrFun ((DaggerNerveHomotopy.natTransMap α).naturality β) (c, s)
      exact h
    apply Sigma.ext hchain
    cases hchain
    apply heq_of_eq
    change (H.map (firstTransport α r ((nerve C).map β c)
        ((Δ[1] : SSet.{u}).map β s))).app r
        (((F ⋙ H).map (initialArrow β c)).app r
          (((F ⋙ H).obj (first c)).map β z)) =
      (H.map (initialArrow β (mixedChain α q c s))).app r
        ((H.obj (first (mixedChain α q c s))).map β
          ((H.map (firstTransport α q c s)).app q z))
    have hn := congrFun ((H.map (firstTransport α q c s)).naturality β) z
    simp only [types_comp_apply] at hn
    rw [← hn]
    have hm := firstTransport_map_natural α H β c s
    have hz := congrFun (NatTrans.congr_app hm r)
      (((F ⋙ H).obj (first c)).map β z)
    simpa only [NatTrans.comp_app, types_comp_apply] using hz

/-- The chain and coefficient of the weighted cylinder at an arbitrary time simplex. -/
theorem weightedCylinderMap_app (q : SimplexCategoryᵒᵖ)
    (x : Cell (F ⋙ H) q q) (s : (Δ[1] : SSet.{u}).obj q) :
    (weightedCylinderMap α H).app q (x, s) =
      (⟨mixedChain α q x.1 s,
        (H.map (firstTransport α q x.1 s)).app q x.2⟩ : Cell H q q) := rfl

/-- The strict zero endpoint of the entire weighted cylinder. -/
theorem weightedCylinderMap_zero :
    SSet.ι₀ ≫ weightedCylinderMap α H = diagonalReindex F H := by
  ext q x
  rcases x with ⟨c, z⟩
  let x : (DaggerBisimplicialDiagonal.diag (replacement (F ⋙ H))).obj q := ⟨c, z⟩
  change cylinderCell α H q ⟨c, z⟩ ((SSet.ι₀.app q x).2) =
    (⟨c ⋙ F, z⟩ : Cell H q q)
  have hchain : mixedChain α q c ((SSet.ι₀.app q x).2) = c ⋙ F := by
    have h := congrFun (NatTrans.congr_app (DaggerNerveHomotopy.natTransMap_zero α) q) c
    exact h
  apply Sigma.ext hchain
  change (H.map (𝟙 (F.obj (first c)))).app q z ≍ z
  simp

/-- The strict one endpoint of the entire weighted cylinder. -/
theorem weightedCylinderMap_one :
    SSet.ι₁ ≫ weightedCylinderMap α H =
      diagonalChange (Functor.whiskerRight α H) ≫ diagonalReindex G H := by
  ext q x
  rcases x with ⟨c, z⟩
  let x : (DaggerBisimplicialDiagonal.diag (replacement (F ⋙ H))).obj q := ⟨c, z⟩
  change cylinderCell α H q ⟨c, z⟩ ((SSet.ι₁.app q x).2) =
    (⟨c ⋙ G, (H.map (α.app (first c))).app q z⟩ : Cell H q q)
  have hchain : mixedChain α q c ((SSet.ι₁.app q x).2) = c ⋙ G := by
    have h := congrFun (NatTrans.congr_app (DaggerNerveHomotopy.natTransMap_one α) q) c
    exact h
  apply Sigma.ext hchain
  change (H.map (α.app (first c))).app q z ≍
    (H.map (α.app (first c))).app q z
  exact HEq.rfl

/-- The full simplicial homotopy for the weighted reindexing natural transformation. -/
def weightedReindexHomotopy :
    SSet.Homotopy (diagonalReindex F H)
      (diagonalChange (Functor.whiskerRight α H) ≫ diagonalReindex G H) :=
  SSet.Homotopy.mk (weightedCylinderMap α H)
    (weightedCylinderMap_zero α H) (weightedCylinderMap_one α H)

end
end DaggerModels.PartII.WeightedReplacementHomotopy
