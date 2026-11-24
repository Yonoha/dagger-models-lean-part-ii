import KanBinaryUnitPullback
import OrdinarySegalBinaryComparison

/-!
# The two literal binary unit comparisons of an ordinary Segal space

The binary spine comparison is inserted into both Rezk 12.4 unit squares.
Every face and degeneracy below is the original simplicial-space operator.
Injective Kan fibrancy and the ordinary Segal condition suffice; ordinary
completeness is not used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalUnitPullbackWeak

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private abbrev d₀ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

private abbrev d₁ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private abbrev s (W : Space) : row W 0 ⟶ row W 1 :=
  W.map (SimplexCategory.σ (0 : Fin 1)).op

private abbrev r₀ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (0 : Fin 3)).op

private abbrev r₂ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (Fin.last 2)).op

private abbrev h₀ (W : Space) : row W 1 ⟶ row W 2 :=
  W.map (SimplexCategory.σ (0 : Fin 2)).op

private abbrev h₁ (W : Space) : row W 1 ⟶ row W 2 :=
  W.map (SimplexCategory.σ (1 : Fin 2)).op

private theorem map_op_comp (W : Space) {a b c : SimplexCategory}
    (f : a ⟶ b) (g : b ⟶ c) :
    W.map g.op ≫ W.map f.op = W.map (f ≫ g).op := by
  rw [op_comp, Functor.map_comp]

private theorem s_d₀ (W : Space) : s W ≫ d₀ W = 𝟙 (row W 0) := by
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1) =
      𝟙 ⦋0⦌ := by
    ext i
    fin_cases i
    rfl
  calc
    s W ≫ d₀ W =
        W.map (SimplexCategory.δ (0 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1)).op := map_op_comp W _ _
    _ = 𝟙 (row W 0) := by rw [h, op_id, W.map_id]

private theorem s_d₁ (W : Space) : s W ≫ d₁ W = 𝟙 (row W 0) := by
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1) =
      𝟙 ⦋0⦌ := by
    ext i
    fin_cases i
    rfl
  calc
    s W ≫ d₁ W =
        W.map (SimplexCategory.δ (1 : Fin 2) ≫
          SimplexCategory.σ (0 : Fin 1)).op := map_op_comp W _ _
    _ = 𝟙 (row W 0) := by rw [h, op_id, W.map_id]

private theorem h₀_r₀ (W : Space) : h₀ W ≫ r₀ W = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  calc
    h₀ W ≫ r₀ W =
        W.map (SimplexCategory.δ (0 : Fin 3) ≫
          SimplexCategory.σ (0 : Fin 2)).op := map_op_comp W _ _
    _ = 𝟙 (row W 1) := by rw [h, op_id, W.map_id]

private theorem h₀_r₂ (W : Space) : h₀ W ≫ r₂ W = d₁ W ≫ s W := by
  have h : SimplexCategory.δ (Fin.last 2) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    ext i
    fin_cases i <;> rfl
  calc
    h₀ W ≫ r₂ W =
        W.map (SimplexCategory.δ (Fin.last 2) ≫
          SimplexCategory.σ (0 : Fin 2)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (1 : Fin 2)).op := by rw [h]
    _ = d₁ W ≫ s W := (map_op_comp W _ _).symm

private theorem h₁_r₂ (W : Space) : h₁ W ≫ r₂ W = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (Fin.last 2) ≫ SimplexCategory.σ (1 : Fin 2) =
      𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  calc
    h₁ W ≫ r₂ W =
        W.map (SimplexCategory.δ (Fin.last 2) ≫
          SimplexCategory.σ (1 : Fin 2)).op := map_op_comp W _ _
    _ = 𝟙 (row W 1) := by rw [h, op_id, W.map_id]

private theorem h₁_r₀ (W : Space) : h₁ W ≫ r₀ W = d₀ W ≫ s W := by
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by
    ext i
    fin_cases i <;> rfl
  calc
    h₁ W ≫ r₀ W =
        W.map (SimplexCategory.δ (0 : Fin 3) ≫
          SimplexCategory.σ (1 : Fin 2)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (0 : Fin 2)).op := by rw [h]
    _ = d₀ W ≫ s W := (map_op_comp W _ _).symm

/-- The literal first unit insertion `σ₀` into the composable-edge pullback. -/
def firstUnitComparison (W : Space) : row W 1 ⟶ pullback (r₂ W) (s W) :=
  KanBinaryUnitPullback.unitComparison (d₁ W) (s W) (r₂ W)
    (h₀ W) (h₀_r₂ W)

/-- The second unit insertion `σ₁`, with the two outer faces exchanged. -/
def secondUnitComparison (W : Space) : row W 1 ⟶ pullback (r₀ W) (s W) :=
  KanBinaryUnitPullback.unitComparison (d₀ W) (s W) (r₀ W)
    (h₁ W) (h₁_r₀ W)

private def binarySymmetry (W : Space) :
    row W 2 ⟶ pullback (d₀ W) (d₁ W) :=
  OrdinarySegalBinaryComparison.binaryComparison W ≫
    (pullbackSymmetry (d₁ W) (d₀ W)).hom

private theorem binarySymmetry_fst (W : Space) :
    binarySymmetry W ≫ pullback.fst (d₀ W) (d₁ W) = r₂ W := by
  dsimp only [binarySymmetry]
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact OrdinarySegalBinaryComparison.binaryComparison_snd W

private theorem binarySymmetry_snd (W : Space) :
    binarySymmetry W ≫ pullback.snd (d₀ W) (d₁ W) = r₀ W := by
  dsimp only [binarySymmetry]
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact OrdinarySegalBinaryComparison.binaryComparison_fst W

/-- Rezk's first literal unit square is a Kan weak equivalence under only
injective Kan fibrancy and the ordinary Segal condition. -/
theorem firstUnitComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (firstUnitComparison W) := by
  have hq := OrdinarySegalBinaryComparison.binaryComparison_trivialFibration W hSegal
  letI : Fibration (OrdinarySegalBinaryComparison.binaryComparison W) := hq.1
  letI : WeakEquivalence (OrdinarySegalBinaryComparison.binaryComparison W) := hq.2
  exact KanBinaryUnitPullback.unitComparison_weak
    (d₀ W) (d₁ W) (s W) (s_d₀ W) (r₀ W) (r₂ W)
    (OrdinarySegalBinaryComparison.binaryComparison W)
    (OrdinarySegalBinaryComparison.binaryComparison_fst W)
    (OrdinarySegalBinaryComparison.binaryComparison_snd W)
    (h₀ W) (h₀_r₀ W) (h₀_r₂ W)

/-- Rezk's second literal unit square, using the same binary comparison
and the exact pullback symmetry, is also Kan weak. -/
theorem secondUnitComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (secondUnitComparison W) := by
  have hq := OrdinarySegalBinaryComparison.binaryComparison_trivialFibration W hSegal
  letI : Fibration (OrdinarySegalBinaryComparison.binaryComparison W) := hq.1
  letI : WeakEquivalence (OrdinarySegalBinaryComparison.binaryComparison W) := hq.2
  haveI : Fibration (binarySymmetry W) := by
    dsimp only [binarySymmetry]
    infer_instance
  haveI : WeakEquivalence (binarySymmetry W) := by
    dsimp only [binarySymmetry]
    infer_instance
  exact KanBinaryUnitPullback.unitComparison_weak
    (d₁ W) (d₀ W) (s W) (s_d₁ W) (r₂ W) (r₀ W)
    (binarySymmetry W) (binarySymmetry_fst W) (binarySymmetry_snd W)
    (h₁ W) (h₁_r₂ W) (h₁_r₀ W)

#print axioms firstUnitComparison
#print axioms secondUnitComparison
#print axioms firstUnitComparison_weak
#print axioms secondUnitComparison_weak

end

end DaggerModels.PartII.OrdinarySegalUnitPullbackWeak
