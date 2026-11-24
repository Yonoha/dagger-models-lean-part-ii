import DaggerModelsPartII.JTCylinderStaircase

/-!
# Coordinate faces of the maximal prism simplices

The maximal staircase order map is injective. Its first coordinate
records the cut between the two horizontal rows, and the first
projection of its simplex is the corresponding cut map to `Δ[1]`.
This module concerns the uncollapsed prism.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTCylinderStaircaseFaces

open JTCylinderStaircase

/-- The sum of the two prism coordinates recovers the ordinal index
of a maximal staircase chain. -/
private theorem staircaseOrder_sum (k : ℕ) (t : Fin (k + 1))
    (i : Fin (k + 2)) :
    (staircaseOrder k t i).1.val + (staircaseOrder k t i).2.val = i.val := by
  dsimp [staircaseOrder]
  split_ifs with hi
  · simp
  · have hpos : 0 < i.val := by omega
    simp
    omega

/-- The maximal staircase chain has no repeated prism vertex. -/
theorem staircaseOrder_injective (k : ℕ) (t : Fin (k + 1)) :
    Function.Injective (staircaseOrder k t) := by
  intro i j h
  apply Fin.ext
  have hs := congrArg
    (fun p : Fin 2 × Fin (k + 1) ↦ p.1.val + p.2.val) h
  change (staircaseOrder k t i).1.val + (staircaseOrder k t i).2.val =
    (staircaseOrder k t j).1.val + (staircaseOrder k t j).2.val at hs
  rw [staircaseOrder_sum k t i, staircaseOrder_sum k t j] at hs
  exact hs

/-- Evaluation of a maximal prism simplex is composition with its
explicit maximal-chain order map. -/
theorem staircaseSimplex_objEquiv (k : ℕ) (t : Fin (k + 1))
    {n : ℕ} (z : (Δ[k + 1] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    SSet.prodStdSimplex.objEquiv
        ((staircaseSimplex k t).app (Opposite.op ⦋n⦌) z) =
      (staircaseOrder k t).comp
        (SSet.stdSimplex.objEquiv z).toOrderHom := by
  apply OrderHom.ext
  funext i
  rfl

/-- The chosen maximal prism simplex is monic in simplicial sets. -/
theorem staircaseSimplex_mono (k : ℕ) (t : Fin (k + 1)) :
    Mono (staircaseSimplex k t) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h n =>
      apply (mono_iff_injective _).mpr
      intro x y hxy
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      have hcoord := congrArg SSet.prodStdSimplex.objEquiv hxy
      rw [staircaseSimplex_objEquiv, staircaseSimplex_objEquiv] at hcoord
      exact staircaseOrder_injective k t (DFunLike.congr_fun hcoord i)

/-- A vertex of the maximal simplex lies in the initial pure row
exactly before or at the cut. -/
theorem staircaseOrder_first_iff (k : ℕ) (t : Fin (k + 1))
    (i : Fin (k + 2)) :
    (staircaseOrder k t i).1 = 0 ↔ i.val ≤ t.val := by
  dsimp [staircaseOrder]
  split_ifs with hi
  · simp [hi]
  · simp [hi]

/-- A vertex of the maximal simplex lies in the terminal pure row
exactly after the cut. -/
theorem staircaseOrder_second_iff (k : ℕ) (t : Fin (k + 1))
    (i : Fin (k + 2)) :
    (staircaseOrder k t i).1 = 1 ↔ t.val < i.val := by
  dsimp [staircaseOrder]
  split_ifs with hi
  · simp [hi]
  · simp [Nat.lt_of_not_ge hi]

/-- An input simplex maps entirely into the initial row precisely
when all of its ordinal vertices lie at or before the cut. -/
theorem staircaseSimplex_firstRow_iff (k : ℕ) (t : Fin (k + 1))
    {n : ℕ} (z : (Δ[k + 1] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (∀ i : Fin (n + 1),
      (SSet.prodStdSimplex.objEquiv
        ((staircaseSimplex k t).app (Opposite.op ⦋n⦌) z) i).1 = 0) ↔
      ∀ i : Fin (n + 1),
        ((SSet.stdSimplex.objEquiv z).toOrderHom i).val ≤ t.val := by
  simp only [staircaseSimplex_objEquiv, OrderHom.comp_coe, Function.comp_apply]
  constructor
  · intro h i
    exact (staircaseOrder_first_iff k t _).mp (h i)
  · intro h i
    exact (staircaseOrder_first_iff k t _).mpr (h i)

/-- An input simplex maps entirely into the terminal row precisely
when all of its ordinal vertices lie strictly after the cut. -/
theorem staircaseSimplex_lastRow_iff (k : ℕ) (t : Fin (k + 1))
    {n : ℕ} (z : (Δ[k + 1] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (∀ i : Fin (n + 1),
      (SSet.prodStdSimplex.objEquiv
        ((staircaseSimplex k t).app (Opposite.op ⦋n⦌) z) i).1 = 1) ↔
      ∀ i : Fin (n + 1),
        t.val < ((SSet.stdSimplex.objEquiv z).toOrderHom i).val := by
  simp only [staircaseSimplex_objEquiv, OrderHom.comp_coe, Function.comp_apply]
  constructor
  · intro h i
    exact (staircaseOrder_second_iff k t _).mp (h i)
  · intro h i
    exact (staircaseOrder_second_iff k t _).mpr (h i)

/-- The initial pure row as an ordinal face of the maximal simplex. -/
def firstFaceHom (k : ℕ) (t : Fin (k + 1)) :
    ⦋t.val⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.mkHom
    ⟨fun i ↦ ⟨i.val, by omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      exact Fin.le_iff_val_le_val.mpr hij⟩

/-- The terminal pure row as the complementary ordinal face. -/
def lastFaceHom (k : ℕ) (t : Fin (k + 1)) :
    ⦋k - t.val⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.mkHom
    ⟨fun i ↦ ⟨t.val + 1 + i.val, by omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      apply Fin.le_iff_val_le_val.mpr
      change t.val + 1 + i.val ≤ t.val + 1 + j.val
      omega⟩

/-- A simplex whose image lies in the initial pure prism row factors
through the actual initial ordinal face of the maximal simplex. -/
theorem firstRow_factor (k : ℕ) (t : Fin (k + 1)) {n : ℕ}
    (z : (Δ[k + 1] : SSet.{0}).obj (Opposite.op ⦋n⦌))
    (hz : ∀ i : Fin (n + 1),
      (SSet.prodStdSimplex.objEquiv
        ((staircaseSimplex k t).app (Opposite.op ⦋n⦌) z) i).1 = 0) :
    ∃ y : (Δ[t.val] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (SSet.stdSimplex.map (firstFaceHom k t)).app (Opposite.op ⦋n⦌) y = z := by
  have hcut := (staircaseSimplex_firstRow_iff k t z).mp hz
  let f := (SSet.stdSimplex.objEquiv z).toOrderHom
  let g : Fin (n + 1) →o Fin (t.val + 1) :=
    ⟨fun i ↦ ⟨(f i).val, by
      have hi := hcut i
      change (f i).val ≤ t.val at hi
      omega⟩, by
      intro i j hij
      exact Fin.le_iff_val_le_val.mpr
        (Fin.le_iff_val_le_val.mp (f.monotone hij))⟩
  refine ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk g), ?_⟩
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  rfl

/-- A simplex whose image lies in the terminal pure prism row factors
through the actual terminal ordinal face of the maximal simplex. -/
theorem lastRow_factor (k : ℕ) (t : Fin (k + 1)) {n : ℕ}
    (z : (Δ[k + 1] : SSet.{0}).obj (Opposite.op ⦋n⦌))
    (hz : ∀ i : Fin (n + 1),
      (SSet.prodStdSimplex.objEquiv
        ((staircaseSimplex k t).app (Opposite.op ⦋n⦌) z) i).1 = 1) :
    ∃ y : (Δ[k - t.val] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (SSet.stdSimplex.map (lastFaceHom k t)).app (Opposite.op ⦋n⦌) y = z := by
  have hcut := (staircaseSimplex_lastRow_iff k t z).mp hz
  let f := (SSet.stdSimplex.objEquiv z).toOrderHom
  let g : Fin (n + 1) →o Fin (k - t.val + 1) :=
    ⟨fun i ↦ ⟨(f i).val - (t.val + 1), by
      have hi := hcut i
      change t.val < (f i).val at hi
      have hfi := (f i).isLt
      change (f i).val < k + 2 at hfi
      have ht := t.isLt
      omega⟩, by
      intro i j hij
      apply Fin.le_iff_val_le_val.mpr
      have hmon := Fin.le_iff_val_le_val.mp (f.monotone hij)
      change (f i).val - (t.val + 1) ≤ (f j).val - (t.val + 1)
      exact Nat.sub_le_sub_right hmon _⟩
  refine ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk g), ?_⟩
  change SSet.stdSimplex.objEquiv.symm
    ((SimplexCategory.Hom.mk g : ⦋n⦌ ⟶ ⦋k - t.val⦌) ≫ lastFaceHom k t) = z
  apply SSet.stdSimplex.objEquiv.injective
  simp only [Equiv.apply_symm_apply]
  refine SimplexCategory.Hom.ext
    ((SimplexCategory.Hom.mk g : ⦋n⦌ ⟶ ⦋k - t.val⦌) ≫ lastFaceHom k t)
    (SSet.stdSimplex.objEquiv z) ?_
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have hi := hcut i
  change t.val < (f i).val at hi
  change t.val + 1 + ((f i).val - (t.val + 1)) = (f i).val
  omega

/-- The order map which records the height of each vertex of a
maximal prism simplex. -/
def cutHom (k : ℕ) (t : Fin (k + 1)) : ⦋k + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk
    (OrderHom.fst.comp (staircaseOrder k t))

/-- The chosen maximal simplex has the literal cut-height map as its
first projection. -/
theorem staircaseSimplex_fst (k : ℕ) (t : Fin (k + 1)) :
    staircaseSimplex k t ≫
        CartesianMonoidalCategory.fst (Δ[1] : SSet.{0}) Δ[k] =
      SSet.stdSimplex.map (cutHom k t) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  rfl

end DaggerModels.PartII.JTCylinderStaircaseFaces
