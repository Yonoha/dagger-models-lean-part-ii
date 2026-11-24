import DaggerModelsPartII.JTCommonCoefficientParameter

/-!
# An ordered bridge for changing the coefficient

The two copies of the common parameter retain their original vertex orders.
The bridge compares coefficient images first, then the copy, then the rank
within the corresponding old parameter.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChangingCoefficientBridgeOrder

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientParameter

noncomputable section

variable {k b b' : SimplexCategory}

/-- The standard simplex with two copies of every old parameter vertex. -/
def bridge (k n : SimplexCategory) : SimplexCategory :=
  ⦋(common k n).len * 2 + 1⦌

def Vertex (k n : SimplexCategory) :=
  (Fin (k.len + 1) × Fin (n.len + 1)) × Fin 2

/-- The rank within the old parameter simplex on the selected side. -/
def sideRank (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    (x : Vertex k n) : Fin ((common k n).len + 1) :=
  if x.2 = 0 then JTCommonCoefficientParameter.vertexEquiv c n x.1
  else JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x.1

private def key (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    (x : Vertex k n) :
    Fin (b'.len + 1) ×ₗ (Fin 2 ×ₗ Fin ((common k n).len + 1)) :=
  toLex ((c ≫ h).toOrderHom x.1.1, toLex (x.2, sideRank c h n x))

private theorem key_injective (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) : Function.Injective (key c h n) := by
  intro x y e
  have he : x.2 = y.2 := congrArg (fun z ↦ (ofLex (ofLex z).2).1) e
  have hr : sideRank c h n x = sideRank c h n y :=
    congrArg (fun z ↦ (ofLex (ofLex z).2).2) e
  apply Prod.ext
  · by_cases hx : x.2 = 0
    · have hy : y.2 = 0 := he ▸ hx
      have hr' : JTCommonCoefficientParameter.vertexEquiv c n x.1 =
          JTCommonCoefficientParameter.vertexEquiv c n y.1 := by
        simpa only [sideRank, hx, hy, ↓reduceIte] using hr
      exact (JTCommonCoefficientParameter.vertexEquiv c n).injective hr'
    · have hy : y.2 ≠ 0 := by simpa only [he] using hx
      have hr' : JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x.1 =
          JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n y.1 := by
        simpa only [sideRank, hx, hy, ↓reduceIte] using hr
      exact (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).injective hr'
  · exact he

private def vertexOrder (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    LinearOrder (Vertex k n) :=
  LinearOrder.lift' (key c h n) (key_injective c h n)

instance (k n : SimplexCategory) : Fintype (Vertex k n) :=
  inferInstanceAs (Fintype ((Fin (k.len + 1) × Fin (n.len + 1)) × Fin 2))

private theorem card (k n : SimplexCategory) :
    Fintype.card (Vertex k n) = (bridge k n).len + 1 := by
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin]
  change ((k.len + 1) * (n.len + 1)) * 2 =
    (k.len * (n.len + 1) + n.len) * 2 + 1 + 1
  ring

private def rank (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    Vertex k n ≃ Fin ((bridge k n).len + 1) := by
  letI := vertexOrder c h n
  exact (Fintype.orderIsoFinOfCardEq _ (card k n)).symm.toEquiv

/-- The exact vertex enumeration of the ordered bridge. -/
def vertexEquiv (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    Vertex k n ≃ Fin ((bridge k n).len + 1) :=
  rank c h n

theorem vertex_le_iff (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    (x y : Vertex k n) :
    vertexEquiv c h n x ≤ vertexEquiv c h n y ↔
      (c ≫ h).toOrderHom x.1.1 ≤ (c ≫ h).toOrderHom y.1.1 ∧
        ((c ≫ h).toOrderHom x.1.1 = (c ≫ h).toOrderHom y.1.1 →
          x.2 ≤ y.2 ∧ (x.2 = y.2 → sideRank c h n x ≤ sideRank c h n y)) := by
  letI := vertexOrder c h n
  change ((Fintype.orderIsoFinOfCardEq _ (card k n)).symm :
    Vertex k n ≃o Fin ((bridge k n).len + 1)) x ≤
    ((Fintype.orderIsoFinOfCardEq _ (card k n)).symm :
      Vertex k n ≃o Fin ((bridge k n).len + 1)) y ↔ _
  rw [OrderIso.le_iff_le]
  change key c h n x ≤ key c h n y ↔ _
  simp only [key, Prod.Lex.toLex_le_toLex']

@[simp] theorem sideRank_zero (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    sideRank c h n (x, 0) = JTCommonCoefficientParameter.vertexEquiv c n x := by
  simp [sideRank]

@[simp] theorem sideRank_one (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    sideRank c h n (x, 1) =
      JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x := by
  simp [sideRank]

theorem cross_copy_le (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    {a a' : Fin (k.len + 1)} (ha : a ≤ a')
    (t t' : Fin (n.len + 1)) {ε ε' : Fin 2} (he : ε < ε') :
    vertexEquiv c h n ((a, t), ε) ≤ vertexEquiv c h n ((a', t'), ε') := by
  apply (vertex_le_iff c h n _ _).2
  exact ⟨(c ≫ h).toOrderHom.monotone ha, fun _ ↦
    ⟨le_of_lt he, fun heq ↦ (ne_of_lt he heq).elim⟩⟩

/-- The product order embeds in the bridge order. -/
def prismOrder (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    ((Fin (k.len + 1) × Fin (n.len + 1)) × Fin 2) →o
      Fin ((bridge k n).len + 1) :=
  ⟨vertexEquiv c h n, by
    intro x y hxy
    apply (vertex_le_iff c h n x y).2
    refine ⟨(c ≫ h).toOrderHom.monotone hxy.1.1, ?_⟩
    intro _
    refine ⟨hxy.2, ?_⟩
    intro he
    have hr : JTCommonCoefficientParameter.vertexEquiv c n x.1 ≤
        JTCommonCoefficientParameter.vertexEquiv c n y.1 := by
      exact (JTCommonCoefficientParameter.prismOrder c n).monotone hxy.1
    by_cases hx : x.2 = 0
    · have hy : y.2 = 0 := he ▸ hx
      simpa only [sideRank, hx, hy, ↓reduceIte] using hr
    · have hy : y.2 ≠ 0 := by simpa only [he] using hx
      simpa only [sideRank, hx, hy, ↓reduceIte] using
        (JTCommonCoefficientParameter.prismOrder (c ≫ h) n).monotone hxy.1⟩

/-- Insert one original common parameter simplex into the bridge. -/
def side (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    (ε : Fin 2) : common k n ⟶ bridge k n :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    vertexEquiv c h n
      ((if ε = 0 then (JTCommonCoefficientParameter.vertexEquiv c n).symm v
        else (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).symm v), ε), by
    intro v w hvw
    apply (vertex_le_iff c h n _ _).2
    by_cases he : ε = 0
    · let x := (JTCommonCoefficientParameter.vertexEquiv c n).symm v
      let y := (JTCommonCoefficientParameter.vertexEquiv c n).symm w
      have hxy : JTCommonCoefficientParameter.vertexEquiv c n x ≤
          JTCommonCoefficientParameter.vertexEquiv c n y := by simpa [x, y] using hvw
      have hc := ((JTCommonCoefficientParameter.vertex_le_iff c n x y).1 hxy).1
      simp only [he, ↓reduceIte]
      refine ⟨h.toOrderHom.monotone hc, fun _ ↦ ⟨le_rfl, fun _ ↦ ?_⟩⟩
      simpa only [sideRank, he, ↓reduceIte, x, y] using hxy
    · let x := (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).symm v
      let y := (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).symm w
      have hxy : JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x ≤
          JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n y := by
        simpa [x, y] using hvw
      have hc := ((JTCommonCoefficientParameter.vertex_le_iff (c ≫ h) n x y).1 hxy).1
      simp only [he, ↓reduceIte]
      refine ⟨hc, fun _ ↦ ⟨le_rfl, fun _ ↦ ?_⟩⟩
      simpa only [sideRank, he, ↓reduceIte, x, y] using hxy⟩

@[simp] theorem side_vertexEquiv_zero (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (side c h n 0).toOrderHom (JTCommonCoefficientParameter.vertexEquiv c n x) =
      vertexEquiv c h n (x, 0) := by
  simp [side]

@[simp] theorem side_vertexEquiv_one (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (side c h n 1).toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x) =
      vertexEquiv c h n (x, 1) := by
  simp [side]

theorem side_injective (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
    (ε : Fin 2) : Function.Injective (side c h n ε).toOrderHom := by
  intro v w hvw
  by_cases he : ε = 0
  · simp only [side, he, ↓reduceIte] at hvw
    have hp := (vertexEquiv c h n).injective hvw
    exact (JTCommonCoefficientParameter.vertexEquiv c n).symm.injective
      (congrArg Prod.fst hp)
  · simp only [side, he, ↓reduceIte] at hvw
    have hp := (vertexEquiv c h n).injective hvw
    exact (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).symm.injective
      (congrArg Prod.fst hp)

/-- Projection of the bridge to the changed coefficient. -/
def base (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) : bridge k n ⟶ b' :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    (c ≫ h).toOrderHom ((vertexEquiv c h n).symm v).1.1, by
    intro v w hvw
    obtain ⟨x, rfl⟩ := (vertexEquiv c h n).surjective v
    obtain ⟨y, rfl⟩ := (vertexEquiv c h n).surjective w
    simpa only [Equiv.symm_apply_apply] using ((vertex_le_iff c h n x y).1 hvw).1⟩

@[simp] theorem base_vertexEquiv (c : k ⟶ b) (h : b ⟶ b')
    (n : SimplexCategory) (x : Vertex k n) :
    (base c h n).toOrderHom (vertexEquiv c h n x) =
      (c ≫ h).toOrderHom x.1.1 := by
  simp [base]

theorem side_base_zero (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    side c h n 0 ≫ base c h n = JTCommonCoefficientParameter.base c n ≫ h := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv c n).surjective v
  change (base c h n).toOrderHom ((side c h n 0).toOrderHom
    (JTCommonCoefficientParameter.vertexEquiv c n x)) =
    h.toOrderHom ((JTCommonCoefficientParameter.base c n).toOrderHom
      (JTCommonCoefficientParameter.vertexEquiv c n x))
  rw [side_vertexEquiv_zero, base_vertexEquiv,
    JTCommonCoefficientParameter.base_vertexEquiv]
  rfl

theorem side_base_one (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory) :
    side c h n 1 ≫ base c h n = JTCommonCoefficientParameter.base (c ≫ h) n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).surjective v
  change (base c h n).toOrderHom ((side c h n 1).toOrderHom
    (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x)) =
    (JTCommonCoefficientParameter.base (c ≫ h) n).toOrderHom
      (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x)
  rw [side_vertexEquiv_one, base_vertexEquiv,
    JTCommonCoefficientParameter.base_vertexEquiv]

end

end DaggerModels.PartII.JTChangingCoefficientBridgeOrder
