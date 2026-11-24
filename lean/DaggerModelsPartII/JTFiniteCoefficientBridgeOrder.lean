import DaggerModelsPartII.JTCommonCoefficientParameter

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeOrder

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientParameter

noncomputable section

variable {k b' : SimplexCategory} {m : ℕ} {b : Fin (m + 1) → SimplexCategory}

/-- The simplex containing `m + 1` copies of a common parameter. -/
def bridge (k n : SimplexCategory) (m : ℕ) : SimplexCategory :=
  ⦋(common k n).len * (m + 1) + m⦌

def Vertex (k n : SimplexCategory) (m : ℕ) :=
  (Fin (k.len + 1) × Fin (n.len + 1)) × Fin (m + 1)

/-- The old parameter rank on the selected copy. -/
def sideRank (c : ∀ e : Fin (m + 1), k ⟶ b e) (n : SimplexCategory)
    (x : Vertex k n m) : Fin ((common k n).len + 1) :=
  JTCommonCoefficientParameter.vertexEquiv (c x.2) n x.1

private def key (c : ∀ e : Fin (m + 1), k ⟶ b e) (u : k ⟶ b')
    (n : SimplexCategory) (x : Vertex k n m) :
    Fin (b'.len + 1) ×ₗ (Fin (m + 1) ×ₗ Fin ((common k n).len + 1)) :=
  toLex (u.toOrderHom x.1.1, toLex (x.2, sideRank c n x))

private theorem key_injective (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) : Function.Injective (key c u n) := by
  intro x y e
  have he : x.2 = y.2 := congrArg (fun z ↦ (ofLex (ofLex z).2).1) e
  have hr : sideRank c n x = sideRank c n y :=
    congrArg (fun z ↦ (ofLex (ofLex z).2).2) e
  apply Prod.ext
  · have hr' : JTCommonCoefficientParameter.vertexEquiv (c x.2) n x.1 =
        JTCommonCoefficientParameter.vertexEquiv (c x.2) n y.1 := by
      change JTCommonCoefficientParameter.vertexEquiv (c x.2) n x.1 =
        JTCommonCoefficientParameter.vertexEquiv (c y.2) n y.1 at hr
      rw [← he] at hr
      exact hr
    exact (JTCommonCoefficientParameter.vertexEquiv (c x.2) n).injective hr'
  · exact he

private def vertexOrder (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) : LinearOrder (Vertex k n m) :=
  LinearOrder.lift' (key c u n) (key_injective c u n)

instance (k n : SimplexCategory) (m : ℕ) : Fintype (Vertex k n m) :=
  inferInstanceAs (Fintype ((Fin (k.len + 1) × Fin (n.len + 1)) × Fin (m + 1)))

private theorem card (k n : SimplexCategory) (m : ℕ) :
    Fintype.card (Vertex k n m) = (bridge k n m).len + 1 := by
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin]
  change ((k.len + 1) * (n.len + 1)) * (m + 1) =
    (k.len * (n.len + 1) + n.len) * (m + 1) + m + 1
  ring

private def rank (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) :
    Vertex k n m ≃ Fin ((bridge k n m).len + 1) := by
  letI := vertexOrder c u n
  exact (Fintype.orderIsoFinOfCardEq _ (card k n m)).symm.toEquiv

/-- Rank vertices first by final coefficient, then copy, then old rank. -/
def vertexEquiv (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) :
    Vertex k n m ≃ Fin ((bridge k n m).len + 1) :=
  rank c u n

theorem vertex_le_iff (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) (x y : Vertex k n m) :
    vertexEquiv c u n x ≤ vertexEquiv c u n y ↔
      u.toOrderHom x.1.1 ≤ u.toOrderHom y.1.1 ∧
        (u.toOrderHom x.1.1 = u.toOrderHom y.1.1 →
          x.2 ≤ y.2 ∧ (x.2 = y.2 → sideRank c n x ≤ sideRank c n y)) := by
  letI := vertexOrder c u n
  change ((Fintype.orderIsoFinOfCardEq _ (card k n m)).symm :
    Vertex k n m ≃o Fin ((bridge k n m).len + 1)) x ≤
    ((Fintype.orderIsoFinOfCardEq _ (card k n m)).symm :
      Vertex k n m ≃o Fin ((bridge k n m).len + 1)) y ↔ _
  rw [OrderIso.le_iff_le]
  change key c u n x ≤ key c u n y ↔ _
  simp only [key, Prod.Lex.toLex_le_toLex']

theorem cross_copy_le (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory)
    {a a' : Fin (k.len + 1)} (ha : a ≤ a')
    (t t' : Fin (n.len + 1)) {e e' : Fin (m + 1)} (he : e < e') :
    vertexEquiv c u n ((a, t), e) ≤ vertexEquiv c u n ((a', t'), e') := by
  apply (vertex_le_iff c u n _ _).2
  exact ⟨u.toOrderHom.monotone ha, fun _ ↦
    ⟨le_of_lt he, fun heq ↦ (ne_of_lt he heq).elim⟩⟩

theorem same_copy_le (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) (e : Fin (m + 1))
    {a a' : Fin (k.len + 1)} {t t' : Fin (n.len + 1)}
    (ha : a ≤ a') (ht : t ≤ t') :
    vertexEquiv c u n ((a, t), e) ≤ vertexEquiv c u n ((a', t'), e) := by
  apply (vertex_le_iff c u n _ _).2
  refine ⟨u.toOrderHom.monotone ha, fun _ ↦ ⟨le_rfl, fun _ ↦ ?_⟩⟩
  exact (JTCommonCoefficientParameter.prismOrder (c e) n).monotone ⟨ha, ht⟩

/-- Insert one old parameter into its selected copy. -/
def side (c : ∀ e : Fin (m + 1), k ⟶ b e) (u : k ⟶ b')
    (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)
    (n : SimplexCategory) (e : Fin (m + 1)) : common k n ⟶ bridge k n m :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    vertexEquiv c u n ((JTCommonCoefficientParameter.vertexEquiv (c e) n).symm v, e), by
    intro v w hvw
    apply (vertex_le_iff c u n _ _).2
    let x := (JTCommonCoefficientParameter.vertexEquiv (c e) n).symm v
    let y := (JTCommonCoefficientParameter.vertexEquiv (c e) n).symm w
    have hxy : JTCommonCoefficientParameter.vertexEquiv (c e) n x ≤
        JTCommonCoefficientParameter.vertexEquiv (c e) n y := by simpa [x, y] using hvw
    have hc := ((JTCommonCoefficientParameter.vertex_le_iff (c e) n x y).1 hxy).1
    have hux : u.toOrderHom x.1 = (h e).toOrderHom ((c e).toOrderHom x.1) :=
      (congrArg (fun f : k ⟶ b' ↦ f.toOrderHom x.1) (hu e)).symm
    have huy : u.toOrderHom y.1 = (h e).toOrderHom ((c e).toOrderHom y.1) :=
      (congrArg (fun f : k ⟶ b' ↦ f.toOrderHom y.1) (hu e)).symm
    refine ⟨?_, fun _ ↦ ⟨le_rfl, fun _ ↦ ?_⟩⟩
    · rw [hux, huy]
      exact (h e).toOrderHom.monotone hc
    · exact hxy⟩

@[simp] theorem side_vertexEquiv (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
    (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory) (e : Fin (m + 1))
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (side c u h hu n e).toOrderHom (JTCommonCoefficientParameter.vertexEquiv (c e) n x) =
      vertexEquiv c u n (x, e) := by
  simp [side]

theorem side_injective (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
    (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory) (e : Fin (m + 1)) :
    Function.Injective (side c u h hu n e).toOrderHom := by
  intro v w hvw
  simp only [side] at hvw
  exact (JTCommonCoefficientParameter.vertexEquiv (c e) n).symm.injective
    (congrArg Prod.fst ((vertexEquiv c u n).injective hvw))

/-- Projection to the final coefficient. -/
def base (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) : bridge k n m ⟶ b' :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    u.toOrderHom ((vertexEquiv c u n).symm v).1.1, by
    intro v w hvw
    obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
    obtain ⟨y, rfl⟩ := (vertexEquiv c u n).surjective w
    simpa only [Equiv.symm_apply_apply] using ((vertex_le_iff c u n x y).1 hvw).1⟩

@[simp] theorem base_vertexEquiv (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) (x : Vertex k n m) :
    (base c u n).toOrderHom (vertexEquiv c u n x) = u.toOrderHom x.1.1 := by
  simp [base]

theorem side_base (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
    (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory) (e : Fin (m + 1)) :
    side c u h hu n e ≫ base c u n = JTCommonCoefficientParameter.base (c e) n ≫ h e := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c e) n).surjective v
  change (base c u n).toOrderHom ((side c u h hu n e).toOrderHom
    (JTCommonCoefficientParameter.vertexEquiv (c e) n x)) =
    (h e).toOrderHom ((JTCommonCoefficientParameter.base (c e) n).toOrderHom
      (JTCommonCoefficientParameter.vertexEquiv (c e) n x))
  rw [side_vertexEquiv, base_vertexEquiv,
    JTCommonCoefficientParameter.base_vertexEquiv]
  exact congrArg (fun f : k ⟶ b' ↦ f.toOrderHom x.1) (hu e) |>.symm

/-- Reindex the copies through an injective ordered map. -/
def mapCopies {m' : ℕ} {b₂ : Fin (m' + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), k ⟶ b₂ e)
    (u : k ⟶ b') (n : SimplexCategory)
    (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (hr : ∀ (e : Fin (m + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (c e) n x =
        JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x) :
    bridge k n m ⟶ bridge k n m' :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let x := (vertexEquiv c u n).symm v
    vertexEquiv d u n (x.1, j.toOrderHom x.2), by
    intro v w hvw
    obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
    obtain ⟨y, rfl⟩ := (vertexEquiv c u n).surjective w
    simp only [Equiv.symm_apply_apply]
    have hxy := (vertex_le_iff c u n x y).1 hvw
    apply (vertex_le_iff d u n _ _).2
    refine ⟨hxy.1, fun he ↦ ⟨j.toOrderHom.monotone (hxy.2 he).1, fun hej ↦ ?_⟩⟩
    have heq : x.2 = y.2 := hj hej
    have hlocal := (hxy.2 he).2 heq
    change JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom x.2)) n x.1 ≤
      JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom y.2)) n y.1
    rw [← hr x.2 x.1, ← hr y.2 y.1]
    exact hlocal⟩

@[simp] theorem mapCopies_vertexEquiv {m' : ℕ}
    {b₂ : Fin (m' + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), k ⟶ b₂ e)
    (u : k ⟶ b') (n : SimplexCategory)
    (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (hr : ∀ (e : Fin (m + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (c e) n x =
        JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x)
    (x : Vertex k n m) :
    (mapCopies c d u n j hj hr).toOrderHom (vertexEquiv c u n x) =
      vertexEquiv d u n (x.1, j.toOrderHom x.2) := by
  simp [mapCopies]

theorem mapCopies_base {m' : ℕ}
    {b₂ : Fin (m' + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), k ⟶ b₂ e)
    (u : k ⟶ b') (n : SimplexCategory)
    (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (hr : ∀ (e : Fin (m + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (c e) n x =
        JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x) :
    mapCopies c d u n j hj hr ≫ base d u n = base c u n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
  change (base d u n).toOrderHom
    ((mapCopies c d u n j hj hr).toOrderHom (vertexEquiv c u n x)) =
      (base c u n).toOrderHom (vertexEquiv c u n x)
  rw [mapCopies_vertexEquiv, base_vertexEquiv, base_vertexEquiv]

theorem side_mapCopies {m' : ℕ}
    {b₂ : Fin (m' + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), k ⟶ b₂ e)
    (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
    (h₂ : ∀ e, b₂ e ⟶ b')
    (hu : ∀ e, c e ≫ h e = u)
    (hu₂ : ∀ e, d e ≫ h₂ e = u)
    (n : SimplexCategory)
    (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (hr : ∀ (e : Fin (m + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (c e) n x =
        JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x)
    (e : Fin (m + 1)) :
    side c u h hu n e ≫ mapCopies c d u n j hj hr =
      side d u h₂ hu₂ n (j.toOrderHom e) := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c e) n).surjective v
  change (mapCopies c d u n j hj hr).toOrderHom
    ((side c u h hu n e).toOrderHom
      (JTCommonCoefficientParameter.vertexEquiv (c e) n x)) =
    (side d u h₂ hu₂ n (j.toOrderHom e)).toOrderHom
      (JTCommonCoefficientParameter.vertexEquiv (c e) n x)
  rw [side_vertexEquiv, mapCopies_vertexEquiv, hr e x, side_vertexEquiv]

theorem mapCopies_id
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (u : k ⟶ b') (n : SimplexCategory) :
    mapCopies c c u n (𝟙 ⦋m⦌) (fun _ _ h ↦ h) (by intros; rfl) =
      𝟙 (bridge k n m) := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
  rw [mapCopies_vertexEquiv]
  rfl

theorem mapCopies_comp {m' m'' : ℕ}
    {b₂ : Fin (m' + 1) → SimplexCategory}
    {b₃ : Fin (m'' + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e)
    (d : ∀ e : Fin (m' + 1), k ⟶ b₂ e)
    (f : ∀ e : Fin (m'' + 1), k ⟶ b₃ e)
    (u : k ⟶ b') (n : SimplexCategory)
    (j : ⦋m⦌ ⟶ ⦋m'⦌) (j' : ⦋m'⦌ ⟶ ⦋m''⦌)
    (hj : Function.Injective j.toOrderHom)
    (hj' : Function.Injective j'.toOrderHom)
    (hr : ∀ (e : Fin (m + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (c e) n x =
        JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x)
    (hr' : ∀ (e : Fin (m' + 1))
      (x : Fin (k.len + 1) × Fin (n.len + 1)),
      JTCommonCoefficientParameter.vertexEquiv (d e) n x =
        JTCommonCoefficientParameter.vertexEquiv (f (j'.toOrderHom e)) n x) :
    mapCopies c f u n (j ≫ j') (hj'.comp hj)
        (by intro e x; exact (hr e x).trans (hr' (j.toOrderHom e) x)) =
      mapCopies c d u n j hj hr ≫ mapCopies d f u n j' hj' hr' := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
  change (mapCopies c f u n (j ≫ j') (hj'.comp hj) _).toOrderHom
      (vertexEquiv c u n x) =
    (mapCopies d f u n j' hj' hr').toOrderHom
      ((mapCopies c d u n j hj hr).toOrderHom (vertexEquiv c u n x))
  simp only [mapCopies_vertexEquiv]
  rfl

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeOrder
