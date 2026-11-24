import DaggerModelsPartII.JTGraphParameterInterpolation
import DaggerModelsPartII.JTParameterBlockOperators

/-! Two actual ordinal copies of a time parameter and a full interpolation between them. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTDoubledGraphTime

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTCodiscreteParameterPairing (coord coord_map)
open JTParameterBlocks (common leftIn rightIn)
open JTGraphParameterInterpolation (interpolate coord_interpolate)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev iso (n : SimplexCategory) := parameterCodiscreteIso.app n

/-- Two ordered copies of the original time ordinal. -/
abbrev degree (n : SimplexCategory) := common n n

/-- A time operator acts on each copy through the same original operator. -/
abbrev operator {n n' : SimplexCategory} (a : n ⟶ n') : degree n ⟶ degree n' :=
  JTParameterBlockOperators.map a a

/-- The two copies form an actual functor on all simplex operators. -/
def doubling : SimplexCategory ⥤ SimplexCategory where
  obj := degree
  map := operator
  map_id n := JTParameterBlockOperators.map_id n n
  map_comp a b := (JTParameterBlockOperators.map_comp a b a b).symm

private def decode (n : SimplexCategory) (u : Fin ((degree n).len + 1)) :
    Fin (n.len + 1) × Fin 2 :=
  if h : u.val < n.len + 1 then (⟨u.val, h⟩, 0)
  else (⟨u.val - (n.len + 1), by
    have hu := u.isLt
    change u.val < n.len + n.len + 1 + 1 at hu
    omega⟩, 1)

private theorem decode_left (n : SimplexCategory) (u : Fin (n.len + 1)) :
    decode n ((leftIn n n).toOrderHom u) = (u, 0) := by
  unfold decode
  rw [dif_pos (show ((leftIn n n).toOrderHom u).val < n.len + 1 from u.isLt)]
  rfl

private theorem decode_right (n : SimplexCategory) (u : Fin (n.len + 1)) :
    decode n ((rightIn n n).toOrderHom u) = (u, 1) := by
  unfold decode
  have h : ¬ ((rightIn n n).toOrderHom u).val < n.len + 1 := by
    change ¬ n.len + 1 + u.val < n.len + 1
    omega
  rw [dif_neg h]
  apply Prod.ext
  · apply Fin.ext
    change n.len + 1 + u.val - (n.len + 1) = u.val
    omega
  · rfl

private theorem blocks_cover (n : SimplexCategory) (u : Fin ((degree n).len + 1)) :
    (∃ v, (leftIn n n).toOrderHom v = u) ∨ (∃ v, (rightIn n n).toOrderHom v = u) := by
  by_cases h : u.val < n.len + 1
  · exact Or.inl ⟨⟨u.val, h⟩, Fin.ext rfl⟩
  · have hu := u.isLt
    change u.val < n.len + n.len + 1 + 1 at hu
    refine Or.inr ⟨⟨u.val - (n.len + 1), by omega⟩, Fin.ext ?_⟩
    change n.len + 1 + (u.val - (n.len + 1)) = u.val
    omega

private theorem decode_map {n n' : SimplexCategory} (a : n ⟶ n')
    (u : Fin ((degree n).len + 1)) :
    decode n' ((operator a).toOrderHom u) = (a.toOrderHom (decode n u).1, (decode n u).2) := by
  rcases blocks_cover n u with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · have h := SimplexCategory.congr_toOrderHom_apply (JTParameterBlockOperators.leftIn_map a a) v
    change (operator a).toOrderHom ((leftIn n n).toOrderHom v) =
      (leftIn n' n').toOrderHom (a.toOrderHom v) at h
    rw [h, decode_left, decode_left]
  · have h := SimplexCategory.congr_toOrderHom_apply (JTParameterBlockOperators.rightIn_map a a) v
    change (operator a).toOrderHom ((rightIn n n).toOrderHom v) =
      (rightIn n' n').toOrderHom (a.toOrderHom v) at h
    rw [h, decode_right, decode_right]

/-- The groupoid-parameter map specified by an arbitrary function of vertices. -/
def vertexMap {a b : SimplexCategory}
    (f : Fin (a.len + 1) → Fin (b.len + 1)) : J.obj a ⟶ J.obj b :=
  mapOfVertices _ (fun z ↦ f (vertexLabels (iso a).hom z)) ≫ (iso b).inv

theorem coord_vertexMap {a b : SimplexCategory}
    (f : Fin (a.len + 1) → Fin (b.len + 1)) (q : SimplexCategoryᵒᵖ)
    (z : (J.obj a).obj q) (v : Fin (q.unop.len + 1)) :
    coord b q ((vertexMap f).app q z) v = f (coord a q z v) := by
  have h : vertexMap f ≫ (iso b).hom =
      mapOfVertices _ (fun w ↦ f (vertexLabels (iso a).hom w)) := by
    unfold vertexMap
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he := congrArg (fun w ↦ (w.obj v).as) (congrFun (NatTrans.congr_app h q) z)
  change coord b q ((vertexMap f).app q z) v =
    f (vertexLabels (iso a).hom ((J.obj a).map ((⦋0⦌ : SimplexCategory).const q.unop v).op z))
    at he
  rw [vertexLabels_natural] at he
  exact he

/-- The map of actual groupoid parameters that forgets the copy. -/
def fold (n : SimplexCategory) : J.obj (degree n) ⟶ J.obj n :=
  vertexMap (fun u ↦ (decode n u).1)

private def phase (n : SimplexCategory) : J.obj (degree n) ⟶ J.obj ⦋1⦌ :=
  vertexMap (fun u ↦ (decode n u).2)

/-- Folding the literal copies is natural in arbitrary time maps. -/
theorem fold_natural {n n' : SimplexCategory} (a : n ⟶ n') :
    J.map (operator a) ≫ fold n' = fold n ≫ J.map a := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n' q ((fold n').app q ((J.map (operator a)).app q z)) v =
    coord n' q ((J.map a).app q ((fold n).app q z)) v
  rw [fold, fold, coord_vertexMap, coord_map (operator a), decode_map, coord_map a, coord_vertexMap]

private theorem fold_left (n : SimplexCategory) : J.map (leftIn n n) ≫ fold n = 𝟙 _ := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n q ((fold n).app q ((J.map (leftIn n n)).app q z)) v = coord n q z v
  rw [fold, coord_vertexMap, coord_map, decode_left]

private theorem fold_right (n : SimplexCategory) : J.map (rightIn n n) ≫ fold n = 𝟙 _ := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n q ((fold n).app q ((J.map (rightIn n n)).app q z)) v = coord n q z v
  rw [fold, coord_vertexMap, coord_map, decode_right]

private abbrev pick {A : Type*} (x y : A) (v : Fin 2) :=
  if v = 0 then x else y

variable {X : SSet.{0}} {n k m : SimplexCategory}

/-- Interpolate two whole graphs with the same coefficient into one literal ordinal time. -/
def extendPair (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m) : X ⊗ J.obj (degree n) ⟶ J.obj m :=
  (X ◁ lift (fold n) (phase n)) ≫ (α_ X (J.obj n) (J.obj ⦋1⦌)).inv ≫
    interpolate (pick p₀ p₁)

private theorem coord_extendPair (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m) (q : SimplexCategoryᵒᵖ)
    (z : (X ⊗ J.obj (degree n)).obj q) (v : Fin (q.unop.len + 1)) :
    coord m q ((extendPair p₀ p₁).app q z) v =
      coord m q ((pick p₀ p₁ (decode n (coord (degree n) q z.2 v)).2).app q
        (z.1, (fold n).app q z.2)) v := by
  change coord m q ((interpolate (n := ⦋1⦌) (pick p₀ p₁)).app q
    ((z.1, (fold n).app q z.2), (phase n).app q z.2)) v = _
  rw [coord_interpolate]
  change coord m q
    ((pick p₀ p₁ (coord ⦋1⦌ q ((phase n).app q z.2) v)).app q
      (z.1, (fold n).app q z.2)) v = _
  rw [phase, coord_vertexMap]

theorem extendPair_left (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m) :
    (X ◁ J.map (leftIn n n)) ≫ extendPair p₀ p₁ = p₀ := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord m q ((extendPair p₀ p₁).app q (z.1, (J.map (leftIn n n)).app q z.2)) v =
    coord m q (p₀.app q z) v
  rw [coord_extendPair, coord_map (leftIn n n), decode_left]
  have h : (fold n).app q ((J.map (leftIn n n)).app q z.2) = z.2 :=
    congrFun (NatTrans.congr_app (fold_left n) q) z.2
  rw [h]
  rfl

theorem extendPair_right (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m) :
    (X ◁ J.map (rightIn n n)) ≫ extendPair p₀ p₁ = p₁ := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord m q ((extendPair p₀ p₁).app q (z.1, (J.map (rightIn n n)).app q z.2)) v =
    coord m q (p₁.app q z) v
  rw [coord_extendPair, coord_map (rightIn n n), decode_right]
  have h : (fold n).app q ((J.map (rightIn n n)).app q z.2) = z.2 :=
    congrFun (NatTrans.congr_app (fold_right n) q) z.2
  rw [h]
  rfl

variable (p : X ⊗ J.obj n ⟶ J.obj k) (e₀ e₁ : k ⟶ m)

/-- Interpolate in one actual ordinal time simplex between two coefficient placements. -/
def extend : X ⊗ J.obj (degree n) ⟶ J.obj m :=
  extendPair (p ≫ J.map e₀) (p ≫ J.map e₁)

theorem extend_left :
    (X ◁ J.map (leftIn n n)) ≫ extend p e₀ e₁ = p ≫ J.map e₀ :=
  extendPair_left _ _

theorem extend_right :
    (X ◁ J.map (rightIn n n)) ≫ extend p e₀ e₁ = p ≫ J.map e₁ :=
  extendPair_right _ _

/-- Simultaneous native, time and coefficient transport commutes with the
whole doubled graph if both original graphs commute. -/
theorem extendPair_square {Y : SSet.{0}} {n' m' : SimplexCategory}
    (g : X ⟶ Y) (a : n ⟶ n') (c : m ⟶ m')
    (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m) (p₀' p₁' : Y ⊗ J.obj n' ⟶ J.obj m')
    (h₀ : (g ⊗ₘ J.map a) ≫ p₀' = p₀ ≫ J.map c)
    (h₁ : (g ⊗ₘ J.map a) ≫ p₁' = p₁ ≫ J.map c) :
    (g ⊗ₘ J.map (operator a)) ≫ extendPair p₀' p₁' = extendPair p₀ p₁ ≫ J.map c := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let t := (decode n (coord (degree n) q z.2 v)).2
  let w := (z.1, (fold n).app q z.2)
  have ht : (fold n').app q ((J.map (operator a)).app q z.2) =
      (J.map a).app q ((fold n).app q z.2) :=
    congrFun (NatTrans.congr_app (fold_natural a) q) z.2
  have he : (g ⊗ₘ J.map a) ≫ pick p₀' p₁' t = pick p₀ p₁ t ≫ J.map c := by
    by_cases h : t = 0
    · simpa only [pick, if_pos h] using h₀
    · simpa only [pick, if_neg h] using h₁
  have hp := congrArg (fun u ↦ coord m' q u v) (congrFun (NatTrans.congr_app he q) w)
  change coord m' q ((pick p₀' p₁' t).app q (g.app q w.1, (J.map a).app q w.2)) v =
    coord m' q ((J.map c).app q ((pick p₀ p₁ t).app q w)) v at hp
  rw [coord_map] at hp
  change coord m' q ((extendPair p₀' p₁').app q (g.app q z.1, (J.map (operator a)).app q z.2)) v =
    coord m' q ((J.map c).app q ((extendPair p₀ p₁).app q z)) v
  rw [coord_extendPair, coord_map (operator a), decode_map, ht, coord_map c, coord_extendPair]
  exact hp

/-- A simultaneous native, time and coefficient square extends through
the whole doubled time whenever both coefficient placements commute. -/
theorem extend_square {Y : SSet.{0}} {n' k' m' : SimplexCategory}
    (g : X ⟶ Y) (a : n ⟶ n') (b : k ⟶ k') (c : m ⟶ m')
    (p' : Y ⊗ J.obj n' ⟶ J.obj k') (e₀' e₁' : k' ⟶ m')
    (h : (g ⊗ₘ J.map a) ≫ p' = p ≫ J.map b)
    (h₀ : e₀ ≫ c = b ≫ e₀') (h₁ : e₁ ≫ c = b ≫ e₁') :
    (g ⊗ₘ J.map (operator a)) ≫ extend p' e₀' e₁' = extend p e₀ e₁ ≫ J.map c := by
  unfold extend
  apply extendPair_square
  · rw [← Category.assoc, h, Category.assoc, ← J.map_comp, ← h₀, J.map_comp, ← Category.assoc]
  · rw [← Category.assoc, h, Category.assoc, ← J.map_comp, ← h₁, J.map_comp, ← Category.assoc]

/-- If both graphs have the same restricted parameter after an output
map, the entire mixed comparison has that restricted parameter. -/
theorem extendPair_over {A : SSet.{0}} {l : SimplexCategory} (ι : A ⟶ X)
    (p₀ p₁ : X ⊗ J.obj n ⟶ J.obj m)
    (r : m ⟶ l) (s : A ⊗ J.obj n ⟶ J.obj l)
    (h₀ : (ι ▷ J.obj n) ≫ p₀ ≫ J.map r = s)
    (h₁ : (ι ▷ J.obj n) ≫ p₁ ≫ J.map r = s) :
    (ι ▷ J.obj (degree n)) ≫ extendPair p₀ p₁ ≫ J.map r = (A ◁ fold n) ≫ s := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let t := (decode n (coord (degree n) q z.2 v)).2
  let w := (z.1, (fold n).app q z.2)
  change coord l q ((J.map r).app q ((extendPair p₀ p₁).app q (ι.app q z.1, z.2))) v =
    coord l q (s.app q w) v
  rw [coord_map, coord_extendPair]
  have h : (ι ▷ J.obj n) ≫ pick p₀ p₁ t ≫ J.map r = s := by
    by_cases ht : t = 0
    · simpa only [pick, if_pos ht] using h₀
    · simpa only [pick, if_neg ht] using h₁
  have he := congrArg (fun u ↦ coord l q u v) (congrFun (NatTrans.congr_app h q) w)
  change coord l q ((J.map r).app q
    ((pick p₀ p₁ t).app q (ι.app q w.1, w.2))) v = _ at he
  rw [coord_map] at he
  exact he

/-- Two coefficient placements with the same restricted parameter retain
that parameter on the whole doubled graph. -/
theorem extend_over {A : SSet.{0}} {l : SimplexCategory} (ι : A ⟶ X)
    (r : m ⟶ l) (s : A ⊗ J.obj n ⟶ J.obj l)
    (h₀ : (ι ▷ J.obj n) ≫ p ≫ J.map (e₀ ≫ r) = s)
    (h₁ : (ι ▷ J.obj n) ≫ p ≫ J.map (e₁ ≫ r) = s) :
    (ι ▷ J.obj (degree n)) ≫ extend p e₀ e₁ ≫ J.map r = (A ◁ fold n) ≫ s :=
  extendPair_over ι (p ≫ J.map e₀) (p ≫ J.map e₁) r s
    (by simpa only [J.map_comp, Category.assoc] using h₀)
    (by simpa only [J.map_comp, Category.assoc] using h₁)

end

end DaggerModels.PartII.JTDoubledGraphTime
