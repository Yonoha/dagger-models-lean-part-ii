import DaggerModelsPartII.JTDoubledGraphTime
import DaggerModelsPartII.JTFiniteCoefficientBridgeTime
import DaggerModelsPartII.JTHigherInterleavedOperators

/-! Whole graph families in the original finite joining time, with exact face restrictions. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTHigherGraphTimeFamily

open JTDoubledGraphTime (vertexMap coord_vertexMap)
open JTCodiscreteParameterPairing (coord coord_map)
open JTGraphParameterInterpolation (interpolate coord_interpolate)
open JTHigherInterleavedParameter (common vertexEquiv vertical ret)
open JTFiniteCoefficientBridgeTime (mapCopies mapCopies_vertex)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {X : SSet.{0}} {k n m : SimplexCategory}

/-- Forget the phase while retaining the entire original time simplex. -/
def fold (k n : SimplexCategory) : J.obj (common k n) ⟶ J.obj n :=
  vertexMap (fun u ↦ ((vertexEquiv k n).symm u).2)

private theorem fold_vertical (k n : SimplexCategory) (i : Fin (k.len + 1)) :
    J.map (vertical k n i) ≫ fold k n = 𝟙 (J.obj n) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n q ((fold k n).app q ((J.map (vertical k n i)).app q z)) v = coord n q z v
  rw [fold, coord_vertexMap, coord_map]
  change ((vertexEquiv k n).symm (vertexEquiv k n (i, coord n q z v))).2 = _
  rw [Equiv.symm_apply_apply]

/-- Folding the common parameter commutes with every original time operator. -/
theorem fold_mapTime {n n' : SimplexCategory} (k : SimplexCategory) (a : n ⟶ n') :
    J.map (JTHigherInterleavedParameter.mapTime k a) ≫ fold k n' =
      fold k n ≫ J.map a := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n' q ((fold k n').app q
      ((J.map (JTHigherInterleavedParameter.mapTime k a)).app q z)) v =
    coord n' q ((J.map a).app q ((fold k n).app q z)) v
  rw [fold, coord_vertexMap, coord_map, coord_map, fold, coord_vertexMap]
  obtain ⟨x, hx⟩ := (vertexEquiv k n).surjective (coord (common k n) q z v)
  rw [← hx, JTHigherInterleavedParameter.mapTime_vertexEquiv,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Interpolate one whole graph at each phase of the lexicographic common ordinal. -/
def extendFamily (p : Fin (k.len + 1) → (X ⊗ J.obj n ⟶ J.obj m)) :
    X ⊗ J.obj (common k n) ⟶ J.obj m :=
  (X ◁ lift (fold k n) (J.map (ret k n))) ≫
    (α_ X (J.obj n) (J.obj k)).inv ≫ interpolate p

private theorem coord_extendFamily
    (p : Fin (k.len + 1) → (X ⊗ J.obj n ⟶ J.obj m))
    (q : SimplexCategoryᵒᵖ) (z : (X ⊗ J.obj (common k n)).obj q)
    (v : Fin (q.unop.len + 1)) :
    coord m q ((extendFamily p).app q z) v =
      coord m q ((p ((vertexEquiv k n).symm (coord (common k n) q z.2 v)).1).app q
        (z.1, (fold k n).app q z.2)) v := by
  change coord m q ((interpolate p).app q
    ((z.1, (fold k n).app q z.2), (J.map (ret k n)).app q z.2)) v = _
  rw [coord_interpolate, coord_map]
  change coord m q
    ((p ((ret k n).toOrderHom (coord (common k n) q z.2 v))).app q
      (z.1, (fold k n).app q z.2)) v = _
  rfl

/-- Repeating the same full graph simply precomposes it with folded time. -/
theorem extendFamily_const (p : X ⊗ J.obj n ⟶ J.obj m) :
    extendFamily (k := k) (fun _ ↦ p) = (X ◁ fold k n) ≫ p := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  exact coord_extendFamily (fun _ ↦ p) q z v

/-- Every vertical copy restricts to its specified full graph parameter. -/
theorem extendFamily_vertical
    (p : Fin (k.len + 1) → (X ⊗ J.obj n ⟶ J.obj m))
    (i : Fin (k.len + 1)) :
    (X ◁ J.map (vertical k n i)) ≫ extendFamily p = p i := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord m q ((extendFamily p).app q (z.1, (J.map (vertical k n i)).app q z.2)) v =
    coord m q ((p i).app q z) v
  rw [coord_extendFamily, coord_map]
  change coord m q
      ((p ((vertexEquiv k n).symm (vertexEquiv k n (i, coord n q z.2 v))).1).app q
        (z.1, (fold k n).app q ((J.map (vertical k n i)).app q z.2))) v = _
  rw [Equiv.symm_apply_apply]
  have h : (fold k n).app q ((J.map (vertical k n i)).app q z.2) = z.2 :=
    congrFun (NatTrans.congr_app (fold_vertical k n i) q) z.2
  rw [h]
  rfl

/-- A common graph restriction on all phases remains exact on the whole prism. -/
theorem extendFamily_over {A : SSet.{0}} {l : SimplexCategory} (ι : A ⟶ X)
    (p : Fin (k.len + 1) → (X ⊗ J.obj n ⟶ J.obj m))
    (r : m ⟶ l) (s : A ⊗ J.obj n ⟶ J.obj l)
    (h : ∀ i, (ι ▷ J.obj n) ≫ p i ≫ J.map r = s) :
    (ι ▷ J.obj (common k n)) ≫ extendFamily p ≫ J.map r =
      (A ◁ fold k n) ≫ s := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let i := ((vertexEquiv k n).symm (coord (common k n) q z.2 v)).1
  let w := (z.1, (fold k n).app q z.2)
  change coord l q ((J.map r).app q ((extendFamily p).app q (ι.app q z.1, z.2))) v =
    coord l q (s.app q w) v
  rw [coord_map, coord_extendFamily]
  have he := congrArg (fun u ↦ coord l q u v) (congrFun (NatTrans.congr_app (h i) q) w)
  change coord l q ((J.map r).app q ((p i).app q (ι.app q w.1, w.2))) v = _ at he
  rw [coord_map] at he
  exact he


/-- Simultaneous native, original time, and coefficient changes commute
with the entire finite interpolation. -/
theorem extendFamily_square {Y : SSet.{0}} {n' m' : SimplexCategory}
    (g : X ⟶ Y) (a : n ⟶ n') (c : m ⟶ m')
    (p : Fin (k.len + 1) → (X ⊗ J.obj n ⟶ J.obj m))
    (p' : Fin (k.len + 1) → (Y ⊗ J.obj n' ⟶ J.obj m'))
    (h : ∀ i, (g ⊗ₘ J.map a) ≫ p' i = p i ≫ J.map c) :
    (g ⊗ₘ J.map (JTHigherInterleavedParameter.mapTime k a)) ≫ extendFamily p' =
      extendFamily p ≫ J.map c := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let i := ((vertexEquiv k n).symm (coord (common k n) q z.2 v)).1
  let w := (z.1, (fold k n).app q z.2)
  have ht : (fold k n').app q
      ((J.map (JTHigherInterleavedParameter.mapTime k a)).app q z.2) =
      (J.map a).app q ((fold k n).app q z.2) :=
    congrFun (NatTrans.congr_app (fold_mapTime k a) q) z.2
  have hp := congrArg (fun u ↦ coord m' q u v) (congrFun (NatTrans.congr_app (h i) q) w)
  change coord m' q ((p' i).app q (g.app q w.1, (J.map a).app q w.2)) v =
    coord m' q ((J.map c).app q ((p i).app q w)) v at hp
  rw [coord_map] at hp
  change coord m' q ((extendFamily p').app q
      (g.app q z.1, (J.map (JTHigherInterleavedParameter.mapTime k a)).app q z.2)) v =
    coord m' q ((J.map c).app q ((extendFamily p).app q z)) v
  rw [coord_extendFamily, coord_map, ht, coord_map c, coord_extendFamily]
  have hi : ((vertexEquiv k n').symm
      ((JTHigherInterleavedParameter.mapTime k a).toOrderHom
        (coord (common k n) q z.2 v))).1 = i := by
    dsimp [i]
    obtain ⟨x, hx⟩ := (vertexEquiv k n).surjective (coord (common k n) q z.2 v)
    rw [← hx, JTHigherInterleavedParameter.mapTime_vertexEquiv,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [hi]
  exact hp

private theorem mapCopies_coordinates {i j : ℕ} (a : ⦋i⦌ ⟶ ⦋j⦌)
    (h : Function.Injective a.toOrderHom) (n : SimplexCategory)
    (v : Fin ((common ⦋i⦌ n).len + 1)) :
    (vertexEquiv ⦋j⦌ n).symm ((mapCopies a h n).toOrderHom v) =
      (a.toOrderHom ((vertexEquiv ⦋i⦌ n).symm v).1, ((vertexEquiv ⦋i⦌ n).symm v).2) := by
  obtain ⟨x, rfl⟩ := (vertexEquiv ⦋i⦌ n).surjective v
  have hx : (mapCopies a h n).toOrderHom (vertexEquiv ⦋i⦌ n x) =
      vertexEquiv ⦋j⦌ n (a.toOrderHom x.1, x.2) := mapCopies_vertex a h n x
  rw [hx, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Folding the common parameter commutes with inclusions of complete time faces. -/
theorem fold_mapCopies {i j : ℕ} (a : ⦋i⦌ ⟶ ⦋j⦌) (h : Function.Injective a.toOrderHom)
    (n : SimplexCategory) : J.map (mapCopies a h n) ≫ fold ⦋j⦌ n = fold ⦋i⦌ n := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord n q ((fold ⦋j⦌ n).app q ((J.map (mapCopies a h n)).app q z)) v =
    coord n q ((fold ⦋i⦌ n).app q z) v
  rw [fold, coord_vertexMap, coord_map, fold, coord_vertexMap]
  rw [mapCopies_coordinates]

/-- Restricting the full interpolation to the selected copies gives the
interpolation of exactly the selected family. -/
theorem extendFamily_mapCopies {i j : ℕ} (a : ⦋i⦌ ⟶ ⦋j⦌) (h : Function.Injective a.toOrderHom)
    (p : Fin (j + 1) → (X ⊗ J.obj n ⟶ J.obj m)) :
    (X ◁ J.map (mapCopies a h n)) ≫ extendFamily (k := ⦋j⦌) p =
      extendFamily (k := ⦋i⦌) (fun e ↦ p (a.toOrderHom e)) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord m q ((extendFamily (k := ⦋j⦌) p).app q
      (z.1, (J.map (mapCopies a h n)).app q z.2)) v =
    coord m q ((extendFamily (k := ⦋i⦌) (fun e ↦ p (a.toOrderHom e))).app q z) v
  have ht : (fold ⦋j⦌ n).app q ((J.map (mapCopies a h n)).app q z.2) =
      (fold ⦋i⦌ n).app q z.2 := congrFun (NatTrans.congr_app (fold_mapCopies a h n) q) z.2
  rw [coord_extendFamily, coord_map, ht, coord_extendFamily]
  rw [mapCopies_coordinates]

/-- Restricting to selected copies and changing the original time commute. -/
theorem mapCopies_mapTime {i j : ℕ} (a : ⦋i⦌ ⟶ ⦋j⦌) (h : Function.Injective a.toOrderHom)
    {n n' : SimplexCategory} (b : n ⟶ n') :
    mapCopies a h n ≫ JTHigherInterleavedParameter.mapTime ⦋j⦌ b =
      JTHigherInterleavedParameter.mapTime ⦋i⦌ b ≫ mapCopies a h n' := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (vertexEquiv ⦋i⦌ n).surjective v
  change (JTHigherInterleavedParameter.mapTime ⦋j⦌ b).toOrderHom
      ((mapCopies a h n).toOrderHom (vertexEquiv ⦋i⦌ n x)) =
    (mapCopies a h n').toOrderHom
      ((JTHigherInterleavedParameter.mapTime ⦋i⦌ b).toOrderHom (vertexEquiv ⦋i⦌ n x))
  have hu : (mapCopies a h n).toOrderHom (vertexEquiv ⦋i⦌ n x) =
      vertexEquiv ⦋j⦌ n (a.toOrderHom x.1, x.2) := mapCopies_vertex a h n x
  rw [hu, JTHigherInterleavedParameter.mapTime_vertexEquiv,
    JTHigherInterleavedParameter.mapTime_vertexEquiv]
  exact (mapCopies_vertex a h n' (x.1, b.toOrderHom x.2)).symm

/-- All per-copy squares give one exact square on the full family, even if
only a selected subfamily of the target is used. -/
theorem extendFamily_mixed {Y : SSet.{0}} {n' m' : SimplexCategory} {i j : ℕ}
    (a : ⦋i⦌ ⟶ ⦋j⦌) (ha : Function.Injective a.toOrderHom) (g : X ⟶ Y)
    (b : n ⟶ n') (c : m ⟶ m') (p : Fin (i + 1) → (X ⊗ J.obj n ⟶ J.obj m))
    (p' : Fin (j + 1) → (Y ⊗ J.obj n' ⟶ J.obj m'))
    (h : ∀ e, (g ⊗ₘ J.map b) ≫ p' (a.toOrderHom e) = p e ≫ J.map c) :
    (g ⊗ₘ J.map (JTHigherInterleavedParameter.mapTime ⦋i⦌ b ≫ mapCopies a ha n')) ≫
        extendFamily (k := ⦋j⦌) p' = extendFamily (k := ⦋i⦌) p ≫ J.map c := by
  rw [J.map_comp, ← Category.comp_id g, ← tensorHom_comp_tensorHom, Category.assoc,
    id_tensorHom, extendFamily_mapCopies]
  exact extendFamily_square (k := ⦋i⦌) g b c p (fun e ↦ p' (a.toOrderHom e)) h

end
end DaggerModels.PartII.JTHigherGraphTimeFamily
