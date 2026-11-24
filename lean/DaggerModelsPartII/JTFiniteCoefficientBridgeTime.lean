import DaggerModelsPartII.JTDisjointSubcomplexCover
import DaggerModelsPartII.JTChangingCoefficientBridgeTime

/-!
# Joining finitely many exact normalization simplices
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeTime

open SSet.Subcomplex
open JTHigherInterleavedParameter (common)

noncomputable section

abbrev time (m : ℕ) (n : SimplexCategory) := common ⦋m⦌ n

abbrev timeVertexEquiv (m : ℕ) (n : SimplexCategory) :
    Fin (m + 1) × Fin (n.len + 1) ≃ Fin ((time m n).len + 1) :=
  JTHigherInterleavedParameter.vertexEquiv ⦋m⦌ n

abbrev timeSide {m : ℕ} (n : SimplexCategory) (e : Fin (m + 1)) : n ⟶ time m n :=
  JTHigherInterleavedParameter.vertical ⦋m⦌ n e

theorem timeSide_injective {m : ℕ} (n : SimplexCategory) (e : Fin (m + 1)) :
    Function.Injective (timeSide n e).toOrderHom := by
  intro a b h
  exact congrArg Prod.snd ((timeVertexEquiv m n).injective h)

instance timeSide_mono {m : ℕ} (n : SimplexCategory) (e : Fin (m + 1)) : Mono (timeSide n e) :=
  SimplexCategory.mono_iff_injective.mpr (timeSide_injective n e)

theorem le_copy (m : ℕ) (n : SimplexCategory) {x y : Fin (m + 1) × Fin (n.len + 1)}
    (h : timeVertexEquiv m n x ≤ timeVertexEquiv m n y) : x.1 ≤ y.1 := by
  have H := (JTHigherInterleavedParameter.ret ⦋m⦌ n).toOrderHom.monotone h
  change (JTHigherInterleavedParameter.ret ⦋m⦌ n).toOrderHom
      (JTHigherInterleavedParameter.vertexEquiv ⦋m⦌ n x) ≤
    (JTHigherInterleavedParameter.ret ⦋m⦌ n).toOrderHom
      (JTHigherInterleavedParameter.vertexEquiv ⦋m⦌ n y) at H
  rwa [JTHigherInterleavedParameter.ret_vertexEquiv,
    JTHigherInterleavedParameter.ret_vertexEquiv] at H

theorem le_time_of_copy_eq (m : ℕ) (n : SimplexCategory) {x y : Fin (m + 1) × Fin (n.len + 1)}
    (he : x.1 = y.1) (h : timeVertexEquiv m n x ≤ timeVertexEquiv m n y) : x.2 ≤ y.2 := by
  change x.2.val + (n.len + 1) * x.1.val ≤ y.2.val + (n.len + 1) * y.1.val at h
  rw [he] at h
  exact Nat.le_of_add_le_add_right h

theorem cross_copy_le {m : ℕ} (n : SimplexCategory) {e e' : Fin (m + 1)} (h : e < e')
    (a a' : Fin (n.len + 1)) : timeVertexEquiv m n (e, a) ≤ timeVertexEquiv m n (e', a') := by
  change a.val + (n.len + 1) * e.val ≤ a'.val + (n.len + 1) * e'.val
  calc
    _ ≤ (n.len + 1) * (e.val + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ (n.len + 1) * e'.val := Nat.mul_le_mul_left _ h
    _ ≤ _ := Nat.le_add_left _ _

/-- The inclusion of a subcollection of entire time faces. -/
def mapCopies {m m' : ℕ} (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (n : SimplexCategory) : time m n ⟶ time m' n :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let x := (timeVertexEquiv m n).symm v
    timeVertexEquiv m' n (j.toOrderHom x.1, x.2), by
    intro v w hvw
    obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
    obtain ⟨y, rfl⟩ := (timeVertexEquiv m n).surjective w
    simp only [Equiv.symm_apply_apply]
    rcases lt_or_eq_of_le (le_copy m n hvw) with h | h
    · exact cross_copy_le n (j.toOrderHom.monotone.strictMono_of_injective hj h) x.2 y.2
    · exact (JTHigherInterleavedParameter.prismOrder ⦋m'⦌ n).monotone
        ⟨j.toOrderHom.monotone h.le, le_time_of_copy_eq m n h hvw⟩⟩

theorem mapCopies_vertex {m m' : ℕ} (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
    (n : SimplexCategory) (x : Fin (m + 1) × Fin (n.len + 1)) :
    (mapCopies j hj n).toOrderHom (timeVertexEquiv m n x) =
      timeVertexEquiv m' n (j.toOrderHom x.1, x.2) := by
  simp [mapCopies]

theorem timeSide_mapCopies {m m' : ℕ} (j : ⦋m⦌ ⟶ ⦋m'⦌)
    (hj : Function.Injective j.toOrderHom) (n : SimplexCategory) (e : Fin (m + 1)) :
    timeSide n e ≫ mapCopies j hj n = timeSide n (j.toOrderHom e) := by
  ext a : 3
  exact mapCopies_vertex j hj n (e, a)

theorem mapCopies_comp {m m' m'' : ℕ} (j : ⦋m⦌ ⟶ ⦋m'⦌) (j' : ⦋m'⦌ ⟶ ⦋m''⦌)
    (hj : Function.Injective j.toOrderHom) (hj' : Function.Injective j'.toOrderHom)
    (n : SimplexCategory) :
    mapCopies (j ≫ j') (hj'.comp hj) n = mapCopies j hj n ≫ mapCopies j' hj' n := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
  change (mapCopies (j ≫ j') (hj'.comp hj) n).toOrderHom (timeVertexEquiv m n x) =
    (mapCopies j' hj' n).toOrderHom ((mapCopies j hj n).toOrderHom (timeVertexEquiv m n x))
  rw [mapCopies_vertex, mapCopies_vertex, mapCopies_vertex]
  rfl

theorem timeSide_disjoint (m : ℕ) (n : SimplexCategory) :
    Pairwise fun e e' : Fin (m + 1) ↦
      range (SSet.stdSimplex.{u}.map (timeSide n e)) ⊓
        range (SSet.stdSimplex.map (timeSide n e')) = ⊥ := by
  intro e e' he
  ext q z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have h := congrArg (fun w ↦ (SSet.stdSimplex.objEquiv w).toOrderHom 0) (hx.trans hy.symm)
    change timeVertexEquiv m n (e, (SSet.stdSimplex.objEquiv x).toOrderHom 0) =
      timeVertexEquiv m n (e', (SSet.stdSimplex.objEquiv y).toOrderHom 0) at h
    exact he (congrArg Prod.fst ((timeVertexEquiv m n).injective h))
  · exact False.elim

/-- All given simplices extend simultaneously to one simplex of the same space. -/
theorem exists_join {X : SSet.{u}} (hX : X.KanComplex)
    (h : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from X))
    (m : ℕ) (n : SimplexCategory) (x : Fin (m + 1) → X.obj (op n)) :
    ∃ z : X.obj (op (time m n)), ∀ e, X.map (timeSide n e).op z = x e := by
  let i (e : Fin (m + 1)) := SSet.stdSimplex.{u}.map (timeSide n e)
  let B := ⨆ e, range (i e)
  haveI (e : Fin (m + 1)) : Mono (i e) := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _
  obtain ⟨g, hg⟩ := JTDisjointSubcomplexCover.exists_glue_ranges i (timeSide_disjoint m n)
    (fun e ↦ SSet.yonedaEquiv.symm (x e))
  let p := SSet.stdSimplex.isTerminalObj₀.from X
  haveI : IsFibrant X := hX
  haveI : Fibration p :=
    (isFibrant_iff_of_isTerminal p SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  haveI : WeakEquivalence p := h
  haveI : Cofibration B.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let S : CommSq g B.ι p
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj (time m n))) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  refine ⟨SSet.yonedaEquiv S.lift, fun e ↦ ?_⟩
  have H : i e ≫ S.lift = SSet.yonedaEquiv.symm (x e) := by
    calc
      _ = (JTDisjointSubcomplexCover.rangeLeg i e ≫ B.ι) ≫ S.lift :=
        congrArg (fun f ↦ f ≫ S.lift) (JTDisjointSubcomplexCover.rangeLeg_ι i e).symm
      _ = _ := by rw [Category.assoc, S.fac_left, hg]
  rw [← SSet.yonedaEquiv_map_comp, H, Equiv.apply_symm_apply]

theorem fixedSquare_exists_join
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [WeakEquivalence i] [Fibration p]
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) (m : ℕ) (n : SimplexCategory)
    (x : Fin (m + 1) → (SSet.ihomToPullbackFiber sq).obj (op n)) :
    ∃ z : (SSet.ihomToPullbackFiber sq).obj (op (time m n)), ∀ e,
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map (timeSide n e).op z = x e :=
  exists_join (ParameterVertexLiftSpace.fixedSquare_liftSpace_kan sq)
    (ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak sq) m n x

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeTime
