import DaggerModelsPartII.JTInterleavedTimeFace
import DaggerModelsPartII.ParameterVertexLiftSpace
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The full time simplex joining two independent normalization families
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTChangingCoefficientBridgeTime

open SSet.Subcomplex

noncomputable section

/-- First copy, then time, with all vertices of both copies retained. -/
abbrev time (n : SimplexCategory) := JTHigherInterleavedParameter.common ⦋1⦌ n

abbrev timeVertexEquiv (n : SimplexCategory) :
    Fin 2 × Fin (n.len + 1) ≃ Fin ((time n).len + 1) :=
  JTHigherInterleavedParameter.vertexEquiv ⦋1⦌ n

/-- Each side is an entire face of the full time simplex. -/
abbrev timeSide (n : SimplexCategory) (e : Fin 2) : n ⟶ time n :=
  JTHigherInterleavedParameter.vertical ⦋1⦌ n e

theorem timeSide_injective (n : SimplexCategory) (e : Fin 2) :
    Function.Injective (timeSide n e).toOrderHom := by
  intro a b h
  exact congrArg Prod.snd ((timeVertexEquiv n).injective h)

instance timeSide_mono (n : SimplexCategory) (e : Fin 2) : Mono (timeSide n e) :=
  SimplexCategory.mono_iff_injective.mpr (timeSide_injective n e)

theorem le_copy (n : SimplexCategory) {x y : Fin 2 × Fin (n.len + 1)}
    (h : timeVertexEquiv n x ≤ timeVertexEquiv n y) : x.1 ≤ y.1 := by
  have h' := (JTHigherInterleavedParameter.ret ⦋1⦌ n).toOrderHom.monotone h
  change (JTHigherInterleavedParameter.ret ⦋1⦌ n).toOrderHom
      (JTHigherInterleavedParameter.vertexEquiv ⦋1⦌ n x) ≤
    (JTHigherInterleavedParameter.ret ⦋1⦌ n).toOrderHom
      (JTHigherInterleavedParameter.vertexEquiv ⦋1⦌ n y) at h'
  rw [JTHigherInterleavedParameter.ret_vertexEquiv,
    JTHigherInterleavedParameter.ret_vertexEquiv] at h'
  exact h'

theorem le_time_of_copy_eq (n : SimplexCategory) {x y : Fin 2 × Fin (n.len + 1)}
    (he : x.1 = y.1) (h : timeVertexEquiv n x ≤ timeVertexEquiv n y) : x.2 ≤ y.2 := by
  change x.2.val + (n.len + 1) * x.1.val ≤ y.2.val + (n.len + 1) * y.1.val at h
  rw [he] at h
  exact Nat.le_of_add_le_add_right h

/-- Two inclusions with disjoint simplicial images admit a joint
descent on their union, retaining both given whole maps. -/
theorem glue_disjoint {K X Y₀ Y₁ : SSet.{u}} (f₀ : Y₀ ⟶ K) (f₁ : Y₁ ⟶ K)
    [Mono f₀] [Mono f₁] (hd : range f₀ ⊓ range f₁ = ⊥)
    (g₀ : Y₀ ⟶ X) (g₁ : Y₁ ⟶ X) :
    ∃ g : (range f₀ ⊔ range f₁ : K.Subcomplex).toSSet ⟶ X,
      (toRange f₀ ≫ SSet.Subcomplex.homOfLE le_sup_left) ≫ g = g₀ ∧
      (toRange f₁ ≫ SSet.Subcomplex.homOfLE le_sup_right) ≫ g = g₁ := by
  let S : BicartSq (⊥ : K.Subcomplex) (range f₀) (range f₁) (range f₀ ⊔ range f₁) :=
    ⟨rfl, hd⟩
  let f := inv (toRange f₀) ≫ g₀
  let g := inv (toRange f₁) ≫ g₁
  let h := S.isPushout.desc f g (isInitialBot.hom_ext _ _)
  have hf : SSet.Subcomplex.homOfLE S.le₂₄ ≫ h = f := S.isPushout.inl_desc _ _ _
  have hg : SSet.Subcomplex.homOfLE S.le₃₄ ≫ h = g := S.isPushout.inr_desc _ _ _
  refine ⟨h, ?_, ?_⟩
  · change (toRange f₀ ≫ SSet.Subcomplex.homOfLE S.le₂₄) ≫ h = _
    rw [Category.assoc, hf, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · change (toRange f₁ ≫ SSet.Subcomplex.homOfLE S.le₃₄) ≫ h = _
    rw [Category.assoc, hg, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

theorem timeSide_disjoint (n : SimplexCategory) :
    range (SSet.stdSimplex.{u}.map (timeSide n 0)) ⊓
      range (SSet.stdSimplex.map (timeSide n 1)) = ⊥ := by
  ext q z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have h := congrArg (fun w ↦ (SSet.stdSimplex.objEquiv w).toOrderHom 0) (hx.trans hy.symm)
    change timeVertexEquiv n (0, (SSet.stdSimplex.objEquiv x).toOrderHom 0) =
      timeVertexEquiv n (1, (SSet.stdSimplex.objEquiv y).toOrderHom 0) at h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst ((timeVertexEquiv n).injective h))
  · intro h
    exact False.elim h

/-- Any two actual time simplices of a trivially fibrant lift space
extend across the join of their two time faces. -/
theorem exists_join {X : SSet.{u}} (hX : X.KanComplex)
    (h : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from X))
    (n : SimplexCategory) (x₀ x₁ : X.obj (op n)) :
    ∃ x : X.obj (op (time n)), X.map (timeSide n 0).op x = x₀ ∧
      X.map (timeSide n 1).op x = x₁ := by
  let i₀ := SSet.stdSimplex.{u}.map (timeSide n 0)
  let i₁ := SSet.stdSimplex.{u}.map (timeSide n 1)
  let B := range i₀ ⊔ range i₁
  let j₀ : SSet.stdSimplex.{u}.obj n ⟶ B := toRange i₀ ≫ SSet.Subcomplex.homOfLE le_sup_left
  let j₁ : SSet.stdSimplex.{u}.obj n ⟶ B := toRange i₁ ≫ SSet.Subcomplex.homOfLE le_sup_right
  have hj₀ : j₀ ≫ B.ι = i₀ := by simp [j₀]
  have hj₁ : j₁ ≫ B.ι = i₁ := by simp [j₁]
  haveI : Mono i₀ := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _
  haveI : Mono i₁ := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _
  obtain ⟨g, hg₀, hg₁⟩ := glue_disjoint i₀ i₁ (timeSide_disjoint n)
    (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm x₁)
  let p := SSet.stdSimplex.isTerminalObj₀.from X
  haveI : IsFibrant X := hX
  haveI : Fibration p :=
    (isFibrant_iff_of_isTerminal p SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  haveI : WeakEquivalence p := h
  haveI : Cofibration B.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let S : CommSq g B.ι p (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj (time n))) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have H₀ : i₀ ≫ S.lift = SSet.yonedaEquiv.symm x₀ := by
    calc
      _ = (j₀ ≫ B.ι) ≫ S.lift := congrArg (fun f ↦ f ≫ S.lift) hj₀.symm
      _ = _ := by rw [Category.assoc, S.fac_left]; exact hg₀
  have H₁ : i₁ ≫ S.lift = SSet.yonedaEquiv.symm x₁ := by
    calc
      _ = (j₁ ≫ B.ι) ≫ S.lift := congrArg (fun f ↦ f ≫ S.lift) hj₁.symm
      _ = _ := by rw [Category.assoc, S.fac_left]; exact hg₁
  refine ⟨SSet.yonedaEquiv S.lift, ?_, ?_⟩
  · rw [← SSet.yonedaEquiv_map_comp, H₀, Equiv.apply_symm_apply]
  · rw [← SSet.yonedaEquiv_map_comp, H₁, Equiv.apply_symm_apply]

/-- The interpolation uses the same actual fixed-square normalization
space and permits independent input simplices on the two sides. -/
theorem fixedSquare_exists_join
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [WeakEquivalence i] [Fibration p]
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) (n : SimplexCategory)
    (x₀ x₁ : (SSet.ihomToPullbackFiber sq).obj (op n)) :
    ∃ x : (SSet.ihomToPullbackFiber sq).obj (op (time n)),
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map (timeSide n 0).op x = x₀ ∧
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map (timeSide n 1).op x = x₁ :=
  exists_join (ParameterVertexLiftSpace.fixedSquare_liftSpace_kan sq)
    (ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak sq) n x₀ x₁

end

end DaggerModels.PartII.JTChangingCoefficientBridgeTime
