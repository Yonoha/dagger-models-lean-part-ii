import DaggerModelsPartII.JTChangingCoefficientBridgeOverlap
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-!
# Relative extension over a change of coefficient
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTChangingCoefficientBridgeLift

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism JTChangingCoefficientBridgeOverlap
open JTFixedLiftSpaceTimeEquiv
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

/-- Extend two whole side maps and the joined ordinary prism, retaining
their exact side restrictions, changed base and stationary equations. -/
theorem exists_extension {A X Y : SSet.{u}} {i : A ⟶ simplex k} {p : X ⟶ Y}
    [Mono i] [WeakEquivalence i] [Fibration p] {t : A ⟶ X}
    (g : simplex b' ⟶ Y) (sq : CommSq t i p (SSet.stdSimplex.map (c ≫ h) ≫ g))
    (E : (e : Fin 2) → simplex (JTHigherInterleavedParameter.common k n) ⟶ X)
    (hbase : ∀ e, E e ≫ p =
      SSet.stdSimplex.map (side c h n e) ≫ SSet.stdSimplex.map (base c h n) ≫ g)
    (hstat : ∀ e, (i ▷ simplex n) ≫ sidePrism c h n e ≫ E e =
      fst A (simplex n) ≫ t) :
    ∃ L : simplex (bridge k n) ⟶ X,
      (∀ e, SSet.stdSimplex.map (side c h n e) ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c h n) ≫ g ∧
      (i ▷ simplex (time n)) ≫ prism c h n ≫ L = fst A (simplex (time n)) ≫ t := by
  let f := prism.{u} c h n
  let F := sideUnion.{u} c h n
  let U := fullUnion.{u} c h n
  let q := SSet.stdSimplex.map (base c h n) ≫ g
  let j (e : Fin 2) := SSet.stdSimplex.{u}.map (side c h n e)
  let m (e : Fin 2) : sideRange.{u} c h n e ≤ F := by
    fin_cases e
    · exact le_sup_left
    · exact le_sup_right
  let d (e : Fin 2) : simplex (JTHigherInterleavedParameter.common k n) ⟶ F :=
    toRange (j e) ≫ SSet.Subcomplex.homOfLE (m e)
  have hd (e : Fin 2) : d e ≫ F.ι = j e := by
    simp [d]
  haveI (e : Fin 2) : Mono (j e) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _
  have sideBase (e : Fin 2) : sidePrism.{u} c h n e ≫ j e ≫ q =
      fst (simplex.{u} k) (simplex n) ≫ SSet.stdSimplex.map (c ≫ h) ≫ g := by
    rw [← Category.assoc, ← prism_side, Category.assoc]
    change (simplex k ◁ SSet.stdSimplex.map (timeSide n e)) ≫
      f ≫ SSet.stdSimplex.map (base c h n) ≫ g = _
    rw [← Category.assoc f, prism_base, Category.assoc, whiskerLeft_fst_assoc]
  let v (e : Fin 2) : TimeLift sq n :=
    ⟨sidePrism c h n e ≫ E e, hstat e,
      by rw [Category.assoc, hbase]; exact sideBase e⟩
  obtain ⟨x, hx₀, hx₁⟩ := fixedSquare_exists_join sq n
    ((timeEquiv sq n).symm (v 0)) ((timeEquiv sq n).symm (v 1))
  have hx (e : Fin 2) :
      (SSet.ihomToPullbackFiber sq : SSet.{u}).map (timeSide n e).op x =
        (timeEquiv sq n).symm (v e) := by
    fin_cases e
    · exact hx₀
    · exact hx₁
  let V := timeMap sq (time n) x
  have hV (e : Fin 2) : (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ V =
      sidePrism c h n e ≫ E e := by
    rw [← timeMap_map sq (timeSide n e) x, hx, ← timeEquiv_apply_val,
      Equiv.apply_symm_apply]
  obtain ⟨G, hG₀, hG₁⟩ := glue_disjoint (j 0) (j 1) (side_disjoint c h n) (E 0) (E 1)
  have hG (e : Fin 2) : d e ≫ G = E e := by
    fin_cases e
    · exact hG₀
    · exact hG₁
  let S : BicartSq (sideRange.{u} c h n 0 ⊓ sideRange c h n 1)
      (sideRange c h n 0) (sideRange c h n 1) F := ⟨rfl, rfl⟩
  have Hbase : G ≫ p = F.ι ≫ q := by
    have Hr (e : Fin 2) :
        SSet.Subcomplex.homOfLE (m e) ≫ G ≫ p =
          SSet.Subcomplex.homOfLE (m e) ≫ F.ι ≫ q := by
      apply (cancel_epi (toRange (j e))).1
      simp only [← Category.assoc]
      change (d e ≫ G) ≫ p = (d e ≫ F.ι) ≫ q
      rw [hG, hd]
      exact hbase e
    exact S.isPushout.hom_ext (Hr 0) (Hr 1)
  let S' : BicartSq ((sideRange.{u} c h n 0 ⊓ sideRange c h n 1).preimage f)
      ((sideRange c h n 0).preimage f) ((sideRange c h n 1).preimage f)
      (F.preimage f) := ⟨(preimage_max _ _ _).symm, (preimage_min _ _ _).symm⟩
  have Hoverlap : (F.preimage f).ι ≫ V = F.fromPreimage f ≫ G := by
    have Hr (e : Fin 2) :
        SSet.Subcomplex.homOfLE (show (sideRange c h n e).preimage f ≤ F.preimage f
          from fun a ↦ Set.preimage_mono (m e a)) ≫ (F.preimage f).ι ≫ V =
        SSet.Subcomplex.homOfLE (show (sideRange c h n e).preimage f ≤ F.preimage f
          from fun a ↦ Set.preimage_mono (m e a)) ≫ F.fromPreimage f ≫ G := by
      apply (cancel_epi (sidePreimageIso c h n e).hom).1
      rw [homOfLE_ι_assoc, sidePreimageIso_ι_assoc, hV]
      rw [← Category.assoc (SSet.Subcomplex.homOfLE _) (F.fromPreimage f),
        JTFiniteSubcomplexPreimageGluing.fromPreimage_homOfLE f (m e)]
      simp only [← Category.assoc]
      dsimp only [f]
      rw [sidePreimageIso_compare]
      simp only [Category.assoc]
      change sidePrism c h n e ≫ E e = sidePrism c h n e ≫ (d e ≫ G)
      rw [hG]
    exact S'.isPushout.hom_ext (Hr 0) (Hr 1)
  let P := JTSubcomplexRangeUnion.isPushout f F
  let W := P.desc V G Hoverlap
  let a := JTSubcomplexRangeUnion.inl f F
  let z := JTSubcomplexRangeUnion.inr f F
  have ha : a ≫ W = V := P.inl_desc _ _ _
  have hz : z ≫ W = G := P.inr_desc _ _ _
  have haU : a ≫ U.ι = f := JTSubcomplexRangeUnion.inl_ι f F
  have hzU : z ≫ U.ι = F.ι := JTSubcomplexRangeUnion.inr_ι f F
  have H : W ≫ p = U.ι ≫ q := by
    apply P.hom_ext
    · rw [← Category.assoc, ha, ← Category.assoc, haU,
        (timeMap_conditions sq (time n) x).2]
      dsimp only [f, q]
      rw [← Category.assoc (prism c h n), prism_base]
      simp only [Category.assoc]
    · rw [← Category.assoc, hz, ← Category.assoc, hzU]
      exact Hbase
  haveI : WeakEquivalence U.ι := fullUnion_weak c h n
  haveI : Cofibration U.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let lifting : CommSq W U.ι p q := ⟨H⟩
  have hf : f ≫ lifting.lift = V := by
    calc
      _ = (a ≫ U.ι) ≫ lifting.lift := congrArg (fun j ↦ j ≫ lifting.lift) haU.symm
      _ = _ := by rw [Category.assoc, lifting.fac_left, ha]
  have hF : F.ι ≫ lifting.lift = G := by
    calc
      _ = (z ≫ U.ι) ≫ lifting.lift := congrArg (fun j ↦ j ≫ lifting.lift) hzU.symm
      _ = _ := by rw [Category.assoc, lifting.fac_left, hz]
  refine ⟨lifting.lift, ?_, lifting.fac_right, ?_⟩
  · intro e
    change j e ≫ lifting.lift = E e
    rw [← hd, Category.assoc, hF, hG]
  · change (i ▷ simplex (time n)) ≫ f ≫ lifting.lift = _
    rw [hf]
    exact (timeMap_conditions sq (time n) x).1

private abbrev vertex (k : SimplexCategory) (a : Fin (k.len + 1)) :
    simplex.{u} ⦋0⦌ ⟶ simplex k :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k a)

theorem vertex_tensor (k m : SimplexCategory) (a : Fin (k.len + 1)) :
    vertex.{u} k a ▷ simplex m =
      snd (simplex ⦋0⦌) (simplex m) ≫ JTHigherInterleavedParameter.verticalSection k m a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, JTHigherInterleavedParameter.verticalSection, lift_fst,
      whiskerRight_fst]
    have H : fst (simplex.{u} ⦋0⦌) (simplex m) =
        snd (simplex ⦋0⦌) (simplex m) ≫ SSet.stdSimplex.map
          (SimplexCategory.const m ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [H, Category.assoc, vertex, ← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
    rfl
  · simp only [JTHigherInterleavedParameter.verticalSection, Category.assoc, lift_snd,
      whiskerRight_snd, Category.comp_id]

abbrev sideVertical (a : Fin (k.len + 1)) (e : Fin 2) :
    n ⟶ JTHigherInterleavedParameter.common k n :=
  if e = 0 then JTCommonCoefficientParameter.vertical c n a
  else JTCommonCoefficientParameter.vertical (c ≫ h) n a

/-- The full vertical simplex at a selected coefficient vertex remains
stationary, including every joining time between the two old copies. -/
theorem exists_vertex_extension {X Y : SSet.{u}} {p : X ⟶ Y} [Fibration p]
    (g : simplex b' ⟶ Y) (a : Fin (k.len + 1)) (t : simplex ⦋0⦌ ⟶ X)
    (sq : CommSq t (vertex k a) p
      (SSet.stdSimplex.map (c ≫ h) ≫ g))
    (E : (e : Fin 2) → simplex (JTHigherInterleavedParameter.common k n) ⟶ X)
    (hbase : ∀ e, E e ≫ p =
      SSet.stdSimplex.map (side c h n e) ≫ SSet.stdSimplex.map (base c h n) ≫ g)
    (hvert : ∀ e, SSet.stdSimplex.map (sideVertical c h n a e) ≫ E e =
      SSet.stdSimplex.isTerminalObj₀.from (simplex n) ≫ t) :
    ∃ L : simplex (bridge k n) ⟶ X,
      (∀ e, SSet.stdSimplex.map (side c h n e) ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c h n) ≫ g ∧
      SSet.stdSimplex.map (vertical c h n a) ≫ L =
        SSet.stdSimplex.isTerminalObj₀.from (simplex (time n)) ≫ t := by
  let i := vertex.{u} k a
  haveI : Mono i := SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence i := JTInterleavedParameter.standardMap_weak _
  have hs (e : Fin 2) : JTHigherInterleavedParameter.verticalSection.{u} k n a ≫
      sidePrism c h n e = SSet.stdSimplex.map (sideVertical c h n a e) := by
    by_cases he : e = 0 <;>
      simp only [sidePrism, sideVertical, he, if_true, if_false,
        JTCommonCoefficientParameter.verticalSection_prism]
  have hstat (e : Fin 2) : (i ▷ simplex n) ≫ sidePrism c h n e ≫ E e =
      fst (simplex ⦋0⦌) (simplex n) ≫ t := by
    change (vertex k a ▷ simplex n) ≫ _ = _
    rw [vertex_tensor, Category.assoc, ← Category.assoc
      (JTHigherInterleavedParameter.verticalSection k n a), hs, hvert,
      ← Category.assoc]
    congr 1
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  obtain ⟨L, hL, hP, hV⟩ := exists_extension c h n g sq E hbase hstat
  refine ⟨L, hL, hP, ?_⟩
  have hc : JTHigherInterleavedParameter.verticalSection.{u} k (time n) a =
      lift (SSet.stdSimplex.isTerminalObj₀.from (simplex (time n))) (𝟙 (simplex (time n))) ≫
        (i ▷ simplex (time n)) := by
    change _ = _ ≫ (vertex k a ▷ _)
    rw [vertex_tensor, lift_snd_assoc, Category.id_comp]
  rw [← verticalSection_prism, hc, Category.assoc, Category.assoc, hV, lift_fst_assoc]

end

end DaggerModels.PartII.JTChangingCoefficientBridgeLift
