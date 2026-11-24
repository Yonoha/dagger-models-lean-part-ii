import DaggerModelsPartII.ChosenHomotopyFiberComparison
import DaggerModelsPartII.NativeOverModelCompatibility
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Independence of a chosen lift in a Kan homotopy-fiber comparison

Two extensions of the same map across a trivial cofibration into a Kan
fibration over a possibly different base induce the same map of specified
fibers after Kan localization. The original source projection is not assumed
to be a fibration. The proof uses a path object in the actual overcategory
and base change of trivial fibrations.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ChosenFiberLiftIndependence

noncomputable section

open DaggerNativeSSetFibrationSquareFibreWeak

section OverBase

variable (B K : SSet.{u})

private local instance : ModelCategory (Over B) := ModelCategory.over B

/-- Equal restrictions to a trivial cofibration yield a path between the
extensions in the actual model structure on the overcategory. -/
private theorem lift_path {A Z Y : Over B} (i : A ⟶ Z) (v w : Z ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [IsFibrant Y]
    (h : i ≫ v = i ≫ w) :
    ∃ (P : PathObject Y) (_ : P.IsVeryGood) (H : Z ⟶ P.P),
      H ≫ P.p₀ = v ∧ H ≫ P.p₁ = w := by
  let P := (PathObject.exists_very_good Y).choose
  letI : P.IsVeryGood := (PathObject.exists_very_good Y).choose_spec
  have sq : CommSq ((i ≫ v) ≫ P.ι) i P.p (prod.lift v w) := by
    constructor
    apply prod.hom_ext
    · simp only [Category.assoc, P.p_fst, P.ι_p₀, Category.comp_id, prod.lift_fst]
    · simp only [Category.assoc, P.p_snd, P.ι_p₁, Category.comp_id, prod.lift_snd]
      exact h
  letI : HasLiftingProperty i P.p := inferInstance
  have hv : sq.lift ≫ P.p₀ = v := by
    rw [← P.p_fst, ← Category.assoc, sq.fac_right]
    exact prod.lift_fst _ _
  have hw : sq.lift ≫ P.p₁ = w := by
    rw [← P.p_snd, ← Category.assoc, sq.fac_right]
    exact prod.lift_snd _ _
  exact ⟨P, inferInstance, sq.lift, hv, hw⟩

/-- The same two maps induce equal localized maps after pullback along an
arbitrary point object. No fibrancy of that point object is used. -/
private theorem baseChange_lifts_localized_eq {A Z Y : Over B} (i : A ⟶ Z)
    (v w : Z ⟶ Y) [Cofibration i] [WeakEquivalence i] [IsFibrant Y]
    (h : i ≫ v = i ≫ w) (b : K ⟶ B) :
    (weakEquivalences SSet.{u}).Q.map ((Over.pullback b).map v).left =
      (weakEquivalences SSet.{u}).Q.map ((Over.pullback b).map w).left := by
  obtain ⟨P, hP, H, hv, hw⟩ := lift_path B i v w h
  letI : P.IsVeryGood := hP
  let T := Over.pullback b
  let F : Over B ⥤ SSet.{u} := T ⋙ Over.forget K
  let G := F ⋙ (weakEquivalences SSet.{u}).Q
  have hp₀ : trivialFibrations SSet.{u} (F.map P.p₀) := by
    change trivialFibrations SSet.{u} (T.map P.p₀).left
    exact (trivialFibrations SSet.{u}).baseChange_map b P.p₀
      (mem_trivialFibrations P.p₀.left)
  have h₀ : G.map P.ι ≫ G.map P.p₀ = 𝟙 _ := by
    rw [← G.map_comp, P.ι_p₀, G.map_id]
  have h₁ : G.map P.ι ≫ G.map P.p₁ = 𝟙 _ := by
    rw [← G.map_comp, P.ι_p₁, G.map_id]
  letI : IsIso (G.map P.p₀) :=
    (weakEquivalences SSet.{u}).Q_inverts _
      ((weakEquivalence_iff _).mp ((mem_trivialFibrations_iff _).mp hp₀).2)
  haveI : IsIso (G.map P.ι ≫ G.map P.p₀) := by rw [h₀]; infer_instance
  haveI : IsIso (G.map P.ι) := IsIso.of_isIso_comp_right _ (G.map P.p₀)
  have he : G.map P.p₀ = G.map P.p₁ :=
    (cancel_epi (G.map P.ι)).mp (h₀.trans h₁.symm)
  change G.map v = G.map w
  rw [← hv, ← hw, G.map_comp, G.map_comp, he]

end OverBase

section OriginalFiber

variable {A Z Y B D K : SSet.{u}} (i : A ⟶ Z) (p : Z ⟶ B)
  (q : Y ⟶ D) (g : B ⟶ D) (u v : Z ⟶ Y)
  (hu : p ≫ g = u ≫ q) (hv : p ≫ g = v ≫ q)
  [Cofibration i] [WeakEquivalence i] [Fibration q]
  (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)

private def pulledTarget : Over B := Over.mk (pullback.snd q g)

private def overSource : Over B := Over.mk p

private def overInput : Over B := Over.mk (i ≫ p)

private def overInclusion : overInput i p ⟶ overSource p := Over.homMk i (by rfl)

private def overLift (a : Z ⟶ Y) (ha : p ≫ g = a ≫ q) :
    overSource p ⟶ pulledTarget q g :=
  Over.homMk (pullback.lift a p ha.symm) (by
    change pullback.lift a p ha.symm ≫ pullback.snd q g = p
    simp only [pullback.lift_snd])

omit [Cofibration i] [WeakEquivalence i] [Fibration q] in
private theorem overLift_eq_on_input (h : i ≫ u = i ≫ v) :
    overInclusion i p ≫ overLift p q g u hu =
      overInclusion i p ≫ overLift p q g v hv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Category.assoc, overInclusion, overLift, Over.comp_left,
      Over.homMk_left, pullback.lift_fst] using h
  · simp only [Category.assoc, overInclusion, overLift, Over.comp_left,
      Over.homMk_left, pullback.lift_snd]

private theorem pulledTarget_fibrant : IsFibrant (pulledTarget q g) := by
  letI : ModelCategory (Over B) := ModelCategory.over B
  haveI : Fibration (pullback.snd q g) := inferInstance
  let t : pulledTarget q g ⟶ Over.mk (𝟙 B) := Over.homMk (pullback.snd q g)
  apply (isFibrant_iff_of_isTerminal t Over.mkIdTerminal).2
  apply (fibrations_over_iff B t).2
  change Fibration (pullback.snd q g)
  infer_instance

private theorem overInclusion_trivial :
    Cofibration (overInclusion i p) ∧ WeakEquivalence (overInclusion i p) := by
  letI : ModelCategory (Over B) := ModelCategory.over B
  constructor
  · apply (cofibrations_over_iff B (overInclusion i p)).2
    change Cofibration i
    infer_instance
  · apply (weakEquivalences_over_iff B (overInclusion i p)).2
    change WeakEquivalence i
    infer_instance

private def targetFiberIso : pullback (pullback.snd q g) b ≅ pullback q d := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  have square : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  exact square.isoPullback

omit [Fibration q] in
private theorem overLift_fiberMap (a : Z ⟶ Y) (ha : p ≫ g = a ≫ q) :
    ((Over.pullback b).map (overLift p q g a ha)).left ≫
        (targetFiberIso q g b d hb).hom = fibreMap p q a g ha b d hb := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    have hfst : (targetFiberIso q g b d hb).hom ≫ pullback.fst q d =
        pullback.fst (pullback.snd q g) b ≫ pullback.fst q g := by
      exact IsPullback.isoPullback_hom_fst _
    rw [hfst, ← Category.assoc, Over.pullback_map_left]
    change (pullback.lift (pullback.fst p b ≫ pullback.lift a p ha.symm)
      (pullback.snd p b) _ ≫ pullback.fst (pullback.snd q g) b) ≫
        pullback.fst q g = _
    rw [pullback.lift_fst]
    rw [Category.assoc, pullback.lift_fst]
    exact (fibreMap_fst p q a g ha b d hb).symm
  · rw [Category.assoc]
    have hsnd : (targetFiberIso q g b d hb).hom ≫ pullback.snd q d =
        pullback.snd (pullback.snd q g) b := by
      exact IsPullback.isoPullback_hom_snd _
    rw [hsnd, Over.pullback_map_left]
    change pullback.lift (pullback.fst p b ≫ pullback.lift a p ha.symm)
      (pullback.snd p b) _ ≫ pullback.snd (pullback.snd q g) b = _
    rw [pullback.lift_snd]
    exact (fibreMap_snd p q a g ha b d hb).symm

/-- Two actual extensions agreeing on a trivial cofibration give the same
specified homotopy-fiber map after Kan localization. -/
theorem fibreMap_localized_eq_of_same_restriction
    (h : i ≫ u = i ≫ v) :
    (weakEquivalences SSet.{u}).Q.map (fibreMap p q u g hu b d hb) =
      (weakEquivalences SSet.{u}).Q.map (fibreMap p q v g hv b d hb) := by
  letI : ModelCategory (Over B) := ModelCategory.over B
  have htriv := overInclusion_trivial i p
  letI : Cofibration (overInclusion i p) := htriv.1
  letI : WeakEquivalence (overInclusion i p) := htriv.2
  letI : IsFibrant (pulledTarget q g) := pulledTarget_fibrant q g
  have he := baseChange_lifts_localized_eq B K (overInclusion i p)
    (overLift p q g u hu) (overLift p q g v hv) (overLift_eq_on_input i p q g u v hu hv h) b
  let Q := (weakEquivalences SSet.{u}).Q
  change Q.map ((Over.pullback b).map (overLift p q g u hu)).left =
    Q.map ((Over.pullback b).map (overLift p q g v hv)).left at he
  rw [← overLift_fiberMap (p := p) (q := q) (g := g) (b := b) (d := d)
      (hb := hb) u hu,
      ← overLift_fiberMap (p := p) (q := q) (g := g) (b := b) (d := d)
      (hb := hb) v hv,
      Q.map_comp, Q.map_comp, he]

end OriginalFiber

end

end DaggerModels.PartII.ChosenFiberLiftIndependence
