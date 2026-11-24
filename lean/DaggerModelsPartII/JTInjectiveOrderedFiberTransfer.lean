import DaggerModelsPartII.JTPQOrderedFiberTransfer
import DaggerModelsPartII.FibrationSquareComponentFibers
import OriginalSimplicialPiZeroWeakEquivalence

/-! Exact passage from projectively resolved source to a map between injective-local objects. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels DaggerNativeSSetFibrationSquareFibreWeak
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTInjectiveOrderedFiberTransfer

open SegalLocalizers JTProjectiveOrderedFiberComparison JTFirstRowWeakRecognition
open JTPQOrderedFiberTransfer
open JTStrictificationMaps (Qproj p)

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev Inj := InjectiveKanDiagram.modelCategory J
local instance : ModelCategory S := Inj

/-- Factor the original projective resolution map in the injective model. -/
def factor (W : S) := factorizationData (trivialCofibrations S) (fibrations S) (p.app W)

private theorem i_cofibration (W : S) : Cofibration (factor W).i :=
  (cofibration_iff _).mpr (factor W).hi.1

private theorem i_weak (W : S) : WeakEquivalence (factor W).i :=
  (weakEquivalence_iff _).mpr (factor W).hi.2

private theorem p_projective_trivial (W : S) :
    letI := ProjectiveKanDiagram.modelCategory J
    Fibration (p.app W) ∧ WeakEquivalence (p.app W) := by
  letI := ProjectiveKanDiagram.modelCategory J
  exact (mem_trivialFibrations_iff _).mp (JTStrictificationMaps.p_trivialFibration W)

private theorem p_injective_weak (W : S) : WeakEquivalence (p.app W) := by
  have h : ProjectiveKanDiagram.weakEquivalences J (p.app W) := by
    letI := ProjectiveKanDiagram.modelCategory J
    exact (weakEquivalence_iff _).mp (p_projective_trivial W).2
  exact (weakEquivalence_iff _).mpr (by
    rw [InjectiveKanDiagram.model_weakEquivalences]
    exact h)

private theorem r_weak (W : S) : WeakEquivalence (factor W).p := by
  letI := i_weak W
  letI := p_injective_weak W
  exact weakEquivalence_of_precomp_of_fac (factor W).fac

private theorem middle_fibrant (W : S) [IsFibrant W] : IsFibrant (factor W).Z := by
  letI : Fibration (factor W).p := (fibration_iff _).mpr (factor W).hp
  letI : IsFibrant ((𝟭 S).obj W) := inferInstanceAs (IsFibrant W)
  exact isFibrant_of_fibration (factor W).p

/-- The new source is local whenever the original injective source is local. -/
theorem middle_local (W : S) (hW : Localization.localObject localizingFamily W) :
    Localization.localObject localizingFamily (factor W).Z := by
  letI := hW.1
  letI : IsFibrant ((𝟭 S).obj W) := inferInstanceAs (IsFibrant W)
  letI := middle_fibrant W
  exact (Localization.localObject_iff_of_weak localizingFamily
    (factor W).p ((weakEquivalence_iff _).mp (r_weak W))).mpr hW

/-- Extend the actual map across the specified injective trivial cofibration. -/
def extend {W Z : S} [IsFibrant Z] (g : Qproj.obj W ⟶ Z) : (factor W).Z ⟶ Z := by
  letI := i_cofibration W
  letI := i_weak W
  exact (show CommSq g (factor W).i (terminal.from Z) (terminal.from (factor W).Z) from
    ⟨terminalIsTerminal.hom_ext _ _⟩).lift

@[simp] theorem extend_i {W Z : S} [IsFibrant Z] (g : Qproj.obj W ⟶ Z) :
    (factor W).i ≫ extend g = g := by
  letI := i_cofibration W
  letI := i_weak W
  exact (show CommSq g (factor W).i (terminal.from Z) (terminal.from (factor W).Z) from
    ⟨terminalIsTerminal.hom_ext _ _⟩).fac_left

private theorem row_fibrant_of_projective (V : S)
    (hV : letI := ProjectiveKanDiagram.modelCategory J; IsFibrant V)
    (m : SimplexCategory) : IsFibrant (row V m) := by
  haveI : IsFibrant (V.obj (op (ReverseSimplex.inclusion.obj m))) :=
    (ProjectiveKanDiagram.model_isFibrant_iff J V).mp hV
      (op (ReverseSimplex.inclusion.obj m))
  exact (isFibrant_iff_of_isTerminal ((rowRestrictionIso V m).hom ≫ terminal.from _)
    terminalIsTerminal).mpr inferInstance

private theorem source_row_fibrant (W : S) [IsFibrant W] (m : SimplexCategory) :
    IsFibrant (row (Qproj.obj W) m) := by
  apply row_fibrant_of_projective
  have hW := ProjectiveInjectiveComparison.isFibrant_projective J W
    (show IsFibrant W from inferInstance)
  letI := ProjectiveKanDiagram.modelCategory J
  letI := hW
  letI : IsFibrant ((𝟭 S).obj W) := hW
  letI : Fibration (p.app W) := (p_projective_trivial W).1
  exact isFibrant_of_fibration (p.app W)

private theorem middle_row_fibrant (W : S) [IsFibrant W] (m : SimplexCategory) :
    IsFibrant (row (factor W).Z m) :=
  row_fibrant_of_projective _ (ProjectiveInjectiveComparison.isFibrant_projective J _
    (middle_fibrant W)) m

private theorem i_row_weak (W : S) (m : SimplexCategory) :
    WeakEquivalence (rowMap (factor W).i m) := by
  apply rowMap_weak_of_projective
  have hi := (weakEquivalence_iff _).mp (i_weak W)
  rw [InjectiveKanDiagram.model_weakEquivalences] at hi
  exact hi

private theorem i_fiber_weak (W : S) [IsFibrant W]
    (x y : (row (Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (fiberMap (factor W).i x y) := by
  letI := source_row_fibrant W ⦋0⦌
  letI := middle_row_fibrant W ⦋0⦌
  letI := i_row_weak W ⦋0⦌
  letI := i_row_weak W ⦋1⦌
  exact fiberMap_weak_of_rows (factor W).i x y

private theorem fiberMap_weak_congr {V Z : S} {f g : V ⟶ Z}
    (h : f = g) (x y : (row V ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (fiberMap f x y) ↔ WeakEquivalence (fiberMap g x y) := by
  subst g
  rfl

private theorem extendedFiber_weak_at_images {W Z : S} [IsFibrant W] [IsFibrant Z]
    (g : Qproj.obj W ⟶ Z) (x y : (row (Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌))
    (hg : WeakEquivalence (fiberMap g x y)) :
    WeakEquivalence (fiberMap (extend g)
      ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) x)
      ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) y)) := by
  let i := (factor W).i
  let Q := (weakEquivalences SSet.{0}).Q
  have hi : IsIso (Q.map (fiberMap i x y)) :=
    Localization.inverts Q _ _ ((weakEquivalence_iff _).mp (i_fiber_weak W x y))
  have hc : WeakEquivalence (fiberMap (i ≫ extend g) x y) :=
    (fiberMap_weak_congr (extend_i g) x y).mpr hg
  have hIso : IsIso (Q.map (fiberMap (i ≫ extend g) x y)) :=
    Localization.inverts Q _ _ ((weakEquivalence_iff _).mp hc)
  apply (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q _).mpr
  apply (isIso_comp_left_iff (Q.map (fiberMap i x y)) _).mp
  rw [fiberMap_localized_comp]
  exact hIso

/-- The literal strict ordered fiber map for a reversal-diagram arrow. -/
def strictFiberMap {V Z : S} (g : V ⟶ Z) (x y : (row V ⦋0⦌).obj (op ⦋0⦌)) :=
  fibreMap (endpointArrow V) (endpointArrow Z) (rowMap g ⦋1⦌)
    (prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)) (endpoint_square g)
    (point V x y) (point V x y ≫ prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)) rfl

private theorem fibreMap_weak_congr_point {X Y B D K : SSet.{0}}
    (a : X ⟶ B) (b : Y ⟶ D) (u : X ⟶ Y) (v : B ⟶ D) (h : a ≫ v = u ≫ b)
    (c : K ⟶ B) {d d' : K ⟶ D} (hc : c ≫ v = d) (hc' : c ≫ v = d')
    (e : d = d') :
    WeakEquivalence (fibreMap a b u v h c d hc) ↔
      WeakEquivalence (fibreMap a b u v h c d' hc') := by
  cases e
  rfl

private theorem strictFiber_weak_of_chosen {V Z : S} [IsFibrant V] [IsFibrant Z]
    (g : V ⟶ Z) (x y : (row V ⦋0⦌).obj (op ⦋0⦌))
    (h : WeakEquivalence (fiberMap g x y)) : WeakEquivalence (strictFiberMap g x y) := by
  let a := endpointArrow V
  let b := endpointArrow Z
  let u := rowMap g ⦋1⦌
  let v := prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)
  let c := point V x y
  let d := point Z ((rowMap g ⦋0⦌).app (op ⦋0⦌) x)
    ((rowMap g ⦋0⦌).app (op ⦋0⦌) y)
  letI : Fibration a := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration V inferInstance
  letI : Fibration b := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration Z inferInstance
  letI := ChosenHomotopyFiberTriangle.inclusion_weak a c
  letI := ChosenHomotopyFiberTriangle.inclusion_weak b d
  letI : WeakEquivalence (ChosenHomotopyFiberFunctor.chosenMap a b u v
    (endpoint_square g) c d (point_square g x y)) := h
  have hw := ChosenHomotopyFiberFunctor.inclusion_chosenMap a b u v
    (endpoint_square g) c d (point_square g x y)
  have h' : WeakEquivalence (fibreMap a b u v (endpoint_square g) c d (point_square g x y)) :=
    weakEquivalence_of_postcomp_of_fac hw.symm
  exact (fibreMap_weak_congr_point a b u v (endpoint_square g) c
    (point_square g x y) rfl (point_square g x y).symm).mp h'

/-- Exact ordered strict-fiber weakness for the injective comparison at the
literal images of the original specified vertices. -/
theorem extendedStrictFiber_weak_at_images {W Z : S} [IsFibrant W] [IsFibrant Z]
    (g : Qproj.obj W ⟶ Z) (x y : (row (Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌))
    (hg : WeakEquivalence (fiberMap g x y)) :
    WeakEquivalence (strictFiberMap (extend g)
      ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) x)
      ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) y)) := by
  letI := middle_fibrant W
  exact strictFiber_weak_of_chosen _ _ _ (extendedFiber_weak_at_images g x y hg)


private theorem i_base_weak (W : S) [IsFibrant W] :
    WeakEquivalence (prod.map (rowMap (factor W).i ⦋0⦌) (rowMap (factor W).i ⦋0⦌)) := by
  let A := row (Qproj.obj W) ⦋0⦌
  let B := row (factor W).Z ⦋0⦌
  let f : A ⟶ B := rowMap (factor W).i ⦋0⦌
  letI : IsFibrant A := source_row_fibrant W _
  letI : IsFibrant B := middle_row_fibrant W _
  letI : WeakEquivalence f := i_row_weak W _
  haveI : WeakEquivalence (prod.map f (𝟙 A)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f A).flip
  haveI : WeakEquivalence (prod.map f (𝟙 B)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f B).flip
  have hb : prod.map (𝟙 B) f =
      (prod.braiding B A).hom ≫ prod.map f (𝟙 B) ≫ (prod.braiding B B).hom := by
    apply prod.hom_ext <;> simp
  haveI : WeakEquivalence (prod.map (𝟙 B) f) := by rw [hb]; infer_instance
  have hc : prod.map f (𝟙 A) ≫ prod.map (𝟙 B) f = prod.map f f := by
    simp only [prod.map_map, Category.comp_id, Category.id_comp]
  change WeakEquivalence (prod.map f f)
  rw [← hc]
  infer_instance

private theorem point_exhaustive (V : S) (b : (Δ[0] : SSet.{0}) ⟶ row V ⦋0⦌ ⨯ row V ⦋0⦌) :
    b = point V (SSet.yonedaEquiv (b ≫ prod.fst)) (SSet.yonedaEquiv (b ≫ prod.snd)) := by
  apply prod.hom_ext
  · simp only [point, prod.lift_fst, vertexPoint, Equiv.symm_apply_apply]
  · simp only [point, prod.lift_snd, vertexPoint, Equiv.symm_apply_apply]

/-- The exact comparison is weak on all strict ordered endpoint fibers,
using surjectivity on components of the weak map on the original bases. -/
theorem extendedStrictFiber_weak {W Z : S} [IsFibrant W] [IsFibrant Z]
    (g : Qproj.obj W ⟶ Z)
    (hg : ∀ x y : (row (Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌),
      WeakEquivalence (fiberMap g x y))
    (x y : (row (factor W).Z ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (strictFiberMap (extend g) x y) := by
  let V := (factor W).Z
  let e := extend g
  let a := endpointArrow V
  let b := endpointArrow Z
  let u := rowMap e ⦋1⦌
  let v := prod.map (rowMap e ⦋0⦌) (rowMap e ⦋0⦌)
  let w := prod.map (rowMap (factor W).i ⦋0⦌) (rowMap (factor W).i ⦋0⦌)
  let z := SSet.yonedaEquiv (point V x y)
  letI : WeakEquivalence w := i_base_weak W
  obtain ⟨s, hs⟩ := (bijective_mapPiZero w).2 (SSet.π₀.mk z)
  obtain ⟨t, rfl⟩ := SSet.π₀.mk_surjective s
  let h := SSet.yonedaEquiv.symm t
  let x₀ := SSet.yonedaEquiv (h ≫ prod.fst)
  let y₀ := SSet.yonedaEquiv (h ≫ prod.snd)
  have ht : h = point (Qproj.obj W) x₀ y₀ := point_exhaustive _ _
  have hc : SSet.yonedaEquiv.symm (w.app (op ⦋0⦌) t) =
      point V ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) x₀)
        ((rowMap (factor W).i ⦋0⦌).app (op ⦋0⦌) y₀) := by
    calc
      _ = h ≫ w := by apply SSet.yonedaEquiv.injective; simp [h]
      _ = _ := ht ▸ point_square (factor W).i x₀ y₀
  letI : IsFibrant V := middle_fibrant W
  letI : Fibration a := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration V inferInstance
  letI : Fibration b := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration Z inferInstance
  have he := FibrationSquareComponentFibers.fibreMap_weak_iff_of_component a b u v
    (endpoint_square e) (w.app (op ⦋0⦌) t) z hs
  have H := extendedStrictFiber_weak_at_images g x₀ y₀ (hg x₀ y₀)
  unfold strictFiberMap at H ⊢
  have hweak : WeakEquivalence (fibreMap a b u v (endpoint_square e)
      (SSet.yonedaEquiv.symm (w.app (op ⦋0⦌) t))
      (SSet.yonedaEquiv.symm (w.app (op ⦋0⦌) t) ≫ v) rfl) := by
    rw [hc]
    exact H
  have hout := he.mp hweak
  change WeakEquivalence (fibreMap a b u v (endpoint_square e)
    (SSet.yonedaEquiv.symm z) (SSet.yonedaEquiv.symm z ≫ v) rfl) at hout
  have hz : SSet.yonedaEquiv.symm z = point V x y :=
    SSet.yonedaEquiv.symm_apply_apply _
  rw [hz] at hout
  exact hout

/-- The chosen injective comparison is surjective on zero-row components
whenever the original specified map has that property. -/
theorem extend_components_surjective {W Z : S} [IsFibrant Z]
    (g : Qproj.obj W ⟶ Z) (hg : Function.Surjective (SSet.mapπ₀ (rowMap g ⦋0⦌))) :
    Function.Surjective (SSet.mapπ₀ (rowMap (extend g) ⦋0⦌)) := by
  have hr : rowMap (factor W).i ⦋0⦌ ≫ rowMap (extend g) ⦋0⦌ = rowMap g ⦋0⦌ := by
    change (JTRealizationDiagonal.ordinaryCurry.map
      (JTReversalInput.ordinaryInput.map (factor W).i)).app _ ≫
      (JTRealizationDiagonal.ordinaryCurry.map (JTReversalInput.ordinaryInput.map (extend g))).app _ =
      (JTRealizationDiagonal.ordinaryCurry.map (JTReversalInput.ordinaryInput.map g)).app _
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, extend_i]
  intro z
  obtain ⟨t, ht⟩ := hg z
  refine ⟨SSet.mapπ₀ (rowMap (factor W).i ⦋0⦌) t, ?_⟩
  rw [← SSet.mapπ₀_comp_apply, hr]
  exact ht

end

end DaggerModels.PartII.JTInjectiveOrderedFiberTransfer
