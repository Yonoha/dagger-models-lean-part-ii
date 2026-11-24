import OrdinaryZeroCoskeleton
import OrdinarySegalEndpointSquareFiberwiseRecognition

/-!
# The first two actual ordinary relative rows

The evaluation right adjoint gives the zero and one rows of the literal
ordinary zero coskeleton. The first relative row is the original ordered
endpoint pullback. No completeness or CSS weak-to-DK assertion is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryRelativeRows

open OrdinaryCSSLocalization (Space)
open OrdinaryZeroCoskeleton (coskeleton vertices targetOverZero relativeComparison)
open OrdinarySegalOrderedMappingFibres (endpointArrow)
open OrdinarySegalOrderedMappingMaps (endpointMap mappingMap)

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev zero : J := op ⦋0⦌
private abbrev one : J := op ⦋1⦌

private theorem zeroHom_unique (a b : zero ⟶ zero) : a = b := by
  apply Quiver.Hom.unop_inj
  exact (SimplexCategory.eq_const_to_zero a.unop).trans
    (SimplexCategory.eq_const_to_zero b.unop).symm

private abbrev projection (K : SSet.{0}) {j : J} (a : j ⟶ zero) :
    (coskeleton.obj K).obj j ⟶ K := Pi.π (fun _ ↦ K) a

private theorem vertices_projection (X : Space) {j : J} (a : j ⟶ zero) :
    (vertices X).app j ≫ projection (X.obj zero) a = X.map a := by
  simp [vertices, evaluationAdjunctionLeft_unit_app_app]

private theorem coskeleton_map_projection {K L : SSet.{0}} (f : K ⟶ L)
    {j : J} (a : j ⟶ zero) :
    (coskeleton.map f).app j ≫ projection L a = projection K a ≫ f := by
  simp [evaluationRightAdjoint_map_app]

/-- The actual zero row of the ordinary zero coskeleton is its coefficient. -/
def zeroIso (K : SSet.{0}) : (coskeleton.obj K).obj zero ≅ K where
  hom := projection K (𝟙 zero)
  inv := Pi.lift (fun _ : zero ⟶ zero ↦ 𝟙 K)
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    rw [Category.assoc, Pi.lift_π, Category.comp_id, Category.id_comp,
      zeroHom_unique a (𝟙 zero)]
  inv_hom_id := Pi.lift_π _ _

private theorem vertices_zero_isIso (X : Space) : IsIso ((vertices X).app zero) := by
  have h : (vertices X).app zero ≫ (zeroIso (X.obj zero)).hom = 𝟙 _ :=
    (vertices_projection X (𝟙 zero)).trans (X.map_id zero)
  exact IsIso.of_isIso_fac_right h

/-- The literal relative comparison is invertible in horizontal degree zero. -/
theorem relative_zero_isIso {W Z : Space} (f : W ⟶ Z) :
    IsIso ((relativeComparison f).app zero) := by
  let k := coskeleton.map (f.app zero)
  let e := (evaluation J SSet.{0}).obj zero
  have hs := ((IsPullback.of_hasPullback (vertices Z) k).map e).flip
  letI : IsIso (e.map (vertices Z)) := vertices_zero_isIso Z
  letI : IsIso (e.map (pullback.snd (vertices Z) k)) := hs.isIso_fst_of_isIso
  have h : e.map (relativeComparison f) ≫ e.map (pullback.snd (vertices Z) k) =
      e.map (vertices W) := by
    rw [← e.map_comp]
    exact congrArg e.map (pullback.lift_snd _ _ _)
  letI : IsIso (e.map (vertices W)) := vertices_zero_isIso W
  change IsIso (e.map (relativeComparison f))
  exact IsIso.of_isIso_fac_right h

private abbrev endOp (i : Fin 2) : one ⟶ zero :=
  (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op

private theorem endOp_eval (i : Fin 2) : (endOp i).unop.toOrderHom 0 = i := rfl

private theorem endOp_surj (a : one ⟶ zero) : ∃ i, endOp i = a := by
  refine ⟨a.unop.toOrderHom 0, Quiver.Hom.unop_inj ?_⟩
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  have hj : j = (0 : Fin 1) := by
    apply Fin.ext
    have hj := j.isLt
    change j.val < 1 at hj
    change j.val = 0
    omega
  rw [hj]
  exact endOp_eval _

/-- The one row is the ordered pair of coefficient values at the two vertices. -/
def oneIso (K : SSet.{0}) : (coskeleton.obj K).obj one ≅ K ⨯ K where
  hom := prod.lift (projection K (endOp 0)) (projection K (endOp 1))
  inv := Pi.lift (fun a : one ⟶ zero ↦
    Fin.cases (motive := fun _ : Fin 2 ↦ (K ⨯ K ⟶ K))
      (prod.fst : K ⨯ K ⟶ K) (fun _ : Fin 1 ↦ (prod.snd : K ⨯ K ⟶ K))
      (a.unop.toOrderHom 0))
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    obtain ⟨i, rfl⟩ := endOp_surj a
    rw [Category.assoc, Pi.lift_π, Category.id_comp]
    fin_cases i
    · exact prod.lift_fst (projection K (endOp 0)) (projection K (endOp 1))
    · exact prod.lift_snd (projection K (endOp 0)) (projection K (endOp 1))
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Pi.lift_π, Category.id_comp]
      rfl
    · rw [Category.assoc, prod.lift_snd, Pi.lift_π, Category.id_comp]
      rfl

private theorem oneIso_natural {K L : SSet.{0}} (f : K ⟶ L) :
    (coskeleton.map f).app one ≫ (oneIso L).hom =
      (oneIso K).hom ≫ prod.map f f := by
  apply prod.hom_ext
  · simpa only [oneIso, Category.assoc, prod.lift_fst, prod.map_fst,
      prod.lift_fst_assoc] using coskeleton_map_projection f (endOp 0)
  · simpa only [oneIso, Category.assoc, prod.lift_snd, prod.map_snd,
      prod.lift_snd_assoc] using coskeleton_map_projection f (endOp 1)

private theorem endOp_zero :
    endOp 0 = (SimplexCategory.δ (1 : Fin 2)).op := by
  apply Quiver.Hom.unop_inj
  ext j
  fin_cases j; rfl

private theorem endOp_one :
    endOp 1 = (SimplexCategory.δ (0 : Fin 2)).op := by
  apply Quiver.Hom.unop_inj
  ext j
  fin_cases j; rfl

/-- The unit to the one-row coskeleton records precisely `(d₁,d₀)`. -/
theorem vertices_one (X : Space) :
    (vertices X).app one ≫ (oneIso (X.obj zero)).hom = endpointArrow X := by
  apply prod.hom_ext
  · simp only [oneIso, Category.assoc, prod.lift_fst,
      OrdinarySegalOrderedMappingFibres.endpointArrow_fst]
    rw [vertices_projection X (endOp 0), endOp_zero]
  · simp only [oneIso, Category.assoc, prod.lift_snd,
      OrdinarySegalOrderedMappingFibres.endpointArrow_snd]
    rw [vertices_projection X (endOp 1), endOp_one]

/-- The degree-one relative target is the original ordered endpoint pullback. -/
theorem relative_one_pullback {W Z : Space} (f : W ⟶ Z) :
    IsPullback
      ((pullback.fst (vertices Z) (coskeleton.map (f.app zero))).app one)
      ((pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫
        (oneIso (W.obj zero)).hom)
      (endpointArrow Z) (endpointMap f) := by
  let k := coskeleton.map (f.app zero)
  let e := (evaluation J SSet.{0}).obj one
  have h := (IsPullback.of_hasPullback (vertices Z) k).map e
  have hb : IsPullback (e.map k) (oneIso (W.obj zero)).hom
      (oneIso (Z.obj zero)).hom (endpointMap f) :=
    IsPullback.of_vert_isIso ⟨oneIso_natural (f.app zero)⟩
  have hv : e.map (vertices Z) ≫ (oneIso (Z.obj zero)).hom = endpointArrow Z :=
    vertices_one Z
  rw [← hv]
  exact h.paste_vert hb

/-- The relative map retains the actual ordered source endpoint pair. -/
theorem relative_one_endpoints {W Z : Space} (f : W ⟶ Z) :
    (relativeComparison f).app one ≫
      ((pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫
        (oneIso (W.obj zero)).hom) = endpointArrow W := by
  rw [← Category.assoc, ← NatTrans.comp_app]
  change ((pullback.lift f (vertices W) _) ≫
    pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫ _ = _
  rw [pullback.lift_snd, vertices_one]

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Weakness on every original ordered mapping fiber makes the literal
relative comparison weak in horizontal degree one. -/
theorem relative_one_weak {W Z : Space} (f : W ⟶ Z)
    [IsFibrant W] [IsFibrant Z]
    (hf : ∀ x y : (W.obj zero).obj (op ⦋0⦌), WeakEquivalence (mappingMap f x y)) :
    WeakEquivalence ((relativeComparison f).app one) := by
  let k := coskeleton.map (f.app zero)
  let t := (pullback.fst (vertices Z) k).app one
  let s := (pullback.snd (vertices Z) k).app one ≫ (oneIso (W.obj zero)).hom
  let r := (relativeComparison f).app one
  let h : IsPullback t s (endpointArrow Z) (endpointMap f) := relative_one_pullback f
  let e := h.isoPullback
  have hrT : r ≫ t = f.app one := by
    have h : relativeComparison f ≫ pullback.fst (vertices Z) k = f :=
      pullback.lift_fst _ _ _
    exact congrArg (fun m ↦ m.app one) h
  have hrS : r ≫ s = endpointArrow W := relative_one_endpoints f
  have he : r ≫ e.hom = OrdinarySegalEndpointSquareFiberwiseRecognition.comparison f := by
    apply pullback.hom_ext
    · rw [Category.assoc, h.isoPullback_hom_fst,
        OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_fst]
      exact hrT
    · rw [Category.assoc, h.isoPullback_hom_snd,
        OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_snd]
      exact hrS
  have hc : WeakEquivalence (OrdinarySegalEndpointSquareFiberwiseRecognition.comparison f) :=
    OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_weak_of_mappingMap_weak
      f hf
  have : WeakEquivalence (r ≫ e.hom) := by rw [he]; exact hc
  exact weakEquivalence_of_postcomp r e.hom

#print axioms zeroIso
#print axioms oneIso
#print axioms relative_zero_isIso
#print axioms relative_one_pullback
#print axioms relative_one_endpoints
#print axioms relative_one_weak

end

end DaggerModels.PartII.OrdinaryRelativeRows
