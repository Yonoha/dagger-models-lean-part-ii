import DaggerModelsPartII.JTZeroCoskeleton
import DaggerModelsPartII.JTInjectiveOrderedFiberTransfer
import DaggerModelsPartII.OrderedSimplexEndpointFiber

/-! The first two rows of the actual comparison over the source zero row. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRelativeRows

open SegalLocalizers JTZeroCoskeleton JTProjectiveOrderedFiberComparison
open JTFirstRowWeakRecognition DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev zero : J := op ⟨0⟩
private abbrev one : J := op ⟨1⟩

private theorem zeroHom_unique (a b : zero ⟶ zero) : a = b := by
  apply Quiver.Hom.unop_inj
  apply ReverseSimplex.Hom.ext
  intro i
  let x : Fin 1 := a.unop.toFun i
  let y : Fin 1 := b.unop.toFun i
  change x = y
  apply Fin.ext
  omega

private abbrev projection (K : SSet.{0}) {j : J} (a : j ⟶ zero) :
    (coskeleton.obj K).obj j ⟶ K := Pi.π (fun _ ↦ K) a

private theorem vertices_projection (X : S) {j : J} (a : j ⟶ zero) :
    (vertices X).app j ≫ projection (X.obj zero) a = X.map a := by
  simp [vertices, evaluationAdjunctionLeft_unit_app_app]

private theorem coskeleton_map_projection {K L : SSet.{0}} (f : K ⟶ L)
    {j : J} (a : j ⟶ zero) :
    (coskeleton.map f).app j ≫ projection L a = projection K a ≫ f := by
  simp [evaluationRightAdjoint_map_app]

private def zeroIso (K : SSet.{0}) : (coskeleton.obj K).obj zero ≅ K where
  hom := projection K (𝟙 zero)
  inv := Pi.lift (fun _ : zero ⟶ zero ↦ 𝟙 K)
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    rw [Category.assoc, Pi.lift_π, Category.comp_id, Category.id_comp,
      zeroHom_unique a (𝟙 zero)]
  inv_hom_id := Pi.lift_π _ _

private theorem vertices_zero_isIso (X : S) : IsIso ((vertices X).app zero) := by
  have h : (vertices X).app zero ≫ (zeroIso (X.obj zero)).hom = 𝟙 _ :=
    (vertices_projection X (𝟙 zero)).trans (X.map_id zero)
  exact IsIso.of_isIso_fac_right h

/-- The actual relative comparison induces an isomorphism on the original zero row. -/
theorem relative_zero_isIso {W Z : S} (f : W ⟶ Z) :
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
  (ReverseSimplex.inclusion.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)).op

private theorem endOp_eval (i : Fin 2) : (endOp i).unop.toFun 0 = i := rfl

private theorem endOp_surj (a : one ⟶ zero) : ∃ i, endOp i = a := by
  refine ⟨a.unop.toFun 0, Quiver.Hom.unop_inj ?_⟩
  apply ReverseSimplex.Hom.ext
  intro j
  have hj : j = (0 : Fin 1) := by
    apply Fin.ext
    have hj := j.isLt
    change j.val < 1 at hj
    change j.val = 0
    omega
  rw [hj]
  exact endOp_eval _

private def oneIso (K : SSet.{0}) : (coskeleton.obj K).obj one ≅ K ⨯ K where
  hom := prod.lift (projection K (endOp 0)) (projection K (endOp 1))
  inv := Pi.lift (fun a : one ⟶ zero ↦ Fin.cases prod.fst (fun _ ↦ prod.snd) (a.unop.toFun 0))
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
  · simpa only [oneIso, Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
      using coskeleton_map_projection f (endOp 0)
  · simpa only [oneIso, Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      using coskeleton_map_projection f (endOp 1)

private def nativeEndpoint (X : S) : X.obj one ⟶ X.obj zero ⨯ X.obj zero :=
  prod.lift (X.map (endOp 0)) (X.map (endOp 1))

private theorem vertices_one (X : S) :
    (vertices X).app one ≫ (oneIso (X.obj zero)).hom = nativeEndpoint X := by
  apply prod.hom_ext
  · simpa only [oneIso, nativeEndpoint, Category.assoc, prod.lift_fst] using
      vertices_projection X (endOp 0)
  · simpa only [oneIso, nativeEndpoint, Category.assoc, prod.lift_snd] using
      vertices_projection X (endOp 1)


/-- In the first row, the relative target is the pullback of the two actual
ordered endpoint maps along the two copies of the source zero-row map. -/
theorem relative_one_pullback {W Z : S} (f : W ⟶ Z) :
    IsPullback
      ((pullback.fst (vertices Z) (coskeleton.map (f.app zero))).app one)
      ((pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫
        (oneIso (W.obj zero)).hom)
      (nativeEndpoint Z)
      (prod.map (f.app zero) (f.app zero)) := by
  let k := coskeleton.map (f.app zero)
  let e := (evaluation J SSet.{0}).obj one
  let h := (IsPullback.of_hasPullback (vertices Z) k).map e
  have hb : IsPullback (e.map k) (oneIso (W.obj zero)).hom
      (oneIso (Z.obj zero)).hom (prod.map (f.app zero) (f.app zero)) :=
    IsPullback.of_vert_isIso ⟨oneIso_natural (f.app zero)⟩
  have hv : e.map (vertices Z) ≫ (oneIso (Z.obj zero)).hom = nativeEndpoint Z :=
    vertices_one Z
  rw [← hv]
  exact h.paste_vert hb

/-- The relative comparison itself preserves the original pair of endpoints. -/
theorem relative_one_endpoints {W Z : S} (f : W ⟶ Z) :
    (relativeComparison f).app one ≫
      ((pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫
        (oneIso (W.obj zero)).hom) = nativeEndpoint W := by
  rw [← Category.assoc, ← NatTrans.comp_app]
  change ((pullback.lift f (vertices W) _) ≫
    pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app one ≫ _ = _
  rw [pullback.lift_snd, vertices_one]



local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

private theorem rowMap_natural {W Z : S} (f : W ⟶ Z) (n : ℕ) :
    rowMap f ⦋n⦌ ≫ (rowRestrictionIso Z ⦋n⦌).hom =
      (rowRestrictionIso W ⦋n⦌).hom ≫ f.app (op ⟨n⟩) := by
  apply NatTrans.ext
  funext q x
  rfl

private abbrev baseIso (X : S) :=
  prod.mapIso (rowRestrictionIso X ⦋0⦌) (rowRestrictionIso X ⦋0⦌)

private theorem baseIso_natural {W Z : S} (f : W ⟶ Z) :
    prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) ≫ (baseIso Z).hom =
      (baseIso W).hom ≫ prod.map (f.app zero) (f.app zero) := by
  change prod.map _ _ ≫ prod.map _ _ = prod.map _ _ ≫ prod.map _ _
  rw [prod.map_map, prod.map_map, rowMap_natural]

private theorem nativeEndpoint_natural (X : S) :
    (rowRestrictionIso X ⦋1⦌).hom ≫ nativeEndpoint X =
      endpointArrow X ≫ (baseIso X).hom := by
  apply prod.hom_ext
  · simp only [Category.assoc, nativeEndpoint, endpointArrow, prod.lift_fst]
    change (rowRestrictionIso X ⦋1⦌).hom ≫ X.map (endOp 0) =
      prod.lift (endpoint X 0) (endpoint X 1) ≫
        prod.map (rowRestrictionIso X ⦋0⦌).hom (rowRestrictionIso X ⦋0⦌).hom ≫ prod.fst
    rw [prod.map_fst, prod.lift_fst_assoc]
    have h := OrderedSimplexEndpointFiber.rowRestriction_endpoint X 0
    rw [Iso.inv_comp_eq] at h
    rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Category.assoc, nativeEndpoint, endpointArrow, prod.lift_snd]
    change (rowRestrictionIso X ⦋1⦌).hom ≫ X.map (endOp 1) =
      prod.lift (endpoint X 0) (endpoint X 1) ≫
        prod.map (rowRestrictionIso X ⦋0⦌).hom (rowRestrictionIso X ⦋0⦌).hom ≫ prod.snd
    rw [prod.map_snd, prod.lift_snd_assoc]
    have h := OrderedSimplexEndpointFiber.rowRestriction_endpoint X 1
    rw [Iso.inv_comp_eq] at h
    rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

open DaggerNativeSSetFibrationsOverBaseWeakPullbacks

/-- The original ordered strict-fiber test gives weakness of the first row
after pulling the target back to the source zero row. -/
theorem relative_one_weak {W Z : S} (f : W ⟶ Z) [IsFibrant W] [IsFibrant Z]
    (hf : ∀ x y : (row W ⦋0⦌).obj (op ⦋0⦌), WeakEquivalence
      (JTInjectiveOrderedFiberTransfer.strictFiberMap f x y)) :
    WeakEquivalence ((relativeComparison f).app one) := by
  let P := targetOverZero f
  let k := coskeleton.map (f.app zero)
  let t₀ : P ⟶ Z := pullback.fst (vertices Z) k
  let τ₀ := (pullback.snd (vertices Z) k).app one ≫ (oneIso (W.obj zero)).hom
  let t := rowMap t₀ ⦋1⦌
  let τ := (rowRestrictionIso P ⦋1⦌).hom ≫ τ₀ ≫ (baseIso W).inv
  let r := rowMap (relativeComparison f) ⦋1⦌
  let p := endpointArrow W
  let q := endpointArrow Z
  let c := prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌)
  have ht : IsPullback t τ q c :=
    (relative_one_pullback f).of_iso' (rowRestrictionIso P ⦋1⦌) (rowRestrictionIso Z ⦋1⦌)
      (baseIso W) (baseIso Z) (rowMap_natural t₀ 1).symm
      (by simp only [τ, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl)
      (nativeEndpoint_natural Z) (baseIso_natural f).symm
  have hr : r ≫ τ = p := by
    have hn : (relativeComparison f).app one ≫ τ₀ = nativeEndpoint W :=
      relative_one_endpoints f
    let e₁ := (rowRestrictionIso W ⦋1⦌).hom
    let e₂ := (rowRestrictionIso P ⦋1⦌).hom
    let i := (baseIso W).inv
    calc
      r ≫ τ = (r ≫ e₂) ≫ (τ₀ ≫ i) := (Category.assoc _ _ _).symm
      _ = (e₁ ≫ (relativeComparison f).app one) ≫ (τ₀ ≫ i) := by
        exact congrArg (fun t ↦ t ≫ (τ₀ ≫ i)) (rowMap_natural (relativeComparison f) 1)
      _ = (e₁ ≫ nativeEndpoint W) ≫ i := by
        rw [Category.assoc e₁, ← Category.assoc ((relativeComparison f).app one),
          hn, ← Category.assoc e₁]
      _ = p := by
        change ((rowRestrictionIso W ⦋1⦌).hom ≫ nativeEndpoint W) ≫ (baseIso W).inv = p
        rw [nativeEndpoint_natural, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hrt : r ≫ t = rowMap f ⦋1⦌ := by
    change rowMap (relativeComparison f) ⦋1⦌ ≫ rowMap t₀ ⦋1⦌ = _
    let E := JTReversalInput.ordinaryInput ⋙ JTRealizationDiagonal.ordinaryCurry ⋙
      (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋1⦌)
    change E.map (relativeComparison f) ≫ E.map t₀ = E.map f
    rw [← E.map_comp]
    exact congrArg E.map (pullback.lift_fst _ _ _)
  letI : Fibration p := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W inferInstance
  letI : Fibration q := JTInjectiveOrderedEndpointFibration.endpointArrow_fibration Z inferInstance
  letI : Fibration τ := by
    apply (fibration_iff τ).mpr
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback ht (mem_fibrations q)
  have hq : p ≫ c = rowMap f ⦋1⦌ ≫ q := by
    rw [← hrt, Category.assoc, ht.w, ← Category.assoc, hr]
  haveI : WeakEquivalence r := by
    apply DaggerNativeFibrewiseWeakRecognition.weak_of_vertex_base_changes p τ r hr
    intro b
    let x := SSet.yonedaEquiv (b ≫ prod.fst)
    let y := SSet.yonedaEquiv (b ≫ prod.snd)
    have hb : b = point W x y := by
      apply prod.hom_ext
      · simp only [point, prod.lift_fst, vertexPoint, x, Equiv.symm_apply_apply]
      · simp only [point, prod.lift_snd, vertexPoint, y, Equiv.symm_apply_apply]
    let sq := (IsPullback.of_hasPullback τ b).paste_horiz ht
    let u := mapOver p τ r hr b
    let j := fibreMap p q (rowMap f ⦋1⦌) c hq b (b ≫ c) rfl
    letI : WeakEquivalence j := by
      change WeakEquivalence (fibreMap p q (rowMap f ⦋1⦌) c hq b (b ≫ c) rfl)
      rw [hb]
      exact hf x y
    have hm : u ≫ sq.isoPullback.hom = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc u, mapOver_fst,
          Category.assoc, hrt, fibreMap_fst]
      · rw [Category.assoc, sq.isoPullback_hom_snd, fibreMap_snd]
        exact pullback.lift_snd _ _ _
    exact weakEquivalence_of_postcomp_of_fac hm
  exact weakEquivalence_of_precomp_of_fac (rowMap_natural (relativeComparison f) 1).symm

end

end DaggerModels.PartII.JTRelativeRows
