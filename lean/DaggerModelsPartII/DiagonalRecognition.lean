import DaggerModelsPartII.FibrationSquareComponentFibers
import DaggerModelsPartII.FibrationSquareWeakRecognition
import NativeFibrationSurjectiveComponents
import NativeFibrationWeakFromVertexFibres
import NativeAllCofibrantLocalizationSaturation

/-! Chosen diagonal homotopy fibers and component surjectivity detect Kan weak equivalences. -/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DiagonalRecognition
noncomputable section

/-- Products of weak maps between Kan complexes are weak. -/
theorem prodMap_weak {A B : SSet.{0}} (f : A ⟶ B)
    [IsFibrant A] [IsFibrant B] [WeakEquivalence f] :
    WeakEquivalence (prod.map f f) := by
  haveI : WeakEquivalence (prod.map f (𝟙 A)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f A).flip
  haveI : WeakEquivalence (prod.map f (𝟙 B)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f B).flip
  have h : prod.map (𝟙 B) f =
      (prod.braiding B A).hom ≫ prod.map f (𝟙 B) ≫ (prod.braiding B B).hom := by
    apply prod.hom_ext <;> simp
  haveI : WeakEquivalence (prod.map (𝟙 B) f) := by rw [h]; infer_instance
  have hcomp : prod.map f (𝟙 A) ≫ prod.map (𝟙 B) f = prod.map f f := by
    simp only [prod.map_map, Category.comp_id, Category.id_comp]
  rw [← hcomp]
  infer_instance

open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor

/-- A weak square induces a weak map between the chosen fibers. -/
theorem chosenMap_weak_of_weak_square {X Y B D K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)
    [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (chosenMap p q f g h b d hb) := by
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  letI : WeakEquivalence (replacement q).i :=
    (weakEquivalence_iff _).mpr (replacement q).hi.2
  have hs : p ≫ g = (f ≫ (replacement q).i) ≫ (replacement q).p := by
    rw [Category.assoc, (replacement q).fac]
    exact h
  change WeakEquivalence (comparison p (replacement q).p
    (f ≫ (replacement q).i) g hs b d hb)
  exact comparison_weak p (replacement q).p (f ≫ (replacement q).i) g hs b d hb

/-- Weakness of a chosen map is invariant under equality of its total and base arrows. -/
theorem chosenMap_weak_congr {X Y B D K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D)
    (f f' : X ⟶ Y) (g g' : B ⟶ D)
    (hf : f = f') (hg : g = g')
    (h : p ≫ g = f ≫ q) (h' : p ≫ g' = f' ≫ q)
    (b : K ⟶ B)
    [WeakEquivalence (chosenMap p q f' g' h' b (b ≫ g') rfl)] :
    WeakEquivalence (chosenMap p q f g h b (b ≫ g) rfl) := by
  cases hf
  cases hg
  exact inferInstance

/-- Cancel a weak chosen-fiber map from a composite pointed square. -/
theorem chosenMap_weak_of_composite {X Y Z B D H K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (r : Z ⟶ H)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (a : Y ⟶ Z) (c : D ⟶ H) (h' : q ≫ c = a ≫ r)
    (b : K ⟶ B) (d : K ⟶ D) (e : K ⟶ H)
    (hb : b ≫ g = d) (hd : d ≫ c = e)
    [WeakEquivalence (chosenMap p q f g h b d hb)]
    (hcomp : p ≫ (g ≫ c) = (f ≫ a) ≫ r)
    (hecomp : b ≫ (g ≫ c) = e)
    [WeakEquivalence (chosenMap p r (f ≫ a) (g ≫ c) hcomp b e hecomp)] :
    WeakEquivalence (chosenMap q r a c h' d e hd) := by
  let Q := (weakEquivalences SSet.{0}).Q
  have hm := chosenMap_comp p q r f g h a c h' b d e hb hd
  haveI : IsIso (Q.map (chosenMap p q f g h b d hb)) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp inferInstance
  haveI : IsIso (Q.map (chosenMap p r (f ≫ a) (g ≫ c) hcomp b e hecomp)) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp inferInstance
  have hc : IsIso (Q.map (chosenMap p q f g h b d hb) ≫
      Q.map (chosenMap q r a c h' d e hd)) := by
    rw [hm]
    infer_instance
  haveI : IsIso (Q.map (chosenMap q r a c h' d e hd)) := by
    letI := hc
    exact IsIso.of_isIso_comp_left
      (Q.map (chosenMap p q f g h b d hb))
      (Q.map (chosenMap q r a c h' d e hd))
  exact (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q _).mpr inferInstance

/-- Chosen-fiber weakness is constant on components of the source base. -/
theorem chosenMap_weak_iff_of_component {X Y B D : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q)
    (z w : B.obj (op ⦋0⦌)) (hz : SSet.π₀.mk z = SSet.π₀.mk w) :
    WeakEquivalence (chosenMap p q f g h (SSet.yonedaEquiv.symm z)
      (SSet.yonedaEquiv.symm z ≫ g) rfl) ↔
    WeakEquivalence (chosenMap p q f g h (SSet.yonedaEquiv.symm w)
      (SSet.yonedaEquiv.symm w ≫ g) rfl) := by
  letI : Fibration (replacement p).p := (fibration_iff _).mpr (replacement p).hp
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  have hs : p ≫ g = (f ≫ (replacement q).i) ≫ (replacement q).p := by
    rw [Category.assoc, (replacement q).fac]
    exact h
  let F := comparisonTotal p (replacement q).p (f ≫ (replacement q).i) g hs
  have hF : (replacement p).p ≫ g = F ≫ (replacement q).p :=
    (comparisonTotal_projection p (replacement q).p
      (f ≫ (replacement q).i) g hs).symm
  change WeakEquivalence (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (replacement p).p (replacement q).p F g hF
      (SSet.yonedaEquiv.symm z) (SSet.yonedaEquiv.symm z ≫ g) rfl) ↔
    WeakEquivalence (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (replacement p).p (replacement q).p F g hF
      (SSet.yonedaEquiv.symm w) (SSet.yonedaEquiv.symm w ≫ g) rfl)
  exact FibrationSquareComponentFibers.fibreMap_weak_iff_of_component
    (replacement p).p (replacement q).p F g hF z w hz

/-- Transfer chosen-fiber weakness through a weak source square and component-surjective base. -/
theorem chosenMap_weak_all_of_composite {X Y Z B D H : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (r : Z ⟶ H)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (a : Y ⟶ Z) (c : D ⟶ H) (h' : q ≫ c = a ≫ r)
    [WeakEquivalence f] [WeakEquivalence g]
    (hg : Function.Surjective (SSet.mapπ₀ g))
    (hcomp : ∀ b : (Δ[0] : SSet.{0}) ⟶ B,
      WeakEquivalence (chosenMap p r (f ≫ a) (g ≫ c)
        (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])
        b (b ≫ (g ≫ c)) rfl))
    (d : (Δ[0] : SSet.{0}) ⟶ D) :
    WeakEquivalence (chosenMap q r a c h' d (d ≫ c) rfl) := by
  let w := SSet.yonedaEquiv d
  obtain ⟨u, hu⟩ := hg (SSet.π₀.mk w)
  obtain ⟨z, rfl⟩ := SSet.π₀.mk_surjective u
  let b : (Δ[0] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm z
  let d' := b ≫ g
  have hzw : SSet.π₀.mk (SSet.yonedaEquiv d') = SSet.π₀.mk w := by
    change SSet.π₀.mk (SSet.yonedaEquiv (b ≫ g)) = SSet.π₀.mk w
    rw [SSet.yonedaEquiv_comp, ← SSet.mapπ₀_mk]
    simpa only [b, Equiv.apply_symm_apply] using hu
  haveI : WeakEquivalence (chosenMap p q f g h b d' rfl) :=
    chosenMap_weak_of_weak_square p q f g h b d' rfl
  have hsq : p ≫ (g ≫ c) = (f ≫ a) ≫ r := by
    rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]
  haveI : WeakEquivalence (chosenMap p r (f ≫ a) (g ≫ c)
      hsq b (d' ≫ c) (by simp [d', Category.assoc])) := by
    convert hcomp b using 1
  have hd' : WeakEquivalence (chosenMap q r a c h' d' (d' ≫ c) rfl) :=
    chosenMap_weak_of_composite p q r f g h a c h' b d' (d' ≫ c) rfl rfl
      hsq rfl
  have hc := (chosenMap_weak_iff_of_component q r a c h'
    (SSet.yonedaEquiv d') w hzw).mp
  have hd_eq : SSet.yonedaEquiv.symm (SSet.yonedaEquiv d') = d' :=
    SSet.yonedaEquiv.symm_apply_apply d'
  rw [hd_eq] at hc
  have htarget_eq : SSet.yonedaEquiv.symm w = d :=
    SSet.yonedaEquiv.symm_apply_apply d
  rw [htarget_eq] at hc
  exact hc hd'

/-- Surjectivity on components descends to the fibration factor of a map. -/
theorem replacement_components_surjective {A B : SSet.{0}} (f : A ⟶ B)
    (hf : Function.Surjective (SSet.mapπ₀ f)) :
    Function.Surjective (SSet.mapπ₀ (replacement f).p) := by
  intro b
  obtain ⟨a, ha⟩ := hf b
  refine ⟨SSet.mapπ₀ (replacement f).i a, ?_⟩
  rw [← SSet.mapπ₀_comp_apply, (replacement f).fac]
  exact ha


private theorem replacement_unit_prod_components_surjective {A B : SSet.{0}}
    (f : A ⟶ B) [A.KanComplex] [B.KanComplex] :
    Function.Surjective (SSet.mapπ₀ (prod.map (replacement f).i (replacement f).i)) := by
  letI : Fibration (replacement f).p := (fibration_iff _).mpr (replacement f).hp
  letI : WeakEquivalence (replacement f).i :=
    (weakEquivalence_iff _).mpr (replacement f).hi.2
  letI : IsFibrant A := inferInstance
  letI : IsFibrant B := inferInstance
  letI : IsFibrant (replacement f).Z := isFibrant_of_fibration (replacement f).p
  letI : IsFibrant (A ⨯ A) := by
    haveI : Fibration (prod.fst : A ⨯ A ⟶ A) := inferInstance
    exact isFibrant_of_fibration (prod.fst : A ⨯ A ⟶ A)
  letI : IsFibrant ((replacement f).Z ⨯ (replacement f).Z) := by
    haveI : Fibration (prod.fst :
      (replacement f).Z ⨯ (replacement f).Z ⟶ (replacement f).Z) := inferInstance
    exact isFibrant_of_fibration (prod.fst :
      (replacement f).Z ⨯ (replacement f).Z ⟶ (replacement f).Z)
  letI : (A ⨯ A).KanComplex := inferInstance
  letI : ((replacement f).Z ⨯ (replacement f).Z).KanComplex := inferInstance
  haveI : WeakEquivalence (prod.map (replacement f).i (replacement f).i) :=
    prodMap_weak (replacement f).i
  exact ((SSet.weakEquivalence_iff_kanComplexW _).mp inferInstance).bijective_mapπ₀.surjective

variable {E B : SSet.{0}} (p : E ⟶ B)

/-- The diagonal into the chosen binary product of a simplicial set with itself. -/
def ordinaryDiagonal (X : SSet.{0}) : X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

private theorem ordinaryDiagonal_natural (f : E ⟶ B) :
    ordinaryDiagonal E ≫ prod.map f f = f ≫ ordinaryDiagonal B := by
  apply prod.hom_ext <;> simp [ordinaryDiagonal]

private abbrev pathProjection (B : SSet.{0}) :=
  (replacement (ordinaryDiagonal B)).p

private abbrev pathInclusion (B : SSet.{0}) :=
  (replacement (ordinaryDiagonal B)).i

private abbrev pathPullback (p : E ⟶ B) : SSet.{0} :=
  pullback (pathProjection B) (prod.map p p)

private def kernelToPath : pullback p p ⟶ pathPullback p :=
  pullback.lift
    (pullback.fst p p ≫ p ≫ pathInclusion B)
    (prod.lift (pullback.fst p p) (pullback.snd p p))
    (by
      simp only [Category.assoc, pathInclusion, pathProjection]
      rw [(replacement (ordinaryDiagonal B)).fac]
      apply prod.hom_ext
      · simp [ordinaryDiagonal]
      · simp [ordinaryDiagonal, pullback.condition])

private theorem kernelToPath_fst :
    kernelToPath p ≫ pullback.fst (pathProjection B) (prod.map p p) =
      pullback.fst p p ≫ p ≫ pathInclusion B := by
  simp [kernelToPath]

private theorem kernelToPath_snd :
    kernelToPath p ≫ pullback.snd (pathProjection B) (prod.map p p) =
      prod.lift (pullback.fst p p) (pullback.snd p p) := by
  simp [kernelToPath]

private theorem pathPullback_fst_fibration [Fibration p] :
    Fibration (pullback.fst (pathProjection B) (prod.map p p)) := by
  haveI : Fibration (prod.map p p) := inferInstance
  infer_instance

private def kernelToDiagonalPullback :
    pullback p p ⟶ pullback (prod.map p p) (ordinaryDiagonal B) :=
  pullback.lift (prod.lift (pullback.fst p p) (pullback.snd p p))
    (pullback.fst p p ≫ p) (by
      apply prod.hom_ext
      · simp [ordinaryDiagonal]
      · simp [ordinaryDiagonal, pullback.condition])

private def diagonalPullbackToKernel :
    pullback (prod.map p p) (ordinaryDiagonal B) ⟶ pullback p p :=
  pullback.lift
    (pullback.fst (prod.map p p) (ordinaryDiagonal B) ≫ prod.fst)
    (pullback.fst (prod.map p p) (ordinaryDiagonal B) ≫ prod.snd)
    (by
      have h := pullback.condition (f := prod.map p p) (g := ordinaryDiagonal B)
      have h₁ := congrArg (fun k ↦ k ≫ prod.fst) h
      have h₂ := congrArg (fun k ↦ k ≫ prod.snd) h
      have a : pullback.fst (prod.map p p) (ordinaryDiagonal B) ≫ prod.fst ≫ p =
          pullback.snd (prod.map p p) (ordinaryDiagonal B) := by
        simpa [ordinaryDiagonal, Category.assoc] using h₁
      have b : pullback.fst (prod.map p p) (ordinaryDiagonal B) ≫ prod.snd ≫ p =
          pullback.snd (prod.map p p) (ordinaryDiagonal B) := by
        simpa [ordinaryDiagonal, Category.assoc] using h₂
      exact a.trans b.symm)

private def kernelDiagonalPullbackIso :
    pullback p p ≅ pullback (prod.map p p) (ordinaryDiagonal B) where
  hom := kernelToDiagonalPullback p
  inv := diagonalPullbackToKernel p
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [kernelToDiagonalPullback, diagonalPullbackToKernel]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;>
        simp [kernelToDiagonalPullback, diagonalPullbackToKernel]
    · have h := congrArg (fun k ↦ k ≫ prod.fst)
        (pullback.condition (f := prod.map p p) (g := ordinaryDiagonal B))
      simpa [kernelToDiagonalPullback, diagonalPullbackToKernel, ordinaryDiagonal,
        Category.assoc] using h

private theorem kernelDiagonal_isPullback :
    IsPullback (prod.lift (pullback.fst p p) (pullback.snd p p))
      (pullback.fst p p ≫ p) (prod.map p p) (ordinaryDiagonal B) := by
  apply IsPullback.of_iso_pullback (by
    constructor
    apply prod.hom_ext <;> simp [ordinaryDiagonal, pullback.condition])
    (kernelDiagonalPullbackIso p)
  · simp [kernelDiagonalPullbackIso, kernelToDiagonalPullback]
  · simp [kernelDiagonalPullbackIso, kernelToDiagonalPullback]

private theorem kernelToPath_weak [Fibration p] : WeakEquivalence (kernelToPath p) := by
  haveI : Fibration (pullback.fst (pathProjection B) (prod.map p p)) :=
    pathPullback_fst_fibration p
  haveI : WeakEquivalence (pathInclusion B) :=
    (weakEquivalence_iff _).mpr (replacement (ordinaryDiagonal B)).hi.2
  have houter : IsPullback
      (kernelToPath p ≫ pullback.snd (pathProjection B) (prod.map p p))
      (pullback.fst p p ≫ p) (prod.map p p)
      (pathInclusion B ≫ pathProjection B) := by
    rw [(replacement (ordinaryDiagonal B)).fac]
    simpa only [kernelToPath_snd] using kernelDiagonal_isPullback p
  have hright : IsPullback
      (pullback.snd (pathProjection B) (prod.map p p))
      (pullback.fst (pathProjection B) (prod.map p p))
      (prod.map p p) (pathProjection B) :=
    (IsPullback.of_hasPullback (pathProjection B) (prod.map p p)).flip
  have hsq : IsPullback (kernelToPath p) (pullback.fst p p ≫ p)
      (pullback.fst (pathProjection B) (prod.map p p)) (pathInclusion B) :=
    houter.of_right (kernelToPath_fst p) hright
  exact DaggerSSetRightProper.weakEquivalence_of_isPullback hsq

private def relativeDiagonal : E ⟶ pullback p p :=
  pullback.lift (𝟙 E) (𝟙 E) (by simp)

private def pathCompare : E ⟶ pathPullback p :=
  pullback.lift (p ≫ pathInclusion B) (ordinaryDiagonal E) (by
    rw [Category.assoc, (replacement (ordinaryDiagonal B)).fac]
    exact (ordinaryDiagonal_natural p).symm)

private theorem relativeDiagonal_kernelToPath :
    relativeDiagonal p ≫ kernelToPath p = pathCompare p := by
  apply pullback.hom_ext
  · simp [relativeDiagonal, kernelToPath, pathCompare, Category.assoc]
  · apply prod.hom_ext <;>
      simp [relativeDiagonal, kernelToPath, pathCompare, ordinaryDiagonal,
        Category.assoc]

private theorem diagonal_path_square :
    ordinaryDiagonal E ≫ prod.map p p =
      (p ≫ pathInclusion B) ≫ pathProjection B := by
  rw [ordinaryDiagonal_natural, Category.assoc,
    (replacement (ordinaryDiagonal B)).fac]

private def pathTotalLift :
    (replacement (ordinaryDiagonal E)).Z ⟶ (replacement (ordinaryDiagonal B)).Z := by
  letI : Fibration (pathProjection B) :=
    (fibration_iff _).mpr (replacement (ordinaryDiagonal B)).hp
  exact comparisonTotal (ordinaryDiagonal E) (pathProjection B)
    (p ≫ pathInclusion B) (prod.map p p) (diagonal_path_square p)

private theorem pathTotalLift_i :
    (replacement (ordinaryDiagonal E)).i ≫ pathTotalLift p =
      p ≫ pathInclusion B := by
  letI : Fibration (pathProjection B) :=
    (fibration_iff _).mpr (replacement (ordinaryDiagonal B)).hp
  exact replacement_i_comparisonTotal (ordinaryDiagonal E) (pathProjection B)
    (p ≫ pathInclusion B) (prod.map p p) (diagonal_path_square p)

private theorem pathTotalLift_p :
    pathTotalLift p ≫ pathProjection B =
      (replacement (ordinaryDiagonal E)).p ≫ prod.map p p := by
  letI : Fibration (pathProjection B) :=
    (fibration_iff _).mpr (replacement (ordinaryDiagonal B)).hp
  exact comparisonTotal_projection (ordinaryDiagonal E) (pathProjection B)
    (p ≫ pathInclusion B) (prod.map p p) (diagonal_path_square p)

private def liftToPath : (replacement (ordinaryDiagonal E)).Z ⟶ pathPullback p :=
  pullback.lift (pathTotalLift p) (replacement (ordinaryDiagonal E)).p
    (pathTotalLift_p p)

private theorem liftToPath_fst :
    liftToPath p ≫ pullback.fst (pathProjection B) (prod.map p p) =
      pathTotalLift p := by simp [liftToPath]

private theorem liftToPath_snd :
    liftToPath p ≫ pullback.snd (pathProjection B) (prod.map p p) =
      (replacement (ordinaryDiagonal E)).p := by simp [liftToPath]

private theorem inclusion_liftToPath :
    (replacement (ordinaryDiagonal E)).i ≫ liftToPath p = pathCompare p := by
  apply pullback.hom_ext
  · simp [pathCompare, Category.assoc, liftToPath_fst, pathTotalLift_i]
  · simp [pathCompare, Category.assoc, liftToPath_snd,
      (replacement (ordinaryDiagonal E)).fac]

private theorem liftToPath_fiber_weak [Fibration p]
    (hdiag : ∀ b : (Δ[0] : SSet.{0}) ⟶ E ⨯ E,
      WeakEquivalence (chosenMap (ordinaryDiagonal E) (ordinaryDiagonal B)
        p (prod.map p p) (ordinaryDiagonal_natural p) b
        (b ≫ prod.map p p) rfl))
    (b : (Δ[0] : SSet.{0}) ⟶ E ⨯ E) :
    WeakEquivalence (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (replacement (ordinaryDiagonal E)).p
      (pullback.snd (pathProjection B) (prod.map p p))
      (liftToPath p) (𝟙 (E ⨯ E))
      (by simp [liftToPath_snd]) b b (by simp)) := by
  let q := pathProjection B
  let g := prod.map p p
  let ρ := pullback.snd q g
  let rp := (replacement (ordinaryDiagonal E)).p
  let F := liftToPath p
  have hF : rp ≫ 𝟙 (E ⨯ E) = F ≫ ρ := by
    simpa only [Category.comp_id] using (liftToPath_snd p).symm
  let u := DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    rp ρ F (𝟙 (E ⨯ E)) hF b b (by simp)
  have sq : IsPullback (pullback.fst ρ b ≫ pullback.fst q g)
      (pullback.snd ρ b) q (b ≫ g) :=
    (IsPullback.of_hasPullback ρ b).paste_horiz (IsPullback.of_hasPullback q g)
  let v := sq.isoPullback.hom
  have hv : u ≫ v = DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      rp q (pathTotalLift p) g (pathTotalLift_p p).symm b (b ≫ g) rfl := by
    apply pullback.hom_ext
    · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc]
      rw [DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
        Category.assoc, liftToPath_fst,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst]
    · rw [Category.assoc, sq.isoPullback_hom_snd]
      rw [DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
  have hw : WeakEquivalence (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      rp q (pathTotalLift p) g (pathTotalLift_p p).symm b (b ≫ g) rfl) := by
    change WeakEquivalence (chosenMap (ordinaryDiagonal E) (ordinaryDiagonal B)
      p g (ordinaryDiagonal_natural p) b (b ≫ g) rfl)
    exact hdiag b
  haveI : WeakEquivalence v := inferInstance
  have hu : WeakEquivalence u := weakEquivalence_of_postcomp_of_fac hv
  exact hu

private theorem pathCompare_weak_of_chosen_diagonal_fibers [Fibration p]
    (hdiag : ∀ b : (Δ[0] : SSet.{0}) ⟶ E ⨯ E,
      WeakEquivalence (chosenMap (ordinaryDiagonal E) (ordinaryDiagonal B)
        p (prod.map p p) (ordinaryDiagonal_natural p) b
        (b ≫ prod.map p p) rfl)) : WeakEquivalence (pathCompare p) := by
  letI : Fibration (replacement (ordinaryDiagonal E)).p :=
    (fibration_iff _).mpr (replacement (ordinaryDiagonal E)).hp
  letI : Fibration (pathProjection B) :=
    (fibration_iff _).mpr (replacement (ordinaryDiagonal B)).hp
  letI : Fibration (pullback.snd (pathProjection B) (prod.map p p)) := inferInstance
  have hF : (replacement (ordinaryDiagonal E)).p ≫ 𝟙 (E ⨯ E) =
      liftToPath p ≫ pullback.snd (pathProjection B) (prod.map p p) := by
    simpa only [Category.comp_id] using (liftToPath_snd p).symm
  have hweak : WeakEquivalence (liftToPath p) :=
    FibrationSquareWeakRecognition.weak_of_weak_base_and_vertex_fibers
      (replacement (ordinaryDiagonal E)).p
      (pullback.snd (pathProjection B) (prod.map p p))
      (liftToPath p) (𝟙 (E ⨯ E)) hF
      (fun b ↦ liftToPath_fiber_weak p hdiag b)
  haveI : WeakEquivalence (replacement (ordinaryDiagonal E)).i :=
    (weakEquivalence_iff _).mpr (replacement (ordinaryDiagonal E)).hi.2
  haveI : WeakEquivalence (liftToPath p) := hweak
  rw [← inclusion_liftToPath p]
  infer_instance

private theorem relativeDiagonal_weak_of_pathCompare_weak
    [Fibration p] [WeakEquivalence (pathCompare p)] : WeakEquivalence (relativeDiagonal p) := by
  haveI : WeakEquivalence (kernelToPath p) := kernelToPath_weak p
  exact weakEquivalence_of_postcomp_of_fac (relativeDiagonal_kernelToPath p)

private theorem relativeDiagonal_fst : relativeDiagonal p ≫ pullback.fst p p = 𝟙 E := by
  simp [relativeDiagonal]

private theorem fst_weak_of_relativeDiagonal_weak
    [WeakEquivalence (relativeDiagonal p)] :
    WeakEquivalence (pullback.fst p p) :=
  weakEquivalence_of_precomp_of_fac (relativeDiagonal_fst p)

private def relativeFiberComparison (e : (Δ[0] : SSet.{0}) ⟶ E) :
    pullback (pullback.fst p p) e ⟶ pullback p (e ≫ p) :=
  pullback.lift
    (pullback.fst (pullback.fst p p) e ≫ pullback.snd p p)
    (pullback.snd (pullback.fst p p) e)
    (by
      rw [Category.assoc, ← pullback.condition]
      rw [← Category.assoc, pullback.condition, Category.assoc])

private def relativeFiberComparisonInv (e : (Δ[0] : SSet.{0}) ⟶ E) :
    pullback p (e ≫ p) ⟶ pullback (pullback.fst p p) e :=
  pullback.lift
    (pullback.lift
      (pullback.snd p (e ≫ p) ≫ e)
      (pullback.fst p (e ≫ p))
      (by rw [Category.assoc, ← pullback.condition]))
    (pullback.snd p (e ≫ p))
    (by simp)

private theorem relativeFiberComparison_left_inv (e : (Δ[0] : SSet.{0}) ⟶ E) :
    relativeFiberComparison p e ≫ relativeFiberComparisonInv p e =
      𝟙 (pullback (pullback.fst p p) e) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [relativeFiberComparison, relativeFiberComparisonInv, Category.assoc,
        pullback.condition]
    · simp [relativeFiberComparison, relativeFiberComparisonInv]
  · simp [relativeFiberComparison, relativeFiberComparisonInv]

private theorem relativeFiberComparison_right_inv (e : (Δ[0] : SSet.{0}) ⟶ E) :
    relativeFiberComparisonInv p e ≫ relativeFiberComparison p e =
      𝟙 (pullback p (e ≫ p)) := by
  apply pullback.hom_ext <;>
    simp [relativeFiberComparison, relativeFiberComparisonInv]

private theorem relativeFiberComparison_isIso (e : (Δ[0] : SSet.{0}) ⟶ E) :
    IsIso (relativeFiberComparison p e) :=
  ⟨⟨relativeFiberComparisonInv p e,
    relativeFiberComparison_left_inv p e,
    relativeFiberComparison_right_inv p e⟩⟩

private theorem relativeFiberProjection_weak
    [Fibration p] [WeakEquivalence (relativeDiagonal p)]
    (e : (Δ[0] : SSet.{0}) ⟶ E) :
    WeakEquivalence (pullback.snd p (e ≫ p)) := by
  haveI : WeakEquivalence (pullback.fst p p) :=
    fst_weak_of_relativeDiagonal_weak p
  letI : (trivialFibrations SSet.{0}).IsStableUnderBaseChange := by
    rw [← rlp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    infer_instance
  have hr : trivialFibrations SSet.{0} (pullback.fst p p) :=
    (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
  haveI : WeakEquivalence (pullback.snd (pullback.fst p p) e) :=
    (mem_trivialFibrations_iff _).mp
      ((trivialFibrations SSet.{0}).pullback_snd _ _ hr) |>.2
  haveI : IsIso (relativeFiberComparison p e) :=
    relativeFiberComparison_isIso p e
  have h : relativeFiberComparison p e ≫ pullback.snd p (e ≫ p) =
      pullback.snd (pullback.fst p p) e := by
    simp [relativeFiberComparison]
  exact weakEquivalence_of_precomp_of_fac h


/-- A surjective Kan fibration with weak relative diagonal is weak. -/
private theorem weak_of_relativeDiagonal_weak
    [Fibration p] [WeakEquivalence (relativeDiagonal p)]
    (hp : Function.Surjective (SSet.mapπ₀ p)) : WeakEquivalence p := by
  apply DaggerNativeFibrationWeakFromVertexFibres.weak_of_vertex_fibres_weak p
  intro b
  obtain ⟨e, he⟩ := DaggerNativeFibrationSurjectiveComponents.vertices_surjective_of_components
    p hp (SSet.yonedaEquiv b)
  let e' : (Δ[0] : SSet.{0}) ⟶ E := SSet.yonedaEquiv.symm e
  have h : e' ≫ p = b := by
    apply SSet.yonedaEquiv.injective
    simpa only [e', SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using he
  rw [← h]
  exact relativeFiberProjection_weak p e'


/-- Recognition for a component-surjective Kan fibration from chosen diagonal fibers. -/
theorem weak_fibration_of_chosen_diagonal_fibers [Fibration p]
    (hp : Function.Surjective (SSet.mapπ₀ p))
    (hdiag : ∀ b : (Δ[0] : SSet.{0}) ⟶ E ⨯ E,
      WeakEquivalence (chosenMap (ordinaryDiagonal E) (ordinaryDiagonal B)
        p (prod.map p p) (ordinaryDiagonal_natural p) b
        (b ≫ prod.map p p) rfl)) : WeakEquivalence p := by
  haveI : WeakEquivalence (pathCompare p) :=
    pathCompare_weak_of_chosen_diagonal_fibers p hdiag
  haveI : WeakEquivalence (relativeDiagonal p) :=
    relativeDiagonal_weak_of_pathCompare_weak p
  exact weak_of_relativeDiagonal_weak p hp


/-- Chosen diagonal homotopy-fiber equivalences and π₀-surjectivity detect weak equivalences. -/
theorem weak_of_chosen_diagonal_fibers {A B : SSet.{0}} (f : A ⟶ B)
    [A.KanComplex] [B.KanComplex]
    (hπ : Function.Surjective (SSet.mapπ₀ f))
    (hdiag : ∀ b : (Δ[0] : SSet.{0}) ⟶ A ⨯ A,
      WeakEquivalence (chosenMap (ordinaryDiagonal A) (ordinaryDiagonal B)
        f (prod.map f f) (ordinaryDiagonal_natural f) b
        (b ≫ prod.map f f) rfl)) : WeakEquivalence f := by
  let E := (replacement f).Z
  let i : A ⟶ E := (replacement f).i
  let p : E ⟶ B := (replacement f).p
  letI : Fibration p := (fibration_iff _).mpr (replacement f).hp
  letI : WeakEquivalence i := (weakEquivalence_iff _).mpr (replacement f).hi.2
  letI : IsFibrant A := inferInstance
  letI : IsFibrant B := inferInstance
  letI : IsFibrant E := isFibrant_of_fibration p
  haveI : WeakEquivalence (prod.map i i) := prodMap_weak i
  have hg : Function.Surjective (SSet.mapπ₀ (prod.map i i)) :=
    replacement_unit_prod_components_surjective f
  have hcomp : ∀ b : (Δ[0] : SSet.{0}) ⟶ A ⨯ A,
      WeakEquivalence (chosenMap (ordinaryDiagonal A) (ordinaryDiagonal B)
        (i ≫ p) (prod.map i i ≫ prod.map p p)
        (by rw [← Category.assoc, ordinaryDiagonal_natural i,
          Category.assoc, ordinaryDiagonal_natural p, ← Category.assoc])
        b (b ≫ (prod.map i i ≫ prod.map p p)) rfl) := by
    intro b
    have hif : i ≫ p = f := (replacement f).fac
    have hgp : prod.map i i ≫ prod.map p p = prod.map f f := by
      rw [prod.map_map, hif]
    letI : WeakEquivalence (chosenMap (ordinaryDiagonal A) (ordinaryDiagonal B)
        f (prod.map f f) (ordinaryDiagonal_natural f) b
        (b ≫ prod.map f f) rfl) := hdiag b
    exact chosenMap_weak_congr (ordinaryDiagonal A) (ordinaryDiagonal B)
      (i ≫ p) f (prod.map i i ≫ prod.map p p) (prod.map f f)
      hif hgp _ (ordinaryDiagonal_natural f) b
  have hE : ∀ b : (Δ[0] : SSet.{0}) ⟶ E ⨯ E,
      WeakEquivalence (chosenMap (ordinaryDiagonal E) (ordinaryDiagonal B)
        p (prod.map p p) (ordinaryDiagonal_natural p) b
        (b ≫ prod.map p p) rfl) :=
    chosenMap_weak_all_of_composite
      (ordinaryDiagonal A) (ordinaryDiagonal E) (ordinaryDiagonal B)
      i (prod.map i i) (ordinaryDiagonal_natural i)
      p (prod.map p p) (ordinaryDiagonal_natural p)
      hg hcomp
  have hpπ : Function.Surjective (SSet.mapπ₀ p) :=
    replacement_components_surjective f hπ
  haveI : WeakEquivalence p := weak_fibration_of_chosen_diagonal_fibers p hpπ hE
  rw [← (replacement f).fac]
  infer_instance

end
end DaggerModels.PartII.DiagonalRecognition
