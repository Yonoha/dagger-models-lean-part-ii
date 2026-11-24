import DaggerModelsPartII.LengthStageCellData
import DaggerModelsPartII.CellBoundaryGeometry
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.LengthStageAttaching

open PathOrbitCells CharacteristicComposite CharacteristicInterior
open CharacteristicQuotient CharacteristicOuterBoundary
open FreeDaggerPathChains DaggerNerveLengthFiltration
open ChainPathCoverage ReversalOuterFaceSubobject
open ReversalOuterFaceAction ReversalRepresentableFixedPoints
open DiscreteBorelDiagram C2InvolutionActions CellBoundaryGeometry

noncomputable section

private theorem isPushout_of_pointwise
    {K C : Type*} [Category K] [Category C]
    {A B D E : K ⥤ C} {t : A ⟶ B} {l : A ⟶ D}
    {r : B ⟶ E} {b : D ⟶ E}
    (h : ∀ k : K, IsPushout (t.app k) (l.app k) (r.app k) (b.app k)) :
    IsPushout t l r b := by
  have w : t ≫ r = l ≫ b := by
    ext k
    exact (h k).w
  apply IsPushout.of_isColimit (c := PushoutCocone.mk r b w)
  apply evaluationJointlyReflectsColimits
  intro k
  exact (isColimitMapCoconePushoutCoconeEquiv
    ((evaluation K C).obj k) w).symm (by
      change IsColimit (h k).cocone
      exact (h k).isColimit)

private theorem types_isPushout_of_boundary_data
    {A B C D : Type 0} (t : A ⟶ B) (l : A ⟶ C)
    (r : B ⟶ D) (b : C ⟶ D)
    (hw : ∀ a, r (t a) = b (l a))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hpre : ∀ c : C, (∃ x : B, r x = b c) ↔ ∃ a : A, l a = c)
    (hcover : ∀ d : D, (∃ x : B, r x = d) ∨ (∃ c : C, b c = d))
    (hinterior : ∀ c d : C,
      (¬ ∃ a : A, l a = c) → (¬ ∃ a : A, l a = d) →
        b c = b d → c = d) :
    IsPushout t l r b := by
  haveI : Mono r := (mono_iff_injective r).mpr hr
  have hpb : IsPullback t l r b := by
    apply (Types.isPullback_iff (t := t) (l := l) (r := r) (b := b)).mpr
    refine ⟨by funext a; exact hw a, ?_, ?_⟩
    · intro x y hxy
      exact hl hxy.2
    · intro x c hxc
      obtain ⟨a, ha⟩ := (hpre c).mp ⟨x, hxc⟩
      refine ⟨a, ?_, ha⟩
      apply hr
      calc
        r (t a) = b (l a) := hw a
        _ = b c := congrArg b ha
        _ = r x := hxc.symm
  have hsurj : Set.range r ⊔ Set.range b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro d
    simpa only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ] using
      hcover d
  exact Types.isPushout_of_isPullback_of_mono' hpb hsurj hinterior

private theorem wordCharacteristic_apply_cast {m ℓ : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (h : letterLength p = ℓ) {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) :
    (wordCharacteristic (⟨Arrow.mk p, h⟩ : Word m ℓ)).app (op k)
        (h ▸ φ) = (characteristic p).app (op k) φ := by
  cases h
  rfl

private theorem wordCharacteristic_dagger {m ℓ : ℕ} (w : Word m ℓ) :
    wordCharacteristic (daggerWord w) =
      yoneda.map (ReverseSimplex.reversal (⟨ℓ⟩ : ReverseSimplex)) ≫
        wordCharacteristic w := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact characteristic_dagger p.hom

private theorem wordStageCharacteristic_ι {m ℓ : ℕ} (w : Word m ℓ) :
    wordStageCharacteristic w ≫ (lengthFiltration m ℓ).ι =
      wordCharacteristic w := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact stageCharacteristic_ι p.hom

private theorem wordCharacteristic_dagger_apply {m ℓ : ℕ}
    (w : Word m ℓ) {k : ReverseSimplex}
    (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex)) :
    (wordCharacteristic (daggerWord w)).app (op k) φ =
      (wordCharacteristic w).app (op k) (flip φ) := by
  have h := congrFun (NatTrans.congr_app (wordCharacteristic_dagger w) (op k)) φ
  simpa only [NatTrans.comp_app, yoneda_map_app,
    ReversalRepresentableFixedPoints.flip] using h

private theorem wordStageCharacteristic_dagger_apply {m ℓ : ℕ}
    (w : Word m ℓ) {k : ReverseSimplex}
    (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex)) :
    (wordStageCharacteristic (daggerWord w)).app (op k) φ =
      (wordStageCharacteristic w).app (op k) (flip φ) := by
  apply Subtype.ext
  have hleft := congrFun (NatTrans.congr_app
    (wordStageCharacteristic_ι (daggerWord w)) (op k)) φ
  have hright := congrFun (NatTrans.congr_app
    (wordStageCharacteristic_ι w) (op k)) (flip φ)
  exact hleft.trans ((wordCharacteristic_dagger_apply w φ).trans hright.symm)

private def wordOfChain {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) : Word m ℓ :=
  ⟨Arrow.mk (fullPath F), (totalLength_eq_fullPath F).symm.trans hF⟩

private def chainParameter {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) :
    (⟨k⟩ : ReverseSimplex) ⟶ (⟨ℓ⟩ : ReverseSimplex) :=
  (wordOfChain F hF).property ▸ prefixParameter F

private theorem wordCharacteristic_covers_chain {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) :
    (wordCharacteristic (wordOfChain F hF)).app
      (op (⟨k⟩ : ReverseSimplex)) (chainParameter F hF) = F := by
  exact (wordCharacteristic_apply_cast (fullPath F)
    (wordOfChain F hF).property (prefixParameter F)).trans
    (characteristic_covers_chain F)

private def stageChain {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) :
    (lengthFiltration m ℓ).toFunctor.obj (op (⟨k⟩ : ReverseSimplex)) :=
  ⟨F, le_of_eq hF⟩

private theorem wordStageCharacteristic_covers_chain {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) :
    (wordStageCharacteristic (wordOfChain F hF)).app
      (op (⟨k⟩ : ReverseSimplex)) (chainParameter F hF) = stageChain F hF := by
  apply Subtype.ext
  have h := congrFun (NatTrans.congr_app
    (wordStageCharacteristic_ι (wordOfChain F hF))
    (op (⟨k⟩ : ReverseSimplex))) (chainParameter F hF)
  exact h.trans (wordCharacteristic_covers_chain F hF)

private theorem stageCharacteristic_preceding_iff_boundary
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p) (k : ReverseSimplex)
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) :
    (∃ y : (lengthFiltration m (letterLength p - 1)).toFunctor.obj (op k),
      (Subfunctor.homOfLe
        (lengthFiltration_mono m (Nat.sub_le (letterLength p) 1))).app (op k) y =
        (stageCharacteristic p).app (op k) φ) ↔
      φ ∈ (outerFaceSubpresheafAt (letterLength p) hp).obj (op k) := by
  rw [mem_outerFace_iff_not_interior hp φ]
  have hlen := characteristic_totalLength_eq_iff_interior p hp φ
  change totalLength k.len m
    ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) =
        letterLength p ↔ Interior φ at hlen
  have hbound := (totalLength_extensionMap m φ (letterChain p)).trans_eq
    (totalLength_letterChain p)
  constructor
  · rintro ⟨y, hy⟩ hφ
    have hshort : totalLength k.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤
          letterLength p - 1 := by
      have heq := congrArg Subtype.val hy
      change y.val = (characteristic p).app (op k) φ at heq
      rw [characteristic_app] at heq
      change y.val =
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap φ (letterChain p) at heq
      rw [← heq]
      exact y.property
    have hfull := hlen.mpr hφ
    omega
  · intro hnot
    have hshort : totalLength k.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤
          letterLength p - 1 := by
      have hne : totalLength k.len m
          ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≠
              letterLength p := fun h => hnot (hlen.mp h)
      omega
    refine ⟨⟨(characteristic p).app (op k) φ, ?_⟩, ?_⟩
    · rw [characteristic_app]
      exact hshort
    · apply Subtype.ext
      rfl

private theorem wordStage_preceding_iff_boundary
    {m ℓ : ℕ} (hℓ : 2 ≤ ℓ) (w : Word m ℓ)
    (k : ReverseSimplex)
    (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex)) :
    (∃ y : (lengthFiltration m (ℓ - 1)).toFunctor.obj (op k),
      (stageInclusion m ℓ).app (op k) y =
        (wordStageCharacteristic w).app (op k) φ) ↔
      φ ∈ (outerFaceSubpresheafAt ℓ (by omega : 1 ≤ ℓ)).obj (op k) := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact stageCharacteristic_preceding_iff_boundary p.hom (by omega) k φ

private theorem wordStageOrbit_preceding_iff_boundary
    {m ℓ : ℕ} (hℓ : 2 ≤ ℓ) (w : Word m ℓ)
    (hw : Palindromic w) (k : ReverseSimplex)
    (q : (representableOrbitPresheaf ℓ).obj (op k)) :
    (∃ y : (lengthFiltration m (ℓ - 1)).toFunctor.obj (op k),
      (stageInclusion m ℓ).app (op k) y =
        (palStageTypeMap w hw).app (op k) q) ↔
      q ∈ Set.range ((boundaryOrbitTypeInclusion ℓ (by omega : 1 ≤ ℓ)).app (op k)) := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact stageCharacteristicOrbitMap_preceding_iff_boundary p.hom
      (by omega) (wordPal_arrow ⟨p, rfl⟩ hw) k q

private theorem boundaryOrbitTypeInclusion_injective
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (k : ReverseSimplex) :
    Function.Injective ((boundaryOrbitTypeInclusion ℓ hℓ).app (op k)) := by
  change Function.Injective (boundaryOrbitInclusionPoint ℓ hℓ k)
  exact DiscreteOrbitSubobject.orbitInclusion_injective _ _ _ _

private theorem boundaryToCell_injective
    (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (k : ReverseSimplex) :
    Function.Injective ((boundaryToCell m ℓ hℓ).app (op k)) := by
  intro x y hxy
  rcases x with ⟨r, φ⟩ | ⟨s, q⟩ <;>
    rcases y with ⟨r', φ'⟩ | ⟨s', q'⟩
  · change Sum.inl (r, φ.val) = Sum.inl (r', φ'.val) at hxy
    have h := Sum.inl.inj hxy
    have hr := congrArg Prod.fst h
    have hφ := congrArg Prod.snd h
    cases hr
    exact congrArg Sum.inl (Prod.ext rfl (Subtype.ext hφ))
  · cases hxy
  · cases hxy
  · change Sum.inr (s, (boundaryOrbitTypeInclusion ℓ hℓ).app (op k) q) =
      Sum.inr (s', (boundaryOrbitTypeInclusion ℓ hℓ).app (op k) q') at hxy
    have h := Sum.inr.inj hxy
    have hs := congrArg Prod.fst h
    have hq := congrArg Prod.snd h
    cases hs
    exact congrArg Sum.inr (Prod.ext rfl
      ((boundaryOrbitTypeInclusion_injective ℓ hℓ k) hq))

private theorem stageInclusion_injective
    (m ℓ : ℕ) (k : ReverseSimplex) :
    Function.Injective ((stageInclusion m ℓ).app (op k)) := by
  intro x y h
  have hv := congrArg
    (fun z : (lengthFiltration m ℓ).toFunctor.obj (op k) => z.val) h
  exact Subtype.ext hv

private theorem cell_preimage_iff_boundary
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex)
    (c : (cellPresheaf m ℓ).obj (op k)) :
    (∃ y : (lengthFiltration m (ℓ - 1)).toFunctor.obj (op k),
      (stageInclusion m ℓ).app (op k) y =
        (cellToStage m ℓ).app (op k) c) ↔
      ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
        (boundaryToCell m ℓ (by omega)).app (op k) a = c := by
  constructor
  · intro h
    rcases c with ⟨r, φ⟩ | ⟨s, q⟩
    · have hmem := (wordStage_preceding_iff_boundary hℓ
        (representative r.val) k φ).mp h
      refine ⟨Sum.inl (r, ⟨φ, hmem⟩), ?_⟩
      rfl
    · obtain ⟨v, hv⟩ := (wordStageOrbit_preceding_iff_boundary hℓ
        (representative s.val) s.property k q).mp h
      refine ⟨Sum.inr (s, v), ?_⟩
      change Sum.inr (s, (boundaryOrbitTypeInclusion ℓ (by omega)).app (op k) v) =
        Sum.inr (s, q)
      rw [hv]
  · rintro ⟨a, ha⟩
    refine ⟨(boundaryToPrevious m ℓ hℓ).app (op k) a, ?_⟩
    have hs := congrFun (NatTrans.congr_app (boundary_square m ℓ hℓ) (op k)) a
    change (stageInclusion m ℓ).app (op k)
        ((boundaryToPrevious m ℓ hℓ).app (op k) a) =
      (cellToStage m ℓ).app (op k)
        ((boundaryToCell m ℓ (by omega)).app (op k) a) at hs
    rw [ha] at hs
    exact hs

private theorem palStageTypeMap_orbitClass {m ℓ : ℕ}
    (w : Word m ℓ) (hw : Palindromic w)
    {k : ReverseSimplex} (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex)) :
    (palStageTypeMap w hw).app (op k) (orbitClass ℓ φ) =
      (wordStageCharacteristic w).app (op k) φ := by
  cases w with
  | mk p hlen =>
    cases hlen
    rfl

private theorem cell_covers_exact_chain {k m ℓ : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F = ℓ) :
    ∃ c : (cellPresheaf m ℓ).obj (op (⟨k⟩ : ReverseSimplex)),
      (cellToStage m ℓ).app (op (⟨k⟩ : ReverseSimplex)) c =
        stageChain F hF := by
  let w := wordOfChain F hF
  let φ := chainParameter F hF
  let r := PathOrbitCells.orbit w
  have hcover := representative_cover w
  by_cases hpal : OrbitPalindromic r
  · let s : PalOrbit m ℓ := ⟨r, hpal⟩
    rcases hcover with hw | hw
    · refine ⟨Sum.inr (s, orbitClass ℓ φ), ?_⟩
      change (palStageTypeMap (representative r) hpal).app
        (op (⟨k⟩ : ReverseSimplex)) (orbitClass ℓ φ) = stageChain F hF
      rw [palStageTypeMap_orbitClass, ← hw]
      exact wordStageCharacteristic_covers_chain F hF
    · refine ⟨Sum.inr (s, orbitClass ℓ (flip φ)), ?_⟩
      change (palStageTypeMap (representative r) hpal).app
        (op (⟨k⟩ : ReverseSimplex)) (orbitClass ℓ (flip φ)) = stageChain F hF
      rw [palStageTypeMap_orbitClass]
      have hdag := wordStageCharacteristic_dagger_apply (representative r) φ
      have hcoverF := wordStageCharacteristic_covers_chain F hF
      change (wordStageCharacteristic w).app
        (op (⟨k⟩ : ReverseSimplex)) φ = stageChain F hF at hcoverF
      rw [hw] at hcoverF
      exact hdag.symm.trans hcoverF
  · let s : NonpalOrbit m ℓ := ⟨r, hpal⟩
    rcases hcover with hw | hw
    · refine ⟨Sum.inl (s, φ), ?_⟩
      change (wordStageCharacteristic (representative r)).app
        (op (⟨k⟩ : ReverseSimplex)) φ = stageChain F hF
      rw [← hw]
      exact wordStageCharacteristic_covers_chain F hF
    · refine ⟨Sum.inl (s, flip φ), ?_⟩
      change (wordStageCharacteristic (representative r)).app
        (op (⟨k⟩ : ReverseSimplex)) (flip φ) = stageChain F hF
      have hdag := wordStageCharacteristic_dagger_apply (representative r) φ
      rw [← hw] at hdag
      exact hdag.symm.trans (wordStageCharacteristic_covers_chain F hF)

private theorem stage_jointly_covered (m ℓ : ℕ) (k : ReverseSimplex)
    (x : (lengthFiltration m ℓ).toFunctor.obj (op k)) :
    (∃ y : (lengthFiltration m (ℓ - 1)).toFunctor.obj (op k),
      (stageInclusion m ℓ).app (op k) y = x) ∨
    (∃ c : (cellPresheaf m ℓ).obj (op k),
      (cellToStage m ℓ).app (op k) c = x) := by
  by_cases hshort : totalLength k.len m x.val ≤ ℓ - 1
  · left
    refine ⟨⟨x.val, hshort⟩, ?_⟩
    exact Subtype.ext rfl
  · right
    have hfull : totalLength k.len m x.val = ℓ := by
      have hbound := x.property
      change totalLength k.len m x.val ≤ ℓ at hbound
      omega
    obtain ⟨c, hc⟩ := cell_covers_exact_chain x.val hfull
    refine ⟨c, ?_⟩
    exact hc.trans (Subtype.ext rfl)

private theorem nonpal_interior_of_outside
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex)
    (r : NonpalOrbit m ℓ)
    (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex))
    (hout : ¬ ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
      (boundaryToCell m ℓ (by omega)).app (op k) a = Sum.inl (r, φ)) :
    Interior φ := by
  by_contra hnot
  have hface := (mem_outerFace_iff_not_interior (by omega : 1 ≤ ℓ) φ).mpr hnot
  apply hout
  exact ⟨Sum.inl (r, ⟨φ, hface⟩), rfl⟩

private theorem pal_interior_of_outside
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex)
    (s : PalOrbit m ℓ)
    (q : (representableOrbitPresheaf ℓ).obj (op k))
    (hout : ¬ ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
      (boundaryToCell m ℓ (by omega)).app (op k) a = Sum.inr (s, q)) :
    q ∈ InteriorOrbit ℓ k := by
  by_contra hnot
  have hboundary := (boundaryOrbitInclusionPoint_range_iff_not_interior
    ℓ (by omega : 1 ≤ ℓ) k q).mpr hnot
  obtain ⟨v, hv⟩ := hboundary
  apply hout
  refine ⟨Sum.inr (s, v), ?_⟩
  change Sum.inr (s, (boundaryOrbitTypeInclusion ℓ (by omega)).app (op k) v) =
    Sum.inr (s, q)
  change (boundaryOrbitTypeInclusion ℓ (by omega)).app (op k) v = q at hv
  rw [hv]

private theorem wordCharacteristic_interior_composite
    {m ℓ : ℕ} (w : Word m ℓ) {k : ReverseSimplex}
    (φ : k ⟶ (⟨ℓ⟩ : ReverseSimplex)) (hφ : Interior φ) :
    compositeArrow ((wordCharacteristic w).app (op k) φ) = w.val ∨
      compositeArrow ((wordCharacteristic w).app (op k) φ) =
        daggerArrow w.val := by
  cases w with
  | mk p hlen =>
    cases hlen
    simpa only [Arrow.mk_eq] using
      characteristic_interior_composite p.hom φ hφ

private theorem wordOrbit_eq_of_interior_image_eq
    {m ℓ : ℕ} (u v : Word m ℓ) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨ℓ⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ)
    (heq : (wordCharacteristic u).app (op k) φ =
      (wordCharacteristic v).app (op k) ψ) :
    PathOrbitCells.orbit u = PathOrbitCells.orbit v := by
  have hc := congrArg compositeArrow heq
  rcases wordCharacteristic_interior_composite u φ hφ with hu | hu <;>
    rcases wordCharacteristic_interior_composite v ψ hψ with hv | hv
  · apply (PathOrbitCells.orbit_eq_iff u v).mpr
    exact Or.inl (Subtype.ext (hu.symm.trans (hc.trans hv)))
  · apply (PathOrbitCells.orbit_eq_iff u v).mpr
    exact Or.inr (Subtype.ext (hu.symm.trans (hc.trans hv)))
  · apply (PathOrbitCells.orbit_eq_iff u v).mpr
    have h := congrArg daggerArrow (hu.symm.trans (hc.trans hv))
    exact Or.inr (Subtype.ext (by
      simpa only [daggerArrow_involutive m u.val] using h))
  · apply (PathOrbitCells.orbit_eq_iff u v).mpr
    have h := congrArg daggerArrow (hu.symm.trans (hc.trans hv))
    exact Or.inl (Subtype.ext (by
      simpa only [daggerArrow_involutive m u.val,
        daggerArrow_involutive m v.val] using h))

private theorem wordCharacteristic_injective_of_nonpal
    {m ℓ : ℕ} (w : Word m ℓ) (hℓ : 2 ≤ ℓ)
    (hnot : ¬ Palindromic w) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨ℓ⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ)
    (heq : (wordCharacteristic w).app (op k) φ =
      (wordCharacteristic w).app (op k) ψ) : φ = ψ := by
  have hnotarrow : Arrow.mk w.val.hom ≠ daggerArrow (Arrow.mk w.val.hom) := by
    intro hpal
    apply hnot
    apply Subtype.ext
    simpa only [Arrow.mk_eq] using hpal.symm
  cases w with
  | mk p hlen =>
    cases hlen
    exact characteristic_interior_injective_of_nonpal p.hom
      (by omega) hnotarrow φ ψ hφ hψ heq

private theorem palStage_injOn_interior
    {m ℓ : ℕ} (w : Word m ℓ) (hℓ : 2 ≤ ℓ)
    (hw : Palindromic w) (k : ReverseSimplex) :
    Set.InjOn ((palStageTypeMap w hw).app (op k)) (InteriorOrbit ℓ k) := by
  cases w with
  | mk p hlen =>
    cases hlen
    intro q hq q' hq' heq
    obtain ⟨φ, hφ, rfl⟩ := hq
    obtain ⟨ψ, hψ, rfl⟩ := hq'
    rw [palStageTypeMap_orbitClass, palStageTypeMap_orbitClass] at heq
    have h := congrArg Subtype.val heq
    change (characteristic p.hom).app (op k) φ =
      (characteristic p.hom).app (op k) ψ at h
    exact characteristicOrbitMap_injective_on_interior p.hom (by omega)
      (wordPal_arrow ⟨p, rfl⟩ hw) φ ψ hφ hψ h

private def cellOrbit {m ℓ : ℕ} {k : ReverseSimplex}
    (c : (cellPresheaf m ℓ).obj (op k)) : WordOrbit m ℓ :=
  match c with
  | Sum.inl (r, _) => r.val
  | Sum.inr (s, _) => s.val

private def cellInterior {m ℓ : ℕ} {k : ReverseSimplex}
    (c : (cellPresheaf m ℓ).obj (op k)) : Prop :=
  match c with
  | Sum.inl (_, φ) => Interior φ
  | Sum.inr (_, q) => q ∈ InteriorOrbit ℓ k

private theorem stageValues_eq_wordCharacteristic_eq
    {m ℓ : ℕ} (u v : Word m ℓ) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨ℓ⟩ : ReverseSimplex))
    (heq : (wordStageCharacteristic u).app (op k) φ =
      (wordStageCharacteristic v).app (op k) ψ) :
    (wordCharacteristic u).app (op k) φ =
      (wordCharacteristic v).app (op k) ψ := by
  have hu := congrFun (NatTrans.congr_app (wordStageCharacteristic_ι u) (op k)) φ
  have hv := congrFun (NatTrans.congr_app (wordStageCharacteristic_ι v) (op k)) ψ
  have hh := congrArg
    (fun z : (lengthFiltration m ℓ).toFunctor.obj (op k) => z.val) heq
  exact hu.symm.trans (hh.trans hv)

private theorem cellInterior_of_outside
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex)
    (c : (cellPresheaf m ℓ).obj (op k))
    (hout : ¬ ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
      (boundaryToCell m ℓ (by omega)).app (op k) a = c) :
    cellInterior c := by
  rcases c with ⟨r, φ⟩ | ⟨s, q⟩
  · exact nonpal_interior_of_outside m ℓ hℓ k r φ hout
  · exact pal_interior_of_outside m ℓ hℓ k s q hout

private theorem cellOrbit_of_interior_image_eq
    (m ℓ : ℕ) (k : ReverseSimplex)
    (c d : (cellPresheaf m ℓ).obj (op k))
    (hc : cellInterior c) (hd : cellInterior d)
    (heq : (cellToStage m ℓ).app (op k) c =
      (cellToStage m ℓ).app (op k) d) :
    cellOrbit c = cellOrbit d := by
  rcases c with ⟨r, φ⟩ | ⟨r, q⟩ <;>
    rcases d with ⟨s, ψ⟩ | ⟨s, q'⟩
  · change (wordStageCharacteristic (representative r.val)).app (op k) φ =
      (wordStageCharacteristic (representative s.val)).app (op k) ψ at heq
    have hv := stageValues_eq_wordCharacteristic_eq
      (representative r.val) (representative s.val) φ ψ heq
    have h := wordOrbit_eq_of_interior_image_eq
      (representative r.val) (representative s.val) φ ψ hc hd hv
    simpa only [PathOrbitCells.orbit_representative] using h
  · obtain ⟨ψ, hψ, hq'⟩ := hd
    change (wordStageCharacteristic (representative r.val)).app (op k) φ =
      (palStageTypeMap (representative s.val) s.property).app (op k) q' at heq
    rw [← hq', palStageTypeMap_orbitClass] at heq
    have hv := stageValues_eq_wordCharacteristic_eq
      (representative r.val) (representative s.val) φ ψ heq
    have h := wordOrbit_eq_of_interior_image_eq
      (representative r.val) (representative s.val) φ ψ hc hψ hv
    simpa only [PathOrbitCells.orbit_representative] using h
  · obtain ⟨φ, hφ, hq⟩ := hc
    change (palStageTypeMap (representative r.val) r.property).app (op k) q =
      (wordStageCharacteristic (representative s.val)).app (op k) ψ at heq
    rw [← hq, palStageTypeMap_orbitClass] at heq
    have hv := stageValues_eq_wordCharacteristic_eq
      (representative r.val) (representative s.val) φ ψ heq
    have h := wordOrbit_eq_of_interior_image_eq
      (representative r.val) (representative s.val) φ ψ hφ hd hv
    simpa only [PathOrbitCells.orbit_representative] using h
  · obtain ⟨φ, hφ, hq⟩ := hc
    obtain ⟨ψ, hψ, hq'⟩ := hd
    change (palStageTypeMap (representative r.val) r.property).app (op k) q =
      (palStageTypeMap (representative s.val) s.property).app (op k) q' at heq
    rw [← hq, ← hq', palStageTypeMap_orbitClass,
      palStageTypeMap_orbitClass] at heq
    have hv := stageValues_eq_wordCharacteristic_eq
      (representative r.val) (representative s.val) φ ψ heq
    have h := wordOrbit_eq_of_interior_image_eq
      (representative r.val) (representative s.val) φ ψ hφ hψ hv
    simpa only [PathOrbitCells.orbit_representative] using h

private theorem cellToStage_injective_outside_boundary
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex)
    (c d : (cellPresheaf m ℓ).obj (op k))
    (hc : ¬ ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
      (boundaryToCell m ℓ (by omega)).app (op k) a = c)
    (hd : ¬ ∃ a : (boundaryPresheaf m ℓ (by omega)).obj (op k),
      (boundaryToCell m ℓ (by omega)).app (op k) a = d)
    (heq : (cellToStage m ℓ).app (op k) c =
      (cellToStage m ℓ).app (op k) d) : c = d := by
  have hic := cellInterior_of_outside m ℓ hℓ k c hc
  have hid := cellInterior_of_outside m ℓ hℓ k d hd
  have horbit := cellOrbit_of_interior_image_eq m ℓ k c d hic hid heq
  rcases c with ⟨r, φ⟩ | ⟨r, q⟩ <;>
    rcases d with ⟨s, ψ⟩ | ⟨s, q'⟩
  · change r.val = s.val at horbit
    have hrs : r = s := Subtype.ext horbit
    cases hrs
    change Interior φ at hic
    change Interior ψ at hid
    change (wordStageCharacteristic (representative r.val)).app (op k) φ =
      (wordStageCharacteristic (representative r.val)).app (op k) ψ at heq
    have hχ := stageValues_eq_wordCharacteristic_eq
      (representative r.val) (representative r.val) φ ψ heq
    have hφψ := wordCharacteristic_injective_of_nonpal
      (representative r.val) hℓ r.property φ ψ hic hid hχ
    exact congrArg Sum.inl (Prod.ext rfl hφψ)
  · change r.val = s.val at horbit
    exact False.elim (r.property (by simpa only [horbit] using s.property))
  · change r.val = s.val at horbit
    exact False.elim (s.property (by simpa only [horbit] using r.property))
  · change r.val = s.val at horbit
    have hrs : r = s := Subtype.ext horbit
    cases hrs
    change q ∈ InteriorOrbit ℓ k at hic
    change q' ∈ InteriorOrbit ℓ k at hid
    change (palStageTypeMap (representative r.val) r.property).app (op k) q =
      (palStageTypeMap (representative r.val) r.property).app (op k) q' at heq
    have hqq := (palStage_injOn_interior
      (representative r.val) hℓ r.property k) hic hid heq
    exact congrArg Sum.inr (Prod.ext rfl hqq)

private theorem lengthStage_pointwise_isPushout
    (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) (k : ReverseSimplex) :
    IsPushout
      ((boundaryToPrevious m ℓ hℓ).app (op k))
      ((boundaryToCell m ℓ (by omega)).app (op k))
      ((stageInclusion m ℓ).app (op k))
      ((cellToStage m ℓ).app (op k)) := by
  apply types_isPushout_of_boundary_data
  · intro a
    exact congrFun (NatTrans.congr_app (boundary_square m ℓ hℓ) (op k)) a
  · exact boundaryToCell_injective m ℓ (by omega) k
  · exact stageInclusion_injective m ℓ k
  · exact cell_preimage_iff_boundary m ℓ hℓ k
  · exact stage_jointly_covered m ℓ k
  · exact cellToStage_injective_outside_boundary m ℓ hℓ k

/-- The literal fixed-length word cells attach by a pushout of set-valued
reversal presheaves at every stage of length at least two. -/
theorem lengthStage_isPushout (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    IsPushout
      (boundaryToPrevious m ℓ hℓ)
      (boundaryToCell m ℓ (by omega))
      (stageInclusion m ℓ)
      (cellToStage m ℓ) := by
  apply isPushout_of_pointwise
  intro k
  exact lengthStage_pointwise_isPushout m ℓ hℓ k.unop

/-- The same actual attaching square is a pushout in reversal diagrams of
discrete simplicial sets. -/
theorem lengthStage_discrete_isPushout (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    IsPushout
      (discreteDiagram.map (boundaryToPrevious m ℓ hℓ))
      (discreteDiagram.map (boundaryToCell m ℓ (by omega)))
      (discreteDiagram.map (stageInclusion m ℓ))
      (discreteDiagram.map (cellToStage m ℓ)) := by
  apply isPushout_of_pointwise
  intro k
  apply isPushout_of_pointwise
  intro q
  exact lengthStage_pointwise_isPushout m ℓ hℓ k.unop

end

end DaggerModels.PartII.LengthStageAttaching
