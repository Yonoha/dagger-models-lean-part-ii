import DaggerModelsPartII.SpineOuterFacePushout
import NativeTwoBeadSpineGeometry

/-!
# Restrictions of the standard spine to outer faces

The first outer coface carries the standard spine in one lower dimension
exactly onto the part of the spine contained in that face.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerModels.PartII.OuterFaceSpineGeometry

open SpineOuterFacePushout DaggerNativeStandardSpineInner

noncomputable section

private theorem subcomplexTransport_ι {X : SSet.{u}} {A B : X.Subcomplex}
    (h : A = B) :
    (eqToIso (congrArg SSet.Subcomplex.toSSet h)).hom ≫ B.ι = A.ι := by
  cases h
  rfl

/-- The first outer coface has the expected inverse image of the spine. -/
theorem spine_preimage_firstCoface (n : ℕ) :
    (spine.{u} (n + 1)).preimage (SSet.stdSimplex.δ (0 : Fin (n + 2))) =
      spine n := by
  ext q c
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (SSet.stdSimplex.δ (0 : Fin (n + 2))).app (op ⦋d⦌) c ∈
        (spine (n + 1)).obj (op ⦋d⦌) ↔ c ∈ (spine n).obj (op ⦋d⦌)
      rw [mem_spine_iff, mem_spine_iff]
      change ((0 : Fin (n + 2)).succAbove
          (SSet.stdSimplex.asOrderHom c (Fin.last d))).val ≤
        ((0 : Fin (n + 2)).succAbove
          (SSet.stdSimplex.asOrderHom c 0)).val + 1 ↔ _
      simp only [Fin.zero_succAbove, Fin.val_succ]
      omega

/-- The inverse of the first-face isomorphism followed by its coface is the inclusion. -/
theorem firstFaceIso_inv (t : ℕ) :
    (SSet.stdSimplex.faceSingletonComplIso.{u} (0 : Fin (t + 3))).inv ≫
      SSet.stdSimplex.δ 0 = (firstOuterFace t).ι := by
  change (SSet.stdSimplex.faceSingletonComplIso.{u} (0 : Fin (t + 3))).inv ≫
    SSet.stdSimplex.δ 0 =
      (SSet.stdSimplex.face {(0 : Fin (t + 3))}ᶜ).ι
  rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι, Iso.inv_hom_id_assoc]

/-- The first coface identifies the smaller spine with the corresponding spine part. -/
def firstSpinePartMap (t : ℕ) :
    (spine.{u} (t + 1) : SSet.{u}) ⟶ (firstSpinePart t : SSet.{u}) :=
  SSet.Subcomplex.lift ((spine (t + 1)).ι ≫ SSet.stdSimplex.δ 0) (by
    intro q z hz
    obtain ⟨c, rfl⟩ := hz
    constructor
    · have hc : c.val ∈ ((spine (t + 2)).preimage
          (SSet.stdSimplex.δ (0 : Fin (t + 3)))).obj q := by
        rw [spine_preimage_firstCoface]
        exact c.property
      exact hc
    · have hr := SSet.stdSimplex.range_δ.{u} (0 : Fin (t + 3))
      change SSet.Subcomplex.range (SSet.stdSimplex.δ (0 : Fin (t + 3))) =
        firstOuterFace t at hr
      rw [← hr]
      exact ⟨c.val, rfl⟩
    )

/-- The first spine part is isomorphic to the spine one dimension lower. -/
theorem firstSpinePartMap_isIso (t : ℕ) : IsIso (firstSpinePartMap.{u} t) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro c d he
    apply Subtype.ext
    have hf := congrArg Subtype.val he
    change (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q c.val =
      (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q d.val at hf
    have hm : Mono (SSet.stdSimplex.δ (0 : Fin (t + 3)) :
        (Δ[t + 1] : SSet.{u}) ⟶ Δ[t + 2]) := by
      rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
      infer_instance
    have hq := (NatTrans.mono_iff_mono_app _).mp hm q
    exact (CategoryTheory.mono_iff_injective _).mp hq hf
  · intro z
    let zF : (firstOuterFace t : SSet.{u}).obj q := ⟨z.val, z.property.2⟩
    let c := (SSet.stdSimplex.faceSingletonComplIso.{u}
      (0 : Fin (t + 3))).inv.app q zF
    have hc : (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q c = z.val :=
      congrFun (NatTrans.congr_app (firstFaceIso_inv t) q) zF
    have hm : c ∈ (spine (t + 1)).obj q := by
      rw [← spine_preimage_firstCoface]
      change (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q c ∈
        (spine (t + 2)).obj q
      rw [hc]
      exact z.property.1
    refine ⟨⟨c, hm⟩, ?_⟩
    exact Subtype.ext hc

/-- Under the first coface, the final outer face becomes the final outer face
one dimension lower. -/
theorem lastOuterFace_preimage_firstCoface (t : ℕ) :
    (lastOuterFace.{u} t).preimage (SSet.stdSimplex.δ (0 : Fin (t + 3))) =
      DaggerNativeTwoBeadSpineGeometry.firstFace t := by
  ext q c
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (SSet.stdSimplex.δ (0 : Fin (t + 3))).app (op ⦋d⦌) c ∈
        (lastOuterFace t).obj (op ⦋d⦌) ↔
          c ∈ (DaggerNativeTwoBeadSpineGeometry.firstFace t).obj (op ⦋d⦌)
      rw [lastOuterFace, DaggerNativeTwoBeadSpineGeometry.firstFace,
        SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
      simp only [Finset.mem_compl, Finset.mem_singleton]
      change (∀ j : Fin (d + 1),
        (0 : Fin (t + 3)).succAbove (SSet.stdSimplex.asOrderHom c j) ≠
          Fin.last (t + 2)) ↔
          ∀ j : Fin (d + 1), SSet.stdSimplex.asOrderHom c j ≠ Fin.last (t + 1)
      simp only [Fin.zero_succAbove]
      constructor
      · intro h j hj
        apply h j
        apply Fin.ext
        have hv := congrArg Fin.val hj
        simp only [Fin.val_last] at hv
        simp only [Fin.val_succ, Fin.val_last]
        omega
      · intro h j hj
        apply h j
        apply Fin.ext
        have hv := congrArg Fin.val hj
        simp only [Fin.val_succ, Fin.val_last] at hv
        simp only [Fin.val_last]
        omega

/-- The ordinary coface omitting both extreme vertices. -/
def middleCoface (t : ℕ) : (Δ[t] : SSet.{u}) ⟶ Δ[t + 2] :=
  DaggerOriginalCounitRightCone.face t ≫ SSet.stdSimplex.δ 0

/-- The two face restrictions recover the smaller standard spine. -/
theorem spine_preimage_middleCoface (t : ℕ) :
    (spine.{u} (t + 2)).preimage (middleCoface t) = spine t := by
  change ((spine.{u} (t + 2)).preimage (SSet.stdSimplex.δ 0)).preimage
    (DaggerOriginalCounitRightCone.face t) = spine t
  rw [spine_preimage_firstCoface,
    DaggerNativeTwoBeadSpineGeometry.spine_preimage_face]

/-- The middle coface recovers precisely the intersection of the two outer faces. -/
theorem middleFace_preimage_middleCoface (t : ℕ) :
    (middleFace.{u} t).preimage (middleCoface t) = ⊤ := by
  change (((firstOuterFace.{u} t).preimage (SSet.stdSimplex.δ 0)) ⊓
      ((lastOuterFace t).preimage (SSet.stdSimplex.δ 0))).preimage
        (DaggerOriginalCounitRightCone.face t) = ⊤
  have hf : (firstOuterFace.{u} t).preimage
      (SSet.stdSimplex.δ (0 : Fin (t + 3))) = ⊤ := by
    change (SSet.stdSimplex.face {(0 : Fin (t + 3))}ᶜ).preimage
      (SSet.stdSimplex.δ (0 : Fin (t + 3))) = ⊤
    rw [← SSet.stdSimplex.range_δ (0 : Fin (t + 3))]
    exact SSet.Subcomplex.preimage_range _
  rw [hf, top_inf_eq, lastOuterFace_preimage_firstCoface]
  change (DaggerNativeTwoBeadSpineGeometry.firstFace t).preimage
    (DaggerOriginalCounitRightCone.face t) = ⊤
  change (SSet.stdSimplex.face {(Fin.last (t + 1))}ᶜ).preimage
    (SSet.stdSimplex.δ (Fin.last (t + 1))) = ⊤
  rw [← SSet.stdSimplex.range_δ (Fin.last (t + 1))]
  exact SSet.Subcomplex.preimage_range _

/-- The middle coface as a map into the intersection of the outer faces. -/
def middleFaceMap (t : ℕ) : (Δ[t] : SSet.{u}) ⟶ (middleFace t : SSet.{u}) :=
  SSet.Subcomplex.lift (middleCoface t) (by
    intro q z hz
    obtain ⟨c, rfl⟩ := hz
    have h : c ∈ ((middleFace t).preimage (middleCoface t)).obj q := by
      rw [middleFace_preimage_middleCoface]
      trivial
    exact h)

/-- The middle coface as a map into the middle spine portion. -/
def middleSpinePartMap (t : ℕ) : (spine.{u} t : SSet.{u}) ⟶
    (middleSpinePart t : SSet.{u}) :=
  SSet.Subcomplex.lift ((spine t).ι ≫ middleCoface t) (by
    intro q z hz
    obtain ⟨c, rfl⟩ := hz
    have hs : c.val ∈ ((spine (t + 2)).preimage (middleCoface t)).obj q := by
      rw [spine_preimage_middleCoface]
      exact c.property
    have hm : (middleCoface t).app q c.val ∈ (middleFace t).obj q := by
      have h : c.val ∈ ((middleFace t).preimage (middleCoface t)).obj q := by
        rw [middleFace_preimage_middleCoface]
        trivial
      exact h
    exact ⟨⟨hs, hm.1⟩, ⟨hs, hm.2⟩⟩)

/-- The middle face really is a standard simplex of dimension `t`. -/
theorem middleFaceMap_isIso (t : ℕ) : IsIso (middleFaceMap.{u} t) := by
  have hlast : Mono (DaggerOriginalCounitRightCone.face.{u} t) := by
    rw [← DaggerNativeTwoBeadSpineGeometry.firstFaceIso_hom]
    infer_instance
  have hfirst : Mono (SSet.stdSimplex.δ (0 : Fin (t + 3)) :
      (Δ[t + 1] : SSet.{u}) ⟶ Δ[t + 2]) := by
    rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    infer_instance
  have hmiddle : Mono (middleCoface.{u} t) := by
    unfold middleCoface
    infer_instance
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro c d he
    have hq := (NatTrans.mono_iff_mono_app _).mp hmiddle q
    exact (CategoryTheory.mono_iff_injective _).mp hq
      (congrArg Subtype.val he)
  · intro z
    let zF : (firstOuterFace t : SSet.{u}).obj q := ⟨z.val, z.property.1⟩
    let y := (SSet.stdSimplex.faceSingletonComplIso.{u}
      (0 : Fin (t + 3))).inv.app q zF
    have hyz : (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q y = z.val :=
      congrFun (NatTrans.congr_app (firstFaceIso_inv t) q) zF
    have hy : y ∈ (DaggerNativeTwoBeadSpineGeometry.firstFace t).obj q := by
      rw [← lastOuterFace_preimage_firstCoface]
      change (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q y ∈
        (lastOuterFace t).obj q
      rw [hyz]
      exact z.property.2
    let yF : (DaggerNativeTwoBeadSpineGeometry.firstFace t : SSet.{u}).obj q :=
      ⟨y, hy⟩
    let c := (DaggerNativeTwoBeadSpineGeometry.firstFaceIso.{u} t).inv.app q yF
    have hcy : (DaggerOriginalCounitRightCone.face t).app q c = y :=
      congrFun (NatTrans.congr_app
        (DaggerNativeTwoBeadSpineGeometry.firstFaceIso_inv t) q) yF
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change (middleCoface t).app q c = z.val
    change (SSet.stdSimplex.δ (0 : Fin (t + 3))).app q
      ((DaggerOriginalCounitRightCone.face t).app q c) = z.val
    rw [hcy, hyz]

/-- The middle spine portion is the spine of the middle face. -/
theorem middleSpinePartMap_isIso (t : ℕ) : IsIso (middleSpinePartMap.{u} t) := by
  have hface : IsIso (middleFaceMap.{u} t) := middleFaceMap_isIso t
  have hmiddle : Mono (middleCoface.{u} t) := by
    have hf : Mono (middleFaceMap.{u} t) := inferInstance
    change Mono (middleFaceMap t ≫ (middleFace t).ι)
    infer_instance
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro c d he
    apply Subtype.ext
    have hq := (NatTrans.mono_iff_mono_app _).mp hmiddle q
    exact (CategoryTheory.mono_iff_injective _).mp hq
      (congrArg Subtype.val he)
  · intro z
    let zF : (middleFace t : SSet.{u}).obj q :=
      ⟨z.val, ⟨z.property.1.2, z.property.2.2⟩⟩
    let c := (asIso (middleFaceMap t)).inv.app q zF
    have hcz : (middleCoface t).app q c = z.val :=
      congrArg Subtype.val
        (congrFun (NatTrans.congr_app (asIso (middleFaceMap t)).inv_hom_id q) zF)
    have hc : c ∈ (spine t).obj q := by
      rw [← spine_preimage_middleCoface]
      change (middleCoface t).app q c ∈ (spine (t + 2)).obj q
      rw [hcz]
      exact z.property.1.1
    refine ⟨⟨c, hc⟩, ?_⟩
    exact Subtype.ext hcz

/-- The final spine part is the standard spine in one lower dimension. -/
theorem lastPartEq (t : ℕ) :
    DaggerNativeTwoBeadSpineGeometry.firstFace.{u} (t + 1) ⊓ spine (t + 2) =
      lastSpinePart t := by
  change lastOuterFace t ⊓ spine (t + 2) = spine (t + 2) ⊓ lastOuterFace t
  exact inf_comm (lastOuterFace t) (spine (t + 2))

def lastSpinePartMap (t : ℕ) : (spine.{u} (t + 1) : SSet.{u}) ⟶
    (lastSpinePart t : SSet.{u}) :=
  DaggerNativeTwoBeadSpineGeometry.intersectionMap (t + 1) ≫
    (eqToIso (congrArg SSet.Subcomplex.toSSet
      (lastPartEq t))).hom

theorem lastSpinePartMap_isIso (t : ℕ) : IsIso (lastSpinePartMap.{u} t) := by
  unfold lastSpinePartMap
  letI : IsIso (DaggerNativeTwoBeadSpineGeometry.intersectionMap.{u} (t + 1)) :=
    DaggerNativeTwoBeadSpineGeometry.intersectionMap_isIso (t + 1)
  infer_instance

/-- The vertical map on the first outer face. -/
def firstVertical (t : ℕ) : (firstSpinePart.{u} t : SSet.{u}) ⟶
    (firstOuterFace t : SSet.{u}) :=
  SSet.Subcomplex.homOfLE inf_le_right

/-- The vertical map on the final outer face. -/
def lastVertical (t : ℕ) : (lastSpinePart.{u} t : SSet.{u}) ⟶
    (lastOuterFace t : SSet.{u}) :=
  SSet.Subcomplex.homOfLE inf_le_right

/-- The vertical map on the overlap of the two faces. -/
def middleVertical (t : ℕ) : (middleSpinePart.{u} t : SSet.{u}) ⟶
    (middleFace t : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (by
    intro q c hc
    exact ⟨hc.1.2, hc.2.2⟩)

/-- The first vertical arrow is the ordinary Segal inclusion up to isomorphism. -/
def firstVerticalArrowIso (t : ℕ) :
    Arrow.mk (spine.{u} (t + 1)).ι ≅ Arrow.mk (firstVertical t) := by
  letI : IsIso (firstSpinePartMap.{u} t) := firstSpinePartMap_isIso t
  refine Arrow.isoMk (asIso (firstSpinePartMap t))
    (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (t + 3))) ?_
  apply (cancel_mono (firstOuterFace t).ι).mp
  change (spine (t + 1)).ι ≫
      (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (t + 3))).hom ≫
        (firstOuterFace t).ι =
      firstSpinePartMap t ≫ firstVertical t ≫ (firstOuterFace t).ι
  dsimp [firstSpinePartMap, firstVertical]
  rfl

/-- The overlap vertical arrow is the ordinary Segal inclusion up to isomorphism. -/
def middleVerticalArrowIso (t : ℕ) :
    Arrow.mk (spine.{u} t).ι ≅ Arrow.mk (middleVertical t) := by
  letI : IsIso (middleSpinePartMap.{u} t) := middleSpinePartMap_isIso t
  letI : IsIso (middleFaceMap.{u} t) := middleFaceMap_isIso t
  refine Arrow.isoMk (asIso (middleSpinePartMap t))
    (asIso (middleFaceMap t)) ?_
  apply (cancel_mono (middleFace t).ι).mp
  change (spine t).ι ≫ middleFaceMap t ≫ (middleFace t).ι =
    middleSpinePartMap t ≫ middleVertical t ≫ (middleFace t).ι
  dsimp [middleSpinePartMap, middleFaceMap, middleVertical]

/-- The final vertical arrow is the ordinary Segal inclusion up to isomorphism. -/
def lastVerticalArrowIso (t : ℕ) :
    Arrow.mk (spine.{u} (t + 1)).ι ≅ Arrow.mk (lastVertical t) := by
  letI : IsIso (lastSpinePartMap.{u} t) := lastSpinePartMap_isIso t
  refine Arrow.isoMk (asIso (lastSpinePartMap t))
    (DaggerNativeTwoBeadSpineGeometry.firstFaceIso (t + 1)) ?_
  apply (cancel_mono (lastOuterFace t).ι).mp
  change lastSpinePartMap t ≫ lastVertical t ≫ (lastOuterFace t).ι =
    (spine (t + 1)).ι ≫
      (DaggerNativeTwoBeadSpineGeometry.firstFaceIso (t + 1)).hom ≫
        (lastOuterFace t).ι
  have ht :
      (eqToIso (congrArg SSet.Subcomplex.toSSet (lastPartEq.{u} t))).hom ≫
        (lastSpinePart t).ι =
          (DaggerNativeTwoBeadSpineGeometry.firstFace (t + 1) ⊓
            spine (t + 2)).ι := subcomplexTransport_ι (lastPartEq t)
  rw [lastSpinePartMap, lastVertical, SSet.Subcomplex.homOfLE_ι]
  rw [Category.assoc, ht]
  change DaggerNativeTwoBeadSpineGeometry.intersectionMap (t + 1) ≫
      (DaggerNativeTwoBeadSpineGeometry.firstFace (t + 1) ⊓ spine (t + 2)).ι =
    (spine (t + 1)).ι ≫
      (DaggerNativeTwoBeadSpineGeometry.firstFaceIso (t + 1)).hom ≫
        (DaggerNativeTwoBeadSpineGeometry.firstFace (t + 1)).ι
  rw [DaggerNativeTwoBeadSpineGeometry.firstFaceIso_hom]
  rfl

end

end DaggerModels.PartII.OuterFaceSpineGeometry
