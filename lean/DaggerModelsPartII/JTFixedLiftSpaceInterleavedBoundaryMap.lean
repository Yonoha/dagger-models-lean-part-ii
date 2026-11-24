import DaggerModelsPartII.JTInterleavedTimeBoundary
import DaggerModelsPartII.JTFixedLiftSpaceTimeBoundaryChoices

/-!
# Gluing the original boundary choices on enlarged time faces
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceInterleavedBoundaryMap

open JTFixedLiftSpaceInterleaved JTFixedLiftSpaceTimeEquiv JTHigherInterleavedParameter
open JTFixedLiftSpaceTimeBoundaryChoices
open SSet.Subcomplex hiding homOfLE

noncomputable section

variable {A X Y : SSet.{u}} {k n : ℕ} {i : A ⟶ (Δ[k] : SSet.{u})}
variable {t : A ⟶ X} {p : X ⟶ Y} {b : (Δ[k] : SSet.{u}) ⟶ Y}
variable (sq : CommSq t i p b)
variable (β : (SSet.boundary n : SSet.{u}) ⟶ extensionSpace sq)

local notation "TF" => Finset (Fin (n + 1))
private abbrev facet (k n : ℕ) (a : Fin (n + 1)) :=
  timeFace.{u} k n (Finset.univ.erase a)

private theorem timeFace_mono {S T : TF} (h : S ⊆ T) : timeFace.{u} k n S ≤ timeFace k n T := by
  have hst : S ⊓ T = S := inf_eq_left.mpr h
  have ht := timeFace_inf.{u} k n S T
  rw [hst] at ht
  exact inf_eq_left.mp ht.symm

private theorem timeInclusion_not_surj {S : TF} (hS : S.Nonempty) (h : S ≠ Finset.univ) :
    ¬ Function.Surjective (timeInclusion S hS).toOrderHom := by
  intro he
  apply h
  apply Finset.eq_univ_of_forall
  intro a
  have ha : a ∈ Set.range (timeInclusion S hS).toOrderHom := he a
  rw [timeInclusion_range] at ha
  exact ha

private theorem exists_factor {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
    {S : TF} (hS : S.Nonempty) (hj : ∀ v, j.toOrderHom v ∈ S) :
    ∃ a : m ⟶ timeDegree S, a ≫ timeInclusion S hS = j := by
  have ht (v : Fin (m.len + 1)) : j.toOrderHom v ∈ Set.range (timeInclusion S hS).toOrderHom := by
    rw [timeInclusion_range]
    exact hj v
  let a (v : Fin (m.len + 1)) := (ht v).choose
  have ha (v : Fin (m.len + 1)) : (timeInclusion S hS).toOrderHom (a v) = j.toOrderHom v :=
    (ht v).choose_spec
  have hm : StrictMono (timeInclusion S hS).toOrderHom :=
    (timeInclusion S hS).toOrderHom.monotone.strictMono_of_injective
      (timeInclusion_injective S hS)
  refine ⟨SimplexCategory.Hom.mk ⟨a, fun v w hvw ↦ hm.le_iff_le.mp ?_⟩, ?_⟩
  · rw [ha, ha]
    exact j.toOrderHom.monotone hvw
  · ext v : 3
    exact ha v

private abbrev faceIso (S : TF) (hS : S.Nonempty) := timeFaceIso.{u} k n S hS

private theorem timeFace_eq_bot (S : TF) (hS : ¬ S.Nonempty) :
    timeFace.{u} k n S = ⊥ := by
  rw [Finset.not_nonempty_iff_eq_empty.mp hS, timeFace_empty]

private def isInitial_timeFace (S : TF) (hS : ¬ S.Nonempty) :
    IsInitial (timeFace.{u} k n S : SSet.{u}) :=
  SSet.Subcomplex.isInitialBot.ofIso (SSet.Subcomplex.eqToIso (timeFace_eq_bot S hS).symm)

/-- The prescribed map on any proper set of time vertices. -/
def faceMap (S : TF) (hp : S ≠ Finset.univ) : (timeFace.{u} k n S : SSet.{u}) ⟶ X :=
  if hS : S.Nonempty then
    (faceIso S hS).inv ≫ (choice sq β (timeInclusion S hS) (timeInclusion_not_surj hS hp)).map
  else (isInitial_timeFace (k := k) S hS).to X

@[reassoc]
private theorem faceMap_iso (S : TF) (hp : S ≠ Finset.univ) (hS : S.Nonempty) :
    (faceIso (k := k) S hS).hom ≫ faceMap sq β S hp =
      (choice sq β (timeInclusion S hS) (timeInclusion_not_surj hS hp)).map := by
  rw [faceMap, dif_pos hS, Iso.hom_inv_id_assoc]

/-- Maps from nonempty enlarged faces restrict along every factorization
of a time operator through their actual inclusion. -/
private theorem faceMap_factor (S : TF) (hp : S ≠ Finset.univ) (hS : S.Nonempty)
    {m : SimplexCategory} (a : m ⟶ timeDegree S) :
    SSet.stdSimplex.{u}.map (mapTime ⦋k⦌ a) ≫ (faceIso (k := k) S hS).hom ≫ faceMap sq β S hp =
      (choice sq β (a ≫ timeInclusion S hS)
        (fun h ↦ timeInclusion_not_surj hS hp (Function.Surjective.of_comp h))).map := by
  rw [faceMap_iso, choice_comp]
  rfl

private theorem choice_congr {m : SimplexCategory} {j j' : m ⟶ ⦋n⦌} (h : j = j')
    (hj : ¬ Function.Surjective j.toOrderHom) (hj' : ¬ Function.Surjective j'.toOrderHom) :
    choice sq β j hj = choice sq β j' hj' := by
  subst j'
  rfl

private theorem faceMap_natural {S T : TF} (h : S ⊆ T)
    (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ) :
    SSet.Subcomplex.homOfLE (timeFace_mono (k := k) h) ≫ faceMap sq β T hT =
      faceMap sq β S hS := by
  by_cases hs : S.Nonempty
  · have ht := hs.mono h
    have hj (v : Fin ((timeDegree S).len + 1)) : (timeInclusion S hs).toOrderHom v ∈ T := by
      apply h
      have hv : (timeInclusion S hs).toOrderHom v ∈ Set.range (timeInclusion S hs).toOrderHom :=
        ⟨v, rfl⟩
      rw [timeInclusion_range] at hv
      exact hv
    obtain ⟨a, ha⟩ := exists_factor (timeInclusion S hs) ht hj
    have hi : (faceIso (k := k) S hs).hom ≫ SSet.Subcomplex.homOfLE (timeFace_mono h) =
        SSet.stdSimplex.{u}.map (mapTime ⦋k⦌ a) ≫ (faceIso T ht).hom := by
      rw [← cancel_mono (timeFace k n T).ι]
      simp only [Category.assoc, homOfLE_ι, timeFaceIso_ι, ← SSet.stdSimplex.map_comp,
        ← mapTime_comp, ha]
    rw [← cancel_epi (faceIso (k := k) S hs).hom, ← Category.assoc, hi, Category.assoc,
      faceMap_factor, faceMap_iso]
    exact congrArg Extension.map (choice_congr sq β ha _ _)
  · exact (isInitial_timeFace (k := k) S hs).hom_ext _ _

private theorem erase_ne_univ (a : Fin (n + 1)) : (Finset.univ.erase a : TF) ≠ Finset.univ := by
  intro h
  exact Finset.notMem_erase a Finset.univ (h.symm ▸ Finset.mem_univ a)

private def cover (k n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram (timeBoundary.{u} k n) (facet k n)
      (fun a b ↦ facet k n a ⊓ facet k n b) :=
  ⟨(timeBoundary_eq_iSup k n).symm, fun _ _ ↦ rfl⟩

private theorem faceMap_overlap (a b' : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (inf_le_left : facet k n a ⊓ facet k n b' ≤ facet k n a) ≫
      faceMap sq β (Finset.univ.erase a) (erase_ne_univ a) =
    SSet.Subcomplex.homOfLE (inf_le_right : facet k n a ⊓ facet k n b' ≤ facet k n b') ≫
      faceMap sq β (Finset.univ.erase b') (erase_ne_univ b') := by
  let S : TF := Finset.univ.erase a ⊓ Finset.univ.erase b'
  have hA : S ⊆ Finset.univ.erase a := Finset.inter_subset_left
  have hB : S ⊆ Finset.univ.erase b' := Finset.inter_subset_right
  have hS : S ≠ Finset.univ := by
    intro h
    have ha : a ∈ S := h.symm ▸ Finset.mem_univ a
    exact Finset.notMem_erase a _ (hA ha)
  have h₀ : timeFace.{u} k n S = facet k n a ⊓ facet k n b' := timeFace_inf _ _ _ _
  rw [← cancel_epi (SSet.Subcomplex.eqToIso h₀).hom]
  simp only [SSet.Subcomplex.eqToIso_hom]
  exact (faceMap_natural sq β hA hS (erase_ne_univ a)).trans
    (faceMap_natural sq β hB hS (erase_ne_univ b')).symm

/-- The map on the union of the enlarged time faces determined by the
original simplicial boundary of enlargement choices. -/
def boundaryMap : (timeBoundary.{u} k n : SSet.{u}) ⟶ X :=
  Multicofork.IsColimit.desc (cover k n).isColimit
    (fun a ↦ faceMap sq β (Finset.univ.erase a) (erase_ne_univ a))
    (fun a ↦ faceMap_overlap sq β a.1 a.2)

private theorem face_le_boundary (a : Fin (n + 1)) : facet k n a ≤ timeBoundary.{u} k n := by
  rw [timeBoundary_eq_iSup]
  exact le_iSup (facet k n) a

@[reassoc]
theorem boundaryMap_face (a : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (face_le_boundary (k := k) a) ≫ boundaryMap sq β =
      faceMap sq β (Finset.univ.erase a) (erase_ne_univ a) :=
  Multicofork.IsColimit.fac (cover k n).isColimit _ _ a

/-- Recover the exact given extension along any time operator whose
image avoids a time vertex. -/
theorem exists_boundaryMap_operator {m : SimplexCategory} (j : m ⟶ ⦋n⦌)
    (hj : ¬ Function.Surjective j.toOrderHom) :
    ∃ a : SSet.stdSimplex.{u}.obj (common ⦋k⦌ m) ⟶ (timeBoundary k n : SSet.{u}),
      a ≫ (timeBoundary k n).ι = SSet.stdSimplex.map (mapTime ⦋k⦌ j) ∧
      a ≫ boundaryMap sq β = (choice sq β j hj).map := by
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1), ∀ w, j.toOrderHom w ≠ v := by
    simpa only [Function.Surjective, not_forall, not_exists] using hj
  let S := Finset.univ.erase v
  have hS : ∀ w, j.toOrderHom w ∈ S := fun w ↦
    Finset.mem_erase.mpr ⟨hv w, Finset.mem_univ _⟩
  have hs : S.Nonempty := ⟨j.toOrderHom 0, hS 0⟩
  obtain ⟨a, ha⟩ := exists_factor j hs hS
  let incl := SSet.Subcomplex.homOfLE (face_le_boundary (k := k) v)
  refine ⟨SSet.stdSimplex.map (mapTime ⦋k⦌ a) ≫ (faceIso S hs).hom ≫ incl, ?_, ?_⟩
  · have hι : incl ≫ (timeBoundary.{u} k n).ι = (timeFace k n S).ι := homOfLE_ι _
    rw [Category.assoc, Category.assoc, hι, timeFaceIso_ι,
      ← SSet.stdSimplex.map_comp, ← mapTime_comp, ha]
  · have hB : incl ≫ boundaryMap sq β = faceMap sq β S (erase_ne_univ v) :=
      boundaryMap_face sq β v
    rw [Category.assoc, Category.assoc, hB, faceMap_factor]
    exact congrArg Extension.map (choice_congr sq β ha _ _)

/-- The glued boundary has the prescribed base map on its entire domain. -/
theorem boundaryMap_over :
    boundaryMap sq β ≫ p =
      (timeBoundary k n).ι ≫ SSet.stdSimplex.map (ret ⦋k⦌ ⦋n⦌) ≫ b := by
  apply Multicofork.IsColimit.hom_ext (cover k n).isColimit
  intro a
  change Fin (n + 1) at a
  let S : TF := Finset.univ.erase a
  let incl := SSet.Subcomplex.homOfLE (face_le_boundary (k := k) a)
  change incl ≫ (boundaryMap sq β ≫ p) =
    incl ≫ (timeBoundary k n).ι ≫ SSet.stdSimplex.map (ret ⦋k⦌ ⦋n⦌) ≫ b
  have hh : incl ≫ boundaryMap sq β = faceMap sq β S (erase_ne_univ a) :=
    boundaryMap_face sq β a
  rw [← Category.assoc, hh, ← Category.assoc incl, homOfLE_ι]
  by_cases hS : S.Nonempty
  · rw [← cancel_epi (faceIso (k := k) S hS).hom, ← Category.assoc,
      faceMap_iso, (choice sq β (timeInclusion S hS)
        (timeInclusion_not_surj hS (erase_ne_univ a))).over]
    rw [← Category.assoc, timeFaceIso_ι, ← Category.assoc, ← SSet.stdSimplex.map_comp, mapTime_ret]
  · exact (isInitial_timeFace (k := k) S hS).hom_ext _ _


private abbrev P (k n : ℕ) := prism.{u} ⦋k⦌ ⦋n⦌
private abbrev C (k n : ℕ) (a : Fin (n + 1)) := (facet k n a).preimage (P k n)

private def preimageCover (k n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram ((timeBoundary k n).preimage (P k n))
      (C k n) (fun a b ↦ C k n a ⊓ C k n b) := by
  refine ⟨?_, fun _ _ ↦ rfl⟩
  rw [timeBoundary_eq_iSup, preimage_iSup]

private abbrev preimageIso (S : TF) (hS : S.Nonempty) := timeFacePreimageIso.{u} k n S hS

/-- The maps prescribed on the whole prism and all enlarged time faces
agree on their full intersection. -/
theorem boundaryMap_overlap
    (v : (Δ[n] : SSet.{u}) ⟶ (SSet.ihomToPullbackFiber sq : SSet.{u}))
    (h : β ≫ JTFixedLiftSpaceInterleavedProjection.projection sq = (SSet.boundary n).ι ≫ v) :
    (timeBoundary k n).fromPreimage (P k n) ≫ boundaryMap sq β =
      ((timeBoundary k n).preimage (P k n)).ι ≫ timeMap sq ⦋n⦌ (SSet.yonedaEquiv v) := by
  apply Multicofork.IsColimit.hom_ext (preimageCover k n).isColimit
  intro a
  change Fin (n + 1) at a
  let S : TF := Finset.univ.erase a
  let q : C k n a ≤ (timeBoundary k n).preimage (P k n) :=
    fun d ↦ Set.preimage_mono (face_le_boundary (k := k) a d)
  let u := SSet.Subcomplex.homOfLE q
  change u ≫ (timeBoundary k n).fromPreimage (P k n) ≫ boundaryMap sq β =
    u ≫ ((timeBoundary k n).preimage (P k n)).ι ≫ timeMap sq ⦋n⦌ (SSet.yonedaEquiv v)
  rw [homOfLE_ι_assoc]
  have he : u ≫ (timeBoundary k n).fromPreimage (P k n) =
      (facet k n a).fromPreimage (P k n) ≫ SSet.Subcomplex.homOfLE (face_le_boundary (k := k) a) :=
    JTFiniteSubcomplexPreimageGluing.fromPreimage_homOfLE (P k n) (face_le_boundary a)
  rw [← Category.assoc u, he, Category.assoc, boundaryMap_face]
  by_cases hS : S.Nonempty
  · rw [← cancel_epi (preimageIso (k := k) S hS).hom, reassoc_of% timeFacePreimageIso_compare,
      faceMap_iso, reassoc_of% timeFacePreimageIso_ι]
    exact choice_prism sq β v h (timeInclusion S hS) (timeInclusion_not_surj hS (erase_ne_univ a))
  · have h₁ : C k n a = ⊥ := by
      change (timeFace k n S).preimage (P k n) = _
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      exact timeFace_empty_preimage k n
    exact (SSet.Subcomplex.isInitialBot.ofIso (SSet.Subcomplex.eqToIso h₁.symm)).hom_ext _ _


end

end DaggerModels.PartII.JTFixedLiftSpaceInterleavedBoundaryMap
