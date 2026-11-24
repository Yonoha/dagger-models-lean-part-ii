import DaggerModelsPartII.JTCommonCoefficientTimeBoundary
import DaggerModelsPartII.JTDisjointSubcomplexCover

/-!
# Relative filling on all common-coefficient time faces

Compatible maps on the proper injective time operators assemble into a map on
the enlarged boundary. The common-coefficient prism filler then gives the
prescribed restrictions and preserves the original normalization simplex.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen
open SSet.Subcomplex hiding homOfLE

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common timeDegree timeInclusion timeInclusion_range
  timeInclusion_injective timeFace_range_timeInclusion whiskerLeft_timeInclusion_mono)

noncomputable section

variable {b : SimplexCategory} {k n : ℕ} (c : ⦋k⦌ ⟶ b)
private abbrev simplex (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m

/-- Compatible maps indexed by all injective time operators on the boundary. -/
structure BoundaryFamily (X : SSet.{0}) where
  map : ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌), Function.Injective j.toOrderHom →
    (¬ Function.Surjective j.toOrderHom) → (simplex (common ⦋k⦌ ⦋m⦌) ⟶ X)
  map_comp : ∀ {l m : ℕ} (a : ⦋l⦌ ⟶ ⦋m⦌) (j : ⦋m⦌ ⟶ ⦋n⦌)
    (ha : Function.Injective a.toOrderHom) (hj : Function.Injective j.toOrderHom)
    (h : ¬ Function.Surjective j.toOrderHom),
    map (a ≫ j) (hj.comp ha) (fun he ↦ h (Function.Surjective.of_comp he)) =
      SSet.stdSimplex.map (timeOperator c m a ha) ≫ map j hj h

variable {X : SSet.{0}} (β : BoundaryFamily (n := n) c X)

local notation "TF" => Finset (Fin (n + 1))

private theorem timeInclusion_not_surj {S : TF} (hS : S.Nonempty) (h : S ≠ Finset.univ) :
    ¬ Function.Surjective (timeInclusion S hS).toOrderHom := by
  intro he
  apply h
  apply Finset.eq_univ_of_forall
  intro a
  have ha : a ∈ Set.range (timeInclusion S hS).toOrderHom := he a
  rw [timeInclusion_range] at ha
  exact ha

private theorem exists_factor {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    {S : TF} (hS : S.Nonempty) (hj : ∀ v, j.toOrderHom v ∈ S) :
    ∃ a : ⦋m⦌ ⟶ timeDegree S, a ≫ timeInclusion S hS = j := by
  have ht (v : Fin (m + 1)) : j.toOrderHom v ∈ Set.range (timeInclusion S hS).toOrderHom := by
    rw [timeInclusion_range]
    exact hj v
  let a (v : Fin (m + 1)) := (ht v).choose
  have ha (v : Fin (m + 1)) : (timeInclusion S hS).toOrderHom (a v) = j.toOrderHom v :=
    (ht v).choose_spec
  have hm : StrictMono (timeInclusion S hS).toOrderHom :=
    (timeInclusion S hS).toOrderHom.monotone.strictMono_of_injective
      (timeInclusion_injective S hS)
  refine ⟨SimplexCategory.Hom.mk ⟨a, fun v w hvw ↦ hm.le_iff_le.mp ?_⟩, ?_⟩
  · rw [ha, ha]
    exact j.toOrderHom.monotone hvw
  · ext v : 3
    exact ha v

private theorem factor_injective {m : ℕ} {j : ⦋m⦌ ⟶ ⦋n⦌}
    {S : TF} (hs : S.Nonempty) {a : ⦋m⦌ ⟶ timeDegree S}
    (he : a ≫ timeInclusion S hs = j) (hj : Function.Injective j.toOrderHom) :
    Function.Injective a.toOrderHom := by
  intro x y h
  apply hj
  rw [← he]
  exact congrArg (timeInclusion S hs).toOrderHom h

private def emptyFace (S : TF) (hS : ¬ S.Nonempty) :
    IsInitial (timeFace c n S).toSSet :=
  isInitialBot.ofIso (SSet.Subcomplex.eqToIso (timeFace_eq_bot c n S hS).symm)

/-- Evaluate on a full proper time face using the original enumerating operator. -/
def faceMap (S : TF) (hp : S ≠ Finset.univ) : (timeFace c n S).toSSet ⟶ X :=
  if hs : S.Nonempty then
    (timeFaceIso c n S hs).inv ≫ β.map (timeInclusion S hs)
      (timeInclusion_injective S hs) (timeInclusion_not_surj hs hp)
  else (emptyFace c S hs).to X

@[reassoc]
theorem faceMap_iso (S : TF) (hp : S ≠ Finset.univ) (hs : S.Nonempty) :
    (timeFaceIso c n S hs).hom ≫ faceMap c β S hp =
      β.map (timeInclusion S hs) (timeInclusion_injective S hs) (timeInclusion_not_surj hs hp) := by
  rw [faceMap, dif_pos hs, Iso.hom_inv_id_assoc]

private theorem faceMap_factor (S : TF) (hp : S ≠ Finset.univ) (hs : S.Nonempty)
    {m : ℕ} (a : ⦋m⦌ ⟶ timeDegree S) (ha : Function.Injective a.toOrderHom)
    (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
    (hn : ¬ Function.Surjective j.toOrderHom) (he : a ≫ timeInclusion S hs = j) :
    SSet.stdSimplex.map (timeOperator c (timeDegree S).len a ha) ≫
      (timeFaceIso c n S hs).hom ≫ faceMap c β S hp = β.map j hj hn := by
  rw [faceMap_iso, ← β.map_comp]
  subst j
  rfl

private theorem faceMap_natural {S T : TF} (h : S ⊆ T)
    (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ) :
    SSet.Subcomplex.homOfLE (timeFace_mono c n h) ≫ faceMap c β T hT = faceMap c β S hS := by
  by_cases hs : S.Nonempty
  · have ht := hs.mono h
    have hj (v : Fin ((timeDegree S).len + 1)) : (timeInclusion S hs).toOrderHom v ∈ T := by
      apply h
      have hv : (timeInclusion S hs).toOrderHom v ∈ Set.range (timeInclusion S hs).toOrderHom :=
        ⟨v, rfl⟩
      rw [timeInclusion_range] at hv
      exact hv
    obtain ⟨a, he⟩ := exists_factor (timeInclusion S hs) ht hj
    have ha := factor_injective ht he (timeInclusion_injective S hs)
    have hi : (timeFaceIso c n S hs).hom ≫ SSet.Subcomplex.homOfLE (timeFace_mono c n h) =
        SSet.stdSimplex.map (timeOperator c (timeDegree T).len a ha) ≫
          (timeFaceIso c n T ht).hom := by
      rw [← cancel_mono (timeFace c n T).ι]
      simp only [Category.assoc, homOfLE_ι, timeFaceIso_ι, ← SSet.stdSimplex.map_comp,
        ← timeOperator_comp, he]
    rw [← cancel_epi (timeFaceIso c n S hs).hom, ← Category.assoc, hi, Category.assoc,
      faceMap_iso c β S hS hs]
    exact faceMap_factor c β T hT ht a ha _ (timeInclusion_injective S hs)
      (timeInclusion_not_surj hs hS) he
  · exact (emptyFace c S hs).hom_ext _ _

private theorem erase_ne_univ (a : Fin (n + 1)) :
    (Finset.univ.erase a : TF) ≠ Finset.univ := by
  intro h
  exact Finset.notMem_erase a Finset.univ (h.symm ▸ Finset.mem_univ a)

private abbrev facet (a : Fin (n + 1)) := timeFace c n (Finset.univ.erase a)

private theorem faceMap_overlap (a a' : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (inf_le_left : facet c a ⊓ facet c a' ≤ facet c a) ≫
      faceMap c β (Finset.univ.erase a) (erase_ne_univ a) =
    SSet.Subcomplex.homOfLE (inf_le_right : facet c a ⊓ facet c a' ≤ facet c a') ≫
      faceMap c β (Finset.univ.erase a') (erase_ne_univ a') := by
  let S : TF := Finset.univ.erase a ⊓ Finset.univ.erase a'
  have hA : S ⊆ Finset.univ.erase a := Finset.inter_subset_left
  have hB : S ⊆ Finset.univ.erase a' := Finset.inter_subset_right
  have hS : S ≠ Finset.univ := by
    intro h
    have ha : a ∈ S := h.symm ▸ Finset.mem_univ a
    exact Finset.notMem_erase a _ (hA ha)
  have he : timeFace c n S = facet c a ⊓ facet c a' := timeFace_inf _ _ _ _
  rw [← cancel_epi (SSet.Subcomplex.eqToIso he).hom]
  simp only [SSet.Subcomplex.eqToIso_hom]
  exact (faceMap_natural c β hA hS (erase_ne_univ a)).trans
    (faceMap_natural c β hB hS (erase_ne_univ a')).symm

open JTDisjointSubcomplexCover

/-- Glue the prescribed maps on the genuine enlarged time boundary. -/
def boundaryMap : (timeBoundary c n).toSSet ⟶ X :=
  (SSet.Subcomplex.eqToIso (timeBoundary_eq_iSup c n)).hom ≫
    glueCompatible (facet c)
      (fun a ↦ faceMap c β (Finset.univ.erase a) (erase_ne_univ a))
      (faceMap_overlap c β)

private theorem facet_le_boundary (a : Fin (n + 1)) : facet c a ≤ timeBoundary c n := by
  rw [timeBoundary_eq_iSup]
  exact le_iSup (facet c) a

@[reassoc]
theorem boundaryMap_face (a : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (facet_le_boundary c a) ≫ boundaryMap c β =
      faceMap c β (Finset.univ.erase a) (erase_ne_univ a) := by
  unfold boundaryMap
  rw [← Category.assoc, SSet.Subcomplex.eqToIso_hom, SSet.Subcomplex.homOfLE_comp]
  exact inclusion_glueCompatible (facet c) _ _ a

/-- The map on the boundary recovers the original prescribed map at each
proper injective time operator. -/
theorem exists_boundaryMap_operator {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) (hn : ¬ Function.Surjective j.toOrderHom) :
    ∃ a : simplex (common ⦋k⦌ ⦋m⦌) ⟶ (timeBoundary c n).toSSet,
      a ≫ (timeBoundary c n).ι = SSet.stdSimplex.map (timeOperator c n j hj) ∧
      a ≫ boundaryMap c β = β.map j hj hn := by
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1), ∀ w, j.toOrderHom w ≠ v := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  let S := Finset.univ.erase v
  have hS : ∀ w, j.toOrderHom w ∈ S := fun w ↦
    Finset.mem_erase.mpr ⟨hv w, Finset.mem_univ _⟩
  have hs : S.Nonempty := ⟨j.toOrderHom 0, hS 0⟩
  obtain ⟨a, he⟩ := exists_factor j hs hS
  have ha := factor_injective hs he hj
  let incl := SSet.Subcomplex.homOfLE (facet_le_boundary c v)
  refine ⟨SSet.stdSimplex.map (timeOperator c (timeDegree S).len a ha) ≫
    (timeFaceIso c n S hs).hom ≫ incl, ?_, ?_⟩
  · have hι : incl ≫ (timeBoundary c n).ι = (timeFace c n S).ι := homOfLE_ι _
    rw [Category.assoc, Category.assoc, hι, timeFaceIso_ι,
      ← SSet.stdSimplex.map_comp, ← timeOperator_comp]
    subst j
    rfl
  · have hB : incl ≫ boundaryMap c β = faceMap c β S (erase_ne_univ v) := boundaryMap_face c β v
    rw [Category.assoc, Category.assoc, hB]
    exact faceMap_factor c β S (erase_ne_univ v) hs a ha j hj hn he


section Prism

private abbrev fullPrism := prism.{0} c ⦋n⦌
private abbrev preimageFacet (a : Fin (n + 1)) := (facet c a).preimage (fullPrism (n := n) c)

private def boundaryCover :
    SSet.Subcomplex.MulticoequalizerDiagram (timeBoundary c n) (facet c)
      (fun a b ↦ facet c a ⊓ facet c b) :=
  ⟨(timeBoundary_eq_iSup c n).symm, fun _ _ ↦ rfl⟩

private def preimageCover :
    SSet.Subcomplex.MulticoequalizerDiagram ((timeBoundary c n).preimage (fullPrism c))
      (preimageFacet c) (fun a b ↦ preimageFacet c a ⊓ preimageFacet c b) := by
  refine ⟨?_, fun _ _ ↦ rfl⟩
  rw [timeBoundary_eq_iSup, preimage_iSup]

/-- The comparison prism commutes with restriction along an injective time operator. -/
theorem prism_timeOperator {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) :
    prism c ⦋m⦌ ≫ SSet.stdSimplex.map (timeOperator c n j hj) =
      (simplex ⦋k⦌ ◁ SSet.stdSimplex.map j) ≫ prism c ⦋n⦌ := by
  unfold timeOperator
  rw [prism_map, SSet.stdSimplex.{0}.map_id ⦋k⦌, MonoidalCategory.id_tensorHom]

private def facePreimageIso (S : TF) (hs : S.Nonempty) :
    simplex ⦋k⦌ ⊗ simplex (timeDegree S) ≅ (timeFace c n S).preimage (fullPrism c) := by
  let j := timeInclusion S hs
  let f := simplex ⦋k⦌ ◁ SSet.stdSimplex.map j
  letI : Mono f := whiskerLeft_timeInclusion_mono k n S hs
  have h : range f = (timeFace c n S).preimage (fullPrism c) := by
    change range ((𝟙 (simplex ⦋k⦌)) ⊗ₘ SSet.stdSimplex.map (timeInclusion S hs)) = _
    rw [range_tensorHom, range_eq_top, timeFace_range_timeInclusion n S hs, timeFace_preimage]
  exact asIso (toRange f) ≪≫ SSet.Subcomplex.eqToIso h

private theorem facePreimageIso_ι (S : TF) (hs : S.Nonempty) :
    (facePreimageIso c S hs).hom ≫ ((timeFace c n S).preimage (fullPrism c)).ι =
      simplex ⦋k⦌ ◁ SSet.stdSimplex.map (timeInclusion S hs) := by
  simp [facePreimageIso, Category.assoc]

private theorem facePreimageIso_compare (S : TF) (hs : S.Nonempty) :
    (facePreimageIso c S hs).hom ≫ (timeFace c n S).fromPreimage (fullPrism c) =
      prism c (timeDegree S) ≫ (timeFaceIso c n S hs).hom := by
  apply (cancel_mono (timeFace c n S).ι).1
  simp only [Category.assoc, fromPreimage_ι, timeFaceIso_ι]
  rw [← Category.assoc, facePreimageIso_ι]
  exact (prism_timeOperator c (timeInclusion S hs) (timeInclusion_injective S hs)).symm

private theorem boundaryMap_over {Y : SSet.{0}} (p : X ⟶ Y)
    (q : simplex (common ⦋k⦌ ⦋n⦌) ⟶ Y)
    (h : ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom),
      β.map j hj hn ≫ p = SSet.stdSimplex.map (timeOperator c n j hj) ≫ q) :
    boundaryMap c β ≫ p = (timeBoundary c n).ι ≫ q := by
  apply Multicofork.IsColimit.hom_ext (boundaryCover (n := n) c).isColimit
  intro a
  change Fin (n + 1) at a
  let S := Finset.univ.erase a
  let inc := SSet.Subcomplex.homOfLE (facet_le_boundary c a)
  change inc ≫ (boundaryMap c β ≫ p) = inc ≫ (timeBoundary c n).ι ≫ q
  rw [← Category.assoc inc, boundaryMap_face, ← Category.assoc inc, homOfLE_ι]
  by_cases hs : S.Nonempty
  · rw [← cancel_epi (timeFaceIso c n S hs).hom, ← Category.assoc, faceMap_iso,
      h, ← Category.assoc, timeFaceIso_ι]
  · have he := timeFace_eq_bot c n S hs
    exact (isInitialBot.ofIso (SSet.Subcomplex.eqToIso he.symm)).hom_ext _ _

private theorem boundaryMap_overlap (v : simplex ⦋k⦌ ⊗ simplex ⦋n⦌ ⟶ X)
    (h : ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom),
      prism c ⦋m⦌ ≫ β.map j hj hn = (simplex ⦋k⦌ ◁ SSet.stdSimplex.map j) ≫ v) :
    (timeBoundary c n).fromPreimage (fullPrism c) ≫ boundaryMap c β =
      ((timeBoundary c n).preimage (fullPrism c)).ι ≫ v := by
  apply Multicofork.IsColimit.hom_ext (preimageCover (n := n) c).isColimit
  intro a
  change Fin (n + 1) at a
  let S := Finset.univ.erase a
  let hq : preimageFacet c a ≤ (timeBoundary c n).preimage (fullPrism c) :=
    fun d ↦ Set.preimage_mono (facet_le_boundary c a d)
  let inc := SSet.Subcomplex.homOfLE hq
  change inc ≫ (timeBoundary c n).fromPreimage (fullPrism c) ≫ boundaryMap c β =
    inc ≫ ((timeBoundary c n).preimage (fullPrism c)).ι ≫ v
  rw [homOfLE_ι_assoc]
  have he : inc ≫ (timeBoundary c n).fromPreimage (fullPrism c) =
      (facet c a).fromPreimage (fullPrism c) ≫ SSet.Subcomplex.homOfLE (facet_le_boundary c a) :=
    JTFiniteSubcomplexPreimageGluing.fromPreimage_homOfLE (fullPrism c) (facet_le_boundary c a)
  rw [← Category.assoc inc, he, Category.assoc, boundaryMap_face]
  by_cases hs : S.Nonempty
  · rw [← cancel_epi (facePreimageIso c S hs).hom, reassoc_of% facePreimageIso_compare,
      faceMap_iso, reassoc_of% facePreimageIso_ι]
    exact h (timeInclusion S hs) (timeInclusion_injective S hs)
      (timeInclusion_not_surj hs (erase_ne_univ a))
  · have he : preimageFacet c a = ⊥ := by
      change (timeFace c n S).preimage (fullPrism c) = _
      rw [timeFace_eq_bot c n S hs]
      rfl
    exact (isInitialBot.ofIso (SSet.Subcomplex.eqToIso he.symm)).hom_ext _ _

end Prism

section Fill

open JTFixedLiftSpaceTimeEquiv
open JTCommonCoefficientLiftChoices (Extension underlying underlying_timeMap)

variable {A Y : SSet.{0}} {i : A ⟶ simplex ⦋k⦌}
variable {t : A ⟶ X} {p : X ⟶ Y} [Fibration p] {g : simplex b ⟶ Y}
variable (sq : CommSq t i p (SSet.stdSimplex.map c ≫ g))

/-- Fill the all-face boundary of choices while retaining the exact original
simplex and each original enlarged prescribed face. -/
theorem fill_compatible_boundary
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋n⦌))
    (choice : ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌), Function.Injective j.toOrderHom →
      (¬ Function.Surjective j.toOrderHom) → Extension sq ⦋m⦌)
    (hcomp : ∀ {l m : ℕ} (a : ⦋l⦌ ⟶ ⦋m⦌) (j : ⦋m⦌ ⟶ ⦋n⦌)
      (ha : Function.Injective a.toOrderHom) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom),
      (choice (a ≫ j) (hj.comp ha) (fun he ↦ hn (Function.Surjective.of_comp he))).map =
        SSet.stdSimplex.map (timeOperator c m a ha) ≫ (choice j hj hn).map)
    (hv : ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom),
      underlying sq (choice j hj hn) = (SSet.ihomToPullbackFiber sq : SSet.{0}).map j.op v) :
    ∃ E : Extension sq ⦋n⦌, underlying sq E = v ∧
      ∀ {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
        (hn : ¬ Function.Surjective j.toOrderHom),
        SSet.stdSimplex.map (timeOperator c n j hj) ≫ E.map = (choice j hj hn).map := by
  let β : BoundaryFamily (n := n) c X := ⟨fun j hj hn ↦ (choice j hj hn).map, hcomp⟩
  have hbase (m : ℕ) (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom) :
      timeOperator c n j hj ≫ base c ⦋n⦌ = base c ⦋m⦌ :=
    map_base (𝟙 ⦋k⦌) (Category.id_comp c) j hj
  have hb := boundaryMap_over c β p (SSet.stdSimplex.map (base c ⦋n⦌) ≫ g)
    (fun j hj hn ↦ by
      change (choice j hj hn).map ≫ p =
        SSet.stdSimplex.map (timeOperator c n j hj) ≫ SSet.stdSimplex.map (base c ⦋n⦌) ≫ g
      rw [(choice j hj hn).over, ← Category.assoc, ← SSet.stdSimplex.map_comp, hbase])
  have hP := boundaryMap_overlap c β (timeMap sq ⦋n⦌ v)
    (fun j hj hn ↦ by
      change prism c _ ≫ (choice j hj hn).map = _
      rw [← underlying_timeMap sq, hv, timeMap_map])
  obtain ⟨E, hE, hB⟩ := exists_extension_relative c n sq v (boundaryMap c β) hb hP.symm
  refine ⟨E, ?_, ?_⟩
  · apply (timeEquiv sq ⦋n⦌).injective
    apply Subtype.ext
    change timeMap sq ⦋n⦌ (underlying sq E) = timeMap sq ⦋n⦌ v
    exact (underlying_timeMap sq E).trans hE
  · intro m j hj hn
    obtain ⟨a, ha, hb⟩ := exists_boundaryMap_operator c β j hj hn
    rw [← ha, Category.assoc, hB, hb]

end Fill
end
end DaggerModels.PartII.JTCommonCoefficientParameter
