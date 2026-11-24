import DaggerModelsPartII.JTFiniteCoefficientBridgeCopyFace
import DaggerModelsPartII.JTPrismTimeFaceExtension
import DaggerModelsPartII.JTDisjointSubcomplexCover

/-!
# Relative extension across overlapping copy subcollections
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v w

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeFaceCover

open JTFiniteCoefficientBridgeOrder (bridge base)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgePrism (prism prism_base prism_weak)
open JTFiniteCoefficientBridgeCopyFace
open SSet.Subcomplex

noncomputable section

private abbrev simplex (n : SimplexCategory) := SSet.stdSimplex.{v}.obj n

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable {ι : Type w} (S : ι → Finset (Fin (m + 1)))

abbrev coefficientUnion := ⨆ e, copyFace.{v} c u n (S e)
abbrev timeUnion := ⨆ e, timeFace.{v} (m := m) n (S e)

private theorem preimage_iSup_faces :
    (coefficientUnion.{v} c u n S).preimage (prism c u n) =
      (⊤ : (simplex.{v} k).Subcomplex).prod (timeUnion.{v} n S) := by
  rw [preimage_iSup]
  simp only [copyFace_preimage_prism]
  ext q z
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  change (∃ e, z.1 ∈ (⊤ : (simplex.{v} k).Subcomplex).obj q ∧
      z.2 ∈ (timeFace.{v} (m := m) n (S e)).obj q) ↔
    z.1 ∈ (⊤ : (simplex.{v} k).Subcomplex).obj q ∧ z.2 ∈ (timeUnion.{v} n S).obj q
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨fun ⟨e, ha, hb⟩ ↦ ⟨ha, e, hb⟩, fun ⟨ha, e, hb⟩ ↦ ⟨e, ha, hb⟩⟩

private theorem inf_faces (t : Finset ι) :
    t.inf (fun e ↦ copyFace.{v} c u n (S e)) = copyFace c u n (t.inf S) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.inf_empty, Finset.top_eq_univ, copyFace_univ]
  | @insert e t he IH =>
      rw [Finset.inf_insert, Finset.inf_insert, IH, ← copyFace_inter]
      rfl

/-- A finite union of entire copy faces has weak comparison with its
preimage, using all actual intersections of those faces. -/
theorem unionComparison_weak [Fintype ι] :
    WeakEquivalence ((coefficientUnion.{v} c u n S).fromPreimage (prism c u n)) := by
  classical
  change WeakEquivalence ((⨆ e, copyFace.{v} c u n (S e)).fromPreimage (prism c u n))
  rw [← Finset.sup_univ_eq_iSup]
  apply JTFiniteSubcomplexPreimageGluing.weak_finset_sup
  intro t _ _
  rw [inf_faces c u n S t]
  exact copyFaceComparison_weak.{v} c u n (t.inf S)

private theorem tensor_hom_ext {A T X : SSet.{v}} (C : ι → T.Subcomplex)
    {v₁ v₂ : A ⊗ (⨆ e, C e : T.Subcomplex).toSSet ⟶ X}
    (h : ∀ e, (A ◁ JTDisjointSubcomplexCover.inclusion C e) ≫ v₁ =
      (A ◁ JTDisjointSubcomplexCover.inclusion C e) ≫ v₂) : v₁ = v₂ := by
  apply NatTrans.ext
  funext q z
  have H (x : T.obj q) (hx : x ∈ (⨆ e, C e : T.Subcomplex).obj q) :
      ∃ e, x ∈ (C e).obj q := by
    rwa [Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨e, he⟩ := H z.2.val z.2.property
  exact congrFun (NatTrans.congr_app (h e) q) (z.1, ⟨z.2.val, he⟩)

/-- The whole product prism restricted to one copy subcollection. -/
def facePrism (I : Finset (Fin (m + 1))) :
    simplex.{v} k ⊗ (timeFace.{v} (m := m) n I).toSSet ⟶
      (copyFace.{v} c u n I).toSSet :=
  (JTPrismTimeFaceExtension.preimageIso (prism.{v} c u n) (copyFace c u n I)
    (timeFace n I) (copyFace_preimage_prism c u n I)).hom ≫
      (copyFace c u n I).fromPreimage (prism c u n)

private abbrev f := prism.{v} c u n
private abbrev D (e : ι) := copyFace.{v} c u n (S e)
private abbrev C (e : ι) := timeFace.{v} (m := m) n (S e)
private abbrev Q (e : ι) :=
  JTPrismTimeFaceExtension.preimageIso (f.{v} c u n) (D.{v} c u n S e) (C.{v} n S e)
    (copyFace_preimage_prism.{v} c u n (S e))

variable {A X Y : SSet.{v}} {i : A ⟶ simplex k} {p : X ⟶ Y} {t : A ⟶ X}
variable [Mono i] [WeakEquivalence i] [Fibration p] [Fintype ι]
variable (g : simplex b' ⟶ Y) (sq : CommSq t i p (SSet.stdSimplex.map u ≫ g))
variable (E : ∀ e, (D.{v} c u n S e).toSSet ⟶ X)

include sq in
/-- Compatible maps prescribed on overlapping multi-copy faces extend
simultaneously, with the original base and full stationary equation. -/
theorem exists_extension_of_faces
    (hoverlap : ∀ e e', SSet.Subcomplex.homOfLE
      (inf_le_left : D c u n S e ⊓ D c u n S e' ≤ D c u n S e) ≫ E e =
      SSet.Subcomplex.homOfLE
        (inf_le_right : D c u n S e ⊓ D c u n S e' ≤ D c u n S e') ≫ E e')
    (hbase : ∀ e, E e ≫ p = (D c u n S e).ι ≫ SSet.stdSimplex.map (base c u n) ≫ g)
    (hstat : ∀ e, (i ▷ (C.{v} n S e).toSSet) ≫ facePrism.{v} c u n (S e) ≫ E e =
      fst A (C n S e).toSSet ≫ t) :
    ∃ L : simplex (bridge k n m) ⟶ X,
      (∀ e, (D c u n S e).ι ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c u n) ≫ g ∧
      (i ▷ simplex (time m n)) ≫ f c u n ≫ L = fst A (simplex (time m n)) ≫ t := by
  let P := f.{v} c u n
  let B := coefficientUnion.{v} c u n S
  let T := timeUnion.{v} n S
  let q := SSet.stdSimplex.map (base c u n) ≫ g
  let G := JTDisjointSubcomplexCover.glueCompatible (D.{v} c u n S) E hoverlap
  let I := JTPrismTimeFaceExtension.preimageIso P B T (preimage_iSup_faces c u n S)
  have hG (e : ι) : JTDisjointSubcomplexCover.inclusion (D.{v} c u n S) e ≫ G = E e :=
    JTDisjointSubcomplexCover.inclusion_glueCompatible _ _ _ _
  have hGbase : G ≫ p = B.ι ≫ q := by
    apply JTDisjointSubcomplexCover.hom_ext (D.{v} c u n S)
    intro e
    rw [← Category.assoc, hG, homOfLE_ι_assoc]
    exact hbase e
  let V := I.hom ≫ B.fromPreimage P ≫ G
  have hV (e : ι) :
      (simplex.{v} k ◁ JTDisjointSubcomplexCover.inclusion (C.{v} n S) e) ≫ V =
        (Q.{v} c u n S e).hom ≫ (D c u n S e).fromPreimage P ≫ E e := by
    let h₁ : D.{v} c u n S e ≤ B := le_iSup _ e
    let h₂ : C.{v} n S e ≤ T := le_iSup _ e
    let h₃ : (D.{v} c u n S e).preimage P ≤ B.preimage P :=
      fun a ↦ Set.preimage_mono (h₁ a)
    have H₀ : (simplex.{v} k ◁ SSet.Subcomplex.homOfLE h₂) ≫ I.hom =
        (Q.{v} c u n S e).hom ≫ SSet.Subcomplex.homOfLE h₃ :=
      JTPrismTimeFaceExtension.preimageIso_natural P B T (preimage_iSup_faces c u n S)
        (copyFace_preimage_prism c u n (S e)) h₁ h₂
    have H₁ : SSet.Subcomplex.homOfLE h₃ ≫ B.fromPreimage P =
        (D c u n S e).fromPreimage P ≫ SSet.Subcomplex.homOfLE h₁ :=
      JTFiniteSubcomplexPreimageGluing.fromPreimage_homOfLE P h₁
    change (simplex.{v} k ◁ SSet.Subcomplex.homOfLE h₂) ≫ I.hom ≫ B.fromPreimage P ≫ G = _
    rw [← Category.assoc (simplex.{v} k ◁ SSet.Subcomplex.homOfLE h₂), H₀, Category.assoc,
      ← Category.assoc (SSet.Subcomplex.homOfLE h₃), H₁, Category.assoc]
    change _ ≫ _ ≫ JTDisjointSubcomplexCover.inclusion (D.{v} c u n S) e ≫ G = _
    rw [hG]
  have hVstat : (i ▷ T.toSSet) ≫ V = fst A T.toSSet ≫ t := by
    apply tensor_hom_ext (C.{v} n S)
    intro e
    let j := JTDisjointSubcomplexCover.inclusion (C.{v} n S) e
    change (A ◁ j) ≫ (i ▷ T.toSSet) ≫ V = (A ◁ j) ≫ fst A T.toSSet ≫ t
    rw [← Category.assoc (A ◁ j), whisker_exchange, Category.assoc, hV,
      whiskerLeft_fst_assoc]
    simpa only [facePrism, Category.assoc] using hstat e
  have hf : P ≫ q = fst (simplex.{v} k) (simplex (time m n)) ≫ SSet.stdSimplex.map u ≫ g := by
    change prism c u n ≫ SSet.stdSimplex.map (base c u n) ≫ g = _
    rw [← Category.assoc, prism_base, Category.assoc]
  haveI : WeakEquivalence P := prism_weak c u n
  obtain ⟨L, hBL, hLp, hLs⟩ := JTPrismTimeFaceExtension.exists_extension P B T
    (preimage_iSup_faces c u n S) (unionComparison_weak c u n S) sq q hf G hGbase hVstat
  refine ⟨L, fun e ↦ ?_, hLp, hLs⟩
  have H : JTDisjointSubcomplexCover.inclusion (D.{v} c u n S) e ≫ B.ι =
      (D c u n S e).ι := homOfLE_ι _
  rw [← H, Category.assoc, hBL, hG]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeFaceCover
