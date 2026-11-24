import DaggerModelsPartII.JTDisjointSubcomplexCover
import DaggerModelsPartII.JTPrismSubcomplexExtension

/-!
# Simultaneous relative extension on a prism and disjoint sides
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerModels.PartII.JTDisjointPrismExtension

open SSet.Subcomplex

noncomputable section

variable {P K X Y : SSet.{u}} {ι : Type v} [Fintype ι] {B : ι → SSet.{u}}

/-- Extend the prescribed prism and all disjoint sides together. The
overlap tests use the actual preimages in the prism and the full side maps. -/
theorem exists_extension (f : P ⟶ K) [Mono f] [WeakEquivalence f]
    (j : ∀ e, B e ⟶ K) [∀ e, Mono (j e)]
    (hd : Pairwise fun e e' ↦ range (j e) ⊓ range (j e') = ⊥)
    (hw : ∀ e, WeakEquivalence ((range (j e)).fromPreimage f))
    {p : X ⟶ Y} [Fibration p] (q : K ⟶ Y)
    (v : P ⟶ X) (E : ∀ e, B e ⟶ X) (hv : v ≫ p = f ≫ q)
    (hE : ∀ e, E e ≫ p = j e ≫ q)
    (hcompat : ∀ e, ((range (j e)).preimage f).ι ≫ v =
      (range (j e)).fromPreimage f ≫ inv (toRange (j e)) ≫ E e) :
    ∃ L : K ⟶ X, f ≫ L = v ∧ (∀ e, j e ≫ L = E e) ∧ L ≫ p = q := by
  let A (e : ι) := range (j e)
  let F := ⨆ e, A e
  let G := JTDisjointSubcomplexCover.glue A hd (fun e ↦ inv (toRange (j e)) ≫ E e)
  let d := JTDisjointSubcomplexCover.rangeLeg j
  have hdF (e : ι) : d e ≫ F.ι = j e := JTDisjointSubcomplexCover.rangeLeg_ι j e
  have hdG (e : ι) : d e ≫ G = E e := by
    change (toRange (j e) ≫ JTDisjointSubcomplexCover.inclusion A e) ≫
      JTDisjointSubcomplexCover.glue A hd (fun e ↦ inv (toRange (j e)) ≫ E e) = _
    simp only [Category.assoc, JTDisjointSubcomplexCover.inclusion_glue, IsIso.hom_inv_id_assoc]
  have hG : G ≫ p = F.ι ≫ q := by
    apply JTDisjointSubcomplexCover.hom_ext A
    intro e
    apply (cancel_epi (toRange (j e))).1
    simp only [← Category.assoc]
    change (d e ≫ G) ≫ p = (d e ≫ F.ι) ≫ q
    rw [hdG, hdF, hE]
  let C (e : ι) := (A e).preimage f
  let S : MulticoequalizerDiagram (F.preimage f) C (fun e e' ↦ C e ⊓ C e') :=
    ⟨(preimage_iSup A f).symm, fun _ _ ↦ rfl⟩
  have hV : (F.preimage f).ι ≫ v = F.fromPreimage f ≫ G := by
    apply Multicofork.IsColimit.hom_ext S.isColimit
    intro e
    change ι at e
    let he : A e ≤ F := le_iSup A e
    let hpre : C e ≤ F.preimage f := fun n ↦ Set.preimage_mono (he n)
    let a := SSet.Subcomplex.homOfLE hpre
    change a ≫ (F.preimage f).ι ≫ v = a ≫ F.fromPreimage f ≫ G
    have ha : a ≫ F.fromPreimage f =
        (A e).fromPreimage f ≫ JTDisjointSubcomplexCover.inclusion A e :=
      JTFiniteSubcomplexPreimageGluing.fromPreimage_homOfLE f he
    rw [homOfLE_ι_assoc, ← Category.assoc a, ha, Category.assoc]
    change (C e).ι ≫ v = (A e).fromPreimage f ≫
      JTDisjointSubcomplexCover.inclusion A e ≫
        JTDisjointSubcomplexCover.glue A hd (fun e ↦ inv (toRange (j e)) ≫ E e)
    rw [JTDisjointSubcomplexCover.inclusion_glue]
    exact hcompat e
  obtain ⟨L, hf, hF, hLp⟩ := JTPrismSubcomplexExtension.exists_extension f F
    (JTDisjointSubcomplexCover.preimage_weak A f hd hw) q v G hv hG hV
  refine ⟨L, hf, fun e ↦ ?_, hLp⟩
  rw [← hdF, Category.assoc, hF, hdG]

end

end DaggerModels.PartII.JTDisjointPrismExtension
