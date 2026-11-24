import DaggerModelsPartII.JTFiniteCoefficientBridgeFaceCover
import DaggerModelsPartII.JTChangingCoefficientBridgeLift

/-!
# Stationary vertical sections for compatible enlarged faces
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v w

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeVertex

open JTFiniteCoefficientBridgeOrder (bridge base)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgePrism (prism vertical verticalSection_prism)
open JTFiniteCoefficientBridgeCopyFace (copyFace timeFace)
open JTFiniteCoefficientBridgeFaceCover (facePrism exists_extension_of_faces)

noncomputable section

private abbrev simplex (n : SimplexCategory) := SSet.stdSimplex.{v}.obj n
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable {ι : Type w} [Fintype ι] (S : ι → Finset (Fin (m + 1)))

/-- The selected coefficient vertex as an actual standard simplex map. -/
abbrev vertex (k : SimplexCategory) (a : Fin (k.len + 1)) : simplex.{v} ⦋0⦌ ⟶ simplex k :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k a)

variable {X Y : SSet.{v}} {p : X ⟶ Y} [Fibration p]
variable (g : simplex b' ⟶ Y) (a : Fin (k.len + 1)) (t : simplex ⦋0⦌ ⟶ X)
variable (sq : CommSq t (vertex k a) p (SSet.stdSimplex.map u ≫ g))
variable (E : ∀ e, (copyFace.{v} c u n (S e)).toSSet ⟶ X)

include sq in
/-- Overlapping prescribed faces extend with a stationary complete
vertical simplex at the selected coefficient vertex. -/
theorem exists_vertex_extension_of_faces
    (hoverlap : ∀ e e', SSet.Subcomplex.homOfLE
      (inf_le_left : copyFace c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e)) ≫ E e =
      SSet.Subcomplex.homOfLE
        (inf_le_right : copyFace c u n (S e) ⊓ copyFace c u n (S e') ≤ copyFace c u n (S e')) ≫ E e')
    (hbase : ∀ e, E e ≫ p = (copyFace c u n (S e)).ι ≫ SSet.stdSimplex.map (base c u n) ≫ g)
    (hstat : ∀ e, (vertex k a ▷ (timeFace.{v} n (S e)).toSSet) ≫
      facePrism c u n (S e) ≫ E e = fst (simplex ⦋0⦌) (timeFace n (S e)).toSSet ≫ t) :
    ∃ L : simplex (bridge k n m) ⟶ X,
      (∀ e, (copyFace c u n (S e)).ι ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c u n) ≫ g ∧
      SSet.stdSimplex.map (vertical c u n a) ≫ L = term (simplex (time m n)) ≫ t := by
  haveI : Mono (vertex.{v} k a) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence (vertex.{v} k a) := JTInterleavedParameter.standardMap_weak _
  obtain ⟨L, hL, hp, hv⟩ := exists_extension_of_faces c u n S g sq E hoverlap hbase hstat
  refine ⟨L, hL, hp, ?_⟩
  have H : JTHigherInterleavedParameter.verticalSection.{v} k (time m n) a =
      lift (term (simplex (time m n))) (𝟙 (simplex (time m n))) ≫
        (vertex k a ▷ simplex (time m n)) := by
    rw [JTChangingCoefficientBridgeLift.vertex_tensor, lift_snd_assoc, Category.id_comp]
  rw [← verticalSection_prism, H, Category.assoc, Category.assoc, hv, lift_fst_assoc]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeRelativeVertex
