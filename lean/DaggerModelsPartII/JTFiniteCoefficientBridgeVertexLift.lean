import DaggerModelsPartII.JTFiniteCoefficientBridgeLift
import DaggerModelsPartII.JTChangingCoefficientBridgeLift

/-!
# The stationary vertical section of a finite joining prism
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeVertexLift

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime JTFiniteCoefficientBridgePrism

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
variable (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)

private abbrev vertex (k : SimplexCategory) (a : Fin (k.len + 1)) :
    simplex.{u} ⦋0⦌ ⟶ simplex k :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k a)

abbrev sideVertical (a : Fin (k.len + 1)) (e : Fin (m + 1)) :
    n ⟶ JTHigherInterleavedParameter.common k n :=
  JTCommonCoefficientParameter.vertical (c e) n a

/-- The full vertical simplex at a selected coefficient vertex remains
stationary, including the entire time simplex joining all copies. -/
theorem exists_vertex_extension {X Y : SSet.{u}} {p : X ⟶ Y} [Fibration p]
    (g : simplex b' ⟶ Y) (a : Fin (k.len + 1)) (t : simplex ⦋0⦌ ⟶ X)
    (sq : CommSq t (vertex k a) p
      (SSet.stdSimplex.map u ≫ g))
    (E : (e : Fin (m + 1)) → simplex (JTHigherInterleavedParameter.common k n) ⟶ X)
    (hbase : ∀ e, E e ≫ p =
      SSet.stdSimplex.map (side c u h hu n e) ≫ SSet.stdSimplex.map (base c u n) ≫ g)
    (hvert : ∀ e, SSet.stdSimplex.map (sideVertical c n a e) ≫ E e =
      SSet.stdSimplex.isTerminalObj₀.from (simplex n) ≫ t) :
    ∃ L : simplex (bridge k n m) ⟶ X,
      (∀ e, SSet.stdSimplex.map (side c u h hu n e) ≫ L = E e) ∧
      L ≫ p = SSet.stdSimplex.map (base c u n) ≫ g ∧
      SSet.stdSimplex.map (vertical c u n a) ≫ L =
        SSet.stdSimplex.isTerminalObj₀.from (simplex (time m n)) ≫ t := by
  let i := vertex.{u} k a
  haveI : Mono i := SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence i := JTInterleavedParameter.standardMap_weak _
  have hs (e : Fin (m + 1)) : JTHigherInterleavedParameter.verticalSection.{u} k n a ≫
      JTCommonCoefficientParameter.prism (c e) n = SSet.stdSimplex.map (sideVertical c n a e) := by
    exact JTCommonCoefficientParameter.verticalSection_prism (c e) n a
  have hstat (e : Fin (m + 1)) : (i ▷ simplex n) ≫ JTCommonCoefficientParameter.prism (c e) n ≫ E e =
      fst (simplex ⦋0⦌) (simplex n) ≫ t := by
    change (vertex k a ▷ simplex n) ≫ _ = _
    rw [JTChangingCoefficientBridgeLift.vertex_tensor, Category.assoc, ← Category.assoc
      (JTHigherInterleavedParameter.verticalSection k n a), hs, hvert,
      ← Category.assoc]
    congr 1
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  obtain ⟨L, hL, hP, hV⟩ := JTFiniteCoefficientBridgeLift.exists_extension c u h hu n g sq E hbase hstat
  refine ⟨L, hL, hP, ?_⟩
  have hc : JTHigherInterleavedParameter.verticalSection.{u} k (time m n) a =
      lift (SSet.stdSimplex.isTerminalObj₀.from (simplex (time m n))) (𝟙 (simplex (time m n))) ≫
        (i ▷ simplex (time m n)) := by
    change _ = _ ≫ (vertex k a ▷ _)
    rw [JTChangingCoefficientBridgeLift.vertex_tensor, lift_snd_assoc, Category.id_comp]
  rw [← verticalSection_prism, hc, Category.assoc, Category.assoc, hV, lift_fst_assoc]


end

end DaggerModels.PartII.JTFiniteCoefficientBridgeVertexLift
