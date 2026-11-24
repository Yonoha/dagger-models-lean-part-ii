import DaggerModelsPartII.JTRowRealizationGenerator

/-!
# Every actual raw simplex is the graph of a groupoid parameter map in a box

The coend relation removes the horizontal simplex operator and preserves the
entire groupoid parameter map. This gives a box indexed horizontally by the
degree of the raw simplex itself.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRealizationGraphGenerator

open OrdinaryJTRealization JTRealizationGenerators
open CartesianMonoidalCategory

noncomputable section

private abbrev Δ (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

theorem graph_generator_restriction (W : BiPresheaf) {d m k : SimplexCategory}
    (a : d ⟶ m) (s : Δ d ⟶ J k) (w : W.obj (op (m, k))) :
    lift (SSet.stdSimplex.map a) s ≫ generator W (m, k) w =
      lift (𝟙 (Δ d)) s ≫ generator W (d, k)
        (W.map (show (d, k) ⟶ (m, k) from (a, 𝟙 k)).op w) := by
  let f : (d, k) ⟶ (m, k) := (a, 𝟙 k)
  have h : lift (𝟙 (Δ d)) s ≫ tFunctor.map f =
      lift (SSet.stdSimplex.map a) s := by
    have hmap : tFunctor.map f = SSet.stdSimplex.map a ⊗ₘ 𝟙 (J k) := by
      rw [tFunctor_map]
      change SSet.stdSimplex.map a ⊗ₘ GroupoidSimplex.parameter.map (𝟙 k) = _
      rw [CategoryTheory.Functor.map_id]
    rw [hmap]
    apply CartesianMonoidalCategory.hom_ext
    · change (lift (𝟙 (Δ d)) s ≫ (SSet.stdSimplex.map a ⊗ₘ 𝟙 (J k))) ≫
          fst (Δ m) (J k) = lift (SSet.stdSimplex.map a) s ≫ fst (Δ m) (J k)
      rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst, Category.id_comp,
        lift_fst]
    · change (lift (𝟙 (Δ d)) s ≫ (SSet.stdSimplex.map a ⊗ₘ 𝟙 (J k))) ≫
          snd (Δ m) (J k) = lift (SSet.stdSimplex.map a) s ≫ snd (Δ m) (J k)
      simp only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]
  rw [← h, Category.assoc, generator_relation]

/-- A raw simplicial map from a standard simplex has a representative with
the literal horizontal identity and its original groupoid coordinate. -/
theorem exists_graph_generator (W : BiPresheaf) (d : SimplexCategory)
    (g : Δ d ⟶ realization.obj W) :
    ∃ (k : SimplexCategory) (w : W.obj (op (d, k))) (s : Δ d ⟶ J k),
      g = lift (𝟙 (Δ d)) s ≫ generator W (d, k) w := by
  obtain ⟨⟨m, k⟩, w, b, hb⟩ := exists_generator W (op d) (SSet.yonedaEquiv g)
  let v : Δ d ⟶ Δ m ⊗ J k := SSet.yonedaEquiv.symm b
  let a := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (v ≫ fst (Δ m) (J k)))
  let s := v ≫ snd (Δ m) (J k)
  have ha : SSet.stdSimplex.map a = v ≫ fst (Δ m) (J k) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_map]
    exact Equiv.symm_apply_apply _ _
  have hv : v = lift (SSet.stdSimplex.map a) s := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ha]
    · exact (lift_snd _ _).symm
  have hg : g = v ≫ generator W (m, k) w := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    simpa only [v, Equiv.apply_symm_apply] using hb.symm
  refine ⟨k, W.map (show (d, k) ⟶ (m, k) from (a, 𝟙 k)).op w, s, ?_⟩
  rw [hg, hv]
  exact graph_generator_restriction W a s w

/-- The graph factorization lands in the exact realized row label used in the
decorated cylinder, for all horizontal and parameter dimensions. -/
theorem exists_graph_realizedRowCoefficient
    (W : SegalLocalizers.ReverseDaggerSpace.{0}) (d : ℕ)
    (g : Δ ⦋d⦌ ⟶ realization.obj (JTReversalInput.ordinaryInput.obj W)) :
    ∃ (k : SimplexCategory)
      (w : (JTProjectiveOrderedFiberComparison.row W ⦋d⦌).obj (op k))
      (s : Δ ⦋d⦌ ⟶ J k),
      g = lift (𝟙 (Δ ⦋d⦌)) s ≫
        JTNecklaceLabelRealization.realizedLabel (Δ ⦋d⦌) W k
          (JTRowRealizationGenerator.rowCoefficient W d k w) := by
  obtain ⟨k, w, s, h⟩ := exists_graph_generator (JTReversalInput.ordinaryInput.obj W) ⦋d⦌ g
  exact ⟨k, w, s, by rw [JTRowRealizationGenerator.realizedRowCoefficient_eq_generator]; exact h⟩

end

end DaggerModels.PartII.JTRealizationGraphGenerator
