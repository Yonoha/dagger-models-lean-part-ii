import DaggerModelsPartII.JTOrderedLabelPaddingPrism

/-! Ordered chains in the original coefficient-time prism retain the original label. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels.PartII.JTOrderedLabelPaddingSpace (embedding)
open DaggerModels.PartII.JTCommonCoefficientParameter (prism)

namespace DaggerModels.PartII.JTOrderedLabelPaddingChainComparison

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k

variable {m k n : SimplexCategory}

/-- An ordered chain of original coefficient and time coordinates inside the padded prism. -/
def chainMap (f : m ⟶ k) (j : m ⟶ n) :
    m ⟶ JTHigherInterleavedParameter.common (JTPaddedTimeOperators.pad k) n :=
  SimplexCategory.Hom.mk ⟨fun i ↦
    JTCommonCoefficientParameter.vertexEquiv (JTOrderedLabelPaddingPrism.blocks k) n
      (JTPaddedTimeOperators.inside k (f.toOrderHom i), j.toOrderHom i),
    fun _ _ h ↦ (JTCommonCoefficientParameter.prismOrder
      (JTOrderedLabelPaddingPrism.blocks k) n).monotone
        ⟨(JTPaddedTimeOperators.inside k).monotone (f.toOrderHom.monotone h),
          j.toOrderHom.monotone h⟩⟩

/-- The chain is the Cartesian lift of its coefficient and time operators
followed by the ordered prism inclusion. -/
theorem chainMap_prism (f : m ⟶ k) (j : m ⟶ n) :
    SSet.stdSimplex.map (chainMap f j) =
      lift (SSet.stdSimplex.map f ≫ embedding k)
        (SSet.stdSimplex.map j) ≫ prism (JTOrderedLabelPaddingPrism.blocks k) n := by
  cases m using SimplexCategory.rec with
  | _ m =>
    cases k using SimplexCategory.rec with
    | _ k =>
      cases n using SimplexCategory.rec with
      | _ n => rfl

private theorem chain_lift_embedding (f : m ⟶ k) (j : m ⟶ n) :
    lift (SSet.stdSimplex.map f ≫ embedding k) (SSet.stdSimplex.map j) =
      lift (SSet.stdSimplex.map f) (SSet.stdSimplex.map j) ≫
        (embedding k ▷ simplex n) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

/-- Every ordered chain inside the original coefficient-time prism has
exactly the original coefficient label. -/
theorem chain_interior_fixed {Y : SSet.{0}} {a : Y.obj (op k)}
    {v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n)}
    (s : JTOrderedLabelPaddingPrism.Realizations v)
    (f : m ⟶ k) (j : m ⟶ n) :
    SSet.stdSimplex.map (chainMap f j) ≫ s.val =
      SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm a := by
  rw [chainMap_prism, chain_lift_embedding]
  simp only [Category.assoc, JTOrderedLabelPaddingPrism.interior_fixed]
  simp

/-- Restrict a chain along any simplex operator. -/
theorem chainMap_precomp {r : SimplexCategory} (h : r ⟶ m)
    (f : m ⟶ k) (j : m ⟶ n) :
    h ≫ chainMap f j = chainMap (h ≫ f) (h ≫ j) := by
  ext i : 3
  rfl

/-- The chain inclusion commutes with an arbitrary original coefficient
operator and an injective time operator. -/
theorem chainMap_map {l p : SimplexCategory} (f : m ⟶ k) (j : m ⟶ n)
    (g : k ⟶ l) (θ : n ⟶ p) (hθ : Function.Injective θ.toOrderHom) :
    chainMap f j ≫ JTCommonCoefficientParameter.map
      (JTPaddedTimeOperators.map g) (JTOrderedLabelPaddingPrism.map_blocks g) θ hθ =
      chainMap (f ≫ g) (j ≫ θ) := by
  ext i : 3
  simpa only [chainMap, JTPaddedTimeOperators.map_inside] using
    (JTCommonCoefficientParameter.map_vertexEquiv
      (JTPaddedTimeOperators.map g) (JTOrderedLabelPaddingPrism.map_blocks g)
      θ hθ (JTPaddedTimeOperators.inside k (f.toOrderHom i), j.toOrderHom i))

/-- The naturality square also commutes after a chain operator is factored
through an existing parameter simplex. -/
theorem chainMap_factor_map {r l p : SimplexCategory}
    (h : r ⟶ m) (f : m ⟶ k) (j : m ⟶ n)
    (g : k ⟶ l) (θ : n ⟶ p) (hθ : Function.Injective θ.toOrderHom) :
    h ≫ chainMap f j ≫ JTCommonCoefficientParameter.map
      (JTPaddedTimeOperators.map g) (JTOrderedLabelPaddingPrism.map_blocks g) θ hθ =
      chainMap ((h ≫ f) ≫ g) ((h ≫ j) ≫ θ) := by
  rw [← Category.assoc, chainMap_precomp, chainMap_map]

end

end DaggerModels.PartII.JTOrderedLabelPaddingChainComparison
