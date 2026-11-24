import DaggerModelsPartII.JTOrderedLabelPaddingPrism

/-! The original coefficient simplex remains fixed on each time slice
of a higher padded realization. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels.PartII.JTOrderedLabelPaddingSpace (embedding square)
open DaggerModels.PartII.JTCommonCoefficientParameter (prism slice)

namespace DaggerModels.PartII.JTOrderedLabelPaddingSliceComparison

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k

variable {Y : SSet.{0}} {k n : SimplexCategory} {a : Y.obj (op k)}

private theorem ordinarySlice_embedding (t : Fin (n.len + 1)) :
    embedding k ≫ JTHigherInterleavedParameter.ordinarySlice (JTPaddedTimeOperators.pad k) n t =
      JTHigherInterleavedParameter.ordinarySlice k n t ≫
        (embedding k ▷ simplex n) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [JTHigherInterleavedParameter.ordinarySlice]
  · simp [JTHigherInterleavedParameter.ordinarySlice]
    rw [embedding, ← SSet.stdSimplex.map_comp]
    congr 1

/-- Any chosen time slice of a higher padded realization restricts on the
original coefficient simplex to exactly the original label. -/
theorem slice_interior_fixed
    {v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n)}
    (s : JTOrderedLabelPaddingPrism.Realizations v)
    (t : Fin (n.len + 1)) :
    embedding k ≫ SSet.stdSimplex.map (slice (JTOrderedLabelPaddingPrism.blocks k) n t) ≫
      s.val = SSet.yonedaEquiv.symm a := by
  rw [← JTCommonCoefficientParameter.ordinarySlice_prism]
  calc
    _ = (embedding k ≫
          JTHigherInterleavedParameter.ordinarySlice (JTPaddedTimeOperators.pad k) n t) ≫
        prism (JTOrderedLabelPaddingPrism.blocks k) n ≫ s.val := rfl
    _ = (JTHigherInterleavedParameter.ordinarySlice k n t ≫
          (embedding k ▷ simplex n)) ≫
        prism (JTOrderedLabelPaddingPrism.blocks k) n ≫ s.val := by
      rw [ordinarySlice_embedding]
    _ = JTHigherInterleavedParameter.ordinarySlice k n t ≫
        fst (simplex k) (simplex n) ≫ SSet.yonedaEquiv.symm a := by
      have h := congrArg
        (fun f : simplex k ⊗ simplex n ⟶ Y ↦
          JTHigherInterleavedParameter.ordinarySlice k n t ≫ f)
        (JTOrderedLabelPaddingPrism.interior_fixed s)
      simpa only [Category.assoc] using h
    _ = SSet.yonedaEquiv.symm a := by
      simp [JTHigherInterleavedParameter.ordinarySlice]

end
end DaggerModels.PartII.JTOrderedLabelPaddingSliceComparison
