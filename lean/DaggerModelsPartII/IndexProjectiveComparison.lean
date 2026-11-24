import DaggerModelsPartII.IndexKanExtensions
import TopCatModelCategory.QuillenAdjunction

/-! The projective Quillen adjunction from change of index. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe v w

namespace DaggerModels.PartII

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  [ModelCategory SSet.{max v w}]
  [ModelCategory (Cᵒᵖ ⥤ SSet.{max v w})]
  [ModelCategory (Dᵒᵖ ⥤ SSet.{max v w})]

/-- For projective diagram model structures, restriction is right Quillen.
The four equalities are the defining classes of the projective structures. -/
theorem extendIndexLeft_isQuillen (F : C ⥤ D)
    (hCF : fibrations (Cᵒᵖ ⥤ SSet.{max v w}) =
      (fibrations SSet.{max v w}).functorCategory Cᵒᵖ)
    (hDF : fibrations (Dᵒᵖ ⥤ SSet.{max v w}) =
      (fibrations SSet.{max v w}).functorCategory Dᵒᵖ)
    (hCW : weakEquivalences (Cᵒᵖ ⥤ SSet.{max v w}) =
      (weakEquivalences SSet.{max v w}).functorCategory Cᵒᵖ)
    (hDW : weakEquivalences (Dᵒᵖ ⥤ SSet.{max v w}) =
      (weakEquivalences SSet.{max v w}).functorCategory Dᵒᵖ) :
    (extendIndexLeftAdjunction.{v, w} F).IsQuillenAdjunction := by
  let R := restrictIndex.{v, w} F
  have hFib : R.PreservesFibrations := by
    refine R.preservesFibrations_iff.mpr fun _ _ f hf ↦ ?_
    rw [hDF] at hf
    rw [hCF]
    exact fun c ↦ hf (F.op.obj c)
  have hTriv : R.PreservesTrivialFibrations := by
    constructor
    intro X Y f hf
    change (fibrations _ f ∧ weakEquivalences _ f) at hf
    change fibrations _ (R.map f) ∧ weakEquivalences _ (R.map f)
    rw [hDF, hDW] at hf
    rw [hCF, hCW]
    exact ⟨fun c ↦ hf.1 (F.op.obj c), fun c ↦ hf.2 (F.op.obj c)⟩
  have hCof := (extendIndexLeftAdjunction.{v, w} F)
    |>.preservesTrivialFibrations_iff_preservesCofibrations |>.mp hTriv
  letI := hCof
  letI := hFib
  exact ⟨⟩

end DaggerModels.PartII
