import DaggerModelsPartII.OrdinaryJTRealization

/-! Reversal of the ordinary JT parameter's first simplex index. -/

set_option autoImplicit false

open CategoryTheory

namespace DaggerModels.PartII.JTReversalIndex

open OrdinaryJTRealization

/-- Reverse the horizontal simplex operator and retain the groupoid parameter. -/
def indexReversal : Index ⥤ Index :=
  SimplexCategory.rev.prod (𝟭 SimplexCategory)

@[simp] theorem indexReversal_obj (m k : SimplexCategory) :
    indexReversal.obj (m, k) = (m, k) := rfl

@[simp] theorem indexReversal_map {m m' k k' : SimplexCategory}
    (f : (m, k) ⟶ (m', k')) :
    indexReversal.map f = (SimplexCategory.rev.map f.1, f.2) := rfl

/-- Reversing the first simplex index twice is the identity on the full
two-variable index, with the identity object comparison. -/
def indexReversalSquareIso : indexReversal ⋙ indexReversal ≅ 𝟭 Index :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro p q f
    apply Prod.ext
    · simp [indexReversal, SimplexCategory.rev_map_rev_map]
    · rfl)

end DaggerModels.PartII.JTReversalIndex
