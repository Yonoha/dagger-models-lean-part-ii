import SimplicialReplacementChosenFiber
import NativeSimplicialReplacementWeightsChange

/-!
# Chosen fiber of a change of simplicial-replacement weights

At an unchanged constant chain, the change of whole coefficient simplices
has precisely the original coefficient map as its strict fiber map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerNativeSimplicialReplacement (replacement diagonalProjection)
open DaggerNativeSimplicialReplacementWeightsChange (diagonalChange)
open DaggerSimplicialReplacementChosenFiber

namespace DaggerModels.PartII.SimplicialReplacementWeightsChosenFiber
noncomputable section

universe u
variable {C : Type u} [Category.{u} C]
variable {G H : C ⥤ SSet.{u}} (η : G ⟶ H) (c : C)

/-- At the same complete constant chain, changing the whole weight is
literally the original component of the natural transformation. -/
theorem diagonalInclusion_changeWeights :
    diagonalInclusion G c ≫ diagonalChange η =
      η.app c ≫ diagonalInclusion H c := by
  apply NatTrans.ext
  funext q x
  rfl

/-- The map from a chosen value to the zero simplex is unique. -/
private theorem zeroMap_natural :
    η.app c ≫ zeroMap (H.obj c) = zeroMap (G.obj c) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Both vertical projection squares paste to the same unchanged chain.
The resulting top square is a strict pullback for arbitrary weights. -/
theorem chosenValue_isPullback :
    IsPullback (diagonalInclusion G c) (η.app c)
      (diagonalChange η) (diagonalInclusion H c) := by
  have hOuter : IsPullback (diagonalInclusion G c)
      (η.app c ≫ zeroMap (H.obj c))
      (diagonalChange η ≫ diagonalProjection H) (chainPoint c) := by
    rw [zeroMap_natural η c,
      DaggerNativeSimplicialReplacementWeightsChange.projection_square]
    exact diagonalInclusion_isPullback G c
  exact IsPullback.of_bot hOuter
    (diagonalInclusion_changeWeights η c)
    (diagonalInclusion_isPullback H c)

/-- The strict chosen fiber of the whole weight-change map is the
original value `G.obj c`, with the entire `H.obj c` retained. -/
def valueFiberIso : G.obj c ≅
    pullback (diagonalChange η) (diagonalInclusion H c) :=
  (chosenValue_isPullback η c).isoPullback

/-- The first projection is exactly the original constant-chain inclusion. -/
theorem valueFiberIso_fst :
    (valueFiberIso η c).hom ≫
      pullback.fst (diagonalChange η) (diagonalInclusion H c) =
        diagonalInclusion G c :=
  (chosenValue_isPullback η c).isoPullback_hom_fst

/-- The second projection is exactly the original coefficient map. -/
theorem valueFiberIso_snd :
    (valueFiberIso η c).hom ≫
      pullback.snd (diagonalChange η) (diagonalInclusion H c) = η.app c :=
  (chosenValue_isPullback η c).isoPullback_hom_snd

#print axioms diagonalInclusion_changeWeights
#print axioms chosenValue_isPullback
#print axioms valueFiberIso
#print axioms valueFiberIso_fst
#print axioms valueFiberIso_snd

end
end DaggerModels.PartII.SimplicialReplacementWeightsChosenFiber
