import DaggerModelsPartII.ActionStrictOrbits
import OriginalActionFreeForgetAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Strict orbits of free action cells

The orbit of a free action is naturally the underlying cell. This is the
categorical half of the Borel free-cell cancellation bridge and keeps
naturality in arbitrary cell maps.
-/

set_option autoImplicit false

open CategoryTheory Limits
open DaggerOriginalActionFreeForgetAdjunction

universe w v u

namespace DaggerModels.PartII.BorelFreeCellOrbits

noncomputable section

variable (V : Type u) [Category.{v} V] [HasColimits V]
  (G : Type w) [Group G] [HasColimitsOfSize.{w, w} V]
  [HasColimitsOfShape (SingleObj G) V]

private def trivialForgetIso :
    ActionStrictOrbits.trivial V G ⋙ Action.forget V G ≅ 𝟭 V :=
  Iso.refl _

/-- The orbit of the native free action is naturally isomorphic to the
original object, including naturality in every morphism. -/
def freeOrbitIso :
    freeActionFunctor V G ⋙ ActionStrictOrbits.orbit V G ≅ 𝟭 V := by
  let adj : freeActionFunctor V G ⋙ ActionStrictOrbits.orbit V G ⊣
      ActionStrictOrbits.trivial V G ⋙ Action.forget V G :=
    (freeForgetAdjunction V G).comp (ActionStrictOrbits.orbitAdjunction V G)
  exact Adjunction.leftAdjointUniq (adj.ofNatIsoRight (trivialForgetIso V G))
    Adjunction.id

end

end DaggerModels.PartII.BorelFreeCellOrbits
