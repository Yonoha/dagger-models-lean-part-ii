import DaggerModelsPartII.JTReversalInput
import DaggerModelsPartII.JTReversalIndex

/-!
# Horizontal reversal on ordinary JT inputs

The horizontal reversal of a reversal simplicial space induces an involutive
reindexing of its underlying ordinary bisimplicial presheaf.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels

namespace DaggerModels.PartII.JTSimplexReversal

open JTReversalInput JTReversalIndex OrdinaryJTRealization SegalLocalizers

noncomputable section

/-- Reversal intertwines ordinary inclusion with order reversal. -/
def inclusionReversalIso :
    ReverseSimplex.inclusion ≅ SimplexCategory.rev ⋙ ReverseSimplex.inclusion :=
  NatIso.ofComponents
    (fun n =>
      { hom := ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n)
        inv := ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n)
        hom_inv_id := ReverseSimplex.reversal_comp_reversal _
        inv_hom_id := ReverseSimplex.reversal_comp_reversal _ })
    (fun f => ReverseSimplex.reversal_naturality f)

/-- Horizontal reversal, natural in both ordinary simplex directions. -/
def horizontalIso (W : ReverseDaggerSpace.{0}) :
    ordinaryInput.obj W ≅ indexReversal.op ⋙ ordinaryInput.obj W := by
  let i := (NatIso.op inclusionReversalIso).symm
  let j := Functor.isoWhiskerRight i W
  let k := Functor.uncurry.mapIso j
  let l := ((Functor.whiskeringLeft _ _ _).obj
    (CategoryTheory.prodOpEquiv (C := SimplexCategory)
      (D := SimplexCategory)).functor).mapIso k
  exact l

/-- At a represented pair, horizontal reversal is the given action of
`ReverseSimplex.reversal` on the first simplicial direction. -/
@[simp] theorem horizontalIso_hom_app (W : ReverseDaggerSpace.{0})
    (m k : SimplexCategory) :
    (horizontalIso W).hom.app (op (m, k)) =
      (W.map (ReverseSimplex.reversal
        (ReverseSimplex.inclusion.obj m)).op).app (op k) := rfl

/-- Horizontal reversal squares to the identity on every bisimplex. -/
theorem horizontal_twice (W : ReverseDaggerSpace.{0})
    (m k : SimplexCategory)
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (horizontalIso W).hom.app (op (m, k))
      ((horizontalIso W).hom.app (op (m, k)) w) = w := by
  rw [horizontalIso_hom_app]
  change ((W.map (ReverseSimplex.reversal
      (ReverseSimplex.inclusion.obj m)).op ≫
    W.map (ReverseSimplex.reversal
      (ReverseSimplex.inclusion.obj m)).op).app (op k)) w = w
  rw [← W.map_comp, ← op_comp, ReverseSimplex.reversal_comp_reversal,
    op_id, W.map_id]
  rfl

/-- The horizontal reversal commutes with maps of reversal simplicial spaces. -/
theorem horizontal_naturality_input {W V : ReverseDaggerSpace.{0}}
    (f : W ⟶ V) (m k : SimplexCategory)
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (horizontalIso V).hom.app (op (m, k))
      ((ordinaryInput.map f).app (op (m, k)) w) =
      (ordinaryInput.map f).app (op (m, k))
        ((horizontalIso W).hom.app (op (m, k)) w) := by
  rw [horizontalIso_hom_app, horizontalIso_hom_app,
    ordinaryInput_map_app]
  exact congrFun (congrArg (fun h => h.app (op k))
    (f.naturality (ReverseSimplex.reversal
      (ReverseSimplex.inclusion.obj m)).op).symm) w

end

end DaggerModels.PartII.JTSimplexReversal
