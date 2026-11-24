import DaggerModelsPartII.NerveSimplexResolutionHomotopy
import NativeSimplexIndexNerveWeakContractibility

/-!
# Last-vertex evaluation for the original simplex-index nerve

This file constructs the literal last-ordinal evaluation for an arbitrary
simplicial set. The comparison with the full-parameter augmentation is
kept separate until its switch homotopy has been proved.
-/

set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeSimplexIndexResolution
open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)
open DaggerModels.PartII.SimplexResolutionLastOrdinal
open DaggerModels.PartII.SimplexResolutionSwitch
universe u
namespace DaggerModels.PartII.SimplexIndexLastVertexWeak
noncomputable section

variable (X : SSet.{0})

/-- The original degree of a lifted simplex-index object. -/
def degree : LiftedIndex X ⥤ SimplexCategory :=
  ULiftHom.down.{0, 0, 0} ⋙ CostructuredArrow.proj uliftYoneda X

/-- The full last-vertex ordinal, including every original suffix arrow. -/
def lastOrdinalPoint {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q) : ((diagram X).obj (last F)).obj q :=
  ULift.up (lastOrdinal (degree X) F)

/-- Last-ordinal parameters commute with every outer face and degeneracy. -/
theorem lastOrdinalPoint_natural {q r : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q) (α : q ⟶ r) :
    ((diagram X).map (lastArrow α F)).app r
        (lastOrdinalPoint X ((nerve (LiftedIndex X)).map α F)) =
      ((diagram X).obj (last F)).map α (lastOrdinalPoint X F) := by
  apply ULift.ext
  change lastOrdinal (degree X) ((nerve (LiftedIndex X)).map α F) ≫
      (degree X).map (lastArrow α F) =
    α.unop ≫ lastOrdinal (degree X) F
  rw [lastOrdinal_natural]

/-- Evaluate the actual simplex indexed by the last object at its full
last-vertex ordinal. No Kan condition is imposed on `X`. -/
def lastVertexMap : nerve (LiftedIndex X) ⟶ X where
  app q F := ((diagramAugmentation X).app (last F)).app q (lastOrdinalPoint X F)
  naturality q r α := by
    funext F
    let F' := (nerve (LiftedIndex X)).map α F
    let g := lastArrow α F
    have hw := congrFun (NatTrans.congr_app
      ((diagramAugmentation X).naturality g) r) (lastOrdinalPoint X F')
    change ((diagramAugmentation X).app (last F)).app r
        (((diagram X).map g).app r (lastOrdinalPoint X F')) =
      ((diagramAugmentation X).app (last F')).app r (lastOrdinalPoint X F') at hw
    calc
      ((diagramAugmentation X).app (last F')).app r (lastOrdinalPoint X F') =
          ((diagramAugmentation X).app (last F)).app r
            (((diagram X).map g).app r (lastOrdinalPoint X F')) := hw.symm
      _ = ((diagramAugmentation X).app (last F)).app r
            (((diagram X).obj (last F)).map α (lastOrdinalPoint X F)) := by
          rw [lastOrdinalPoint_natural X F α]
      _ = X.map α (((diagramAugmentation X).app (last F)).app q
            (lastOrdinalPoint X F)) :=
          congrFun (((diagramAugmentation X).app (last F)).naturality α)
            (lastOrdinalPoint X F)

/-- The same map is expressed using the original last simplex and ordinal. -/
theorem lastVertexMap_app (q : SimplexCategoryᵒᵖ)
    (F : (nerve (LiftedIndex X)).obj q) :
    (lastVertexMap X).app q F =
      (ULiftHom.down.{0, 0, 0}.obj (last F)).hom.app q
        (ULift.up (lastOrdinal (degree X) F)) := rfl

private abbrev suffix {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q) : first F ⟶ last F :=
  F.map (homOfLE (Fin.zero_le (Fin.last q.unop.len)))

/-- The full first-object parameter, transported to the last original simplex. -/
def firstOrdinal {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q) :
    q.unop ⟶ (degree X).obj (last F) :=
  t.down ≫ (degree X).map (suffix X F)

theorem firstOrdinal_le_last {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q) (i : Fin (q.unop.len + 1)) :
    (firstOrdinal X F t).toOrderHom i ≤
      (lastOrdinal (degree X) F).toOrderHom i :=
  first_le_lastOrdinal (degree X) F (t.down) i

/-- Switch the full first-object parameter to the last-vertex ordinal. -/
def timeOrdinal {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q)
    (u : (Δ[1] : SSet.{0}).obj q) :
    q.unop ⟶ (degree X).obj (last F) :=
  switch (firstOrdinal X F t) (lastOrdinal (degree X) F)
    (firstOrdinal_le_last X F t) (SSet.stdSimplex.objEquiv u)

theorem timeOrdinal_zero {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q) :
    timeOrdinal X F t (SSet.stdSimplex.objEquiv.symm (q.unop.const ⦋1⦌ 0)) =
      firstOrdinal X F t := by
  exact switch_zero _ _ _

theorem timeOrdinal_one {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q) :
    timeOrdinal X F t (SSet.stdSimplex.objEquiv.symm (q.unop.const ⦋1⦌ 1)) =
      lastOrdinal (degree X) F := by
  exact switch_one _ _ _

/-- The whole original augmentation evaluates the first original simplex
at its whole parameter; this is the starting endpoint for the switch. -/
theorem toOriginal_cell (q : SimplexCategoryᵒᵖ)
    (F : (nerve (LiftedIndex X)).obj q)
    (t : ((diagram X).obj (first F)).obj q) :
    (toOriginal X).app q ⟨F, t⟩ =
      ((diagramAugmentation X).app (first F)).app q t := rfl

#print axioms lastOrdinalPoint_natural
#print axioms lastVertexMap
#print axioms firstOrdinal_le_last
#print axioms timeOrdinal_zero
#print axioms timeOrdinal_one

end
end DaggerModels.PartII.SimplexIndexLastVertexWeak
