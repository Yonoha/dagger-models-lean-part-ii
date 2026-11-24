import DaggerModelsPartII.JTCommonCoefficientFinalPullback

/-!
# Comparison inside the original native target comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientFinalComma

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientFinalPullback
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} {T : NecklaceCode}
variable {k b : SimplexCategory} (c : k ⟶ b) (n : SimplexCategory)
variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common b n)))
variable (s : T.toSSet ⟶ J.obj k)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q
private abbrev F := BoundaryNecklaceComma.fiberDiagram (D Q)
private abbrev Fiber := CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj n)
private abbrev Original := CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable (U : (under T).obj n ⟶ (D Q).obj (finalIndex n z))
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n z) = finalCylinder c n z s)

/-- All original internal necklaces map to the pulled label over the
same original target. -/
def pulledPresentation : Fiber (T := T) n ⥤ JTTargetCommaPullback.Presentation W x y Q :=
  CostructuredArrow.map (lift c n z s Q U hU) ⋙ Grothendieck.ι (F Q) (pulledIndex c n z)

/-- The comparison using the existing final label. -/
def finalPresentation : Fiber (T := T) n ⥤ JTTargetCommaPullback.Presentation W x y Q :=
  CostructuredArrow.map U ⋙ Grothendieck.ι (F Q) (finalIndex n z)

/-- Passage to the final label is an actual arrow for every internal
necklace and is natural in its original necklace maps. -/
def comparePresentation :
    pulledPresentation c n z s Q U hU ⟶ finalPresentation n z Q U := by
  let a := labelArrow c n z
  let G := BoundaryNecklaceComma.diagram
  have h : (G.map (lift c n z s Q U hU)).toFunctor ⋙ ((F Q).map a).toFunctor =
      (G.map U).toFunctor := by
    change (G.map (lift c n z s Q U hU)).toFunctor ⋙ (G.map ((D Q).map a)).toFunctor = _
    have hh := congrArg Cat.Hom.toFunctor
      (G.map_comp (lift c n z s Q U hU) ((D Q).map a))
    change (G.map (lift c n z s Q U hU ≫ (D Q).map a)).toFunctor = _ at hh
    rw [lift_compare c n z s Q U hU] at hh
    exact hh.symm
  exact Functor.whiskerLeft (CostructuredArrow.map (lift c n z s Q U hU))
      (Grothendieck.ιNatTrans (F := F Q) a) ≫
    eqToHom (by
      change ((G.map (lift c n z s Q U hU)).toFunctor ⋙ ((F Q).map a).toFunctor) ⋙
          Grothendieck.ι (F Q) (finalIndex n z) =
        (G.map U).toFunctor ⋙ Grothendieck.ι (F Q) (finalIndex n z)
      rw [h])

/-- The pulled comparison in the original target comma. -/
def pulledComma : Fiber (T := T) n ⥤ Original Q :=
  pulledPresentation c n z s Q U hU ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

/-- The existing comparison in the same original target comma. -/
def finalComma : Fiber (T := T) n ⥤ Original Q :=
  finalPresentation n z Q U ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

/-- The comparison takes place in the actual, unchanged target comma. -/
def compareComma : pulledComma c n z s Q U hU ⟶ finalComma n z Q U :=
  Functor.whiskerRight (comparePresentation c n z s Q U hU)
    (JTTargetCommaPullback.equivalence W x y Q).inverse

end

end DaggerModels.PartII.JTCommonCoefficientFinalComma
