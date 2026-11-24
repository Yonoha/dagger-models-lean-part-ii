import DaggerModelsPartII.JTCommonCoefficientFinalPullback

/-!
# Simultaneous coefficient and time operators on the actual pullbacks
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientPullbackOperators

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientParameter JTCommonCoefficientFinalPullback
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} {T : NecklaceCode}
variable {k l b n m : SimplexCategory} {c : k ⟶ b} {d : l ⟶ b}
variable (f : k ⟶ l) (hf : f ≫ d = c) (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common b m)))

private abbrev L := orderedNecklaceLabels W (boundaryPoint W x y)

/-- The original restriction of the final label in the time variable. -/
abbrev finalRestriction :=
  ((L (W := W) (x := x) (y := y)).obj (op T)).map
    (JTHigherInterleavedParameter.mapTime b j).op z

/-- The simultaneous operator in the actual category of decorated labels. -/
def labelOperator : pulledIndex c n (finalRestriction j z) ⟶ pulledIndex d m z := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let a : (T, common k n) ⟶ (T, common l m) := (𝟙 T, map f hf j hj)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (T, common l m)) (pulledLabel W x y T d m z))
    (P.elementsMk (op (T, common k n)) (pulledLabel W x y T c n (finalRestriction j z)))
    a.op ?_).op
  let F := L (W := W) (x := x) (y := y)
  change (F.obj (op T)).map (map f hf j hj).op
    ((F.map (𝟙 (op T))).app (op (common l m)) (pulledLabel W x y T d m z)) = _
  rw [F.map_id]
  exact pulledLabel_map W x y T c n f hf j hj z

theorem underDiagram_labelOperator :
    (underDiagram W x y).map (labelOperator f hf j hj z) = (under T).map (map f hf j hj) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 T) (common k n) ≫ (value T).map (map f hf j hj) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

variable (s : T.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l)
variable (hs : s ≫ J.map f = s')
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q

variable (U : (under T).obj n ⟶ (D Q).obj (finalIndex n (finalRestriction j z)))
variable (V : (under T).obj m ⟶ (D Q).obj (finalIndex m z))
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n (finalRestriction j z)) =
  finalCylinder c n (finalRestriction j z) s)
variable (hV : V ≫ JTTargetCommaPullback.fst W x y Q (finalIndex m z) =
  finalCylinder d m z s')

include hs in
/-- The actual lifted cylinder maps respect both operators once the
native target maps have the original time restriction. -/
theorem lift_natural
    (hNative : U ≫ JTTargetCommaPullback.snd W x y Q (finalIndex n (finalRestriction j z)) =
      (under T).map j ≫ V ≫ JTTargetCommaPullback.snd W x y Q (finalIndex m z)) :
    lift c n (finalRestriction j z) s Q U hU ≫ (D Q).map (labelOperator f hf j hj z) =
      (under T).map j ≫ lift d m z s' Q V hV := by
  apply pullback.hom_ext (f := (underCocone W x y).app (pulledIndex d m z))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (pulledIndex d m z) =
      (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (pulledIndex d m z)
    rw [Category.assoc, JTTargetCommaPullback.map_fst, lift_fst_assoc, Category.assoc,
      lift_fst, underDiagram_labelOperator]
    apply Under.UnderMorphism.ext
    exact cylinderMap_map T f hf j hj s s' hs
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (pulledIndex d m z) =
      (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (pulledIndex d m z)
    rw [Category.assoc, JTTargetCommaPullback.map_snd, lift_snd, Category.assoc, lift_snd]
    exact hNative

end

end DaggerModels.PartII.JTCommonCoefficientPullbackOperators
