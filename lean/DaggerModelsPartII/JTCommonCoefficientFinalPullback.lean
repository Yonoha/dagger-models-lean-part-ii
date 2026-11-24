import DaggerModelsPartII.JTCommonCoefficientFinalCylinder
import DaggerModelsPartII.JTHigherMixedGraphTargetLift

/-!
# Comparison in the actual target pullbacks at a common final coefficient
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCommonCoefficientFinalPullback

open JTHigherInterleavedParameter (common)
open JTCommonCoefficientParameter
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
variable {k b : SimplexCategory} (c : k ⟶ b) (n : SimplexCategory)
variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op (common b n)))

/-- The existing decorated label at the final coefficient. -/
abbrev finalIndex : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (common b n) z

/-- The exact pullback of that label to the source coefficient. -/
abbrev pulledIndex : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (common k n) (pulledLabel W x y T c n z)

/-- The original decorated arrow whose necklace map is the identity and
whose simplex operator is the comparison to the final coefficient. -/
def labelArrow : pulledIndex c n z ⟶ finalIndex n z := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let g : (T, common k n) ⟶ (T, common b n) := (𝟙 T, toFinal c n)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (T, common b n)) z)
    (P.elementsMk (op (T, common k n)) (pulledLabel W x y T c n z))
    g.op ?_).op
  let F := orderedNecklaceLabels W (boundaryPoint W x y)
  change (F.obj (op T)).map (toFinal c n).op
    ((F.map (𝟙 (op T))).app (op (common b n)) z) = pulledLabel W x y T c n z
  rw [F.map_id]
  rfl

theorem underDiagram_labelArrow :
    (underDiagram W x y).map (labelArrow c n z) = (under T).map (toFinal c n) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 T) (common k n) ≫ (value T).map (toFinal c n) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

variable (s : T.toSSet ⟶ J.obj k)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q

/-- The prescribed full cylinder leg at the source coefficient. -/
def sourceCylinder : (under T).obj n ⟶ (underDiagram W x y).obj (pulledIndex c n z) :=
  Under.homMk (cylinderMap T c s n) (cylinderMap_boundary T c s n)

/-- The already checked cylinder leg at the final coefficient. -/
def finalCylinder : (under T).obj n ⟶ (underDiagram W x y).obj (finalIndex n z) :=
  Under.homMk (JTHigherGraphPrismCylinder.cylinderMap T (s ≫ J.map c) n)
    (JTHigherGraphPrismCylinder.cylinderMap_boundary T (s ≫ J.map c) n)

theorem sourceCylinder_compare :
    sourceCylinder c n z s ≫ (underDiagram W x y).map (labelArrow c n z) =
      finalCylinder c n z s := by
  rw [underDiagram_labelArrow]
  apply Under.UnderMorphism.ext
  exact cylinderMap_toFinal T c s n

variable (U : (under T).obj n ⟶ (D Q).obj (finalIndex n z))
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n z) = finalCylinder c n z s)

/-- Transfer a comparison to the original target pullback by pulling
the whole decorated label back and retaining the native projection. -/
def lift : (under T).obj n ⟶ (D Q).obj (pulledIndex c n z) :=
  pullback.lift (sourceCylinder c n z s)
    (U ≫ JTTargetCommaPullback.snd W x y Q (finalIndex n z)) (by
      apply Under.UnderMorphism.ext
      change cylinderMap T c s n ≫
          descend W x y T (common k n) (pulledLabel W x y T c n z) = _
      rw [descend_toFinal]
      have h : finalCylinder c n z s ≫ (underCocone W x y).app (finalIndex n z) =
          (U ≫ JTTargetCommaPullback.snd W x y Q (finalIndex n z)) ≫
            JTTargetCommaPullback.targetMap W x y Q := by
        rw [← hU, Category.assoc, JTTargetCommaPullback.condition, Category.assoc]
      exact congrArg (fun f ↦ f.right) h)

@[reassoc]
theorem lift_fst :
    lift c n z s Q U hU ≫ JTTargetCommaPullback.fst W x y Q (pulledIndex c n z) =
      sourceCylinder c n z s :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem lift_snd :
    lift c n z s Q U hU ≫ JTTargetCommaPullback.snd W x y Q (pulledIndex c n z) =
      U ≫ JTTargetCommaPullback.snd W x y Q (finalIndex n z) :=
  pullback.lift_snd _ _ _

/-- The actual pullback arrow compares the complete lifts and keeps
both original projections. -/
theorem lift_compare :
    lift c n z s Q U hU ≫ (D Q).map (labelArrow c n z) = U := by
  apply pullback.hom_ext (f := (underCocone W x y).app (finalIndex n z))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n z) = _
    rw [Category.assoc, JTTargetCommaPullback.map_fst, lift_fst_assoc,
      sourceCylinder_compare]
    exact hU.symm
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (finalIndex n z) = _
    rw [Category.assoc, JTTargetCommaPullback.map_snd, lift_snd]
    rfl

end

end DaggerModels.PartII.JTCommonCoefficientFinalPullback
