import DaggerModelsPartII.JTProjectiveBar
import ActualDaggerRigidificationQuillen

/-!
# The prescribed natural bar comparison before the density theorem

The manuscript's map beta is the actual capital Lambda at the bar input,
followed by realization of the actual bar augmentation and the strict
vertical-constant realization isomorphism. Naturality identifies it with
realization of the augmentation followed by the already fixed Theta.

No weak-equivalence or projective-cofibrancy premise is asserted here.
The last theorem records precisely the remaining weak-equivalence condition.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.JTBarComparison

open JTProjectiveBar JTFrameAdjunction JTCoendComparison JTFrameZero
open ConstantVertexAdjunction OrdinaryRigidification.DaggerRigidification

noncomputable section

/-- The rigidified strict collapse of the vertically constant JT realization. -/
def constantCollapse :
    delta ⋙ (DaggerJTRealization.daggerRealization ⋙ daggerRigidification) ≅
      daggerRigidification :=
  (Functor.associator delta DaggerJTRealization.daggerRealization
    daggerRigidification).symm ≪≫
    Functor.isoWhiskerRight deltaRealizationIso daggerRigidification ≪≫
    daggerRigidification.leftUnitor

/-- The actual three-factor natural comparison of the bar to Part I
rigidification, before proving projective cofibrancy or weakness. -/
def beta : barOnDagger ⋙ frameRealization ⟶ daggerRigidification :=
  Functor.whiskerLeft barOnDagger comparison ≫
    Functor.whiskerRight barAugmentation
      (DaggerJTRealization.daggerRealization ⋙ daggerRigidification) ≫
    constantCollapse.hom

/-- The named comparison uses the literal capital Lambda and actual bar
augmentation, followed by the original constant-realization collapse. -/
theorem beta_app (X : DaggerSSet.{0}) :
    beta.app X = comparison.app (barOnDagger.obj X) ≫
      daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map (barAugmentation.app X)) ≫
      constantCollapse.hom.app X := rfl

/-- Naturality of the actual Lambda gives the prescribed strict transport
identity for the natural bar comparison. -/
theorem beta_eq :
    beta = Functor.whiskerRight barAugmentation frameRealization ≫
      JTStrictTransport.Theta.hom := by
  apply NatTrans.ext
  funext X
  change comparison.app (barOnDagger.obj X) ≫
      (DaggerJTRealization.daggerRealization ⋙ daggerRigidification).map
        (barAugmentation.app X) ≫ constantCollapse.hom.app X =
    frameRealization.map (barAugmentation.app X) ≫
      (comparison.app (delta.obj X) ≫ constantCollapse.hom.app X)
  rw [comparison.naturality_assoc]

/-- The component form retains the actual augmentation map, rather than an
arbitrary comparison between its source and target objects. -/
theorem beta_app_eq (X : DaggerSSet.{0}) :
    beta.app X = frameRealization.map (barAugmentation.app X) ≫
      JTStrictTransport.Theta.hom.app X :=
  NatTrans.congr_app beta_eq X

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Since Theta is the fixed strict isomorphism, weakness of the prescribed
beta is exactly weakness of realization of the actual bar augmentation.
Neither side of this equivalence is proved by this statement. -/
theorem beta_weak_iff (X : DaggerSSet.{0}) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (beta.app X) ↔
      weakEquivalences DaggerSimplicialCat.{0, 0}
        (frameRealization.map (barAugmentation.app X)) := by
  rw [beta_app_eq]
  exact (weakEquivalences DaggerSimplicialCat.{0, 0}).cancel_right_of_respectsIso _ _

end

end DaggerModels.PartII.JTBarComparison
