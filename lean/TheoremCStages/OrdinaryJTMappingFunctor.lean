import OrdinaryJTMappingFibration
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# The ordinary JT mapping functor in the horizontal coefficient

The literal ordinary JT tensor frame is covariant in its simplicial-set
coefficient. Its opposite, followed by strict Hom into a fixed target,
gives the existing ordinary mapping simplicial sets and restriction maps.
Pointwise tensor colimits and representable limits give limit preservation.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
  MonoidalCategory MonoidalClosed DaggerModels

namespace DaggerModels.PartII.OrdinaryJTMappingFunctor

noncomputable section

open OrdinaryJTMappingFrameWeak

private local instance : BraidedCategory SSet.{0} :=
  .ofCartesianMonoidalCategory

private local instance (K : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft K) :=
  (ihom.adjunction K).leftAdjoint_preservesColimits

private local instance (K : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight K) :=
  ⟨fun {J} _ ↦ by
    letI : PreservesColimitsOfShape J (tensorLeft K) := inferInstance
    exact preservesColimitsOfShape_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight K)⟩

private theorem frameMap_id (A : SSet.{0}) :
    frameMap (𝟙 A) = 𝟙 (frame A) := by
  apply NatTrans.ext
  funext k
  change (𝟙 A) ▷ GroupoidSimplex.parameter.obj k =
    𝟙 (A ⊗ GroupoidSimplex.parameter.obj k)
  exact (tensorRight (GroupoidSimplex.parameter.obj k)).map_id A

private theorem frameMap_comp {A B C : SSet.{0}}
    (f : A ⟶ B) (g : B ⟶ C) :
    frameMap (f ≫ g) = frameMap f ≫ frameMap g := by
  apply NatTrans.ext
  funext k
  change (f ≫ g) ▷ GroupoidSimplex.parameter.obj k =
    (f ▷ GroupoidSimplex.parameter.obj k) ≫
      (g ▷ GroupoidSimplex.parameter.obj k)
  exact (tensorRight (GroupoidSimplex.parameter.obj k)).map_comp f g

/-- The original ordinary JT tensor frame, reversed in its horizontal
coefficient and in its cosimplicial index. -/
def frameOppFunctor :
    SSet.{0}ᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) where
  obj A := (frame A.unop).op
  map {A B} f := NatTrans.op (frameMap f.unop)
  map_id A := by
    change NatTrans.op (frameMap (𝟙 A.unop)) = 𝟙 (frame A.unop).op
    rw [frameMap_id]
    rfl
  map_comp f g := by
    change NatTrans.op (frameMap (g.unop ≫ f.unop)) =
      NatTrans.op (frameMap f.unop) ≫ NatTrans.op (frameMap g.unop)
    rw [frameMap_comp, NatTrans.op_comp]

private local instance : PreservesLimitsOfSize.{0, 0} frameOppFunctor :=
  ⟨fun {J} _ ↦ by
    apply preservesLimitsOfShape_of_evaluation
    intro k
    letI : PreservesLimitsOfSize.{0, 0}
        (tensorRight (GroupoidSimplex.parameter.obj k.unop)).op :=
      preservesLimitsOfSize_op _
    change PreservesLimitsOfShape J
      (tensorRight (GroupoidSimplex.parameter.obj k.unop)).op
    infer_instance⟩

private local instance (X : SSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (StrictFrameMappingWeak.strictMapping X) := by
  dsimp only [StrictFrameMappingWeak.strictMapping]
  exact CategoryTheory.whiskeringRightPreservesLimits (yoneda.obj X)

/-- The full ordinary JT mapping simplicial set, contravariant in its
horizontal simplicial-set coefficient. -/
def mappingFunctor (X : SSet.{0}) : SSet.{0}ᵒᵖ ⥤ SSet.{0} :=
  frameOppFunctor ⋙ StrictFrameMappingWeak.strictMapping X

/-- The object is the already defined full ordinary JT mapping space. -/
theorem mappingFunctor_obj (X A : SSet.{0}) :
    (mappingFunctor X).obj (op A) = mapping X A := rfl

/-- Its morphism is the already defined literal restriction map. -/
theorem mappingFunctor_map (X : SSet.{0}) {A B : SSet.{0}ᵒᵖ}
    (f : A ⟶ B) :
    (mappingFunctor X).map f = restriction X f.unop := rfl

/-- The ordinary JT mapping functor preserves all small limits in the
opposite horizontal coefficient category. -/
instance mappingFunctor_preservesLimits (X : SSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (mappingFunctor X) := by
  dsimp only [mappingFunctor]
  infer_instance

#print axioms mappingFunctor_obj
#print axioms mappingFunctor_map
#print axioms mappingFunctor_preservesLimits

end

end DaggerModels.PartII.OrdinaryJTMappingFunctor
