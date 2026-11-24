import DaggerModelsPartII.JTEndpointCobaseAugmentations

/-!
# Augmentation-compatible maps of the literal endpoint cobases

A map of actual arrow diagrams over the original iota induces a map under
its fixed ordered boundary. Its compatibility with the actual cobase
augmentations follows from the two pushout coprojections. Pointwise weak
augmentations then imply weakness of this same comparison by two-out-of-three.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointCobaseComparison

open JTRelativeReedyFrame JTEndpointCofibrancy JTEndpointCobaseAugmentations

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

variable {F F' : SimplexCategory ⥤ Arrow Coefficient}

/-- The source and target transformations of the actual arrow map. -/
def sourceMap (f : F ⟶ F') : source F ⟶ source F' :=
  Functor.whiskerRight f Arrow.leftFunc

def targetMap (f : F ⟶ F') : target F ⟶ target F' :=
  Functor.whiskerRight f Arrow.rightFunc

/-- The transformation retains the actual source-to-target square. -/
theorem structure_square (f : F ⟶ F') :
    structureMap F ≫ targetMap f = sourceMap f ≫ structureMap F' := by
  apply NatTrans.ext
  funext k
  exact (Arrow.w (f.app k)).symm

variable (f : F ⟶ F')
  (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
  (a' : F' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
  (h : f ≫ a' = a)

include h

/-- The original augmentation equation on its source components. -/
theorem source_augmentation : sourceMap f ≫ sourceAug a' = sourceAug a := by
  apply NatTrans.ext
  funext k
  exact congrArg (fun t ↦ (t.app k).left) h

/-- The same augmentation equation on its target components. -/
theorem target_augmentation : targetMap f ≫ targetAug a' = targetAug a := by
  apply NatTrans.ext
  funext k
  exact congrArg (fun t ↦ (t.app k).right) h

/-- The literal cobase map fixes the same original ordered boundary. -/
def comparison : cobase a ⟶ cobase a' :=
  pushout.map (sourceAug a) (structureMap F) (sourceAug a') (structureMap F')
    (𝟙 _) (targetMap f) (sourceMap f)
    (by simpa only [Category.comp_id] using (source_augmentation f a a' h).symm)
    (structure_square f)

/-- The cobase map is the identity on the fixed boundary. -/
theorem boundary_comparison : boundary a ≫ comparison f a a' h = boundary a' := by
  change pushout.inl _ _ ≫ comparison f a a' h = pushout.inl _ _
  unfold comparison
  simp only [pushout.map, pushout.inl_desc, Category.id_comp]

/-- The other coprojection records the actual target transformation. -/
theorem frameInclusion_comparison :
    frameInclusion a ≫ comparison f a a' h = targetMap f ≫ frameInclusion a' := by
  change pushout.inr _ _ ≫ comparison f a a' h = targetMap f ≫ pushout.inr _ _
  unfold comparison
  simp only [pushout.map, pushout.inr_desc]

/-- The actual comparison preserves the induced augmentation to iota. -/
theorem comparison_cobaseAug : comparison f a a' h ≫ cobaseAug a' = cobaseAug a := by
  apply pushout.hom_ext
  · change boundary a ≫ (comparison f a a' h ≫ cobaseAug a') =
      boundary a ≫ cobaseAug a
    rw [← Category.assoc, boundary_comparison, boundary_cobaseAug, boundary_cobaseAug]
  · change frameInclusion a ≫ (comparison f a a' h ≫ cobaseAug a') =
      frameInclusion a ≫ cobaseAug a
    rw [← Category.assoc, frameInclusion_comparison, Category.assoc,
      frameInclusion_cobaseAug, frameInclusion_cobaseAug]
    exact target_augmentation f a a' h

/-- The exact cobase comparison as a map under the literal boundary. -/
def underComparison : underDiagram a ⟶ underDiagram a' where
  app k := Under.homMk ((comparison f a a' h).app k)
    (NatTrans.congr_app (boundary_comparison f a a' h) k)
  naturality {j k} θ := by
    apply Under.UnderMorphism.ext
    exact (comparison f a a' h).naturality θ

/-- Its equation with the two actual undercategory augmentations. -/
theorem underComparison_augmentation :
    underComparison f a a' h ≫ underAugmentation a' = underAugmentation a := by
  apply NatTrans.ext
  funext k
  apply Under.UnderMorphism.ext
  exact NatTrans.congr_app (comparison_cobaseAug f a a' h) k

/-- Pointwise weak actual augmentations imply weakness of this same cobase map. -/
theorem comparison_weak
    (ha : ∀ k, weakEquivalences Coefficient ((cobaseAug a).app k))
    (ha' : ∀ k, weakEquivalences Coefficient ((cobaseAug a').app k))
    (k : SimplexCategory) :
    weakEquivalences Coefficient ((comparison f a a' h).app k) := by
  apply (weakEquivalences Coefficient).of_postcomp _ ((cobaseAug a').app k) (ha' k)
  rw [show (comparison f a a' h).app k ≫ (cobaseAug a').app k =
    (cobaseAug a).app k from NatTrans.congr_app (comparison_cobaseAug f a a' h) k]
  exact ha k

end

end DaggerModels.PartII.JTEndpointCobaseComparison
