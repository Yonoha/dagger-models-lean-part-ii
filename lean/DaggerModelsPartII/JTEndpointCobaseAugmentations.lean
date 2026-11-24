import DaggerModelsPartII.JTEndpointAugmentations
import DaggerModelsPartII.JTEndpointCobase
import OriginalGlobalLeftProperRecovered

/-!
# The literal cobase augmentations under the original ordered boundary

An actual augmented cosimplicial arrow gives its boundary cobase and a map
to the original iota under the same fixed boundary. The original left proper
model gives weakness of this augmentation under the explicitly stated
pointwise attaching-cofibration and weak-augmentation hypotheses.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointCobaseAugmentations

open JTRelativeReedyFrame JTEndpointObjects JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual source and target diagrams of a diagram of arrows. -/
def source (F : SimplexCategory ⥤ Arrow Coefficient) : SimplexCategory ⥤ Coefficient :=
  F ⋙ Arrow.leftFunc

def target (F : SimplexCategory ⥤ Arrow Coefficient) : SimplexCategory ⥤ Coefficient :=
  F ⋙ Arrow.rightFunc

/-- The literal source-to-target natural transformation. -/
def structureMap (F : SimplexCategory ⥤ Arrow Coefficient) : source F ⟶ target F :=
  Functor.whiskerLeft F Arrow.leftToRight

/-- The source component of an actual augmentation to the original iota. -/
def sourceAug {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    source F ⟶ (Functor.const SimplexCategory).obj Bdagger where
  app k := (a.app k).left
  naturality {j k} θ := by
    exact congrArg (fun f ↦ f.left) (a.naturality θ)

/-- The target component of the same actual augmentation. -/
def targetAug {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    target F ⟶ (Functor.const SimplexCategory).obj Jdagger where
  app k := (a.app k).right
  naturality {j k} θ := by
    exact congrArg (fun f ↦ f.right) (a.naturality θ)

/-- The actual arrow augmentation is the required ordered boundary square. -/
theorem augmentation_square {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    structureMap F ≫ targetAug a =
      sourceAug a ≫ (Functor.const SimplexCategory).map iota := by
  apply NatTrans.ext
  funext k
  exact (Arrow.w (a.app k)).symm

/-- The actual B-first endpoint cobase of this augmented arrow diagram. -/
def cobase {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    SimplexCategory ⥤ Coefficient :=
  JTEndpointCobase.endpointCobase (structureMap F) Bdagger (sourceAug a)

/-- The boundary coprojection of that exact cobase. -/
def boundary {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    (Functor.const SimplexCategory).obj Bdagger ⟶ cobase a :=
  JTEndpointCobase.endpointCobase_inl (structureMap F) Bdagger (sourceAug a)

/-- The frame coprojection of that exact cobase. -/
def frameInclusion {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    target F ⟶ cobase a :=
  JTEndpointCobase.endpointCobase_inr (structureMap F) Bdagger (sourceAug a)

/-- The induced augmentation to the original rigidified interval. -/
def cobaseAug {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    cobase a ⟶ (Functor.const SimplexCategory).obj Jdagger :=
  pushout.desc ((Functor.const SimplexCategory).map iota) (targetAug a)
    (augmentation_square a).symm

/-- The augmentation preserves the original ordered boundary map. -/
theorem boundary_cobaseAug {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    boundary a ≫ cobaseAug a = (Functor.const SimplexCategory).map iota := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

/-- The augmentation restricts to the actual original target augmentation. -/
theorem frameInclusion_cobaseAug {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    frameInclusion a ≫ cobaseAug a = targetAug a := by
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

private theorem original_leftProper
    {A B D P : Coefficient} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P}
    (h : IsPushout i k l r) (hi : cofibrations Coefficient i)
    (hk : weakEquivalences Coefficient k) : weakEquivalences Coefficient l := by
  exact (weakEquivalence_iff l).1
    (DaggerGlobalLeftProper.standard_model_leftProper h.flip
      ((cofibration_iff i).2 hi) ((weakEquivalence_iff k).2 hk))

/-- The actual frame coprojection is weak by the original left properness
under the displayed attaching-cofibration and source-weak hypotheses. -/
theorem frameInclusion_weak {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (hcof : ∀ k, cofibrations Coefficient ((structureMap F).app k))
    (hsource : ∀ k, weakEquivalences Coefficient ((sourceAug a).app k))
    (k : SimplexCategory) :
    weakEquivalences Coefficient ((frameInclusion a).app k) :=
  JTEndpointCobase.endpointCobase_inr_weak original_leftProper
    (structureMap F) Bdagger (sourceAug a) hcof hsource k

/-- The induced cobase augmentation is weak when the two actual arrow
augmentation components are weak and the attaching arrows are cofibrations. -/
theorem cobaseAug_weak {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (hcof : ∀ k, cofibrations Coefficient ((structureMap F).app k))
    (hsource : ∀ k, weakEquivalences Coefficient ((sourceAug a).app k))
    (htarget : ∀ k, weakEquivalences Coefficient ((targetAug a).app k))
    (k : SimplexCategory) : weakEquivalences Coefficient ((cobaseAug a).app k) := by
  apply (weakEquivalences Coefficient).of_precomp ((frameInclusion a).app k) _
    (frameInclusion_weak a hcof hsource k)
  rw [show (frameInclusion a).app k ≫ (cobaseAug a).app k =
    (targetAug a).app k from NatTrans.congr_app (frameInclusion_cobaseAug a) k]
  exact htarget k

/-- The exact collapsed arrow as a diagram under the original boundary. -/
def underDiagram {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    SimplexCategory ⥤ Under Bdagger :=
  Under.lift (cobase a) (boundary a)

/-- The actual cobase augmentation is a map under the same boundary. -/
def underAugmentation {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota)) :
    underDiagram a ⟶ (Functor.const SimplexCategory).obj (Under.mk iota) where
  app k := Under.homMk ((cobaseAug a).app k) (by
    exact NatTrans.congr_app (boundary_cobaseAug a) k)
  naturality {j k} θ := by
    apply Under.UnderMorphism.ext
    exact (cobaseAug a).naturality θ

end

end DaggerModels.PartII.JTEndpointCobaseAugmentations
