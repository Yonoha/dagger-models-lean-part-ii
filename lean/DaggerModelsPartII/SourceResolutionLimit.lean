import DaggerModelsPartII.ResolutionFilteredFibrations
import DaggerModelsPartII.PointwiseSourceResolution

/-! Augmentations at the limit stages of inverse systems of source resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u t z

namespace DaggerModels.PartII

noncomputable section

local instance sourceResolutionLimitLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance sourceResolutionLimitColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance sourceResolutionLimitCoefficientModel : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance sourceResolutionLimitReedyModel : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory
local instance sourceResolutionLimitOppositeModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ ResolutionDiagram.{u}ᵒᵖ) :=
  simplicialReedyModelCategory ResolutionDiagram.{u}ᵒᵖ

variable {J : Type t} [Category.{z} J]
  (X : J ⥤ ResolutionDiagram.{u})
  (G : Jᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ ResolutionDiagram.{u}ᵒᵖ))
  (a : X.op ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ G)
  (cX : Cocone X) (cG : Cone G) (hG : IsLimit cG)

/-- The augmentation at the inverse limit of the resolution diagrams. -/
def sourceResolutionLimitAugmentation :
    (Functor.const SimplexCategoryᵒᵖ).obj (op cX.pt) ⟶ cG.pt :=
  hG.lift
    { pt := (Functor.const SimplexCategoryᵒᵖ).obj (op cX.pt)
      π :=
        { app := fun j ↦ (Functor.const SimplexCategoryᵒᵖ).map (cX.ι.app j.unop).op ≫ a.app j
          naturality := by
            intro j k f
            let K : ResolutionDiagram.{u}ᵒᵖ ⥤
                (SimplexCategoryᵒᵖ ⥤ ResolutionDiagram.{u}ᵒᵖ) := Functor.const SimplexCategoryᵒᵖ
            change 𝟙 _ ≫ (K.map (cX.ι.app k.unop).op ≫ a.app k) =
              (K.map (cX.ι.app j.unop).op ≫ a.app j) ≫ G.map f
            rw [Category.id_comp, Category.assoc, ← a.naturality]
            change _ = K.map (cX.ι.app j.unop).op ≫ K.map (X.map f.unop).op ≫ a.app k
            rw [← Category.assoc, ← K.map_comp, ← op_comp, cX.w] } }

@[reassoc]
theorem sourceResolutionLimitAugmentation_fac (j : J) :
    sourceResolutionLimitAugmentation X G a cX cG hG ≫ cG.π.app (op j) =
      (Functor.const SimplexCategoryᵒᵖ).map (cX.ι.app j).op ≫ a.app (op j) :=
  hG.fac _ _

variable [EssentiallySmall.{u} J] [IsFiltered J]
  [HasLimitsOfShape Jᵒᵖ ResolutionDiagram.{u}ᵒᵖ]

/-- The limit augmentation is still degreewise trivial when the original objects
form a filtered colimit and the individual augmentations are degreewise trivial. -/
theorem sourceResolutionLimitAugmentation_degreewise (hX : IsColimit cX)
    (ha : ∀ j n, trivialFibrations ResolutionDiagram.{u} (((a.app (op j)).app n).unop))
    (n : SimplexCategoryᵒᵖ) :
    trivialFibrations ResolutionDiagram.{u}
      (((sourceResolutionLimitAugmentation X G a cX cG hG).app n).unop) := by
  let ev := (evaluation SimplexCategoryᵒᵖ ResolutionDiagram.{u}ᵒᵖ).obj n
  let F := (G ⋙ ev).unop
  let b : F ⟶ X :=
    { app := fun j ↦ ((a.app (op j)).app n).unop
      naturality := by
        intro j k f
        exact (congrArg Quiver.Hom.unop (congr_app (a.naturality f.op) n)).symm }
  let cF := coconeUnopOfCone (ev.mapCone cG)
  have hF : IsColimit cF := isColimitCoconeUnopOfCone _ (isLimitOfPreserves ev hG)
  apply resolutionReedy_trivialFibration_of_filteredColimit b hF hX _ _ (fun j ↦ ha j n)
  intro j
  exact congrArg Quiver.Hom.unop
    (congr_app (sourceResolutionLimitAugmentation_fac X G a cX cG hG j) n)

/-- At a filtered limit stage, a fibrant limit of the opposite diagrams gives
a pointwise source resolution of the colimit of the original objects. -/
def sourceResolutionAtLimit (hX : IsColimit cX)
    (ha : ∀ j n, trivialFibrations ResolutionDiagram.{u} (((a.app (op j)).app n).unop))
    (hf : IsFibrant cG.pt) : PointwiseSourceResolution cX.pt :=
  ⟨cG.pt, sourceResolutionLimitAugmentation X G a cX cG hG,
    sourceResolutionLimitAugmentation_degreewise X G a cX cG hG hX ha, hf⟩

end

end DaggerModels.PartII
