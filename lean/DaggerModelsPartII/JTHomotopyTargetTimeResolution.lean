import DaggerModelsPartII.JTHomotopyTargetComma
import DaggerModelsPartII.GrothendieckContractibleFibers
import DaggerModelsPartII.SimplicialResolutionFunctor

/-! Native cylinder fibers over the entire simplex category of a time space. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHomotopyTargetTimeResolution

noncomputable section

/-- The original time degree of each simplex and its actual simplex operator. -/
abbrev degree (X : SSet.{0}) : X.Elementsᵒᵖ ⥤ SimplexCategory :=
  (CategoryOfElements.π X).leftOp

/-- All native internal necklaces in the cylinders of a specified time space. -/
abbrev TimeResolution (T : NecklaceCode) (X : SSet.{0}) :=
  BoundaryNecklaceComma.Presentation (degree X ⋙ JTNecklaceEndpointCylinder.under T)

/-- The exact projection to the category of all original time simplices is weak. -/
theorem forget_weak (T : NecklaceCode) (X : SSet.{0}) :
    WeakEquivalence (nerveMap (Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram (degree X ⋙ JTNecklaceEndpointCylinder.under T)))) :=
  GrothendieckContractibleFibers.projection_weak _
    (fun c ↦ JTHomotopyTargetComma.fiber_point_GW_at T c.unop.fst.unop)

private theorem point_iff {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    GW (pointMap X) ↔ GW (pointMap Y) := by
  have h : f ≫ pointMap Y = pointMap X := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← h]
  exact weakEquivalence_precomp_iff f _

/-- Weak contractibility of the time space gives weak contractibility of
the entire native-cylinder resolution, keeping all time and necklace maps. -/
theorem point_GW_iff (T : NecklaceCode) (X : SSet.{0}) :
    GW (pointMap (nerve (TimeResolution T X))) ↔ GW (pointMap X) := by
  let p := nerveMap (Grothendieck.forget
    (BoundaryNecklaceComma.fiberDiagram (degree X ⋙ JTNecklaceEndpointCylinder.under T)))
  let a := SimplicialResolutionFunctor.augmentation.app X
  let b := SimplicialResolutionFunctor.elementsProjection.app X
  letI : WeakEquivalence p := forget_weak T X
  letI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  letI : WeakEquivalence b := SimplicialResolutionFunctor.elementsProjection_weak X
  exact (point_iff p).trans ((point_iff b).symm.trans (point_iff a))


/-- Replacing the time ordinal of each simplex preserves the weak
contractibility criterion for its whole native-cylinder resolution. -/
theorem point_GW_iff_at (T : NecklaceCode) {X : SSet.{0}} (time : X.Elementsᵒᵖ ⥤ SimplexCategory) :
    GW (pointMap (nerve (BoundaryNecklaceComma.Presentation
      (time ⋙ JTNecklaceEndpointCylinder.under T)))) ↔ GW (pointMap X) := by
  let F := BoundaryNecklaceComma.fiberDiagram (time ⋙ JTNecklaceEndpointCylinder.under T)
  let p := nerveMap (Grothendieck.forget F)
  let q := nerveMap (Grothendieck.forget
    (BoundaryNecklaceComma.fiberDiagram (degree X ⋙ JTNecklaceEndpointCylinder.under T)))
  have : WeakEquivalence p := GrothendieckContractibleFibers.projection_weak F
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at T (time.obj a))
  have : WeakEquivalence q := forget_weak T X
  exact (point_iff p).trans ((point_iff q).symm.trans (point_GW_iff T X))

end

end DaggerModels.PartII.JTHomotopyTargetTimeResolution
