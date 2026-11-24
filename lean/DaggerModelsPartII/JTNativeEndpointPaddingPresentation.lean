import DaggerModelsPartII.JTNativeEndpointPaddingCylinder
import DaggerModelsPartII.JTHomotopyTargetComma
import DaggerModelsPartII.GrothendieckContractibleFibers

/-! The full presentation of the padded source projects weakly to the original. -/

set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNativeEndpointPadding

open BoundaryNecklaceComma (fiberDiagram diagram Presentation)

noncomputable section

variable {I : Type} [SmallCategory I]
variable (T : I ⥤ NecklaceCode) (time : I ⥤ SimplexCategory)

private abbrev original := (T.prod' time) ⋙ NecklaceCylinderJointDiagram.cylinderUnder

/-- Project every internal necklace to the original cylinder. -/
def projectPresentation : Presentation (cylinders T time) ⥤ Presentation (original T time) :=
  Grothendieck.map (Functor.whiskerRight (collapseCylinders T time) diagram)

/-- The entire padded presentation lies over exactly the same index. -/
theorem projectPresentation_forget :
    projectPresentation T time ⋙ Grothendieck.forget (fiberDiagram (original T time)) =
      Grothendieck.forget (fiberDiagram (cylinders T time)) :=
  Grothendieck.functor_comp_forget

private theorem weakViaForget {A B C : Type}
    [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (p : A ⥤ B) (q : B ⥤ C) (r : A ⥤ C) (e : p ⋙ q = r)
    (hq : WeakEquivalence (nerveMap q)) (hr : WeakEquivalence (nerveMap r)) :
    WeakEquivalence (nerveMap p) := by
  letI := hq
  apply (weakEquivalence_postcomp_iff (nerveMap p) (nerveMap q)).mp
  change WeakEquivalence (nerveMap (p ⋙ q))
  rw [e]
  exact hr

/-- Adding two native endpoint beads preserves the weak type of the full presentation. -/
theorem projectPresentation_weak :
    WeakEquivalence (nerveMap (projectPresentation T time)) := by
  let q := Grothendieck.forget (fiberDiagram (original T time))
  let r := Grothendieck.forget (fiberDiagram (cylinders T time))
  have hq : WeakEquivalence (nerveMap q) :=
    GrothendieckContractibleFibers.projection_weak _
      (fun i ↦ JTHomotopyTargetComma.fiber_point_GW_at (T.obj i) (time.obj i))
  have hr : WeakEquivalence (nerveMap r) :=
    GrothendieckContractibleFibers.projection_weak _
      (fun i ↦ JTHomotopyTargetComma.fiber_point_GW_at ((T ⋙ pad).obj i) (time.obj i))
  exact weakViaForget (projectPresentation T time) q r (projectPresentation_forget T time) hq hr

end

end DaggerModels.PartII.JTNativeEndpointPadding
