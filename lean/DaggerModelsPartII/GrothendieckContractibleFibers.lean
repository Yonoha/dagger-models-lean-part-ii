import DaggerModelsPartII.GrothendieckCommaRetraction
import OriginalQuillenAHomotopyReconciledRecovered

/-!
# The original Grothendieck projection with contractible fiber nerves

The actual comma category of the original projection retracts to its
unchanged fiber category. Contractible fiber nerves therefore supply the
literal comma hypothesis for the native original Quillen Theorem A.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.GrothendieckContractibleFibers

noncomputable section

variable {C : Type u} [Category.{u} C] (F : C ⥤ Cat.{u,u})

/-- Contractibility of the original fiber nerve transfers through the
checked actual comma-to-fiber retraction, at every original base object. -/
theorem comma_point_GW
    (hF : ∀ c : C, GW (pointMap (nerve (F.obj c)))) (c : C) :
    GW (pointMap (nerve (CostructuredArrow (Grothendieck.forget F) c))) := by
  have hr : WeakEquivalence (nerveMap (GrothendieckCommaRetraction.retract F c)) :=
    GrothendieckCommaRetraction.retract_weak F c
  have hf : WeakEquivalence (pointMap (nerve (F.obj c))) :=
    (weakEquivalence_iff_GW _).2 (hF c)
  have he : nerveMap (GrothendieckCommaRetraction.retract F c) ≫
      pointMap (nerve (F.obj c)) =
        pointMap (nerve (CostructuredArrow (Grothendieck.forget F) c)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← he]
  infer_instance

/-- If every actual fiber nerve is weakly contractible, the ORIGINAL
unlocalized Grothendieck projection is a Kan weak equivalence. -/
theorem projection_weak
    (hF : ∀ c : C, GW (pointMap (nerve (F.obj c)))) :
    WeakEquivalence (nerveMap (Grothendieck.forget F)) :=
  (weakEquivalence_iff_GW _).2
    (DaggerNerveTheoremA.nerveMap_GW (Grothendieck.forget F)
      (comma_point_GW F hF))

end

end DaggerModels.PartII.GrothendieckContractibleFibers
