import DaggerModelsPartII.JTEndpointCobase
import DaggerModelsPartII.OverMatchingRelative
import DaggerModelsPartII.ReedyCoefficientChange
import DaggerModelsPartII.ReedyFibrantDiagrams

/-!
# The relative matching criterion for a cosimplicial object under B

The opposite of an undercategory is the native overcategory of the opposite
base. Its actual matching arrow is identified with the relative matching
arrow to the constant base object. Thus endpoint-relative Reedy cofibrancy
can be tested by the original relative corner maps, including degree zero.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite

universe v u
namespace DaggerModels.PartII.UnderReedyCriterion

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimits C] [HasColimits C] (B : C)

local instance : ModelCategory (Under B) := JTEndpointCobase.underModel B
local instance : ModelCategory (Under B)ᵒᵖ := inferInstance
local instance : ModelCategory Cᵒᵖ := inferInstance
local instance : ModelCategory (Over (op B)) := ModelCategory.over (op B)
local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under B)ᵒᵖ) :=
  simplicialReedyModelCategory (Under B)ᵒᵖ

/-- Fibrancy under the fixed endpoint object is exactly fibrancy of the
original target object in the unchanged coefficient model. -/
theorem under_isFibrant_iff (X : Under B) : IsFibrant X ↔ IsFibrant X.right := by
  have hT : IsTerminal ((⊤_ (Under B)).right) :=
    terminalIsTerminal.isTerminalObj (Under.forget B) _
  change Fibration (terminal.from X) ↔ IsFibrant X.right
  rw [fibration_iff]
  change fibrations C (terminal.from X).right ↔ IsFibrant X.right
  exact ((isFibrant_iff_of_isTerminal (terminal.from X).right hT).trans
    (fibration_iff _)).symm

/-- Cofibrancy under B is precisely cofibrancy of the specified structure
arrow out of B; the initial under-object is the actual identity of B. -/
theorem under_isCofibrant_iff (X : Under B) :
    IsCofibrant X ↔ Cofibration X.hom := by
  let f : Under.mk (𝟙 B) ⟶ X := Under.homMk X.hom (by simp)
  have h := isCofibrant_iff_of_isInitial f Under.mkIdInitial
  have hc : cofibrations (Under B) f ↔ cofibrations C X.hom := Iff.rfl
  exact h.trans ((cofibration_iff f).trans (hc.trans (cofibration_iff X.hom).symm))

/-- The actual canonical duality, with the base object fixed. -/
def underOppositeToOver : (Under B)ᵒᵖ ⥤ Over (op B) :=
  (Over.opEquivOpUnder B).inverse

private theorem fibrations_underOpposite_iff
    {X Y : (Under B)ᵒᵖ} (f : X ⟶ Y) :
    fibrations (Under B)ᵒᵖ f ↔
      fibrations (Over (op B)) ((underOppositeToOver B).map f) := by
  rw [fibrations_op]
  change cofibrations C f.unop.right ↔
    fibrations (Over (op B)) ((underOppositeToOver B).map f)
  rw [fibrations_over_def]
  change cofibrations C f.unop.right ↔ fibrations Cᵒᵖ f.unop.right.op
  rw [fibrations_op]
  rfl

/-- Coefficient duality preserves the complete actual matching arrow. -/
def matchingCoefficientArrowIso
    (W : SimplexCategoryᵒᵖ ⥤ (Under B)ᵒᵖ) (n : ℕ) :
    Arrow.mk ((underOppositeToOver B).map ((matchingComparison n).app W)) ≅
      Arrow.mk ((matchingComparison n).app (W ⋙ underOppositeToOver B)) := by
  letI : PreservesLimitsOfSize.{0, 0} (underOppositeToOver B) := by
    change PreservesLimitsOfSize.{0, 0} (Over.opEquivOpUnder B).inverse
    infer_instance
  exact Arrow.isoMk (Iso.refl _)
    (ReedyCoefficientChange.matchingObjectIso (underOppositeToOver B) n W)
    (by simpa only [Iso.refl_hom, Category.id_comp] using
      (ReedyCoefficientChange.matchingComparison_map (underOppositeToOver B) n W).symm)

/-- The Reedy condition under the fixed endpoints is exactly the relative
matching condition in the original opposite coefficient model. No nonempty
matching-index assumption is used. -/
theorem reedyFibrant_iff_relativeMatching
    (W : SimplexCategoryᵒᵖ ⥤ (Under B)ᵒᵖ) :
    IsFibrant W ↔ reedyMatchingProperty (fibrations Cᵒᵖ)
      (OverMatchingRelative.structureMap (op B) (W ⋙ underOppositeToOver B)) := by
  rw [reedyFibrant_iff_matchingComparison]
  apply forall_congr'
  intro n
  rw [fibrations_underOpposite_iff B]
  have h₁ := (fibrations (Over (op B))).arrow_mk_iso_iff
    (matchingCoefficientArrowIso B W n)
  have h₂ := (fibrations Cᵒᵖ).arrow_mk_iso_iff
    (OverMatchingRelative.matchingArrowIso (op B) (W ⋙ underOppositeToOver B) n)
  exact h₁.trans h₂

end

end DaggerModels.PartII.UnderReedyCriterion
