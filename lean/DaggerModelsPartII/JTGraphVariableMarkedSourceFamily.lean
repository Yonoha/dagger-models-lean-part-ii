import DaggerModelsPartII.JTGraphVariableTotalParametrizedFamily
import DaggerModelsPartII.JTTargetJointMarks
import DaggerModelsPartII.JTJointMarkArrowDecomposition

/-!
An actual marked weak resolution carrying the global full parameter family.
Pull back the EXISTING variable-source resolution along any diagram of
original comma objects, then retain all ordered marks over all target joints.
Terminal mark fibers give the second weak projection. Exact-cut categories
with discrete fibers are not being identified with this marked resolution.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableMarkedSourceFamily

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableResolutionCategory (Total totalLabels)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {B : Type} [SmallCategory B] (original : B ⥤ TargetComma Q)

private abbrev resolution := JTGraphVariableTimeTransport.resolutionDiagram Q

/-- The old full resolution pulled back along every original object and arrow. -/
abbrev Base := Grothendieck (original ⋙ resolution (Q := Q))

/-- Retain all original resolution data in its unchanged total category. -/
def toTotal : Base original ⥤ Total Q :=
  Grothendieck.pre (resolution (Q := Q)) original

/-- The full family native collapse gives the actual diagram over Q.code. -/
def native : Base original ⥤ Over Q.code :=
  toTotal original ⋙ Over.lift (JTParametrizedTargetFamilies.codes (totalLabels Q))
    (JTGraphVariableTotalParametrizedFamily.family Q).collapse

/-- All simultaneous ordered target-joint marks on the actual native source. -/
def marksDiagram : Base original ⥤ Cat.{0, 0} :=
  native original ⋙ JTTargetJointMarks.nativeDiagram Q.code

/-- The weak resolution retaining all original operations and all marks. -/
abbrev Marked := Grothendieck (marksDiagram original)

/-- Forget all marks without dropping any original resolution data. -/
abbrev forgetMarks : Marked original ⥤ Base original :=
  Grothendieck.forget (marksDiagram original)

/-- The ordered mark fibers have terminal objects, so forgetting marks is weak. -/
theorem forgetMarks_weak : WeakEquivalence (nerveMap (forgetMarks original)) :=
  GrothendieckContractibleFibers.projection_weak (marksDiagram original)
    (fun a ↦ JTTargetJointMarks.marks_point_GW ((native original).obj a).hom)

/-- Project to the exact original index category, retaining its original arrows. -/
def projection : Marked original ⥤ B :=
  forgetMarks original ⋙ Grothendieck.forget (original ⋙ resolution (Q := Q))

/-- Both projections are the existing weak Grothendieck projections. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection original)) := by
  have : WeakEquivalence (nerveMap (forgetMarks original)) := forgetMarks_weak original
  have : WeakEquivalence
      (nerveMap (Grothendieck.forget (original ⋙ resolution (Q := Q)))) :=
    JTGraphVariableResolutionCategory.projection_weak_of original
  change WeakEquivalence (nerveMap (forgetMarks original) ≫
    nerveMap (Grothendieck.forget (original ⋙ resolution (Q := Q))))
  infer_instance

/-- The exact old global family index after both actual weak-cover operations. -/
def toFamilyIndex : Marked original ⥤ Total Q :=
  forgetMarks original ⋙ toTotal original

/-- One strict full fixed-Q family on this original marked weak resolution.
Its parameters, raw equation and naturality are derived, not fresh inputs. -/
def family : JTParametrizedTargetFamilies.Family Q
    (toFamilyIndex original ⋙ totalLabels Q)
    (toFamilyIndex original ⋙ JTGraphVariableTotalParametrizedFamily.time Q) :=
  (JTGraphVariableTotalParametrizedFamily.family Q).precomp (toFamilyIndex original)

/-- Every marked arrow decomposes into exact native transport followed by
its genuine vertical mark increase. -/
theorem arrow_factor {a b : Marked original} (f : a ⟶ b) :
    Grothendieck.toTransport a f.base ≫
        JTJointMarkArrowDecomposition.vertical Q.code (native original) f = f :=
  JTJointMarkArrowDecomposition.factor Q.code (native original) f

end
end DaggerModels.PartII.JTGraphVariableMarkedSourceFamily
