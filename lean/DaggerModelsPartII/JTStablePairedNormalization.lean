import DaggerModelsPartII.JTTargetCommaPullback
import DaggerModelsPartII.JTStableEndpointQuotient
import OriginalFlagOriginalNormalization

/-! Pointwise paired normalization over a variable diagram of actual pullback presentations. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification

namespace DaggerModels.PartII.JTStablePairedNormalization

open BoundaryNecklaceComma (necklaceUnder toNative fromNative sourceCode fiberDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I]
variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev G := JTTargetCommaPullback.Presentation W x y Q

/-- The original source necklaces, viewed under their ordered boundaries. -/
def sourceDiagram (S : I ⥤ G W x y Q) : I ⥤ Under B :=
  S ⋙ sourceCode (E W x y Q) ⋙ necklaceUnder

/-- The actual varying paired pullback in the same base parameter. -/
def pairedDiagram (S : I ⥤ G W x y Q) : I ⥤ Under B :=
  S ⋙ Grothendieck.forget (fiberDiagram (E W x y Q)) ⋙ E W x y Q

/-- The map into the actual paired pullback is natural in the full presentation. -/
def evaluation (S : I ⥤ G W x y Q) :
    sourceDiagram W x y Q S ⟶ pairedDiagram W x y Q S :=
  Functor.whiskerLeft S (BoundaryNecklaceComma.evaluation (E W x y Q))

private def nativeAt (P : G W x y Q) :=
  (toNative ((E W x y Q).obj P.base)).obj P.fiber

/-- Normalize the map into the actual paired pullback, retaining both projections. -/
def normalizedAt (P : G W x y Q) :=
  (fromNative ((E W x y Q).obj P.base)).obj (normOver (nativeAt W x y Q P))

/-- Original necklace collapse into the pairwise normalized necklace. -/
def quotientAt (P : G W x y Q) :
    necklaceUnder.obj P.fiber.left ⟶ necklaceUnder.obj (normalizedAt W x y Q P).left :=
  necklaceUnder.map (originalNormalization (nativeAt W x y Q P)).hom

/-- The complete paired map factors through normalization at every parameter. -/
theorem quotientAt_factor (P : G W x y Q) :
    quotientAt W x y Q P ≫ (normalizedAt W x y Q P).hom = P.fiber.hom := by
  apply Under.UnderMorphism.ext
  exact originalNormalization_triangle (nativeAt W x y Q P)

/-- Pointwise normalization of each actual paired pullback map. -/
def normalizedEndpoints (S : I ⥤ G W x y Q) : I → Under B :=
  fun p ↦ necklaceUnder.obj (normalizedAt W x y Q (S.obj p)).left

/-- The finite collapse supplied to the simultaneous stable quotient. -/
def endpointQuotients (S : I ⥤ G W x y Q) (p : I) :
    (sourceDiagram W x y Q S).obj p ⟶ normalizedEndpoints W x y Q S p :=
  quotientAt W x y Q (S.obj p)

/-- The stable quotient of all original necklaces under the paired target diagram. -/
def stableDiagram (S : I ⥤ G W x y Q) : I ⥤ Under B :=
  JTStableEndpointQuotient.diagram (sourceDiagram W x y Q S)
    (normalizedEndpoints W x y Q S) (endpointQuotients W x y Q S)

/-- Its canonical natural quotient from the original internal necklaces. -/
def stableQuotient (S : I ⥤ G W x y Q) :
    sourceDiagram W x y Q S ⟶ stableDiagram W x y Q S :=
  JTStableEndpointQuotient.quotient (sourceDiagram W x y Q S)
    (normalizedEndpoints W x y Q S) (endpointQuotients W x y Q S)

/-- Exact evaluation into the actual paired pullbacks after simultaneous normalization. -/
def stableEvaluation (S : I ⥤ G W x y Q) :
    stableDiagram W x y Q S ⟶ pairedDiagram W x y Q S :=
  JTStableEndpointQuotient.factor (sourceDiagram W x y Q S)
    (normalizedEndpoints W x y Q S) (endpointQuotients W x y Q S)
    (evaluation W x y Q S)
    (fun p ↦ (normalizedAt W x y Q (S.obj p)).hom)
    (fun p ↦ quotientAt_factor W x y Q (S.obj p))

/-- The original natural paired map is recovered exactly, on all arrows. -/
theorem stableQuotient_evaluation (S : I ⥤ G W x y Q) :
    stableQuotient W x y Q S ≫ stableEvaluation W x y Q S =
      evaluation W x y Q S :=
  JTStableEndpointQuotient.quotient_factor (sourceDiagram W x y Q S)
    (normalizedEndpoints W x y Q S) (endpointQuotients W x y Q S)
    (evaluation W x y Q S)
    (fun p ↦ (normalizedAt W x y Q (S.obj p)).hom)
    (fun p ↦ quotientAt_factor W x y Q (S.obj p))

/-- The original codes form an actual presentation over the stable diagram. -/
def covered (S : I ⥤ G W x y Q) :
    I ⥤ BoundaryNecklaceComma.Presentation (stableDiagram W x y Q S) :=
  JTTargetCommaPullback.assemble (stableDiagram W x y Q S) (𝟭 I)
    (S ⋙ sourceCode (E W x y Q)) (stableQuotient W x y Q S)

end

end DaggerModels.PartII.JTStablePairedNormalization
