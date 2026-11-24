import DaggerModelsPartII.JTNativePulledFamilyDiagram
import DaggerModelsPartII.JTGraphCylinderFiberDiagram

/-!
Strict composition and common-refinement comparisons for the full native
pullback family. `JTNativePulledFamilyDiagram.family` carries every subdivision
in one fixed ambient internal source; `JTNativePulledCutComparison.compare`
compares complete internal-necklace evaluations in the original fixed target.
No normalized-cut or mixed ambient-base coherence is asserted.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativePulledCutCoherence

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family)
open JTParametrizedTargetLiftTransport (graph)
open DecoratedCylinderNecklacePresentation (underCocone)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev Index (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)

variable {W : Source} {x y : Vertex W} (i : Index W x y)
private abbrev T := ((pr W x y).obj i).1
private abbrev k := ((pr W x y).obj i).2

variable {R S U : NecklaceCode} (f : S ⟶ T i) (g : R ⟶ S)

/-- The first actual native restriction as an object over the fixed source. -/
abbrev stage : Over (T i) := Over.mk f

/-- Its further native restriction has the literal composite map to the source. -/
abbrev refined : Over (T i) := Over.mk (g ≫ f)

/-- The actual Over-arrow from the refinement to the first stage. -/
def refineArrow : refined i f g ⟶ stage i f := Over.homMk g rfl

/-- The actual arrow from the first stage back to the ambient source. -/
def ambientArrow : stage i f ⟶ Over.mk (𝟙 (T i)) := Over.homMk f (by simp)

/-- The composite keeps exactly the native map `g ≫ f`. -/
theorem refine_ambient_left :
    (refineArrow i f g ≫ ambientArrow i f).left = g ≫ f := rfl

/-- Restricting the decorated label in two steps equals the direct restriction. -/
theorem labels_comp :
    (JTNativePulledFamilyDiagram.labels i).map
      (refineArrow i f g ≫ ambientArrow i f) =
    (JTNativePulledFamilyDiagram.labels i).map (refineArrow i f g) ≫
      (JTNativePulledFamilyDiagram.labels i).map (ambientArrow i f) :=
  (JTNativePulledFamilyDiagram.labels i).map_comp _ _

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (n : SimplexCategory) (c : T i ⟶ Q.code)
variable (p : (T i).toSSet ⊗ J.obj n ⟶ J.obj (k i))
variable (hr : (graph (i := i) p).right ≫ ((underCocone W x y).app i).right =
  augmentation (T i) n ≫ c.map ≫ Q.map)

/-- The full native collapse agrees with the direct composite restriction. -/
theorem collapse_refined :
    (JTNativePulledFamilyDiagram.family i n c p hr).collapse.app (refined i f g) =
      (g ≫ f) ≫ c := rfl

/-- The full old coefficient parameter agrees with direct native pullback. -/
theorem parameter_refined :
    (JTNativePulledFamilyDiagram.family i n c p hr).parameter (refined i f g) =
      (((g ≫ f).map ⊗ₘ 𝟙 (J.obj n)) ≫ p) := rfl

/-- Mixed native and time compatibility is exactly the family law. -/
theorem parameter_refineArrow :
    (g.map ⊗ₘ J.map (𝟙 n)) ≫
      (JTNativePulledFamilyDiagram.family i n c p hr).parameter (stage i f) =
    (JTNativePulledFamilyDiagram.family i n c p hr).parameter (refined i f g) ≫
      J.map (𝟙 (k i)) :=
  (JTNativePulledFamilyDiagram.family i n c p hr).parameter_map (refineArrow i f g)

/-- All native restrictions have one complete fixed-target evaluation functor. -/
abbrev totalEvaluation :
    JTParametrizedTargetFamilies.Presentation
      (L := JTNativePulledFamilyDiagram.labels i)
      (time := JTNativePulledFamilyDiagram.time i n) ⥤
        JTGraphFactoredPresentation.TargetComma Q :=
  JTParametrizedTargetFamilies.evaluate
    (JTNativePulledFamilyDiagram.family i n c p hr)

variable (e : U ⟶ T i) (q : R ⟶ U) (hsq : g ≫ f = q ≫ e)

/-- The shared internal-necklace source at the common refinement. -/
private abbrev Fiber (C : NecklaceCode) := JTGraphInterpolatedComparison.Fiber C n

/-- The left domain map retains the complete common internal-necklace fiber. -/
def leftDomain : Fiber n R ⥤ Fiber n S := JTGraphCylinderFiberDiagram.joint g (𝟙 n)

/-- The right domain map has the same common source and unchanged time. -/
def rightDomain : Fiber n R ⥤ Fiber n U := JTGraphCylinderFiberDiagram.joint q (𝟙 n)

/-- The full common evaluation is over the literal original `Q`. -/
abbrev commonEvaluation : Fiber n R ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTNativePulledCutComparison.evaluation i n c p hr (g ≫ f)

/-- The first full evaluation after native restriction. -/
abbrev leftEvaluation : Fiber n S ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTNativePulledCutComparison.evaluation i n c p hr f

/-- The second full evaluation after native restriction. -/
abbrev rightEvaluation : Fiber n U ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTNativePulledCutComparison.evaluation i n c p hr e

/-- First complete fixed-target comparison from the common refinement. -/
def leftComparison : commonEvaluation i f g n c p hr ⟶
    leftDomain (n := n) g ⋙ leftEvaluation i f n c p hr :=
  JTNativePulledCutComparison.compare i n c p hr (g ≫ f) f g rfl

/-- Second complete comparison from the identical common refinement. -/
def rightComparison : commonEvaluation i f g n c p hr ⟶
    rightDomain (n := n) q ⋙ rightEvaluation i n c p hr e :=
  JTNativePulledCutComparison.compare i n c p hr (g ≫ f) e q hsq.symm

end
end DaggerModels.PartII.JTNativePulledCutCoherence
