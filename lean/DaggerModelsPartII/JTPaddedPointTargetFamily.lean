import DaggerModelsPartII.JTPaddedPrismParameter
import DaggerModelsPartII.JTPaddedSingleNecklaceDiagram
import DaggerModelsPartII.JTConstantOrderedLabelDiagram
import DaggerModelsPartII.JTPointTargetEvaluationCone
import DaggerModelsPartII.JTJointTraceObstruction
import DaggerModelsPartII.JTMarkedFiniteParametrizedTargetFamilies

/-! Turn a whole timed simplex diagram at a point into a comparable decorated family. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTPaddedPointTargetFamily

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTFullPrismSupportedDiagram (prisms)
open JTPaddedPrismParameter (padded includeInterior includePrisms include_parameter)
open JTPaddedSingleNecklaceDiagram (code simplicialIso singleIso_naturality)
open JTPointTargetEvaluationCone (pointTarget)
open JTParametrizedTargetFamilies (Family codes evaluate)
open JTOrderedLabelCoefficientPadding (embedding)
open JTOrderedLabelJointInsertion (toPointNatural)
open JTGraphFactoredPresentation (TargetComma)
open JTMarkedParametrizedTargetFamilyJoin (Mark)
open JTMarkedFiniteParametrizedTargetFamilies (Synchronized)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] (W : Source) (z : Vertex W)
variable {D t k : A ⥤ SimplexCategory} (p : prisms D t ⟶ k ⋙ J)

private abbrev T (D : A ⥤ SimplexCategory) := D ⋙ code

/-- The padded native code and both original raw endpoints are retained. -/
abbrev labels (D k : A ⥤ SimplexCategory) :=
  JTConstantOrderedLabelDiagram.diagram W z (T D) (padded k)

private abbrev iso (a : A) :=
  NecklaceCode.singleIso (JTPaddedTimeOperators.pad (D.obj a)).len

/-- Interpret the complete padded parameter on the actual native bead. -/
def parameter (a : A) :
    ((T D).obj a).toSSet ⊗ J.obj (t.obj a) ⟶ J.obj ((padded k).obj a) :=
  ((iso a).hom ⊗ₘ 𝟙 (J.obj (t.obj a))) ≫ (JTPaddedPrismParameter.parameter p).app a

set_option maxHeartbeats 850000 in
private theorem parameter_natural {a b : A} (f : a ⟶ b) :
    (((T D).map f).map ⊗ₘ J.map (t.map f)) ≫ parameter p b =
      parameter p a ≫ J.map ((padded k).map f) := by
  have h := (JTPaddedPrismParameter.parameter p).naturality f
  change (std.map ((padded D).map f) ⊗ₘ J.map (t.map f)) ≫
      (JTPaddedPrismParameter.parameter p).app b =
    (JTPaddedPrismParameter.parameter p).app a ≫ J.map ((padded k).map f) at h
  have hNative := singleIso_naturality (D.map f)
  change ((T D).map f).map ≫ (iso b).hom = (iso a).hom ≫ std.map ((padded D).map f)
    at hNative
  have ht : (((T D).map f).map ⊗ₘ J.map (t.map f)) ≫ ((iso b).hom ⊗ₘ 𝟙 _) =
      ((iso a).hom ⊗ₘ 𝟙 _) ≫ (std.map ((padded D).map f) ⊗ₘ J.map (t.map f)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, hNative]
  unfold parameter
  rw [← Category.assoc, ht, Category.assoc, h, Category.assoc]

/-- The entire padded family evaluates over the original point of the raw realization. -/
def family : Family (pointTarget W z) (labels W z D k) t where
  collapse := toPointNatural (T D)
  parameter := parameter p
  parameter_map {a b} f := by
    rw [JTConstantOrderedLabelDiagram.projection_map]
    exact parameter_natural p f
  raw a := JTJointTraceObstruction.constant_raw_overPoint W z ((T D).obj a)
    ((padded k).obj a) (t.obj a) (parameter p a)

private def firstMark : Mark (labels W z D k) where
  vertex _ := 0
  naturality f := by
    change ((OrderedLabelElements.projection W (boundaryPoint W z z)).map
      ((labels W z D k).map f)).2.toOrderHom 0 = 0
    rw [JTConstantOrderedLabelDiagram.projection_map]
    exact JTPaddedTimeOperators.map_first (k.map f)

private def lastMark : Mark (labels W z D k) where
  vertex a := Fin.last ((padded k).obj a).len
  naturality {a b} f := by
    change ((OrderedLabelElements.projection W (boundaryPoint W z z)).map
      ((labels W z D k).map f)).2.toOrderHom (Fin.last ((padded k).obj a).len) =
        Fin.last ((padded k).obj b).len
    rw [JTConstantOrderedLabelDiagram.projection_map]
    exact JTPaddedTimeOperators.map_last (k.map f)

/-- Stable outer marks make this family available for the existing ordered gluing. -/
def synchronized : Synchronized t (pointTarget W z) where
  labels := labels W z D k
  family := family W z p
  lower := firstMark W z
  upper := lastMark W z
  lower_bound _ _ _ _ := Fin.zero_le _
  upper_bound _ _ _ _ := Fin.le_last _

/-- The original horizontal simplex is included in the padded bead naturally
for every horizontal operator. -/
def interiorNatural :
    D ⋙ std ⟶ T D ⋙ NecklaceCode.simplicialFunctor :=
  Functor.whiskerRight (includeInterior D) std ≫ Functor.whiskerLeft D simplicialIso.inv

/-- The component of the natural interior inclusion at a horizontal simplex. -/
abbrev interior (a : A) : std.obj (D.obj a) ⟶ ((T D).obj a).toSSet :=
  interiorNatural.app a

/-- Restricting the native diagram parameter to the original interior recovers
its parameter on the entire time prism, with the original coefficient included. -/
theorem interior_parameter (a : A) :
    (interior (D := D) a ⊗ₘ 𝟙 (J.obj (t.obj a))) ≫ (family W z p).parameter a =
      p.app a ≫ J.map (embedding (k.obj a)) := by
  change (interior a ⊗ₘ 𝟙 (J.obj (t.obj a))) ≫ parameter p a = _
  change ((std.map (embedding (D.obj a)) ≫ (iso a).inv) ⊗ₘ
      𝟙 (J.obj (t.obj a))) ≫ ((iso a).hom ⊗ₘ 𝟙 _) ≫
        (JTPaddedPrismParameter.parameter p).app a = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact NatTrans.congr_app (include_parameter p) a

/-- The whole original fixed-point evaluation, on all its internal necklaces,
factors through a weakly contractible category. -/
theorem exists_contractible_factor :
    ∃ (C : Cat.{0, 0}) (u : JTParametrizedTargetFamilies.Presentation
      (L := labels W z D k) (time := t) ⥤ C)
      (v : C ⥤ TargetComma (pointTarget W z)),
      GW (pointMap (nerve C)) ∧ evaluate (family W z p) = u ⋙ v :=
  JTPointTargetEvaluationCone.exists_contractible_factor W z (family W z p)
    (JTConstantOrderedLabelDiagram.toPoint W z (T D) (padded k))

end
end DaggerModels.PartII.JTPaddedPointTargetFamily
