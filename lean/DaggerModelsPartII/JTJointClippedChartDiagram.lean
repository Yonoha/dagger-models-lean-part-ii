import DaggerModelsPartII.JTJointClippedBeadCoefficients
import DaggerModelsPartII.JTNativeSimplexImageDiagram
import DaggerModelsPartII.JTFullPrismSupportedDiagram
import DaggerModelsPartII.JTParametrizedProductSimplices

/-! An original diagram of simplicial charts gives an exact diagram of clipped coefficients. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedChartDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTJointRelativeParameters (withTime)
open JTJointRelativeGraphFamily (native originalParameter coefficient)
open JTJointIntervalQuotient (joint)
open JTJointClippedGluing (nativeGlued nativeComparison)
open JTJointClippedParameters (TraceFactors)
open JTJointClippedBeadCoefficients (simplexImage imageFactor parameter imageParameter_mixed
  imageCoefficient_realizes)
open JTParametrizedBeadGraph (sectionCoefficient)
open JTNativeSimplexImageDiagram (imageDegree imageFace)
open JTFullPrismSupportedDiagram (prisms degrees)
open JTPrismRectangle (prismValue)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev toSSet := NecklaceCode.simplicialFunctor.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable {H : A ⥤ SimplexCategory} (charts : H ⋙ std ⟶ codes L ⋙ toSSet)

private abbrev overClipped := native F ⋙ nativeGlued Q.code j
private abbrev clippedCode := overClipped F j ⋙ Over.forget Q.code
private abbrev k := coefficient (L := L)

private def asBead (a : A) :
    (NecklaceCode.single (H.obj a).len).toSSet ⟶ ((codes L).obj a).toSSet :=
  (NecklaceCode.singleIso (H.obj a).len).hom ≫ charts.app a

private def fromBeads : H ⋙ std ⟶ codes L ⋙ toSSet where
  app a := (NecklaceCode.singleIso (H.obj a).len).inv ≫ asBead charts a
  naturality a b f := by
    simpa only [asBead, Iso.inv_hom_id_assoc] using charts.naturality f

private def comparison : codes L ⋙ toSSet ⟶ clippedCode F j ⋙ toSSet :=
  Functor.whiskerRight (Functor.whiskerLeft (native F) (nativeComparison Q.code j))
    (Over.forget Q.code ⋙ toSSet)

private abbrev images := fromBeads charts ≫ comparison F j

/-- Every original chart diagram has its own exact diagram of clipped image degrees. -/
abbrev chartDegrees := imageDegree H (clippedCode F j) (images F j charts)

private abbrev faces := imageFace H (clippedCode F j) (images F j charts)

private abbrev selected (a : A) := imageFactor F j a (H.obj a).len (asBead charts a)

private abbrev traceType := withTime Q.map J time (native F) (joint Q.code j) ⟶ (k (L := L)) ⋙ J

variable (trace : traceType F j)
variable (h : TraceFactors Q.code j Q.map J time (native F)
  (k (L := L)) (originalParameter F) trace)

set_option maxHeartbeats 1200000 in
/-- The entire descended parameter on the chart images is natural. -/
def chartParameter : prisms (chartDegrees F j charts) time ⟶ (k (L := L)) ⋙ J where
  app a := parameter F j a trace h ((faces F j charts).app a)
  naturality {a b} f := by
    have hf := ((faces F j charts).naturality f).symm
    change (selected F j charts a).face ≫ ((overClipped F j).map f).left.map =
      std.map ((chartDegrees F j charts).map f) ≫ (selected F j charts b).face at hf
    exact imageParameter_mixed F j trace h (H.obj a).len (asBead charts a) f
      (asBead charts b) ((chartDegrees F j charts).map f) hf

set_option maxHeartbeats 1200000 in
/-- The original map into the raw target after cutting, on every time simplex. -/
def chartRaw : prisms (chartDegrees F j charts) time ⟶ (Functor.const A).obj (Raw W) where
  app a := fst (std.obj ((chartDegrees F j charts).obj a)) (J.obj (time.obj a)) ≫
    (faces F j charts).app a ≫ ((overClipped F j).obj a).hom.map ≫ Q.map
  naturality {a b} f := by
    have hf := (faces F j charts).naturality f
    change std.map ((chartDegrees F j charts).map f) ≫ (faces F j charts).app b =
      (faces F j charts).app a ≫ ((overClipped F j).map f).left.map at hf
    have hh := congrArg NecklaceCode.Hom.map (Over.w ((overClipped F j).map f))
    change ((overClipped F j).map f).left.map ≫ ((overClipped F j).obj b).hom.map =
      ((overClipped F j).obj a).hom.map at hh
    change (std.map ((chartDegrees F j charts).map f) ⊗ₘ J.map (time.map f)) ≫
        fst _ (J.obj (time.obj b)) ≫ (faces F j charts).app b ≫
          ((overClipped F j).obj b).hom.map ≫ Q.map =
      (fst _ (J.obj (time.obj a)) ≫ (faces F j charts).app a ≫
        ((overClipped F j).obj a).hom.map ≫ Q.map) ≫ 𝟙 (Raw W)
    rw [Category.comp_id, tensorHom_fst_assoc, ← Category.assoc (std.map _), hf,
      Category.assoc, ← Category.assoc (((overClipped F j).map f).left.map), hh]
    rfl

/-- The coefficient chosen by the actual image section. -/
def chartCoefficient (a : A) :
    (Input W).obj (op ((chartDegrees F j charts).obj a, (k (L := L)).obj a)) :=
  sectionCoefficient a (H.obj a).len (asBead charts a) (selected F j charts a).select

set_option maxHeartbeats 1200000 in
/-- Each chart coefficient has the exact prescribed raw image on its entire time prism. -/
theorem chartCoefficient_realizes (a : A) :
    prismValue (chartCoefficient F j charts a) ((chartParameter F j charts trace h).app a) =
      (chartRaw F j charts).app a :=
  imageCoefficient_realizes F j a trace h (H.obj a).len (asBead charts a)

/-- The section-restricted coefficients assemble on the entire supported chart
diagram, contravariantly in its actual horizontal and coefficient degrees. -/
def chartCoefficientSection :
    (Functor.const Aᵒᵖ).obj (PUnit : Type) ⟶ (degrees (chartParameter F j charts trace h)).op ⋙
      Input W :=
  JTFullPrismSupportedDiagram.coefficientSection (chartParameter F j charts trace h)
    (chartCoefficient F j charts) (chartRaw F j charts)
    (chartCoefficient_realizes F j charts trace h)

section AllCharts

open JTParametrizedProductSimplices (Index base degree simplex simplex_natural)

private abbrev X := codes L ⋙ toSSet
private abbrev baseOf := base (X (L := L))

/-- The tautological chart of every simplex in the original native source diagram. -/
def allCharts :
    degree (X (L := L)) ⋙ std ⟶ codes (baseOf (L := L) ⋙ L) ⋙ toSSet where
  app a := simplex (X (L := L)) a
  naturality _ _ f := (simplex_natural (X (L := L)) f).symm

private abbrev reindexed := F.precomp (baseOf (L := L))

private def reindexedTrace : traceType (reindexed F) j :=
  Functor.whiskerLeft (baseOf (L := L)) trace

include h in
private theorem reindexedTrace_factors :
    TraceFactors Q.code j Q.map J (baseOf (L := L) ⋙ time) (native (reindexed F))
      (k (L := baseOf (L := L) ⋙ L)) (originalParameter (reindexed F))
        (reindexedTrace F j trace) := by
  apply NatTrans.ext
  funext a
  exact NatTrans.congr_app h a.base

/-- The full descended parameter on the clipped images of all original simplices. -/
def allChartParameter :
    prisms (chartDegrees (reindexed F) j (allCharts (L := L))) (baseOf (L := L) ⋙ time) ⟶
      (k (L := baseOf (L := L) ⋙ L)) ⋙ J :=
  chartParameter (reindexed F) j (allCharts (L := L))
    (reindexedTrace F j trace) (reindexedTrace_factors F j trace h)

/-- The actual supported coefficients form one natural section over the
category of all original native simplices, with their original diagram arrows. -/
def allChartCoefficientSection :
    (Functor.const (Index (X (L := L)))ᵒᵖ).obj (PUnit : Type) ⟶
      (degrees (allChartParameter F j trace h)).op ⋙ Input W :=
  chartCoefficientSection (reindexed F) j (allCharts (L := L))
    (reindexedTrace F j trace) (reindexedTrace_factors F j trace h)

end AllCharts
end
end DaggerModels.PartII.JTJointClippedChartDiagram
