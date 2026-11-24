import DaggerModelsPartII.JTJoiningTimeBifunctor
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! Exact evaluation of finite graph families whose native source and label can vary. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteGraphFamilyAssembly

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph)
open JTJoiningTimeBifunctor (joiningTime)
open DecoratedCylinderNecklacePresentation (underCocone)
open NecklaceCylinderAugmentation (augmentation)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev projection {W : Source} {x y : Vertex W} :=
  OrderedLabelElements.projection W (boundaryPoint W x y)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {phase : A ⥤ SemiSimplexCategory} {time : A ⥤ SimplexCategory}

/-- The actual enlarged time of the phase and time diagrams. -/
abbrev times (phase : A ⥤ SemiSimplexCategory) (time : A ⥤ SimplexCategory) :=
  (phase.prod' time) ⋙ joiningTime

private abbrev T (a : A) := ((codes L).obj a)
private abbrev d (a : A) := ((projection.obj (L.obj a))).2

variable (p : ∀ a, Fin ((phase.obj a).len + 1) →
  ((T (L := L) a).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (d (L := L) a)))

/-- The interpolation at each object uses every phase in the original order. -/
def parameter (a : A) :
    (T (L := L) a).toSSet ⊗ J.obj ((times phase time).obj a) ⟶ J.obj (d (L := L) a) :=
  JTHigherGraphTimeFamily.extendFamily (k := ⦋(phase.obj a).len⦌) (p a)

variable (hp : ∀ {a b : A} (f : a ⟶ b) (i : Fin ((phase.obj a).len + 1)),
  (((codes L).map f).map ⊗ₘ J.map (time.map f)) ≫
    p b ((SemiSimplexCategory.homEquiv (phase.map f)) i) =
    p a i ≫ J.map (projection.map (L.map f)).2)

include hp in
/-- Every per-phase square assembles into the exact square of the full graph. -/
theorem parameter_map {a b : A} (f : a ⟶ b) :
    (((codes L).map f).map ⊗ₘ J.map ((times phase time).map f)) ≫ parameter p b =
      parameter p a ≫ J.map (projection.map (L.map f)).2 := by
  exact JTHigherGraphTimeFamily.extendFamily_mixed
    (SemiSimplexCategory.toSimplexCategory.map (phase.map f))
    (SemiSimplexCategory.homEquiv (phase.map f)).injective
    ((codes L).map f).map (time.map f) (projection.map (L.map f)).2 (p a) (p b) (hp f)

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (c : codes L ⟶ (Functor.const A).obj Q.code)
variable (hraw : ∀ a, (graph (parameter p a)).right ≫ ((underCocone W x y).app (L.obj a)).right =
  augmentation (T (L := L) a) ((times phase time).obj a) ≫ (c.app a).map ≫ Q.map)

/-- The full raw equations and per-phase squares give one original family. -/
def family : Family Q L (times phase time) where
  collapse := c
  parameter := parameter p
  parameter_map f := parameter_map p hp f
  raw := hraw

/-- Evaluate every actual internal necklace in the whole finite-family diagram. -/
def evaluate := JTParametrizedTargetFamilies.evaluate (family p hp c hraw)

end

end DaggerModels.PartII.JTFiniteGraphFamilyAssembly
