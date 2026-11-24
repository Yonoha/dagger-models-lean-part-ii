import DaggerModelsPartII.JTParametrizedTargetRelabel
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange

/-! Compare original target evaluations after a native-code relabeling. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTParametrizedTargetRelabelEvaluation

open JTParametrizedTargetFamilies (Family codes cylinders liftNatural evaluate Presentation)
open JTParametrizedTargetRelabel (relabel nativeCylinder lift_component)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTBoundaryNecklacePresentationTransport (comparisonReindexedWithSourceChange)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
variable {L M : A ⥤ I W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (r : L ⟶ M)
variable (ρ : codes L ≅ codes M)
variable (hρ : ∀ a, ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
  (r.app a)).1 = ρ.hom.app a)

private abbrev targetDiagram := JTTargetCommaPullback.diagram W x y Q

/-- The relabeling acts on every internal necklace in the presentation. -/
def presentationTransport : Presentation (L := L) (time := time) ⥤
    Presentation (L := M) (time := time) :=
  Grothendieck.map (Functor.whiskerRight (nativeCylinder ρ)
    BoundaryNecklaceComma.diagram)

/-- The presentation comparison before evaluation. -/
def presentationComparison :=
  comparisonReindexedWithSourceChange targetDiagram (𝟭 A) (liftNatural F)
    (liftNatural (relabel F r ρ hρ)) (nativeCylinder ρ) r
    (lift_component F r ρ hρ)

/-- The comparison after evaluation into the original target comma. -/
def evaluationComparison :=
  Functor.whiskerRight (presentationComparison F r ρ hρ)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

/-- The presentation transport is a weak equivalence on nerves. -/
theorem presentationTransport_weak :
    WeakEquivalence (nerveMap (presentationTransport (time := time) ρ)) := by
  let p₀ := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (cylinders (L := L) (time := time)))
  let p₁ := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (cylinders (L := M) (time := time)))
  haveI : WeakEquivalence (nerveMap p₀) :=
    JTParametrizedTargetFamilies.projection_weak (L := L) (time := time)
  haveI : WeakEquivalence (nerveMap p₁) :=
    JTParametrizedTargetFamilies.projection_weak (L := M) (time := time)
  have he : nerveMap (presentationTransport (time := time) ρ) ≫ nerveMap p₁ =
      nerveMap p₀ :=
    (nerveFunctor.map_comp (presentationTransport (time := time) ρ).toCatHom
      p₁.toCatHom).symm.trans
      (congrArg nerveMap (Grothendieck.functor_comp_forget
        (α := Functor.whiskerRight (nativeCylinder ρ)
          BoundaryNecklaceComma.diagram)))
  exact weakEquivalence_of_postcomp_of_fac he

end
end DaggerModels.PartII.JTParametrizedTargetRelabelEvaluation
