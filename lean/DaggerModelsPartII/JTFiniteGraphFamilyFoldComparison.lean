import DaggerModelsPartII.JTFiniteGraphFamilyAssembly
import DaggerModelsPartII.JTInterpolatedCylinderParameterTime
import DaggerModelsPartII.JTJoiningTimeFold

/-! Repeating an original family on the enlarged time leaves its evaluation unchanged after folding. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteGraphFamilyFoldComparison

open JTFiniteGraphFamilyAssembly (times parameter family)
open JTParametrizedTargetFamilies (Family codes cylinders liftNatural)
open JTParametrizedTargetLiftTransport (graph)
open JTJoiningTimeFold (reducedCylinder_square)
open JTInterpolatedCylinderParameterTime (changeTime changeTime_cylinderMap changeTime_augmentation)
open JTNecklaceEndpointCylinder (nativeMap value)
open JTTargetCommaPullback (diagram fst snd)
open BoundaryNecklaceComma (Presentation)
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

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (phase : A ⥤ SemiSimplexCategory)

private abbrev T (a : A) := (codes L).obj a
private abbrev fold (a : A) := JTHigherGraphTimeFamily.fold ⦋(phase.obj a).len⦌ (time.obj a)

/-- Folding is a natural transformation of the full original cylinder diagrams. -/
def foldNatural : cylinders (L := L) (time := times phase time) ⟶ cylinders (L := L)
    (time := time) where
  app a := changeTime (T (L := L) a) (fold (time := time) phase a)
  naturality {a b} f := by
    apply Under.UnderMorphism.ext
    exact (reducedCylinder_square ((codes L).map f)
      (show (phase.obj a, time.obj a) ⟶ (phase.obj b, time.obj b) from
        (phase.map f, time.map f))).symm

variable (F : Family Q L time)

private abbrev copies (a : A) (_ : Fin ((phase.obj a).len + 1)) := F.parameter a

private theorem copies_parameter (a : A) :
    parameter (copies phase F) a = ((T (L := L) a).toSSet ◁ fold (time := time) phase a) ≫
      F.parameter a :=
  JTHigherGraphTimeFamily.extendFamily_const (F.parameter a)

private theorem graph_fold (a : A) :
    ((foldNatural (L := L) (time := time) phase).app a).right ≫
      (graph (F.parameter a)).right = (graph (parameter (copies phase F) a)).right := by
  rw [copies_parameter]
  exact changeTime_cylinderMap _ _ (F.parameter a)

private theorem raw_copies (a : A) :
    (graph (parameter (copies phase F) a)).right ≫ ((underCocone W x y).app (L.obj a)).right =
      augmentation (T (L := L) a) ((times phase time).obj a) ≫ (F.collapse.app a).map ≫ Q.map := by
  rw [← graph_fold, Category.assoc, F.raw]
  change (changeTime _ (fold (time := time) phase a)).right ≫
      augmentation (T (L := L) a) (time.obj a) ≫ (F.collapse.app a).map ≫ Q.map = _
  rw [← Category.assoc, changeTime_augmentation]
  rfl

/-- Repeating the original graph in every phase supplies an enlarged family
with its complete raw equality and the same decorated labels. -/
def repeatFamily : Family Q L (times phase time) :=
  family (copies phase F) (fun f _ ↦ F.parameter_map f) F.collapse (raw_copies phase F)

/-- Folding commutes with both original fixed-target pullback projections. -/
theorem lift_fold :
    foldNatural phase ≫ liftNatural F = liftNatural (repeatFamily phase F) := by
  apply NatTrans.ext
  funext a
  change (foldNatural phase).app a ≫ (liftNatural F).app a =
    (liftNatural (repeatFamily phase F)).app a
  apply pullback.hom_ext (f := (underCocone W x y).app (L.obj a))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · rw [Category.assoc]
    change (foldNatural phase).app a ≫ (liftNatural F).app a ≫ fst W x y Q (L.obj a) =
      (liftNatural (repeatFamily phase F)).app a ≫ fst W x y Q (L.obj a)
    dsimp only [liftNatural]
    rw [JTCylinderOverTarget.lift_decorated, JTCylinderOverTarget.lift_decorated]
    apply Under.UnderMorphism.ext
    exact graph_fold phase F a
  · rw [Category.assoc]
    change (foldNatural phase).app a ≫ (liftNatural F).app a ≫ snd W x y Q (L.obj a) =
      (liftNatural (repeatFamily phase F)).app a ≫ snd W x y Q (L.obj a)
    dsimp only [liftNatural]
    rw [JTCylinderOverTarget.lift_native, JTCylinderOverTarget.lift_native]
    apply Under.UnderMorphism.ext
    change (changeTime _ (fold (time := time) phase a)).right ≫
        augmentation (T (L := L) a) (time.obj a) ≫ (F.collapse.app a).map =
      augmentation (T (L := L) a) ((times phase time).obj a) ≫ (F.collapse.app a).map
    rw [← Category.assoc, changeTime_augmentation]
    rfl

/-- Fold the native cylinders without discarding any internal necklace. -/
def foldPresentation : JTParametrizedTargetFamilies.Presentation (L := L) (time := times phase time)
    ⥤ JTParametrizedTargetFamilies.Presentation (L := L) (time := time) :=
  Grothendieck.map (Functor.whiskerRight (foldNatural phase) BoundaryNecklaceComma.diagram)

/-- The enlarged evaluation is exactly the original evaluation after folding. -/
theorem evaluate_fold :
    foldPresentation phase ⋙ JTParametrizedTargetFamilies.evaluate F =
      JTParametrizedTargetFamilies.evaluate (repeatFamily phase F) := by
  unfold foldPresentation JTParametrizedTargetFamilies.evaluate
    JTBoundaryNecklacePresentationCone.mapPresentation
  simp only [← Functor.assoc]
  rw [← Grothendieck.map_comp_eq, ← Functor.whiskerRight_comp, lift_fold]

end

end DaggerModels.PartII.JTFiniteGraphFamilyFoldComparison
