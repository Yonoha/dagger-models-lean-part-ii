import DaggerModelsPartII.JTGraphInterpolatedRaw
import DaggerModelsPartII.JTInternalTraversalLifts
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-!
An objectwise full family on the actual internal source necklace.
`JTGraphInterpolatedRaw.index` pulls the ordered label back along the native
augmentation; its `whole_raw_by` retains the original fixed target. No
functorial choice of prism lifts is made here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualObjectLiftedFamily

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceEndpointCylinder (cylinder)
open NecklaceCylinderAugmentation (augmentation)
open JTParametrizedTargetFamilies (Family codes)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev One := Discrete PUnit

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (V : TargetComma Q)

/-- The actual internal source code of the fixed comma object. -/
abbrev source : NecklaceCode := V.left.fiber.left

/-- The actual full reduced-cylinder traversal at the ambient decorated label. -/
abbrev traversal : (source V).toSSet ⟶
    (JTNecklaceEndpointCylinder.value
      (JTGraphLiftTransport.code V.left)).obj (JTGraphLiftTransport.degree V.left) :=
  V.left.fiber.hom.right

variable (s : JTInternalTraversalLifts.Lift (traversal V))

/-- Pull back the ambient ordered label along the native augmentation. -/
abbrev label : DecoratedNecklaceHomDiagram.Index W x y :=
  JTGraphInterpolatedRaw.index V (𝟙 (source V))

/-- The unit indexing category retains exactly this original internal necklace. -/
abbrev labels : One ⥤ DecoratedNecklaceHomDiagram.Index W x y :=
  (Functor.const One).obj (label V)

/-- Time has degree zero; the whole source code remains in the native coordinate. -/
abbrev time : One ⥤ SimplexCategory := (Functor.const One).obj ⦋0⦌

/-- The prism lift supplies the entire old coefficient parameter. -/
abbrev parameter : (source V).toSSet ⊗ J.obj ⦋0⦌ ⟶
    J.obj (JTGraphLiftTransport.degree V.left) :=
  fst (source V).toSSet (J.obj ⦋0⦌) ≫ s.val

/-- The full graph equation follows from the exact original prism lift. -/
theorem parameter_graph :
    lift (fst (source V).toSSet (J.obj ⦋0⦌) ≫
      ((𝟙 (source V) : source V ⟶ source V) ≫
        JTCommaGraphPredecessor.augmentationCode V.left).map)
        (parameter V s) ≫
      (cylinder (JTGraphLiftTransport.code V.left)).app
        (JTGraphLiftTransport.degree V.left) =
      fst (source V).toSSet (J.obj ⦋0⦌) ≫
      (𝟙 (source V) : source V ⟶ source V).map ≫ traversal V := by
  change lift (fst (source V).toSSet (J.obj ⦋0⦌) ≫
      traversal V ≫ augmentation (JTGraphLiftTransport.code V.left)
        (JTGraphLiftTransport.degree V.left))
      (fst (source V).toSSet (J.obj ⦋0⦌) ≫ s.val) ≫ _ = _
  rw [← comp_lift, Category.assoc, s.property]
  rfl

/-- The native target of the pulled family is literally the original map. -/
abbrev nativeCollapse : source V ⟶ Q.code := V.hom.hom

/-- One complete original-target family on the unit category. -/
def family : Family Q (labels V) time where
  collapse := {
    app := fun _ ↦ nativeCollapse V
    naturality := by
      intro a b f
      cases a
      cases b
      simp }
  parameter := fun _ ↦ parameter V s
  parameter_map := by
    intro a b f
    cases a
    cases b
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp [labels, time]
    change ((𝟙 (source V) : source V ⟶ source V).map ▷ J.obj ⦋0⦌) ≫
      parameter V s = parameter V s
    have hmap : (𝟙 (source V) : source V ⟶ source V).map =
        𝟙 (source V).toSSet := by
      change NecklaceCode.simplicialFunctor.map (𝟙 (source V)) = 𝟙 _
      exact NecklaceCode.simplicialFunctor.map_id _
    rw [hmap, id_whiskerRight, Category.id_comp]
  raw := by
    intro a
    have h := JTGraphInterpolatedRaw.whole_raw_by V (𝟙 (source V))
      (parameter V s) (parameter_graph V s)
    simpa only [Category.id_comp] using h

/-- Every object of the family has exactly the original native target map. -/
theorem family_nativeCollapse (a : One) :
    (family V s).collapse.app a = V.hom.hom := rfl

/-- The family uses the actual internal source code, without padding. -/
theorem family_source (a : One) :
    (codes (labels V)).obj a = source V := rfl

/-- The full coefficient degree is unchanged from the ambient decorated label. -/
theorem family_degree (a : One) :
    ((OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        ((labels V).obj a)).2 = JTGraphLiftTransport.degree V.left := rfl

/-- Such an objectwise family exists for every original comma object. -/
theorem exists_family :
    Nonempty {F : Family Q (labels V) time //
      ∀ a : One, F.collapse.app a = V.hom.hom} := by
  obtain ⟨s⟩ := JTInternalTraversalLifts.nonempty_of_necklace (traversal V)
  exact ⟨⟨family V s, family_nativeCollapse V s⟩⟩

end
end DaggerModels.PartII.JTActualObjectLiftedFamily
