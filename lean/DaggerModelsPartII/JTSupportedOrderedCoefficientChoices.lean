import DaggerModelsPartII.JTVariableFixedLiftChoiceDiagram
import DaggerModelsPartII.JTVariableFixedLiftSections
import DaggerModelsPartII.JTParametrizedTargetFamilyComparison
import DaggerModelsPartII.JTOrderedLabelWedge
import DaggerModelsPartII.JTConstantOrderedLabel
import DaggerModelsPartII.JTOrderedNecklaceLabelFibrancy
import DaggerModelsPartII.JTHigherInterleavedParameter

/-! Relative choices for a naturally supported diagram of actual ordered coefficients. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedOrderedCoefficientChoices

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (codes)
open OrderedNecklaceLabelDiagram (necklaceLabels boundaryLabels necklaceBoundaryRestriction)
open JTConstantOrderedLabel (constantCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)

private abbrev T := codes L

/-- The actual old ordered coefficient of each decorated label. -/
def old (a : I) : std.obj ((K W z L).obj a) ⟶
    (necklaceLabels W).obj (op ((T W z L).obj a)) :=
  JTOrderedLabelBinaryGlue.coefficient W z z ((T W z L).obj a) ((K W z L).obj a)
    (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj a))

/-- The literal constant coefficient in the original complete degree. -/
def constant (a : I) : std.obj ((K W z L).obj a) ⟶
    (necklaceLabels W).obj (op ((T W z L).obj a)) :=
  constantCoefficient W z ((T W z L).obj a) ((K W z L).obj a)

/-- The literal constant coefficient on the specified used face. -/
def supportedConstant (a : I) : std.obj (S.obj a) ⟶
    (necklaceLabels W).obj (op ((T W z L).obj a)) :=
  constantCoefficient W z ((T W z L).obj a) (S.obj a)

/-- The original ordered coefficient respects every native and degree operator. -/
theorem old_map {a b : I} (f : a ⟶ b) :
    old W z L a = std.map ((K W z L).map f) ≫ old W z L b ≫
      ((T W z L).op ⋙ necklaceLabels W).map f.op := by
  have h := JTOrderedLabelWedge.coefficient_of_indexHom
    (W := W) (x := z) (y := z)
    (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj a))
    (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj b))
    ((T W z L).map f) ((K W z L).map f) (L.map f)
    (show (OrderedLabelElements.projection W (boundaryPoint W z z)).map (L.map f) =
      ((T W z L).map f, (K W z L).map f) from rfl)
  simpa only [old, Functor.comp_map, Functor.op_map,
    OrderedNecklaceLabelDiagram.necklaceLabels] using h

/-- Literal constants obey the same two original operators. -/
theorem constant_map {a b : I} (f : a ⟶ b) :
    constant W z L a = std.map ((K W z L).map f) ≫ constant W z L b ≫
      ((T W z L).op ⋙ necklaceLabels W).map f.op := by
  change constantCoefficient W z ((T W z L).obj a) ((K W z L).obj a) =
    std.map ((K W z L).map f) ≫
      constantCoefficient W z ((T W z L).obj b) ((K W z L).obj b) ≫
      diagramMappingPrecomp
        (ReversalDiscreteFreeColimits.discreteFree.map ((T W z L).map f).map) W
  rw [← Category.assoc,
    ← JTConstantOrderedLabel.constantCoefficient_ordinal W z
      ((T W z L).obj b) ((K W z L).map f)]
  exact (JTConstantOrderedLabel.constantCoefficient_native W z
    ((T W z L).map f) ((K W z L).obj a))

/-- Both original outer boundary points are fixed by the old coefficient. -/
theorem old_boundary (a : I) :
    old W z L a ≫ (necklaceBoundaryRestriction W).app (op ((T W z L).obj a)) =
    term (std.obj ((K W z L).obj a)) ≫ boundaryPoint W z z :=
  JTOrderedLabelBinaryGlue.coefficient_boundary W z z ((T W z L).obj a) ((K W z L).obj a)
    (OrderedLabelElements.label W (boundaryPoint W z z) (L.obj a))

/-- The same boundary is fixed by the literal degree-wise constant. -/
theorem constant_boundary (a : I) :
    constant W z L a ≫ (necklaceBoundaryRestriction W).app (op ((T W z L).obj a)) =
    term (std.obj ((K W z L).obj a)) ≫ boundaryPoint W z z :=
  JTConstantOrderedLabel.constantCoefficient_boundary W z ((T W z L).obj a) ((K W z L).obj a)

variable (hs : ∀ a : I, std.map (u.app a) ≫ old W z L a =
  supportedConstant W z L S a)

/-- The exact relative fixed-square data, with the original varying native
label spaces and the original coefficient degrees. -/
def diagram : JTVariableFixedLiftChoiceDiagram.Diagram I where
  support := S ⋙ std
  domain := K W z L ⋙ std
  values := (T W z L).op ⋙ necklaceLabels W
  boundary := (Functor.const Iᵒᵖ).obj (boundaryLabels W)
  incl := Functor.whiskerRight u std
  restriction := Functor.whiskerLeft (T W z L).op (necklaceBoundaryRestriction W)
  onSupport a := supportedConstant W z L S a
  base a := term (std.obj ((K W z L).obj a)) ≫ boundaryPoint W z z
  onSupport_map := by
    intro a b f
    change std.map (S.map f) ≫ constantCoefficient W z ((T W z L).obj b) (S.obj b) ≫
      diagramMappingPrecomp
        (ReversalDiscreteFreeColimits.discreteFree.map ((T W z L).map f).map) W =
      constantCoefficient W z ((T W z L).obj a) (S.obj a)
    rw [← Category.assoc,
      ← JTConstantOrderedLabel.constantCoefficient_ordinal W z
        ((T W z L).obj b) (S.map f)]
    exact (JTConstantOrderedLabel.constantCoefficient_native W z
      ((T W z L).map f) (S.obj a)).symm
  base_map := by
    intro a b f
    change std.map ((K W z L).map f) ≫
      (term (std.obj ((K W z L).obj b)) ≫ boundaryPoint W z z) ≫ 𝟙 _ =
      term (std.obj ((K W z L).obj a)) ≫ boundaryPoint W z z
    rw [Category.comp_id, ← Category.assoc]
    congr 1
  comm := by
    intro a
    change supportedConstant W z L S a ≫
      (necklaceBoundaryRestriction W).app (op ((T W z L).obj a)) =
      std.map (u.app a) ≫
        (term (std.obj ((K W z L).obj a)) ≫ boundaryPoint W z z)
    rw [supportedConstant, JTConstantOrderedLabel.constantCoefficient_boundary,
      ← Category.assoc]
    congr 1

/-- All-dimensional fixed-square choices over the actual ordered diagram. -/
abbrev spaces : Iᵒᵖ ⥤ SSet.{0} :=
  JTVariableFixedLiftChoiceDiagram.choices (diagram W z L S u)

/-- The old coefficient is a natural exact point of every relative square. -/
def oldFamily : JTVariableFixedLiftSections.LiftFamily (diagram W z L S u) where
  lift a := old W z L a
  support a := hs a
  boundary a := old_boundary W z L a
  naturality f := (old_map W z L f).symm

/-- The literal full-degree constant is a second natural exact point. -/
def constantFamily : JTVariableFixedLiftSections.LiftFamily (diagram W z L S u) where
  lift a := constant W z L a
  support a := JTConstantOrderedLabel.constantCoefficient_ordinal W z
    ((T W z L).obj a) (u.app a)
  boundary a := constant_boundary W z L a
  naturality f := (constant_map W z L f).symm

/-- The old coefficient as a natural vertex of the full higher choice diagram. -/
def oldSection : (Functor.const Iᵒᵖ).obj (std.obj ⦋0⦌) ⟶ spaces W z L S u :=
  JTVariableFixedLiftSections.sectionOfLifts (diagram W z L S u)
    (oldFamily W z L S u hs)

/-- The literal constant as a natural vertex of the same choice diagram. -/
def constantSection : (Functor.const Iᵒᵖ).obj (std.obj ⦋0⦌) ⟶
    spaces W z L S u :=
  JTVariableFixedLiftSections.sectionOfLifts (diagram W z L S u)
    (constantFamily W z L S u)

/-- Full relative choices are Kan when each original native label has positive length. -/
theorem spaces_kan (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((T W z L).obj a).len) (a : Iᵒᵖ) :
    ((spaces W z L S u).obj a).KanComplex := by
  apply JTVariableFixedLiftChoiceDiagram.choices_kan
    (diagram W z L S u) (by
      intro b
      change Mono (std.map (u.app b))
      letI := hu b
      infer_instance)
  exact fun b ↦ JTOrderedNecklaceLabelFibrancy.necklaceBoundaryRestriction_fibration
    W hW ((T W z L).obj b) (hp b)

/-- The fixed-square choice fiber is weakly contractible objectwise. -/
theorem spaces_toPoint_weak (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((T W z L).obj a).len) (a : Iᵒᵖ) :
    WeakEquivalence (term ((spaces W z L S u).obj a)) := by
  apply JTVariableFixedLiftChoiceDiagram.choices_toPoint_weak
    (diagram W z L S u) (by
      intro b
      change Mono (std.map (u.app b))
      letI := hu b
      infer_instance)
    (fun b ↦ JTInterleavedParameter.standardMap_weak (u.app b))
  exact fun b ↦ JTOrderedNecklaceLabelFibrancy.necklaceBoundaryRestriction_fibration
    W hW ((T W z L).obj b) (hp b)

/-- The total higher choice cover retains the original index and is weak. -/
theorem projection_weak (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((T W z L).obj a).len) :
    WeakEquivalence (nerveMap
      (JTVariableFixedLiftChoiceDiagram.projection (diagram W z L S u))) := by
  apply JTVariableFixedLiftChoiceDiagram.projection_weak
    (diagram W z L S u) (by
      intro b
      change Mono (std.map (u.app b))
      letI := hu b
      infer_instance)
    (fun b ↦ JTInterleavedParameter.standardMap_weak (u.app b))
  exact fun b ↦ JTOrderedNecklaceLabelFibrancy.necklaceBoundaryRestriction_fibration
    W hW ((T W z L).obj b) (hp b)

end
end DaggerModels.PartII.JTSupportedOrderedCoefficientChoices
