import DaggerModelsPartII.JTComposedPrismLabels
import DaggerModelsPartII.JTWhiskerEdgeCoefficient
import DaggerModelsPartII.JTJointEndpointRelativeLift
import DaggerModelsPartII.JTPointTargetEvaluationCone

/-! Normalize both ends of a label while keeping its full supported coefficient. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSupportedNormalizedLabel

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_first
  glue_last glue_left glue_right wedgeMappingPullback)
open JTConstantOrderedLabel (constantCoefficient constantIndex constantLabel)
open OrderedNecklaceVertexPoints (zeroPoint)
open ReversalDiscreteFreeColimits (discreteFree)
open JTProjectiveOrderedFiberComparison (row vertexPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map f) W

variable {W : Source} {T U : NecklaceCode} {k l : SimplexCategory}

/-- Constant coefficients restrict along arbitrary native simplicial maps,
including bead inclusions that do not preserve both outer endpoints. -/
theorem constant_restrict (z : Vertex W) (i : T.toSSet ⟶ U.toSSet) :
    constantCoefficient W z T l = constantCoefficient W z U l ≫ pre W i := by
  have hi : i ≫ term U.toSSet = term T.toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simp only [constantCoefficient, Category.assoc, ← diagramMappingPrecomp_comp,
    ← discreteFree.map_comp, hi]

/-- If both labels are constant on one specified face, their actual glued
mapping-space coefficient is constant on exactly that same face. -/
theorem glue_onFace (u : l ⟶ k) (z : Vertex W)
    (c : std.obj k ⟶ labels W T) (d : std.obj k ⟶ labels W U)
    (h : c ≫ lastRestriction W T = d ≫ firstRestriction W U)
    (hc : std.map u ≫ c = constantCoefficient W z T l)
    (hd : std.map u ≫ d = constantCoefficient W z U l) :
    std.map u ≫ glue W T U k c d h = constantCoefficient W z (wedge T U) l := by
  apply (wedgeMappingPullback W T U).hom_ext
  · calc
      (std.map u ≫ glue W T U k c d h) ≫ pre W (wedgeιLeft T U) =
          std.map u ≫ c := by rw [Category.assoc, glue_left]
      _ = constantCoefficient W z T l := hc
      _ = _ := constant_restrict z (wedgeιLeft T U)
  · calc
      (std.map u ≫ glue W T U k c d h) ≫ pre W (wedgeιRight T U) =
          std.map u ≫ d := by rw [Category.assoc, glue_right]
      _ = constantCoefficient W z U l := hd
      _ = _ := constant_restrict z (wedgeιRight T U)

/-- A full old coefficient and its two correcting native edges. No constancy
of the old coefficient outside its actual support is required. -/
structure Data (W : Source) (T : NecklaceCode) (k : SimplexCategory) (z : Vertex W) where
  middle : std.obj k ⟶ labels W T
  front : std.obj k ⟶ labels W E
  back : std.obj k ⟶ labels W E
  front_join : front ≫ lastRestriction W E = middle ≫ firstRestriction W T
  back_join : middle ≫ lastRestriction W T = back ≫ firstRestriction W E
  first : front ≫ firstRestriction W E = term (std.obj k) ≫ zeroPoint W z
  last : back ≫ lastRestriction W E = term (std.obj k) ≫ zeroPoint W z

variable {z : Vertex W} (D : Data W T k z)

/-- The old coefficient followed by the back correcting edge. -/
def inside := glue W T E k D.middle D.back D.back_join

private theorem seam : D.front ≫ lastRestriction W E =
    inside D ≫ firstRestriction W (wedge T E) := by
  rw [inside, glue_first]
  exact D.front_join

/-- The full normalized triple label, with the original coefficient degree. -/
def coefficients : JTComposedPrismLabels.Coefficients W E (wedge T E) k z z where
  left := D.front
  right := inside D
  seam := seam D
  first := D.first
  last := by rw [inside, glue_last]; exact D.last

/-- All three full coefficients become constant on the same actual support. -/
theorem coefficient_onFace (u : l ⟶ k)
    (hm : std.map u ≫ D.middle = constantCoefficient W z T l)
    (hf : std.map u ≫ D.front = constantCoefficient W z E l)
    (hb : std.map u ≫ D.back = constantCoefficient W z E l) :
    std.map u ≫ JTComposedPrismLabels.coefficient (coefficients D) =
      constantCoefficient W z (wedge E (wedge T E)) l := by
  exact glue_onFace u z D.front (inside D) (seam D) hf
    (glue_onFace u z D.middle D.back D.back_join hm hb)

/-- The actual decorated arrow from the supported constant triple to the
full normalized triple. It keeps the native necklace unchanged. -/
def fromSupported (u : l ⟶ k)
    (hm : std.map u ≫ D.middle = constantCoefficient W z T l)
    (hf : std.map u ≫ D.front = constantCoefficient W z E l)
    (hb : std.map u ≫ D.back = constantCoefficient W z E l) :
    constantIndex W z (wedge E (wedge T E)) l ⟶
      JTComposedPrismLabels.index (coefficients D) := by
  apply JTOrderedLabelWedge.indexHomOfCoefficient (𝟙 _) u
  rw [JTConstantOrderedLabel.coefficient_constantLabel,
    JTOrderedLabelBinaryGlue.coefficient, JTComposedPrismLabels.orderedPoint_coefficient,
    Equiv.symm_apply_apply]
  change constantCoefficient W z (wedge E (wedge T E)) l =
    std.map u ≫ JTComposedPrismLabels.coefficient (coefficients D) ≫ pre W (𝟙 _)
  simp only [pre, discreteFree.map_id, diagramMappingPrecomp_id]
  exact (coefficient_onFace D u hm hf hb).symm

/-- The other leg of the supported span is an actual arrow to the point label. -/
def supportedToPoint : constantIndex W z (wedge E (wedge T E)) l ⟶
    JTPointTargetEvaluationCone.pointLabel W z :=
  JTConstantOrderedLabel.constantIndexHom W z
    (JTOrderedLabelJointInsertion.toPoint _) (SimplexCategory.isTerminalZero.from l)


/-- Convert two strict relative row-one edges into the actual normalized label. -/
def ofEdges (z : Vertex W) (c : std.obj k ⟶ labels W T)
    (f₀ f₁ : std.obj k ⟶ row W ⦋0⦌)
    (hc₀ : c ≫ firstRestriction W T = f₀ ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
    (hc₁ : c ≫ lastRestriction W T = f₁ ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
    (e₀ e₁ : std.obj k ⟶ row W ⦋1⦌)
    (he₀ : e₀ ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointEndpointRelativeLift.reverseBoundaryPair W f₀ z)
    (he₁ : e₁ ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointEndpointRelativeLift.boundaryPair W f₁ z) : Data W T k z where
  middle := c
  front := e₀ ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
  back := e₁ ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
  front_join := by
    rw [JTWhiskerEdgeCoefficient.last,
      (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W f₀ z he₀).2]
    exact hc₀.symm
  back_join := by
    rw [JTWhiskerEdgeCoefficient.first,
      (JTJointEndpointRelativeLift.boundaryPair_endpoints W f₁ z he₁).1]
    exact hc₁
  first := by
    rw [JTWhiskerEdgeCoefficient.first,
      (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W f₀ z he₀).1]
    simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  last := by
    rw [JTWhiskerEdgeCoefficient.last,
      (JTJointEndpointRelativeLift.boundaryPair_endpoints W f₁ z he₁).2]
    simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

/-- Normalize both ends with edges stationary on the full specified face.
The middle coefficient is retained literally at its original degree. -/
theorem exists_supported (z : Vertex W) (u : l ⟶ k) [Mono u]
    (c : std.obj k ⟶ labels W T) (f₀ f₁ : std.obj k ⟶ row W ⦋0⦌)
    (hc₀ : c ≫ firstRestriction W T = f₀ ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
    (hc₁ : c ≫ lastRestriction W T = f₁ ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
    (hf₀ : std.map u ≫ f₀ = term (std.obj l) ≫ vertexPoint W z)
    (hf₁ : std.map u ≫ f₁ = term (std.obj l) ≫ vertexPoint W z)
    (hW : letI : HomotopicalAlgebra.ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; HomotopicalAlgebra.IsFibrant W) :
    ∃ D : Data W T k z, D.middle = c ∧
      std.map u ≫ D.front = constantCoefficient W z E l ∧
      std.map u ≫ D.back = constantCoefficient W z E l := by
  obtain ⟨e₀, he₀, hb₀⟩ :=
    JTJointEndpointRelativeLift.exists_reverse_edge W u f₀ z hW hf₀
  obtain ⟨e₁, he₁, hb₁⟩ :=
    JTJointEndpointRelativeLift.exists_edge W u f₁ z hW hf₁
  refine ⟨ofEdges z c f₀ f₁ hc₀ hc₁ e₀ e₁ hb₀ hb₁, rfl, ?_, ?_⟩
  · exact JTWhiskerEdgeCoefficient.onFace W u z e₀ he₀
  · exact JTWhiskerEdgeCoefficient.onFace W u z e₁ he₁

end
end DaggerModels.PartII.JTSupportedNormalizedLabel
