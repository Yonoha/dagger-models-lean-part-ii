import DaggerModelsPartII.JTGraphRefinementArrowRecognition
import DaggerModelsPartII.JTPaddedGraphParameterRecognition

/-!
# Exact mixed operators of padded graph comparisons

Any arrow of the fixed-target comma whose native component preserves the two
pads is already an exact graph arrow, including for degenerate middle operators.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPaddedGraphArrowRecognition

open JTGraphRefinement JTGraphRefinementMixedArrow
open JTGraphRefinementArrowRecognition
open JTMixedGraphHorizontalTraversal (padded)
open JTMixedGraphRawRefinement (nativeGraphParameter)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTProjectiveOrderedFiberComparison (row)
open JTRealizedLabelEndpoints (orderedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev code := MixedGraphCylinderTraversal.code
private abbrev Δ (d : ℕ) := SSet.stdSimplex.{0}.obj ⦋d⦌
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

abbrev Label (d : ℕ) (k : SimplexCategory) :=
  ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code d))).obj (op k)

/-- The actual refinement with the same prescribed labels and collapse. -/
abbrev graph {d : ℕ} {k : SimplexCategory}
    (z : Label (W := W) (x := x) (y := y) d k) (s : Δ d ⟶ J.obj k) (c : code d ⟶ Q.code)
    (h : realizeGraph W k (nativeGraphParameter s) (orderedLabel W x y (code d) k z) =
      c.map ≫ Q.map) : Refinement W x y Q :=
  ⟨code d, k, z, nativeGraphParameter s, c, h⟩

variable {d e : ℕ} {k l : SimplexCategory}
variable {z : Label (W := W) (x := x) (y := y) d k} {s : Δ d ⟶ J.obj k} {c : code d ⟶ Q.code}
variable {z' : Label (W := W) (x := x) (y := y) e l} {t : Δ e ⟶ J.obj l} {c' : code e ⟶ Q.code}
variable {h : realizeGraph W k (nativeGraphParameter s) (orderedLabel W x y (code d) k z) =
  c.map ≫ Q.map}
variable {h' : realizeGraph W l (nativeGraphParameter t) (orderedLabel W x y (code e) l z') =
  c'.map ≫ Q.map}

private abbrev D := graph z s c h
private abbrev E := graph z' t c' h'

variable (a : (D (h := h)).toComma ⟶ (E (h' := h')).toComma)

private abbrev native := (projection.map a.left.base).1
private abbrev coefficient := (projection.map a.left.base).2

/-- The parameter equation follows from preservation of the actual reduced graph. -/
theorem parameter_eq (u : single d ⟶ single e) (hu : native a = padded u) :
    nativeGraphParameter s ≫ J.map (coefficient a) =
      (native a).map ≫ nativeGraphParameter t := by
  have H := reduced_eq a
  change lift (native a).map (nativeGraphParameter s ≫ J.map (coefficient a)) ≫
      (JTNecklaceEndpointCylinder.cylinder (code e)).app l =
    lift (native a).map ((native a).map ≫ nativeGraphParameter t) ≫
      (JTNecklaceEndpointCylinder.cylinder (code e)).app l at H
  rw [hu] at H ⊢
  exact JTPaddedGraphParameterRecognition.mixed_parameter_eq u (coefficient a) s t H

/-- Recover the literal mixed operator from the original comma arrow. -/
def recoverPadded (hu : ∃ u : single d ⟶ single e, native a = padded u) :
    D (h := h) ⟶ E (h' := h') :=
  recover a (by
    obtain ⟨u, hu⟩ := hu
    exact parameter_eq a u hu)

theorem evaluate_recoverPadded (hu : ∃ u : single d ⟶ single e, native a = padded u) :
    (evaluate Q).map (recoverPadded a hu) = a :=
  evaluate_recover a _

/-- The reduction to mixed operators preserves the arrow uniquely. -/
theorem existsUnique_mixedArrow (hu : ∃ u : single d ⟶ single e, native a = padded u) :
    ∃! f : D (h := h) ⟶ E (h' := h'), (evaluate Q).map f = a := by
  refine ⟨recoverPadded a hu, evaluate_recoverPadded a hu, ?_⟩
  intro f hf
  apply (evaluate Q).map_injective
  exact hf.trans (evaluate_recoverPadded a hu).symm

end

end DaggerModels.PartII.JTPaddedGraphArrowRecognition
