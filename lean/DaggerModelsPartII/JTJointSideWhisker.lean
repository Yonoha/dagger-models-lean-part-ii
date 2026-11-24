import DaggerModelsPartII.JTComposedPrismLabels

/-!
# Attach a relative endpoint edge to one full time-dependent label

The added edge uses the original endpoint parameter at every time. Its
coefficient may vary away from the ordinal face used by that parameter.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointSideWhisker

open TripleBeadEndpointLabel (labels)
open JTComposedPrismLabels (Coefficients rawProduct rawProduct_coefficient rawProduct_constant
  parameter parameter_left parameter_right rawProduct_eq)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev E := single 1
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev pt : SSet.{0} := Δ[0]
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {x z : Vertex W} {T : NecklaceCode}
variable {k l : SimplexCategory} {I : SSet.{0}}

/-- Pull the original endpoint parameter across the added edge, preserving all time simplices. -/
def edgeParameter {m : SimplexCategory} (t : pt ⊗ I ⟶ J.obj m) : E.toSSet ⊗ I ⟶ J.obj m :=
  (term E.toSSet ⊗ₘ 𝟙 I) ≫ t

theorem edgeParameter_boundary {m : SimplexCategory} (t : pt ⊗ I ⟶ J.obj m)
    (v : pt ⟶ E.toSSet) : (v ⊗ₘ 𝟙 I) ≫ edgeParameter t = t := by
  unfold edgeParameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  have h : v ≫ term E.toSSet = 𝟙 pt := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]
  have hi : (𝟙 pt ⊗ₘ 𝟙 I) = 𝟙 (pt ⊗ I) := tensorHom_id _ _
  rw [hi, Category.id_comp]

/-- On the used coefficient face an endpoint edge with the degenerate joint label
realizes to the exact joint at every horizontal and time simplex. -/
theorem edge_raw (u : l ⟶ k) (t : pt ⊗ I ⟶ J.obj l)
    (e : std.obj k ⟶ labels W E)
    (he : std.map u ≫ e = JTConstantOrderedLabel.constantCoefficient W z E l) :
    rawProduct W (edgeParameter (t ≫ J.map u)) e =
      fst E.toSSet I ≫ term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  unfold edgeParameter
  rw [← Category.assoc, rawProduct_coefficient, he, rawProduct_constant]

variable (p : T.toSSet ⊗ I ⟶ J.obj k)

private abbrev lastTrace := (pointAt T (ULift.up (Fin.last T.len)) ⊗ₘ 𝟙 I) ≫ p
private abbrev firstTrace := (pointAt T (ULift.up 0) ⊗ₘ 𝟙 I) ≫ p

/-- Append the edge with the complete original last-endpoint parameter. -/
def appendParameter : (wedge T E).toSSet ⊗ I ⟶ J.obj k :=
  parameter p (edgeParameter (lastTrace p)) (edgeParameter_boundary _ _).symm

/-- Prepend the edge with the complete original first-endpoint parameter. -/
def prependParameter : (wedge E T).toSSet ⊗ I ⟶ J.obj k :=
  parameter (edgeParameter (firstTrace p)) p (edgeParameter_boundary _ _)

theorem appendParameter_interior :
    (wedgeιLeft T E ⊗ₘ 𝟙 I) ≫ appendParameter p = p :=
  parameter_left _ _ _

theorem prependParameter_interior :
    (wedgeιRight E T ⊗ₘ 𝟙 I) ≫ prependParameter p = p :=
  parameter_right _ _ _

/-- The raw right edge of an appended label is the original joint if the
last-endpoint time parameter factors through the face on which the edge is degenerate. -/
theorem append_raw (C : Coefficients W T E k x z) (u : l ⟶ k)
    (t : pt ⊗ I ⟶ J.obj l)
    (htrace : lastTrace p = t ≫ J.map u)
    (hc : std.map u ≫ C.right = JTConstantOrderedLabel.constantCoefficient W z E l)
    (g : (wedge T E).toSSet ⟶ Raw W)
    (hi : rawProduct W p C.left = fst T.toSSet I ≫ wedgeιLeft T E ≫ g)
    (he : wedgeιRight T E ≫ g = term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) :
    rawProduct W (appendParameter p) (JTComposedPrismLabels.coefficient C) =
      fst (wedge T E).toSSet I ≫ g := by
  apply rawProduct_eq C p (edgeParameter (lastTrace p)) _ g hi
  rw [htrace, he]
  exact edge_raw u t C.right hc

/-- The raw left edge of a prepended label is the original joint under the
corresponding first-endpoint restriction. -/
theorem prepend_raw (C : Coefficients W E T k z x) (u : l ⟶ k)
    (t : pt ⊗ I ⟶ J.obj l)
    (htrace : firstTrace p = t ≫ J.map u)
    (hc : std.map u ≫ C.left = JTConstantOrderedLabel.constantCoefficient W z E l)
    (g : (wedge E T).toSSet ⟶ Raw W)
    (hi : rawProduct W p C.right = fst T.toSSet I ≫ wedgeιRight E T ≫ g)
    (he : wedgeιLeft E T ≫ g = term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) :
    rawProduct W (prependParameter p) (JTComposedPrismLabels.coefficient C) =
      fst (wedge E T).toSSet I ≫ g := by
  apply rawProduct_eq C (edgeParameter (firstTrace p)) p _ g _ hi
  rw [htrace, he]
  exact edge_raw u t C.left hc

end
end DaggerModels.PartII.JTJointSideWhisker
