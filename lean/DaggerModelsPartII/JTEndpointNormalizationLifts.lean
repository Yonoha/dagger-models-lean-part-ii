import DaggerModelsPartII.JTParameterVertexKan
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration
import DaggerModelsPartII.ParameterVertexLiftSpace

/-!
# Original endpoint-normalizing families along a specified groupoid parameter

The original endpoint arrow is a Kan fibration under the exact retained
injective Kan fibrancy premise. The two lifts have separate specified
degenerate faces; no simultaneous two-face extension or target finality is
asserted. The input path is explicit, not an arbitrary raw realization edge.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointNormalizationLifts

open JTProjectiveOrderedFiberComparison
open JTParameterContraction

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev C (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

/-- The original horizontal degeneracy gives the complete identity-edge family. -/
def identityFamily (W : Source) : row W ⦋0⦌ ⟶ row W ⦋1⦌ :=
  (C W).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op

theorem identityFamily_endpoint (W : Source) (i : Fin 2) :
    identityFamily W ≫ endpoint W i = 𝟙 (row W ⦋0⦌) := by
  have h : JTXiEndpointCollapseBoundary.ordinaryEndpoint i ≫
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    ext j
    change 0 = j.val
    have hj : j.val < 1 := j.isLt
    omega
  change (C W).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op ≫
    (C W).map (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op = _
  rw [← (C W).map_comp, ← op_comp, h, op_id]
  exact (C W).map_id _

/-- The constant family at the SAME originally specified row vertex. -/
def constantVertexMap (W : Source) (k : SimplexCategory)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) : J k ⟶ row W ⦋0⦌ :=
  SSet.stdSimplex.isTerminalObj₀.from (J k) ≫ vertexPoint W x

theorem vertex_constant (W : Source) (k : SimplexCategory) (a : Fin (k.len + 1))
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    parameterVertex k a ≫ constantVertexMap W k x = vertexPoint W x := by
  dsimp only [constantVertexMap]
  rw [← Category.assoc]
  have h : parameterVertex k a ≫ SSet.stdSimplex.isTerminalObj₀.from (J k) =
      𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

private def leftSquare (W : Source) (k : SimplexCategory) (a : Fin (k.len + 1))
    (z : J k ⟶ row W ⦋0⦌) (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : parameterVertex k a ≫ z = vertexPoint W x) :
    CommSq (vertexPoint W x ≫ identityFamily W) (parameterVertex k a)
      (endpointArrow W) (prod.lift (constantVertexMap W k x) z) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, endpointArrow, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    exact (vertex_constant W k a x).symm
  · simp only [Category.assoc, endpointArrow, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hx.symm

private def rightSquare (W : Source) (k : SimplexCategory) (b : Fin (k.len + 1))
    (z : J k ⟶ row W ⦋0⦌) (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : parameterVertex k b ≫ z = vertexPoint W y) :
    CommSq (vertexPoint W y ≫ identityFamily W) (parameterVertex k b)
      (endpointArrow W) (prod.lift z (constantVertexMap W k y)) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, endpointArrow, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hy.symm
  · simp only [Category.assoc, endpointArrow, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    exact (vertex_constant W k b y).symm

/-- All lifts of the SAME fixed left endpoint-normalization square. -/
def leftLiftSpace (W : Source) (k : SimplexCategory) (a : Fin (k.len + 1))
    (z : J k ⟶ row W ⦋0⦌) (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : parameterVertex k a ≫ z = vertexPoint W x) : SSet.{0} :=
  SSet.ihomToPullbackFiber (leftSquare W k a z x hx)

/-- All lifts of the SAME fixed right endpoint-normalization square. -/
def rightLiftSpace (W : Source) (k : SimplexCategory) (b : Fin (k.len + 1))
    (z : J k ⟶ row W ⦋0⦌) (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : parameterVertex k b ≫ z = vertexPoint W y) : SSet.{0} :=
  SSet.ihomToPullbackFiber (rightSquare W k b z y hy)

theorem leftLiftSpace_toPoint_weak (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (a : Fin (k.len + 1)) (z : J k ⟶ row W ⦋0⦌)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : parameterVertex k a ≫ z = vertexPoint W x) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (leftLiftSpace W k a z x hx)) := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.parameterVertex_liftSpace_toPoint_weak k a
    (leftSquare W k a z x hx)

theorem rightLiftSpace_toPoint_weak (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (b : Fin (k.len + 1)) (z : J k ⟶ row W ⦋0⦌)
    (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : parameterVertex k b ≫ z = vertexPoint W y) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (rightLiftSpace W k b z y hy)) := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.parameterVertex_liftSpace_toPoint_weak k b
    (rightSquare W k b z y hy)

theorem leftLiftSpace_kan (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (a : Fin (k.len + 1)) (z : J k ⟶ row W ⦋0⦌)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : parameterVertex k a ≫ z = vertexPoint W x) :
    (leftLiftSpace W k a z x hx).KanComplex := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : Mono (parameterVertex k a) := JTParameterVertexKan.vertex_mono k a
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (leftSquare W k a z x hx)

theorem rightLiftSpace_kan (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (b : Fin (k.len + 1)) (z : J k ⟶ row W ⦋0⦌)
    (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : parameterVertex k b ≫ z = vertexPoint W y) :
    (rightLiftSpace W k b z y hy).KanComplex := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : Mono (parameterVertex k b) := JTParameterVertexKan.vertex_mono k b
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (rightSquare W k b z y hy)

/-- Actual complete edge families, with only their two SEPARATELY specified faces. -/
structure Families (W : Source) (k : SimplexCategory) (a b : Fin (k.len + 1))
    (z : J k ⟶ row W ⦋0⦌) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) where
  leftFamily : J k ⟶ row W ⦋1⦌
  rightFamily : J k ⟶ row W ⦋1⦌
  left_boundary : leftFamily ≫ endpointArrow W = prod.lift (constantVertexMap W k x) z
  right_boundary : rightFamily ≫ endpointArrow W = prod.lift z (constantVertexMap W k y)
  left_degenerate : parameterVertex k a ≫ leftFamily = vertexPoint W x ≫ identityFamily W
  right_degenerate : parameterVertex k b ≫ rightFamily = vertexPoint W y ≫ identityFamily W

/-- Lift the SAME specified path through the original endpoint fibration.
This does not assert contractibility of endpoint fibers or target commas. -/
def normalizedFamilies (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (a b : Fin (k.len + 1)) (z : J k ⟶ row W ⦋0⦌)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : parameterVertex k a ≫ z = vertexPoint W x)
    (hy : parameterVertex k b ≫ z = vertexPoint W y) : Families W k a b z x y := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : Cofibration (parameterVertex k a) := JTParameterVertexKan.vertex_cofibration k a
  have : WeakEquivalence (parameterVertex k a) := JTParameterVertexKan.vertex_weak k a
  have : Cofibration (parameterVertex k b) := JTParameterVertexKan.vertex_cofibration k b
  have : WeakEquivalence (parameterVertex k b) := JTParameterVertexKan.vertex_weak k b
  exact
    { leftFamily := (leftSquare W k a z x hx).lift
      rightFamily := (rightSquare W k b z y hy).lift
      left_boundary := (leftSquare W k a z x hx).fac_right
      right_boundary := (rightSquare W k b z y hy).fac_right
      left_degenerate := (leftSquare W k a z x hx).fac_left
      right_degenerate := (rightSquare W k b z y hy).fac_left }

theorem simplexUnit_constant (W : Source) (k : SimplexCategory)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    JTCylinderCEComparison.simplexUnit.app k ≫ constantVertexMap W k x =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj k) ≫ vertexPoint W x := by
  dsimp only [constantVertexMap]
  rw [← Category.assoc]
  exact congrArg (fun f ↦ f ≫ vertexPoint W x)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

variable {W : Source} {k : SimplexCategory} {a b : Fin (k.len + 1)}
variable {z : J k ⟶ row W ⦋0⦌} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

/-- Restrict the WHOLE left family along the actual free-groupoid unit. -/
def leftSimplexFamily (d : Families W k a b z x y) :
    SSet.stdSimplex.obj k ⟶ row W ⦋1⦌ :=
  JTCylinderCEComparison.simplexUnit.app k ≫ d.leftFamily

/-- The corresponding WHOLE right family, now of the required coefficient type. -/
def rightSimplexFamily (d : Families W k a b z x y) :
    SSet.stdSimplex.obj k ⟶ row W ⦋1⦌ :=
  JTCylinderCEComparison.simplexUnit.app k ≫ d.rightFamily

theorem leftSimplex_boundary (d : Families W k a b z x y) :
    leftSimplexFamily d ≫ endpointArrow W =
      prod.lift
        (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj k) ≫ vertexPoint W x)
        (JTCylinderCEComparison.simplexUnit.app k ≫ z) := by
  dsimp only [leftSimplexFamily]
  rw [Category.assoc, d.left_boundary, prod.comp_lift, simplexUnit_constant]

theorem rightSimplex_boundary (d : Families W k a b z x y) :
    rightSimplexFamily d ≫ endpointArrow W =
      prod.lift (JTCylinderCEComparison.simplexUnit.app k ≫ z)
        (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj k) ≫ vertexPoint W y) := by
  dsimp only [rightSimplexFamily]
  rw [Category.assoc, d.right_boundary, prod.comp_lift, simplexUnit_constant]

theorem leftSimplex_degenerate (d : Families W k a b z x y) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k a) ≫ leftSimplexFamily d =
      vertexPoint W x ≫ identityFamily W := by
  dsimp only [leftSimplexFamily]
  rw [← Category.assoc, JTParameterVertexKan.simplexUnit_vertex, d.left_degenerate]

theorem rightSimplex_degenerate (d : Families W k a b z x y) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k b) ≫ rightSimplexFamily d =
      vertexPoint W y ≫ identityFamily W := by
  dsimp only [rightSimplexFamily]
  rw [← Category.assoc, JTParameterVertexKan.simplexUnit_vertex, d.right_degenerate]

end

end DaggerModels.PartII.JTEndpointNormalizationLifts
