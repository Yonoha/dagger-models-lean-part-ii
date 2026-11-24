import DaggerModelsPartII.JTJointEndpointRelativeLift
import DaggerModelsPartII.JTTwoFaceUnionWeak

/-! Relative identity-edge lifts over any mono weak subcomplex inclusion. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointSubcomplexRelativeLift

open JTProjectiveOrderedFiberComparison
open JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable (W : Source) {U : SSet.{0}} {k : SimplexCategory} (i : U ⟶ Δ k)
variable (f : Δ k ⟶ row W ⦋0⦌)
variable (z : (row W ⦋0⦌).obj (op ⦋0⦌))
variable (hf : i ≫ f = term U ≫ vertexPoint W z)

/-- The stationary identity edge on the entire subcomplex. -/
def identityOnU : U ⟶ row W ⦋1⦌ :=
  term U ≫ vertexPoint W z ≫ identityFamily W

/-- The variable endpoint followed by the constant endpoint. -/
def boundaryPair : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift f (term (Δ k) ≫ vertexPoint W z)

/-- The constant endpoint followed by the variable endpoint. -/
def reverseBoundaryPair : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift (term (Δ k) ≫ vertexPoint W z) f

/-- The complete fixed square for a stationary edge on U. -/
def square : CommSq (identityOnU W z) i (endpointArrow W)
    (boundaryPair W f z) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, identityOnU, endpointArrow, boundaryPair, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hf.symm
  · simp only [Category.assoc, identityOnU, endpointArrow, boundaryPair, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    rw [← Category.assoc]
    have h : i ≫ term (Δ k) = term U := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]

/-- The reversed complete fixed square. -/
def reverseSquare : CommSq (identityOnU W z) i (endpointArrow W)
    (reverseBoundaryPair W f z) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, identityOnU, endpointArrow, reverseBoundaryPair,
      prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    rw [← Category.assoc]
    have h : i ≫ term (Δ k) = term U := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
  · simp only [Category.assoc, identityOnU, endpointArrow, reverseBoundaryPair,
      prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hf.symm

/-- All-dimensional exact relative lift space. -/
def liftSpace : SSet.{0} := SSet.ihomToPullbackFiber (square W i f z hf)

/-- All-dimensional exact relative lift space in reverse order. -/
def reverseLiftSpace : SSet.{0} := SSet.ihomToPullbackFiber (reverseSquare W i f z hf)

variable [Mono i]

/-- The exact lift space is Kan for an injective-fibrant target. -/
theorem liftSpace_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (liftSpace W i f z hf).KanComplex := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (square W i f z hf)

theorem reverseLiftSpace_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (reverseLiftSpace W i f z hf).KanComplex := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (reverseSquare W i f z hf)

variable [WeakEquivalence i]

/-- Every exact relative lift is parameterized by a weakly contractible space. -/
theorem liftSpace_toPoint_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (term (liftSpace W i f z hf)) := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak (square W i f z hf)

theorem reverseLiftSpace_toPoint_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (term (reverseLiftSpace W i f z hf)) := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak
    (reverseSquare W i f z hf)

include hf in
/-- A strict edge with the prescribed endpoints, stationary on all of U. -/
theorem exists_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ e : Δ k ⟶ row W ⦋1⦌,
      i ≫ e = identityOnU W z ∧ e ≫ endpointArrow W = boundaryPair W f z := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let e := (square W i f z hf).lift
  exact ⟨e, (square W i f z hf).fac_left, (square W i f z hf).fac_right⟩

include hf in
theorem exists_reverse_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ e : Δ k ⟶ row W ⦋1⦌,
      i ≫ e = identityOnU W z ∧ e ≫ endpointArrow W = reverseBoundaryPair W f z := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let e := (reverseSquare W i f z hf).lift
  exact ⟨e, (reverseSquare W i f z hf).fac_left,
    (reverseSquare W i f z hf).fac_right⟩


section TwoFaces

variable {m : ℕ} (S T : Finset (Fin (m + 1)))
variable (v : Fin (m + 1)) (hvS : v ∈ S) (hvT : v ∈ T)

private abbrev twoFace : (Δ ⦋m⦌).Subcomplex :=
  SSet.stdSimplex.face S ⊔ SSet.stdSimplex.face T

include v hvS hvT in
/-- The weak inclusion of the two actual faces supplies both orientation lift spaces. -/
theorem twoFace_liftSpaces_toPoint_weak
    (f : Δ ⦋m⦌ ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : (twoFace S T).ι ≫ f =
      term ((twoFace S T).toSSet) ≫ vertexPoint W z)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (term (liftSpace W (twoFace S T).ι f z hf)) ∧
      WeakEquivalence (term (reverseLiftSpace W (twoFace S T).ι f z hf)) := by
  have : WeakEquivalence (twoFace S T).ι :=
    JTTwoFaceUnionWeak.union_weak_of_common_vertex S T v hvS hvT
  exact ⟨liftSpace_toPoint_weak W (twoFace S T).ι f z hf hW,
    reverseLiftSpace_toPoint_weak W (twoFace S T).ι f z hf hW⟩

include v hvS hvT in
/-- Both strict relative edges exist on a union of faces with a common vertex. -/
theorem twoFace_exists_edges
    (f : Δ ⦋m⦌ ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : (twoFace S T).ι ≫ f =
      term ((twoFace S T).toSSet) ≫ vertexPoint W z)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (∃ e : Δ ⦋m⦌ ⟶ row W ⦋1⦌,
      (twoFace S T).ι ≫ e = identityOnU W z ∧
        e ≫ endpointArrow W = boundaryPair W f z) ∧
    (∃ e : Δ ⦋m⦌ ⟶ row W ⦋1⦌,
      (twoFace S T).ι ≫ e = identityOnU W z ∧
        e ≫ endpointArrow W = reverseBoundaryPair W f z) := by
  have : WeakEquivalence (twoFace S T).ι :=
    JTTwoFaceUnionWeak.union_weak_of_common_vertex S T v hvS hvT
  exact ⟨exists_edge W (twoFace S T).ι f z hf hW,
    exists_reverse_edge W (twoFace S T).ι f z hf hW⟩

end TwoFaces


end
end DaggerModels.PartII.JTJointSubcomplexRelativeLift

