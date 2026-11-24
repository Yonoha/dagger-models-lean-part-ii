import DaggerModelsPartII.JTEndpointNormalizationLifts
import DaggerModelsPartII.JTFixedLiftSpacePrecomp
import DaggerModelsPartII.JTInterleavedTimeFace
import NativeFibrationSurjectiveComponents

/-! Relative identity-edge labels along an injective ordinal face. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory DaggerNativeHornPointWeakEquivalences
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointEndpointRelativeLift

open JTProjectiveOrderedFiberComparison JTEndpointNormalizationLifts
open DaggerNativeStandardSimplexContraction

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable (W : Source) {l k : SimplexCategory} (u : l ⟶ k) [Mono u]
variable (f : Δ k ⟶ row W ⦋0⦌)
variable (z : (row W ⦋0⦌).obj (op ⦋0⦌))
variable (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z)

private def constant (n : SimplexCategory) : Δ n ⟶ row W ⦋0⦌ :=
  term (Δ n) ≫ vertexPoint W z

private theorem constant_natural {m n : SimplexCategory} (a : m ⟶ n) :
    std.map a ≫ constant W z n = constant W z m := by
  dsimp only [constant]
  rw [← Category.assoc]
  have h : std.map a ≫ term (Δ n) = term (Δ m) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]

/-- The prescribed degenerate identity edge on the entire specified face. -/
def identityOnFace : Δ l ⟶ row W ⦋1⦌ :=
  constant W z l ≫ identityFamily W

theorem identityOnFace_natural {m n : SimplexCategory} (a : m ⟶ n) :
    std.map a ≫ identityOnFace W z (l := n) =
      identityOnFace W z (l := m) := by
  simp only [identityOnFace, ← Category.assoc, constant_natural]

/-- The boundary pair in the original zero--one endpoint order. -/
def boundaryPair : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift f (constant W z k)

/-- The same boundary pair with the variable endpoint on the right. -/
def reverseBoundaryPair : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  prod.lift (constant W z k) f

theorem boundaryPair_natural {m n : SimplexCategory} (a : m ⟶ n)
    (g : Δ n ⟶ row W ⦋0⦌) :
    std.map a ≫ boundaryPair W g z =
      boundaryPair W (std.map a ≫ g) z := by
  apply prod.hom_ext
  · simp only [Category.assoc, boundaryPair, prod.lift_fst]
  · simp only [Category.assoc, boundaryPair, prod.lift_snd]
    exact constant_natural W z a

theorem reverseBoundaryPair_natural {m n : SimplexCategory} (a : m ⟶ n)
    (g : Δ n ⟶ row W ⦋0⦌) :
    std.map a ≫ reverseBoundaryPair W g z =
      reverseBoundaryPair W (std.map a ≫ g) z := by
  apply prod.hom_ext
  · simp only [Category.assoc, reverseBoundaryPair, prod.lift_fst]
    exact constant_natural W z a
  · simp only [Category.assoc, reverseBoundaryPair, prod.lift_snd]

/-- The exact lifting square retaining both the full base and the face label. -/
def square (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    CommSq (identityOnFace W z) (std.map u)
    (endpointArrow W) (boundaryPair W f z) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, identityOnFace, constant, endpointArrow,
      boundaryPair, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hf.symm
  · simp only [Category.assoc, identityOnFace, constant, endpointArrow,
      boundaryPair, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    rw [← Category.assoc]
    have h : std.map u ≫ term (Δ k) = term (Δ l) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]

/-- The exact relative square with the variable endpoint on the right. -/
def reverseSquare (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    CommSq (identityOnFace W z) (std.map u)
      (endpointArrow W) (reverseBoundaryPair W f z) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, identityOnFace, constant, endpointArrow,
      reverseBoundaryPair, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    rw [← Category.assoc]
    have h : std.map u ≫ term (Δ k) = term (Δ l) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
  · simp only [Category.assoc, identityOnFace, constant, endpointArrow,
      reverseBoundaryPair, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    exact hf.symm

omit [Mono u] in
private theorem face_weak : WeakEquivalence (std.map u : Δ l ⟶ Δ k) := by
  have hl : WeakEquivalence (toUnit (Δ l)) :=
    contractible_terminal_weak (simplexContractible l.len)
  have hk : WeakEquivalence (toUnit (Δ k)) :=
    contractible_terminal_weak (simplexContractible k.len)
  letI := hl
  letI := hk
  have h : std.map u ≫ toUnit (Δ k) = toUnit (Δ l) :=
    isTerminalTensorUnit.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

/-- All-dimensional space of exact relative endpoint lifts. -/
def liftSpace : SSet.{0} := SSet.ihomToPullbackFiber (square W u f z hf)

/-- All-dimensional space of exact relative lifts in the reversed endpoint order. -/
def reverseLiftSpace : SSet.{0} :=
  SSet.ihomToPullbackFiber (reverseSquare W u f z hf)

/-- The relative lift space is Kan when the original endpoint arrow is a fibration. -/
theorem liftSpace_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (liftSpace W u f z hf).KanComplex := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (square W u f z hf)

theorem reverseLiftSpace_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (reverseLiftSpace W u f z hf).KanComplex := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan
    (reverseSquare W u f z hf)

/-- This fixed relative lift space is weakly contractible. -/
theorem liftSpace_toPoint_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (term (liftSpace W u f z hf)) := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : WeakEquivalence (std.map u : Δ l ⟶ Δ k) := face_weak u
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak (square W u f z hf)

theorem reverseLiftSpace_toPoint_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (term (reverseLiftSpace W u f z hf)) := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : WeakEquivalence (std.map u : Δ l ⟶ Δ k) := face_weak u
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak
    (reverseSquare W u f z hf)

/-- An actual full edge label with both prescribed strict equations. -/
theorem exists_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    ∃ e : Δ k ⟶ row W ⦋1⦌,
      std.map u ≫ e = identityOnFace W z ∧
      e ≫ endpointArrow W = boundaryPair W f z := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : WeakEquivalence (std.map u : Δ l ⟶ Δ k) := face_weak u
  have : Cofibration (std.map u : Δ l ⟶ Δ k) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let e := (square W u f z hf).lift
  exact ⟨e, (square W u f z hf).fac_left, (square W u f z hf).fac_right⟩

/-- A full relative edge with the variable endpoint on the right. -/
theorem exists_reverse_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    ∃ e : Δ k ⟶ row W ⦋1⦌,
      std.map u ≫ e = identityOnFace W z ∧
      e ≫ endpointArrow W = reverseBoundaryPair W f z := by
  have : Mono (std.map u : Δ l ⟶ Δ k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  have : WeakEquivalence (std.map u : Δ l ⟶ Δ k) := face_weak u
  have : Cofibration (std.map u : Δ l ⟶ Δ k) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let e := (reverseSquare W u f z hf).lift
  exact ⟨e, (reverseSquare W u f z hf).fac_left,
    (reverseSquare W u f z hf).fac_right⟩

/-- The two literal endpoint equations encoded by the first orientation. -/
theorem boundaryPair_endpoints {e : Δ k ⟶ row W ⦋1⦌}
    (he : e ≫ endpointArrow W = boundaryPair W f z) :
    e ≫ endpoint W 0 = f ∧
      e ≫ endpoint W 1 = term (Δ k) ≫ vertexPoint W z := by
  constructor
  · have h := congrArg (fun g : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ =>
      g ≫ prod.fst) he
    simpa only [Category.assoc, endpointArrow, boundaryPair, prod.lift_fst]
      using h
  · have h := congrArg (fun g : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ =>
      g ≫ prod.snd) he
    simpa only [Category.assoc, endpointArrow, boundaryPair, constant,
      prod.lift_snd] using h

/-- The two literal endpoint equations encoded by the reversed orientation. -/
theorem reverseBoundaryPair_endpoints {e : Δ k ⟶ row W ⦋1⦌}
    (he : e ≫ endpointArrow W = reverseBoundaryPair W f z) :
    e ≫ endpoint W 0 = term (Δ k) ≫ vertexPoint W z ∧
      e ≫ endpoint W 1 = f := by
  constructor
  · have h := congrArg (fun g : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ =>
      g ≫ prod.fst) he
    simpa only [Category.assoc, endpointArrow, reverseBoundaryPair, constant,
      prod.lift_fst] using h
  · have h := congrArg (fun g : Δ k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌ =>
      g ≫ prod.snd) he
    simpa only [Category.assoc, endpointArrow, reverseBoundaryPair, prod.lift_snd]
      using h

omit [Mono u] in
/-- A relative edge remains relative after a commuting square of ordinal maps. -/
theorem restrict_edge {l' k' : SimplexCategory}
    (u' : l' ⟶ k') (a : l' ⟶ l) (b : k' ⟶ k)
    (h : a ≫ u = u' ≫ b) {e : Δ k ⟶ row W ⦋1⦌}
    (hface : std.map u ≫ e = identityOnFace W z)
    (hend : e ≫ endpointArrow W = boundaryPair W f z) :
    std.map u' ≫ (std.map b ≫ e) = identityOnFace W z ∧
      (std.map b ≫ e) ≫ endpointArrow W =
        boundaryPair W (std.map b ≫ f) z := by
  constructor
  · calc
      std.map u' ≫ (std.map b ≫ e) = std.map (u' ≫ b) ≫ e := by
        rw [std.map_comp, Category.assoc]
      _ = std.map a ≫ (std.map u ≫ e) := by
        rw [← h, std.map_comp, Category.assoc]
      _ = identityOnFace W z := by
        rw [hface, identityOnFace_natural]
  · calc
      (std.map b ≫ e) ≫ endpointArrow W =
          std.map b ≫ (e ≫ endpointArrow W) := by rw [Category.assoc]
      _ = std.map b ≫ boundaryPair W f z := by rw [hend]
      _ = boundaryPair W (std.map b ≫ f) z :=
        boundaryPair_natural W z b f

omit [Mono u] in
/-- The reversed relative edge has the same strict restriction property. -/
theorem restrict_reverse_edge {l' k' : SimplexCategory}
    (u' : l' ⟶ k') (a : l' ⟶ l) (b : k' ⟶ k)
    (h : a ≫ u = u' ≫ b) {e : Δ k ⟶ row W ⦋1⦌}
    (hface : std.map u ≫ e = identityOnFace W z)
    (hend : e ≫ endpointArrow W = reverseBoundaryPair W f z) :
    std.map u' ≫ (std.map b ≫ e) = identityOnFace W z ∧
      (std.map b ≫ e) ≫ endpointArrow W =
        reverseBoundaryPair W (std.map b ≫ f) z := by
  constructor
  · calc
      std.map u' ≫ (std.map b ≫ e) = std.map (u' ≫ b) ≫ e := by
        rw [std.map_comp, Category.assoc]
      _ = std.map a ≫ (std.map u ≫ e) := by
        rw [← h, std.map_comp, Category.assoc]
      _ = identityOnFace W z := by
        rw [hface, identityOnFace_natural]
  · calc
      (std.map b ≫ e) ≫ endpointArrow W =
          std.map b ≫ (e ≫ endpointArrow W) := by rw [Category.assoc]
      _ = std.map b ≫ reverseBoundaryPair W f z := by rw [hend]
      _ = reverseBoundaryPair W (std.map b ≫ f) z :=
        reverseBoundaryPair_natural W z b f

end

end DaggerModels.PartII.JTJointEndpointRelativeLift
