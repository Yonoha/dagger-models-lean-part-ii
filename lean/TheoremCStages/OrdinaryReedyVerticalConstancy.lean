import DaggerModelsPartII.DiagramHomPrecompLifting
import NativeFibrationWeakFromVertexFibres
import NativeJoyalFirstFactorization
import NativeJoyalMappingWeakProperties

/-!
# Vertical categorical constancy of Reedy–Kan fibrant simplicial spaces

This is the actual bisimplicial-set mechanism of Joyal–Tierney,
Proposition 2.8. The outer simplicial diagram is Reedy fibrant with native
Kan coefficients. Precomposition by the zeroth vertex of a vertical simplex
is a Kan trivial fibration of horizontal Hom simplicial sets. Since its
opposite precomposition by the collapse has a section, the canonical map
from the zero horizontal row to the chosen row is ordinary Joyal weak.
The result needs no Segal or completeness locality.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryReedyVerticalConstancy

noncomputable section

private abbrev Space := SimplexCategoryᵒᵖ ⥤ SSet.{0}
private abbrev P := DaggerNativeJoyalMappingTest.weakCategoricalEquivalences

private local instance : ModelCategory Space :=
  simplicialReedyModelCategory SSet.{0}

/-- Yoneda identifies the original vertical-simplex Hom diagram with the
literal horizontal simplicial set at that vertical degree. -/
def rowIso (W : Space) (n : ℕ) :
    diagramHomSSet (Δ[n] : SSet.{0}) W ≅ W.flip.obj (op ⦋n⦌) :=
  NatIso.ofComponents (fun _ ↦ SSet.yonedaEquiv.toIso) (by
    intro q r f
    funext a
    exact SSet.yonedaEquiv_comp a (W.map f))

/-- The row identification respects the literal vertical simplex operator. -/
theorem rowIso_natural {n m : ℕ} (W : Space) (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    diagramHomPrecomp (SSet.stdSimplex.map θ) W ≫ (rowIso W n).hom =
      (rowIso W m).hom ≫ W.flip.map θ.op := by
  apply NatTrans.ext
  funext q a
  exact SSet.yonedaEquiv_map_comp θ a

private def vertex (n : ℕ) : (Δ[0] : SSet.{0}) ⟶ Δ[n] :=
  SSet.const (DaggerNativeStandardSimplexContraction.firstVertex n)

private def collapseSimplex (n : ℕ) : (Δ[n] : SSet.{0}) ⟶ Δ[0] :=
  SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from ⦋n⦌)

private theorem vertex_trivialCofibration (n : ℕ) :
    trivialCofibrations SSet.{0} (vertex n) := by
  have hm : Mono (vertex n) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  have hc : Cofibration (vertex n) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr hm
  have hw : WeakEquivalence (vertex n) :=
    DaggerNativeFibrationWeakFromVertexFibres.first_vertex_weak n
  exact ⟨(cofibration_iff _).mp hc, (weakEquivalence_iff _).mp hw⟩

/-- The native Kan boundary-lifting theorem applies to the actual vertex
restriction for every Reedy–Kan fibrant simplicial space. -/
theorem vertexRestriction_trivialFibration (W : Space) [IsFibrant W]
    (n : ℕ) :
    trivialFibrations SSet.{0} (diagramHomPrecomp (vertex n) W) :=
  diagramHomPrecomp_kanTrivialFibration W (vertex n)
    (vertex_trivialCofibration n)

private theorem vertex_collapse (n : ℕ) :
    vertex n ≫ collapseSimplex n = 𝟙 (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem precomp_collapse_vertex (W : Space) (n : ℕ) :
    diagramHomPrecomp (collapseSimplex n) W ≫
      diagramHomPrecomp (vertex n) W = 𝟙 _ := by
  apply NatTrans.ext
  funext q a
  change vertex n ≫ (collapseSimplex n ≫ a) = a
  rw [← Category.assoc, vertex_collapse, Category.id_comp]

/-- The literal collapse from the zero horizontal row to degree `n` is
ordinary Joyal weak for every Reedy–Kan fibrant bisimplicial set. -/
theorem collapse_weak (W : Space) [IsFibrant W] (n : ℕ) :
    P (W.flip.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op) := by
  let v := vertex n
  let p := collapseSimplex n
  have hv : P (diagramHomPrecomp v W) :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial
      (diagramHomPrecomp v W) (vertexRestriction_trivialFibration W n)).2
  have hp : P (diagramHomPrecomp p W) := by
    apply P.of_postcomp (diagramHomPrecomp p W) (diagramHomPrecomp v W) hv
    rw [show diagramHomPrecomp p W ≫ diagramHomPrecomp v W = 𝟙 _ from
      precomp_collapse_vertex W n]
    exact P.id_mem _
  let e : Arrow.mk (diagramHomPrecomp p W) ≅
      Arrow.mk (W.flip.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op) :=
    Arrow.isoMk (rowIso W 0) (rowIso W n)
      (rowIso_natural W (SimplexCategory.isTerminalZero.from ⦋n⦌)).symm
  exact P.of_retract (Retract.ofIso e.symm) hp

/-- Every original vertical operator acts by a Joyal weak equivalence on
the full horizontal rows of a Reedy–Kan fibrant simplicial space. -/
theorem verticalOperator_weak (W : Space) [IsFibrant W]
    {k l : SimplexCategory} (θ : k ⟶ l) :
    P (W.flip.map θ.op) := by
  let ck : k ⟶ ⦋0⦌ := SimplexCategory.isTerminalZero.from k
  let cl : l ⟶ ⦋0⦌ := SimplexCategory.isTerminalZero.from l
  have hcomp : W.flip.map cl.op ≫ W.flip.map θ.op = W.flip.map ck.op := by
    rw [← W.flip.map_comp]
    congr 1
  have hk : P (W.flip.map ck.op) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = ⦋n⦌ :=
      ⟨k.len, SimplexCategory.ext _ _ rfl⟩
    subst k
    exact collapse_weak W n
  have hl : P (W.flip.map cl.op) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, l = ⦋n⦌ :=
      ⟨l.len, SimplexCategory.ext _ _ rfl⟩
    subst l
    exact collapse_weak W n
  apply P.of_precomp (W.flip.map cl.op) (W.flip.map θ.op) hl
  rw [hcomp]
  exact hk

#print axioms rowIso
#print axioms rowIso_natural
#print axioms vertexRestriction_trivialFibration
#print axioms collapse_weak
#print axioms verticalOperator_weak

end

end DaggerModels.PartII.OrdinaryReedyVerticalConstancy
