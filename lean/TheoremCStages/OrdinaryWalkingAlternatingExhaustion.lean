import OrdinaryWalkingAlternatingFiltration
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# The base edge and exhaustion of the literal alternating filtration

The first stage is the image of the original free-groupoid simplex unit.
Every binary word is a face of a sufficiently long alternating word: insert
one or two positions between successive letters, encoded uniformly by
`j ↦ 2j + bit(j)`. This proves the union is the same whole walking parameter.
No horn attachment or homotopical property is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingAlternatingExhaustion

open OrdinaryWalkingAlternatingFiltration

noncomputable section

private abbrev Walking := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev BinaryNerve :=
  DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj (Fin 2)

/-- The original free-groupoid unit has exactly the chosen degree-one
alternating word under the checked codiscrete comparison. -/
private theorem simplexUnit_binaryWord :
    walkingCodiscreteIso.hom.app (op ⦋1⦌)
        (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) =
      binaryWord 1 := by
  apply nerve.ext_of_isThin
  funext j
  apply Codiscrete.ext
  fin_cases j <;> rfl

/-- The first stage is the image of the literal original simplex unit,
not an isomorphic replacement of its source arrow. -/
theorem stage_one_eq_unit_image :
    stage 1 = SSet.Subcomplex.range (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) := by
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  change SSet.Subcomplex.ofSimplex (alternatingSimplex 1) =
    SSet.Subcomplex.ofSimplex
      (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))
  congr 1
  have h := congrFun (NatTrans.congr_app walkingCodiscreteIso.hom_inv_id
    (op ⦋1⦌))
    (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))
  change walkingCodiscreteIso.inv.app (op ⦋1⦌)
      (walkingCodiscreteIso.hom.app (op ⦋1⦌)
        (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))) =
      SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) at h
  rw [simplexUnit_binaryWord] at h
  exact h

/-- A simplex operator embeds any binary word as a face of the chosen
alternating word of dimension `2n+1`. -/
private def wordEmbedding (n : ℕ) (x : BinaryNerve.obj (op ⦋n⦌)) :
    ⦋n⦌ ⟶ ⦋2 * n + 1⦌ :=
  SimplexCategory.mkHom ⟨fun j ↦ ⟨2 * j.val + (x.obj j).as.val, by
      have hj := j.isLt
      have hb := (x.obj j).as.isLt
      omega⟩,
    by
      intro i j hij
      apply Fin.le_iff_val_le_val.mpr
      by_cases h : i = j
      · subst j
        exact le_refl _
      · have hle : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
        have hne : i.val ≠ j.val := by
          intro heq
          exact h (Fin.ext heq)
        have hbi := (x.obj i).as.isLt
        have hbj := (x.obj j).as.isLt
        dsimp
        omega⟩

/-- The face selected by `wordEmbedding` recovers every original binary
word, including words with repeated adjacent vertices. -/
private theorem binaryWord_wordEmbedding (n : ℕ)
    (x : BinaryNerve.obj (op ⦋n⦌)) :
    BinaryNerve.map (wordEmbedding n x).op (binaryWord (2 * n + 1)) = x := by
  apply nerve.ext_of_isThin
  funext j
  apply Codiscrete.ext
  change ((binaryWord (2 * n + 1)).obj ((wordEmbedding n x).toOrderHom j)).as =
    (x.obj j).as
  change (⟨(2 * j.val + (x.obj j).as.val) % 2,
      Nat.mod_lt _ (by decide)⟩ : Fin 2) = (x.obj j).as
  apply Fin.ext
  have hb := (x.obj j).as.isLt
  change (2 * j.val + (x.obj j).as.val) % 2 = (x.obj j).as.val
  omega

/-- The sequential union of the actual generated subcomplexes is the
whole original walking parameter. -/
theorem iSup_stage_eq_top : (⨆ k : ℕ, stage k) = ⊤ := by
  apply le_antisymm le_top
  intro q y _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = op ⦋n⦌ :=
    ⟨q.unop.len, by simp only [SimplexCategory.mk_len, op_unop]⟩
  let x : BinaryNerve.obj (op ⦋n⦌) := walkingCodiscreteIso.hom.app (op ⦋n⦌) y
  let α := wordEmbedding n x
  have hx := binaryWord_wordEmbedding n x
  have hn := congrFun (walkingCodiscreteIso.inv.naturality α.op)
    (binaryWord (2 * n + 1))
  have hid : walkingCodiscreteIso.inv.app (op ⦋n⦌) x = y := by
    have h := congrFun (NatTrans.congr_app walkingCodiscreteIso.hom_inv_id
      (op ⦋n⦌)) y
    change walkingCodiscreteIso.inv.app (op ⦋n⦌)
      (walkingCodiscreteIso.hom.app (op ⦋n⦌) y) = y at h
    exact h
  have hface : Walking.map α.op (alternatingSimplex (2 * n + 1)) = y := by
    change Walking.map α.op (alternatingSimplex (2 * n + 1)) =
      walkingCodiscreteIso.inv.app (op ⦋n⦌)
        (BinaryNerve.map α.op (binaryWord (2 * n + 1))) at hn
    rw [hx] at hn
    exact hn.trans hid
  change y ∈ (⨆ k : ℕ, stage k).obj (op ⦋n⦌)
  simp only [SSet.Subcomplex.iSup_obj, Set.mem_iUnion]
  refine ⟨2 * n + 1, ?_⟩
  rw [stage, SSet.Subcomplex.mem_ofSimplex_obj_iff]
  exact ⟨α, hface⟩

#print axioms stage_one_eq_unit_image
#print axioms iSup_stage_eq_top

end

end DaggerModels.PartII.OrdinaryWalkingAlternatingExhaustion
