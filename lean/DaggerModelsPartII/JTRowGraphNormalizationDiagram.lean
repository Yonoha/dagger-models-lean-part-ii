import DaggerModelsPartII.JTRowGraphFiber
import DaggerModelsPartII.JTOrdinaryGraphNormalizationSpace
import DaggerModelsPartII.JTFixedLiftSpacePrecomp
import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex
import NativeSimplicialReplacement
import NativeSimplicialOppositeKanWeak
import NativeNerveOppositeIso
import OriginalSimplicialTrivialFibrationTensor

/-!
# The exact contravariant normalization spaces over a fixed raw simplex
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphNormalizationDiagram

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTOrdinaryGraphNormalizationSpace
open JTMixedGraphEdgeFamilyReindex JTRowGraphFiber
open JTFixedLiftSpacePrecomp

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable {q : simplex ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

/-- The original coefficient simplex of a graph in the fixed raw fiber. -/
abbrev coefficient (G : Fiber q) : simplex G.obj.degree ⟶ row W ⦋d⦌ :=
  SSet.yonedaEquiv.symm G.obj.coefficient

/-- The coefficient and parameter realize to the fixed raw simplex. -/
theorem raw_eq (G : Fiber q) :
    rawGraph W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter = q := by
  unfold rawGraph
  rw [Equiv.apply_symm_apply]
  exact G.property

include hx in
/-- The left endpoint of each graph is the fixed raw vertex. -/
theorem leftEndpoint (G : Fiber q) :
    SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫
      rawGraph W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter) = rawVertex W x := by
  rw [raw_eq G]
  exact hx

include hy in
/-- The right endpoint of each graph is the fixed raw vertex. -/
theorem rightEndpoint (G : Fiber q) :
    SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫
      rawGraph W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter) = rawVertex W y := by
  rw [raw_eq G]
  exact hy

private abbrev leftSq (G : Fiber q) := leftSquare W ⦋d⦌ G.obj.degree
  (coefficient G) G.obj.parameter x (leftEndpoint hx G)

private abbrev rightSq (G : Fiber q) := rightSquare W ⦋d⦌ G.obj.degree
  (coefficient G) G.obj.parameter y (rightEndpoint hy G)

private abbrev spaceAt (G : Fiber q) := space W ⦋d⦌ G.obj.degree
  (coefficient G) G.obj.parameter x y (leftEndpoint hx G) (rightEndpoint hy G)

private theorem coefficient_map {G H : Fiber q} (u : G ⟶ H) :
    SSet.stdSimplex.map u.hom.operator ≫ coefficient H = coefficient G := by
  rw [← SSet.yonedaEquiv_symm_map]
  exact congrArg SSet.yonedaEquiv.symm u.hom.coefficient

private theorem vertex_map {G H : Fiber q} (u : G ⟶ H) (i : Fin (d + 1)) :
    vertex G.obj.degree (graphIndex ⦋d⦌ G.obj.degree G.obj.parameter i) ≫
      SSet.stdSimplex.map u.hom.operator =
      vertex H.obj.degree (graphIndex ⦋d⦌ H.obj.degree H.obj.parameter i) := by
  have h : graphIndex ⦋d⦌ H.obj.degree H.obj.parameter i =
      u.hom.operator.toOrderHom (graphIndex ⦋d⦌ G.obj.degree G.obj.parameter i) :=
    (congrArg (fun s ↦ graphIndex ⦋d⦌ H.obj.degree s i) u.hom.parameter).symm.trans
      (graphIndex_reindex u.hom.operator G.obj.parameter i)
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp, h]

private theorem terminal_map {G H : Fiber q} (u : G ⟶ H) :
    SSet.stdSimplex.map u.hom.operator ≫ term (simplex H.obj.degree) =
      term (simplex G.obj.degree) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem leftBase_map {G H : Fiber q} (u : G ⟶ H) :
    SSet.stdSimplex.map u.hom.operator ≫
        prod.lift (term (simplex H.obj.degree) ≫ vertexPoint W x)
          (coefficient H ≫ rowVertex W ⦋d⦌ 0) =
      prod.lift (term (simplex G.obj.degree) ≫ vertexPoint W x)
        (coefficient G ≫ rowVertex W ⦋d⦌ 0) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    rw [← Category.assoc, terminal_map u]
  · simp only [Category.assoc, prod.lift_snd]
    rw [← Category.assoc, coefficient_map u]

private theorem rightBase_map {G H : Fiber q} (u : G ⟶ H) :
    SSet.stdSimplex.map u.hom.operator ≫
        prod.lift (coefficient H ≫ rowVertex W ⦋d⦌ (Fin.last d))
          (term (simplex H.obj.degree) ≫ vertexPoint W y) =
      prod.lift (coefficient G ≫ rowVertex W ⦋d⦌ (Fin.last d))
        (term (simplex G.obj.degree) ≫ vertexPoint W y) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    rw [← Category.assoc, coefficient_map u]
  · simp only [Category.assoc, prod.lift_snd]
    rw [← Category.assoc, terminal_map u]

/-- The actual left endpoint normalization restriction of a graph arrow. -/
def leftMap {G H : Fiber q} (u : G ⟶ H) :
    (SSet.ihomToPullbackFiber (leftSq hx H) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (leftSq hx G) :=
  precomp (leftSq hx G) (leftSq hx H) (SSet.stdSimplex.map u.hom.operator)
    (vertex_map u 0) (leftBase_map u)

/-- The actual right endpoint normalization restriction of a graph arrow. -/
def rightMap {G H : Fiber q} (u : G ⟶ H) :
    (SSet.ihomToPullbackFiber (rightSq hy H) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (rightSq hy G) :=
  precomp (rightSq hy G) (rightSq hy H) (SSet.stdSimplex.map u.hom.operator)
    (vertex_map u (Fin.last d)) (rightBase_map u)

/-- All compatible left and right families restrict along every exact
coefficient operator, in every simplicial degree. -/
def diagram : (Fiber q)ᵒᵖ ⥤ SSet.{0} where
  obj G := spaceAt hx hy G.unop
  map u := prod.map (leftMap hx u.unop) (rightMap hy u.unop)
  map_id G := by
    change prod.map (leftMap hx (𝟙 G.unop)) (rightMap hy (𝟙 G.unop)) = _
    have hL : leftMap hx (𝟙 G.unop) = 𝟙 _ :=
      precomp_id_of_eq _ _ (SSet.stdSimplex.{0}.map_id G.unop.obj.degree) _ _
    have hR : rightMap hy (𝟙 G.unop) = 𝟙 _ :=
      precomp_id_of_eq _ _ (SSet.stdSimplex.{0}.map_id G.unop.obj.degree) _ _
    rw [hL, hR, prod.map_id_id]
    rfl
  map_comp u v := by
    change prod.map (leftMap hx (v.unop ≫ u.unop)) (rightMap hy (v.unop ≫ u.unop)) =
      prod.map (leftMap hx u.unop) (rightMap hy u.unop) ≫
        prod.map (leftMap hx v.unop) (rightMap hy v.unop)
    have fac : SSet.stdSimplex.{0}.map v.unop.hom.operator ≫
          SSet.stdSimplex.map u.unop.hom.operator =
        SSet.stdSimplex.map (v.unop ≫ u.unop).hom.operator :=
      (SSet.stdSimplex.{0}.map_comp v.unop.hom.operator u.unop.hom.operator).symm
    have hL : leftMap hx u.unop ≫ leftMap hx v.unop = leftMap hx (v.unop ≫ u.unop) :=
      precomp_comp_of_fac _ _ _ _ _ _ fac _ _ _ _ _ _
    have hR : rightMap hy u.unop ≫ rightMap hy v.unop = rightMap hy (v.unop ≫ u.unop) :=
      precomp_comp_of_fac _ _ _ _ _ _ fac _ _ _ _ _ _
    rw [← hL, ← hR]
    apply prod.hom_ext <;> simp


/-- The actual ordered edge families are the zero simplices in each fiber. -/
def familiesAtZero (G : Fiber q) :
    ((diagram hx hy).obj (op G)).obj (op ⦋0⦌) ≃
      EdgeFamilies W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter x y :=
  zeroEquiv W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter x y
    (leftEndpoint hx G) (rightEndpoint hy G)


/-- A restricted normalization vertex has exactly the precomposed left family. -/
theorem familiesAtZero_left_reindex {G H : Fiber q} (u : G ⟶ H)
    (v : ((diagram hx hy).obj (op H)).obj (op ⦋0⦌)) :
    (familiesAtZero hx hy G (((diagram hx hy).map u.op).app _ v)).left =
      SSet.stdSimplex.map u.hom.operator ≫ (familiesAtZero hx hy H v).left := by
  have hG := zeroEquiv_left W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter x y
    (leftEndpoint hx G) (rightEndpoint hy G) (((diagram hx hy).map u.op).app _ v)
  have hH := zeroEquiv_left W ⦋d⦌ H.obj.degree (coefficient H) H.obj.parameter x y
    (leftEndpoint hx H) (rightEndpoint hy H) v
  change (familiesAtZero hx hy G (((diagram hx hy).map u.op).app _ v)).left = _ at hG
  change (familiesAtZero hx hy H v).left = _ at hH
  rw [hG, hH]
  have h : (diagram hx hy).map u.op ≫ (prod.fst : spaceAt hx hy G ⟶ _) =
      (prod.fst : spaceAt hx hy H ⟶ _) ≫ leftMap hx u :=
    prod.map_fst _ _
  have hv := congrFun (NatTrans.congr_app h (op ⦋0⦌)) v
  change ((prod.fst : spaceAt hx hy G ⟶ _).app _)
      (((diagram hx hy).map u.op).app _ v) =
    (leftMap hx u).app _ ((prod.fst : spaceAt hx hy H ⟶ _).app _ v) at hv
  rw [hv]
  exact precomp_zero _ _ _ _ _ _

/-- A restricted normalization vertex has exactly the precomposed right family. -/
theorem familiesAtZero_right_reindex {G H : Fiber q} (u : G ⟶ H)
    (v : ((diagram hx hy).obj (op H)).obj (op ⦋0⦌)) :
    (familiesAtZero hx hy G (((diagram hx hy).map u.op).app _ v)).right =
      SSet.stdSimplex.map u.hom.operator ≫ (familiesAtZero hx hy H v).right := by
  have hG := zeroEquiv_right W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter x y
    (leftEndpoint hx G) (rightEndpoint hy G) (((diagram hx hy).map u.op).app _ v)
  have hH := zeroEquiv_right W ⦋d⦌ H.obj.degree (coefficient H) H.obj.parameter x y
    (leftEndpoint hx H) (rightEndpoint hy H) v
  change (familiesAtZero hx hy G (((diagram hx hy).map u.op).app _ v)).right = _ at hG
  change (familiesAtZero hx hy H v).right = _ at hH
  rw [hG, hH]
  have h : (diagram hx hy).map u.op ≫ (prod.snd : spaceAt hx hy G ⟶ _) =
      (prod.snd : spaceAt hx hy H ⟶ _) ≫ rightMap hy u :=
    prod.map_snd _ _
  have hv := congrFun (NatTrans.congr_app h (op ⦋0⦌)) v
  change ((prod.snd : spaceAt hx hy G ⟶ _).app _)
      (((diagram hx hy).map u.op).app _ v) =
    (rightMap hy u).app _ ((prod.snd : spaceAt hx hy H ⟶ _).app _ v) at hv
  rw [hv]
  exact precomp_zero _ _ _ _ _ _

set_option maxHeartbeats 700000 in
/-- The complete normalized ordered label restricts along every exact
coefficient operator. -/
theorem normalizedLabel_reindex {G H : Fiber q} (u : G ⟶ H)
    (v : ((diagram hx hy).obj (op H)).obj (op ⦋0⦌)) :
    JTMixedGraphOrderedLabel.orderedPoint
        (familiesAtZero hx hy G (((diagram hx hy).map u.op).app _ v)) =
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (TripleBeadEndpointLabel.code d))).map u.hom.operator.op
          (JTMixedGraphOrderedLabel.orderedPoint (familiesAtZero hx hy H v)) := by
  apply orderedPoint_reindex_of_rows
  · simp only [JTMixedGraphOrderedLabel.families, ← Category.assoc]
    rw [familiesAtZero_left_reindex]
  · simp only [JTMixedGraphOrderedLabel.families, ← Category.assoc]
    rw [coefficient_map u]
  · simp only [JTMixedGraphOrderedLabel.families, ← Category.assoc]
    rw [familiesAtZero_right_reindex]

/-- Every fixed graph has a weakly contractible paired normalization space. -/
theorem point_at_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G : Fiber q) : WeakEquivalence (term (spaceAt hx hy G)) := by
  let A := leftSpace W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter x (leftEndpoint hx G)
  let B := rightSpace W ⦋d⦌ G.obj.degree (coefficient G) G.obj.parameter y (rightEndpoint hy G)
  haveI : A.KanComplex := leftSpace_kan W ⦋d⦌ G.obj.degree (coefficient G)
    G.obj.parameter x (leftEndpoint hx G) hW
  haveI : B.KanComplex := rightSpace_kan W ⦋d⦌ G.obj.degree (coefficient G)
    G.obj.parameter y (rightEndpoint hy G) hW
  have hA := leftSpace_toPoint_weak W ⦋d⦌ G.obj.degree (coefficient G)
    G.obj.parameter x (leftEndpoint hx G) hW
  have hB := rightSpace_toPoint_weak W ⦋d⦌ G.obj.degree (coefficient G)
    G.obj.parameter y (rightEndpoint hy G) hW
  haveI : Fibration (term A) :=
    (isFibrant_iff_of_isTerminal (term A) SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  haveI : Fibration (term B) :=
    (isFibrant_iff_of_isTerminal (term B) SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  have hP := DaggerOriginalSimplicialTrivialFibrationTensor.prodMap_trivialFibration (term A) (term B)
    ((mem_trivialFibrations_iff _).2 ⟨inferInstance, hA⟩)
    ((mem_trivialFibrations_iff _).2 ⟨inferInstance, hB⟩)
  haveI : WeakEquivalence (prod.map (term A) (term B)) :=
    ((mem_trivialFibrations_iff _).1 hP).2
  let Z : SSet.{0} := Δ[0]
  haveI : IsIso (term (Z ⨯ Z)) := by
    have ht : IsTerminal (Z ⨯ Z) := IsTerminal.ofUniqueHom
      (fun X ↦ prod.lift (term X) (term X)) (by
        intro X f
        apply prod.hom_ext <;> exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    let e := ht.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
    have h : term (Z ⨯ Z) = e.hom := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
    infer_instance
  have he : prod.map (term A) (term B) ≫ term (Z ⨯ Z) = term (spaceAt hx hy G) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← he]
  infer_instance

open DaggerNativeSimplicialReplacement

/-- The entire bar of endpoint normalizations over the fixed actual simplex. -/
def bar : SSet.{0} := DaggerBisimplicialDiagonal.diag (replacement (diagram hx hy))

/-- The bar projects weakly to the opposite of the actual coefficient category. -/
theorem barProjection_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (diagonalProjection (diagram hx hy)) := by
  apply (weakEquivalence_iff_GW _).mpr
  apply diagonalProjection_GW
  intro G
  apply (weakEquivalence_iff_GW _).mp
  have h := point_at_weak hx hy hW G.unop
  haveI : WeakEquivalence (term (spaceAt hx hy G.unop)) := h
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  have he : term (spaceAt hx hy G.unop) ≫ e.hom = pointMap ((diagram hx hy).obj G) :=
    pointIsTerminal.hom_ext _ _
  rw [← he]
  infer_instance

/-- The entire bar of exact normalization choices over the fixed raw
simplex is weakly contractible. -/
theorem bar_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (bar hx hy)) := by
  haveI : WeakEquivalence (pointMap (nerve (Fiber q))) :=
    (weakEquivalence_iff_GW _).mpr (JTRowGraphFiber.point_GW q)
  haveI := DaggerNativeSimplicialOppositeKanWeak.op_weak (pointMap (nerve (Fiber q)))
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso (Fiber q)
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let ht := IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal
  let e' := ht.uniqueUpToIso pointIsTerminal
  have he : e.inv ≫ SSet.opFunctor.map (pointMap (nerve (Fiber q))) ≫ e'.hom =
      pointMap (nerve (Fiber q)ᵒᵖ) := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (pointMap (nerve (Fiber q)ᵒᵖ)) := by
    rw [← he]
    infer_instance
  haveI := barProjection_weak hx hy hW
  have hbar : diagonalProjection (diagram hx hy) ≫ pointMap (nerve (Fiber q)ᵒᵖ) =
      pointMap (bar hx hy) := pointIsTerminal.hom_ext _ _
  rw [← hbar]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTRowGraphNormalizationDiagram
