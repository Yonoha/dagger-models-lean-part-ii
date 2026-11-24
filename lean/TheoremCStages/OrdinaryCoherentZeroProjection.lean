import OrdinaryCoherentZeroCoskeleton
import OrdinaryCoherentArrowNaturality
import OrdinarySegalRestrictionTargetNaturality

/-!
# Reflection of coherent arrows through the ordinary zero-row pullback

The checked walking mapping-space square is strictly Cartesian. A coherent
arrow in the target therefore lifts to the same edge in the relative
zero-row pullback. The original directed edge and all actual vertices are
retained; no Segal or completeness hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentZeroProjection

open OrdinaryCSSLocalization (Space)
open OrdinaryZeroCoskeleton
open OrdinarySegalWalkingEvaluation (edgeEvaluation simplexMappingIso)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex range_edgeEvaluation)
open OrdinaryCoherentZeroCoskeleton (walking_pullback restrict)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌
private abbrev one : SimplexCategoryᵒᵖ := op ⦋1⦌
private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev F := diagramMappingTarget (OrdinaryCSSLocalization.discrete.obj E)
private abbrev G := diagramMappingTarget
  (OrdinaryCSSLocalization.discrete.obj (Δ[1] : SSet.{0}))

/-- The actual projection from the source-zero pullback to its target. -/
private def projection {W Z : Space} (f : W ⟶ Z) : targetOverZero f ⟶ Z :=
  pullback.fst (vertices Z) (coskeleton.map (f.app zero))

/-- The original walking-edge square is Cartesian at every actual vertical
simplex, with the target projection unchanged. -/
theorem projection_reflects_coherent {W Z : Space} (f : W ⟶ Z)
    [IsFibrant Z] [IsFibrant (W.obj zero)]
    (q : SimplexCategoryᵒᵖ)
    (e : ((targetOverZero f).obj one).obj q) :
    e ∈ (coherentArrowSubcomplex (targetOverZero f)).obj q ↔
      ((projection f).app one).app q e ∈
        (coherentArrowSubcomplex Z).obj q := by
  letI : IsFibrant (targetOverZero f) := targetOverZero_fibrant f
  let p := projection f
  let sT := simplexMappingIso (targetOverZero f) 1
  let sZ := simplexMappingIso Z 1
  let bT := sT.inv.app q e
  have hbT : sT.hom.app q bT = e := by
    dsimp only [bT]
    exact congrFun (NatTrans.congr_app sT.inv_hom_id q) e
  have hnat :
      G.map p ≫ sZ.hom =
        sT.hom ≫ p.app one := by
    exact OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post p 1
  constructor
  · intro he
    rw [← range_edgeEvaluation (targetOverZero f)] at he
    obtain ⟨a, ha⟩ := he
    rw [← range_edgeEvaluation Z]
    refine ⟨(OrdinaryCoherentArrowNaturality.walkingMap p).app q a, ?_⟩
    have hn := congrFun
      (NatTrans.congr_app (OrdinaryCoherentArrowNaturality.edgeEvaluation_post p) q) a
    exact hn.trans (congrArg ((p.app one).app q) ha)
  · intro he
    rw [← range_edgeEvaluation Z] at he
    obtain ⟨aZ, haZ⟩ := he
    have hc : (restrict.app Z).app q aZ =
        (G.map p).app q bT := by
      have hi : Function.Injective (sZ.hom.app q) :=
        (isIso_iff_bijective (sZ.hom.app q)).mp inferInstance |>.1
      apply hi
      calc
        sZ.hom.app q ((restrict.app Z).app q aZ) =
            (edgeEvaluation Z).app q aZ := rfl
        _ = (p.app one).app q e := haZ
        _ = (p.app one).app q (sT.hom.app q bT) := by rw [hbT]
        _ = sZ.hom.app q ((G.map p).app q bT) := by
          exact (congrFun (NatTrans.congr_app hnat q) bT).symm
    let a : SSet.stdSimplex.obj q.unop ⟶
        F.obj Z := SSet.yonedaEquiv.symm aZ
    let b : SSet.stdSimplex.obj q.unop ⟶
        G.obj (targetOverZero f) :=
      SSet.yonedaEquiv.symm bT
    have hw : a ≫ restrict.app Z =
        b ≫ G.map p := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
      simpa only [a, b, Equiv.apply_symm_apply] using hc
    let h := walking_pullback f
    let l := h.lift a b hw
    have hl : l ≫ restrict.app (targetOverZero f) = b := h.lift_snd a b hw
    rw [← range_edgeEvaluation (targetOverZero f)]
    refine ⟨SSet.yonedaEquiv l, ?_⟩
    have hb : (restrict.app (targetOverZero f)).app q (SSet.yonedaEquiv l) = bT := by
      have h' := congrArg SSet.yonedaEquiv hl
      simpa only [SSet.yonedaEquiv_comp, b, Equiv.apply_symm_apply] using h'
    change sT.hom.app q
      ((restrict.app (targetOverZero f)).app q (SSet.yonedaEquiv l)) = e
    rw [hb, hbT]

#print axioms projection_reflects_coherent

end
end DaggerModels.PartII.OrdinaryCoherentZeroProjection
