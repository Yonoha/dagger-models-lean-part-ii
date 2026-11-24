import OrdinaryCoherentArrowVertexRecognition
import OrdinaryCoherentArrowEvaluationReflection
import OrdinarySegalCotensorParameterNaturality
import OrdinarySegalCotensorFibrant
import OrdinarySegalCotensorPointEvaluation

/-!
# Reflection of coherent arrows under an actual cotensor vertex

Every vertical simplex of the original coherent-arrow image is recognized by
an extension of its horizontal edge to the unchanged walking groupoid. The
actual horizontal cotensor row is compared through its checked row isomorphism.
The original evaluation map is calibrated by parameter naturality and the
checked point-parameter isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
  MonoidalCategory MonoidalClosed
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentCotensorEvaluationReflection

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (pointIso)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit : (Δ[1] : SSet.{0}) ⟶ E :=
  JTCylinderCEComparison.simplexUnit.app ⦋1⦌
private abbrev flip :=
  flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)

/-- The checked range comparison recognizes every vertical simplex,
with its original horizontal edge and the same walking extension. -/
theorem mem_coherent_iff_extension_at (V : Space) [IsFibrant V]
    (q : SimplexCategoryᵒᵖ) (e : (V.obj (op ⦋1⦌)).obj q) :
    e ∈ (coherentArrowSubcomplex V).obj q ↔
      ∃ H : E ⟶ V.flip.obj q,
        unit ≫ H = (SSet.yonedaEquiv (X := V.flip.obj q) (n := ⦋1⦌)).symm e := by
  rw [← OrdinarySegalCoherentArrowImage.range_edgeEvaluation V]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(OrdinaryDiscreteMapping.levelEquiv E V q.unop) t, ?_⟩
    apply SSet.yonedaEquiv.injective
    rw [← OrdinaryCoherentArrowVertexRecognition.edgeEvaluation_level V q t,
      ht, Equiv.apply_symm_apply]
  · rintro ⟨H, hH⟩
    refine ⟨(OrdinaryDiscreteMapping.levelEquiv E V q.unop).symm H, ?_⟩
    rw [OrdinaryCoherentArrowVertexRecognition.edgeEvaluation_level,
      Equiv.apply_symm_apply, hH, Equiv.apply_symm_apply]

private theorem extension_iff_iso {X Y : SSet.{0}} (A : X ≅ Y)
    (u : (Δ[1] : SSet.{0}) ⟶ X) :
    (∃ H : E ⟶ X, unit ≫ H = u) ↔
      (∃ H : E ⟶ Y, unit ≫ H = u ≫ A.hom) := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨H ≫ A.hom, by rw [← Category.assoc, hH]⟩
  · rintro ⟨H, hH⟩
    refine ⟨H ≫ A.inv, ?_⟩
    rw [← Category.assoc, hH, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- The point row of the checked Fubini isomorphism lands in the original
horizontal row through the original point-parameter isomorphism. -/
def pointRowIso (W : Space) (q : SimplexCategoryᵒᵖ) :
    (ihom (Δ[0] : SSet.{0})).obj (W.flip.obj q) ≅ W.flip.obj q :=
  (OrdinarySegalCotensorMappingIso.rowIso (Δ[0] : SSet.{0}) W q).symm ≪≫
    (flip.mapIso (pointIso W)).app q

/-- The actual evaluation map, after rowwise Fubini, is exactly restriction
along the original parameter vertex and then the point-row isomorphism. -/
theorem evaluation_row_square (W : Space) (k : SimplexCategory)
    (j : Fin (k.len + 1)) (q : SimplexCategoryᵒᵖ) :
    (OrdinarySegalCotensorMappingIso.rowIso
        (GroupoidSimplex.parameter.obj k) W q).hom ≫
      (MonoidalClosed.pre (JTParameterContraction.parameterVertex k j)).app
        (W.flip.obj q) ≫ (pointRowIso W q).hom =
      (flip.map (OrdinarySegalCotensorPointEvaluation.evaluation
        (GroupoidSimplex.parameter.obj k) W
          (JTParameterContraction.parameterVertex k j))).app q := by
  let K := GroupoidSimplex.parameter.obj k
  let v := JTParameterContraction.parameterVertex k j
  have h := OrdinarySegalCotensorParameterNaturality.rowIso_natural_parameter
    v W q
  change (OrdinarySegalCotensorMappingIso.rowIso K W q).hom ≫
      (MonoidalClosed.pre v).app (W.flip.obj q) ≫
        ((OrdinarySegalCotensorMappingIso.rowIso (Δ[0] : SSet.{0}) W q).inv ≫
          (flip.map (pointIso W).hom).app q) = _
  rw [← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id_assoc]
  change (flip.map (pre v W)).app q ≫ (flip.map (pointIso W).hom).app q = _
  rw [← NatTrans.comp_app, ← flip.map_comp]
  rfl

/-- Evaluating at any original groupoid-simplex vertex reflects the actual
coherent-arrow subcomplex in every vertical simplicial degree. -/
theorem evaluation_reflects_coherent (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (k : SimplexCategory) (j : Fin (k.len + 1))
    (q : SimplexCategoryᵒᵖ)
    (e : ((cotensor (GroupoidSimplex.parameter.obj k) W).obj (op ⦋1⦌)).obj q) :
    e ∈ (coherentArrowSubcomplex
        (cotensor (GroupoidSimplex.parameter.obj k) W)).obj q ↔
      (((OrdinarySegalCotensorPointEvaluation.evaluation
        (GroupoidSimplex.parameter.obj k) W
          (JTParameterContraction.parameterVertex k j)).app (op ⦋1⦌)).app q e) ∈
        (coherentArrowSubcomplex W).obj q := by
  let K := GroupoidSimplex.parameter.obj k
  let v := JTParameterContraction.parameterVertex k j
  let V := cotensor K W
  let X := W.flip.obj q
  let A := OrdinarySegalCotensorMappingIso.rowIso K W q
  let B := pointRowIso W q
  let p := (MonoidalClosed.pre v).app X
  let u := (SSet.yonedaEquiv (X := V.flip.obj q) (n := ⦋1⦌)).symm e
  haveI : IsFibrant V :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant K W inferInstance
  obtain ⟨m, hq⟩ : ∃ m : ℕ, op ⦋m⦌ = q :=
    ⟨q.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  haveI : SSet.Quasicategory X := by
    subst q
    exact OrdinaryCoherentArrowVertexRecognition.horizontalRow_quasicategory
      W hSegal m
  haveI : Mono v := JTParameterVertexKan.vertex_mono k j
  have hv : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences v :=
    OrdinaryJTRightNerveCompleteness.parameterVertex_categorical_weak k j
  have hp : trivialFibrations SSet.{0} p :=
    DaggerNativeWeakMonoWholeRestriction.restriction_Kan_trivial v hv X
  let y := ((OrdinarySegalCotensorPointEvaluation.evaluation K W v).app
    (op ⦋1⦌)).app q e
  have hy : u ≫ (flip.map
      (OrdinarySegalCotensorPointEvaluation.evaluation K W v)).app q =
      (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm y := by
    exact SSet.yonedaEquiv_symm_comp _ _
  rw [mem_coherent_iff_extension_at V q e,
    mem_coherent_iff_extension_at W q y]
  change (∃ H : E ⟶ V.flip.obj q, unit ≫ H = u) ↔
    (∃ H : E ⟶ X, unit ≫ H =
      (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm y)
  rw [← hy]
  have hs : u ≫ A.hom ≫ p ≫ B.hom =
      u ≫ (flip.map
        (OrdinarySegalCotensorPointEvaluation.evaluation K W v)).app q := by
    exact congrArg (fun f ↦ u ≫ f) (evaluation_row_square W k j q)
  rw [← hs]
  exact (extension_iff_iso A u).trans
    ((OrdinaryCoherentArrowEvaluationReflection.walking_extension_iff
      p hp (u ≫ A.hom)).trans
        (extension_iff_iso B (u ≫ A.hom ≫ p)))

#print axioms mem_coherent_iff_extension_at
#print axioms evaluation_row_square
#print axioms evaluation_reflects_coherent

end
end DaggerModels.PartII.OrdinaryCoherentCotensorEvaluationReflection
