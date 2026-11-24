import DaggerModelsPartII.DiagramRestrictionLimits

/-!
# Matching objects as restrictions to simplex boundaries

The proper-face matching object is the restriction of the same diagram to the
actual boundary simplicial set. The comparison map is calibrated against the
actual boundary inclusion, with no fibrancy hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII.MatchingRestrictionCalibration

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, v} C]

private abbrev boundaryRestriction (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) : C :=
  diagramRestriction (SSet.boundary.{v} n).toSSet W

private abbrev matchingObject (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) : C :=
  (matchingFunctor n).obj W

private def boundaryMatchingHomEquiv (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) (A : C) :
    (A ⟶ boundaryRestriction W n) ≃ (A ⟶ matchingObject W n) :=
  (diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A W).symm.trans
    (boundaryDiagramHomEquiv n A W)

private theorem boundaryMatchingHomEquiv_precomp (W : SimplexCategoryᵒᵖ ⥤ C)
    (n : ℕ) {A B : C} (i : A ⟶ B) (q : B ⟶ boundaryRestriction W n) :
    boundaryMatchingHomEquiv W n A (i ≫ q) =
      i ≫ boundaryMatchingHomEquiv W n B q := by
  change boundaryDiagramHomEquiv n A W
      ((diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A W).symm (i ≫ q)) =
    i ≫ boundaryDiagramHomEquiv n B W
      ((diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet B W).symm q)
  rw [← boundaryDiagramHomEquiv_precomp]
  congr 1
  apply (diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A W).injective
  rw [Equiv.apply_symm_apply, diagramRestrictionHomEquiv_coeff,
    Equiv.apply_symm_apply]

/-- The matching object is the restriction of the original diagram to the
actual boundary simplicial set. -/
def matchingRestrictionIso (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) :
    matchingObject W n ≅ boundaryRestriction W n where
  hom := (boundaryMatchingHomEquiv W n (matchingObject W n)).symm (𝟙 _)
  inv := boundaryMatchingHomEquiv W n (boundaryRestriction W n) (𝟙 _)
  hom_inv_id := by
    have h := boundaryMatchingHomEquiv_precomp W n
      ((boundaryMatchingHomEquiv W n (matchingObject W n)).symm (𝟙 _))
      (𝟙 (boundaryRestriction W n))
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm
  inv_hom_id := by
    apply (boundaryMatchingHomEquiv W n (boundaryRestriction W n)).injective
    rw [boundaryMatchingHomEquiv_precomp, Equiv.apply_symm_apply,
      Category.comp_id]

private theorem boundaryMatchingHomEquiv_hom (W : SimplexCategoryᵒᵖ ⥤ C)
    (n : ℕ) {A : C} (q : A ⟶ matchingObject W n) :
    boundaryMatchingHomEquiv W n A (q ≫ (matchingRestrictionIso W n).hom) = q := by
  rw [boundaryMatchingHomEquiv_precomp]
  change q ≫ boundaryMatchingHomEquiv W n (matchingObject W n)
      ((boundaryMatchingHomEquiv W n (matchingObject W n)).symm (𝟙 _)) = q
  rw [Equiv.apply_symm_apply, Category.comp_id]

private theorem boundaryMatchingHomEquiv_post {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) (n : ℕ) {A : C} (q : A ⟶ boundaryRestriction W n) :
    boundaryMatchingHomEquiv V n A
        (q ≫ diagramRestrictionPost (SSet.boundary.{v} n).toSSet f) =
      boundaryMatchingHomEquiv W n A q ≫ (matchingFunctor n).map f := by
  change boundaryDiagramHomEquiv n A V
      ((diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A V).symm
        (q ≫ diagramRestrictionPost (SSet.boundary.{v} n).toSSet f)) =
    boundaryDiagramHomEquiv n A W
        ((diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A W).symm q) ≫
      (matchingFunctor n).map f
  rw [← boundaryDiagramHomEquiv_postcomp]
  congr 1
  apply (diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet A V).injective
  rw [Equiv.apply_symm_apply, diagramRestrictionHomEquiv_post,
    Equiv.apply_symm_apply]

/-- The boundary restriction isomorphism commutes with maps of the original
simplicial diagrams. -/
theorem matchingRestrictionIso_natural {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) (n : ℕ) :
    (matchingFunctor n).map f ≫ (matchingRestrictionIso V n).hom =
      (matchingRestrictionIso W n).hom ≫
        diagramRestrictionPost (SSet.boundary.{v} n).toSSet f := by
  apply (boundaryMatchingHomEquiv V n (matchingObject W n)).injective
  rw [boundaryMatchingHomEquiv_hom, boundaryMatchingHomEquiv_post]
  change (matchingFunctor n).map f =
    boundaryMatchingHomEquiv W n (matchingObject W n)
      ((boundaryMatchingHomEquiv W n (matchingObject W n)).symm (𝟙 _)) ≫
        (matchingFunctor n).map f
  rw [Equiv.apply_symm_apply, Category.id_comp]

omit [HasLimitsOfSize.{0, 0} C] in
private theorem simplex_hom_equiv_identity (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) :
    diagramRestrictionHomEquiv (Δ[n] : SSet.{v}) (W.obj (op ⦋n⦌)) W
      ((SSet.yonedaEquiv (X := diagramHomSSet (W.obj (op ⦋n⦌)) W)
        (n := ⦋n⦌)).symm (𝟙 (W.obj (op ⦋n⦌)))) =
        (diagramRestrictionSimplexIso W n).inv := by
  let q := (SSet.yonedaEquiv (X := diagramHomSSet (W.obj (op ⦋n⦌)) W)
    (n := ⦋n⦌)).symm (𝟙 (W.obj (op ⦋n⦌)))
  have h : diagramRestrictionHomEquiv (Δ[n] : SSet.{v})
      (W.obj (op ⦋n⦌)) W q ≫ (diagramRestrictionSimplexIso W n).hom = 𝟙 _ := by
    rw [diagramRestrictionSimplexIso_hom, diagramRestrictionHomEquiv_π]
    change q.app (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 _)) = 𝟙 _
    simp only [q, SSet.yonedaEquiv, uliftYonedaEquiv]
    change (diagramHomSSet (W.obj (op ⦋n⦌)) W).map
      (𝟙 (op ⦋n⦌)) (𝟙 (W.obj (op ⦋n⦌))) = 𝟙 (W.obj (op ⦋n⦌))
    change (𝟙 (W.obj (op ⦋n⦌))) ≫ W.map (𝟙 (op ⦋n⦌)) = 𝟙 _
    rw [W.map_id, Category.id_comp]
  calc
    diagramRestrictionHomEquiv (Δ[n] : SSet.{v}) (W.obj (op ⦋n⦌)) W q =
        (diagramRestrictionHomEquiv (Δ[n] : SSet.{v})
          (W.obj (op ⦋n⦌)) W q ≫ (diagramRestrictionSimplexIso W n).hom) ≫
          (diagramRestrictionSimplexIso W n).inv := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (diagramRestrictionSimplexIso W n).inv := by rw [h, Category.id_comp]

/-- The matching comparison is the restriction map along the actual boundary
inclusion, under the boundary and simplex restriction isomorphisms. -/
theorem matchingRestrictionIso_comp (W : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) :
    (matchingComparison n).app W ≫ (matchingRestrictionIso W n).hom =
      (diagramRestrictionSimplexIso W n).inv ≫
        diagramRestrictionPre (SSet.boundary.{v} n).ι W := by
  apply (boundaryMatchingHomEquiv W n (W.obj (op ⦋n⦌))).injective
  rw [boundaryMatchingHomEquiv_hom]
  let q := (SSet.yonedaEquiv (X := diagramHomSSet (W.obj (op ⦋n⦌)) W)
    (n := ⦋n⦌)).symm (𝟙 (W.obj (op ⦋n⦌)))
  have hq : (diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet
      (W.obj (op ⦋n⦌)) W).symm
      ((diagramRestrictionSimplexIso W n).inv ≫
        diagramRestrictionPre (SSet.boundary.{v} n).ι W) =
        (SSet.boundary.{v} n).ι ≫ q := by
    apply (diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet
      (W.obj (op ⦋n⦌)) W).injective
    rw [Equiv.apply_symm_apply, diagramRestrictionHomEquiv_pre,
      simplex_hom_equiv_identity]
  change (matchingComparison n).app W =
    boundaryDiagramHomEquiv n (W.obj (op ⦋n⦌)) W
      ((diagramRestrictionHomEquiv (SSet.boundary.{v} n).toSSet
        (W.obj (op ⦋n⦌)) W).symm
        ((diagramRestrictionSimplexIso W n).inv ≫
          diagramRestrictionPre (SSet.boundary.{v} n).ι W))
  rw [hq, boundaryDiagramHomEquiv_restrict]
  simp only [q, Equiv.apply_symm_apply, Category.id_comp]

#print axioms matchingRestrictionIso
#print axioms matchingRestrictionIso_natural
#print axioms matchingRestrictionIso_comp

end

end DaggerModels.PartII.MatchingRestrictionCalibration
