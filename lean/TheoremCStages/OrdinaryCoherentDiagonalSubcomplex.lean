import OrdinaryCoherentReplacementComparison
import OrdinaryCoherentReplacementPreimage
import OrdinaryCoherentCotensorEvaluationReflection
import OrdinarySegalComponentImage
import OrdinarySegalCotensorEvaluationNaturality
import OrdinarySegalComponentSubcomplex

/-!
# The coherent-arrow subcomplex of the corrected diagonal

The original diagonal inclusion is degreewise the literal inclusion of the
coherent-arrow component subcomplex. The component-saturation comparison
below uses the original outer and inner first-vertex maps.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentDiagonalSubcomplex

open OrdinaryCSSLocalization (Space)
open OrdinaryCoherentReplacementComparison (diagonalInclusion)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)
open OrdinarySegalComponentImage (componentImage imageComponents)

noncomputable section

private abbrev R (W : Space) := OrdinarySegalPrecompletion.resolution W
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W
private abbrev C (W : Space) :=
  OrdinaryCoherentPrecompletionResolution.coherentResolution W
private abbrev E (q : SimplexCategory) := GroupoidSimplex.parameter.obj q
private def first (q : SimplexCategoryᵒᵖ) : q ⟶ op ⦋0⦌ :=
  (SimplexCategory.const ⦋0⦌ q.unop (0 : Fin (q.unop.len + 1))).op

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- At every diagonal degree, the inclusion is the original subtype inclusion. -/
theorem diagonalInclusion_app (W : Space) (q : SimplexCategoryᵒᵖ)
    (x : (diagonalFunctor.obj (C W)).obj q) :
    (diagonalInclusion W).app q x = x.val := rfl

/-- The original coherent diagonal embeds in the unchanged arrow row. -/
instance diagonalInclusion_mono (W : Space) : Mono (diagonalInclusion W) := by
  exact OrdinaryCoherentReplacementPreimage.diagonalInclusion_mono W

/-- The ordinary range factor is an isomorphism because the diagonal is
degreewise the literal subtype inclusion. -/
def rangeIso (W : Space) :
    diagonalFunctor.obj (C W) ≅
      (SSet.Subcomplex.range (diagonalInclusion W)).toSSet :=
  asIso (SSet.Subcomplex.toRange (diagonalInclusion W))

/-- The range is contained in the union of components met by the same map. -/
theorem range_le_componentImage (W : Space) :
    SSet.Subcomplex.range (diagonalInclusion W) ≤
      componentImage (diagonalInclusion W) := by
  intro q x hx
  obtain ⟨y, rfl⟩ := hx
  exact ((OrdinarySegalComponentImage.factor (diagonalInclusion W)).app q y).property

/-- A coherent-arrow simplex is selected by its first vertical vertex. -/
theorem mem_coherent_first (V : Space) (q : SimplexCategoryᵒᵖ)
    (x : ((V.obj (op ⦋1⦌)).obj q)) :
    x ∈ (coherentArrowSubcomplex V).obj q ↔
      (V.obj (op ⦋1⦌)).map (first q) x ∈
        (coherentArrowSubcomplex V).obj (op ⦋0⦌) := by
  change x ∈ (componentImage (OrdinarySegalWalkingEvaluation.edgeEvaluation V)).obj q ↔
    (V.obj (op ⦋1⦌)).map (first q) x ∈
      (componentImage (OrdinarySegalWalkingEvaluation.edgeEvaluation V)).obj
        (op ⦋0⦌)
  dsimp only [componentImage]
  rw [OrdinarySegalComponentSubcomplex.mem_selected_iff,
    OrdinarySegalComponentImage.mem_selected_zero]
  rfl

/-- Every original parameter transition reflects coherent-arrow membership.
The target vertex is the actual image of the specified source vertex. -/
theorem transition_reflects_coherent (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    {n m : SimplexCategory} (θ : n ⟶ m) (j : Fin (n.len + 1))
    (q : SimplexCategoryᵒᵖ)
    (x : (((R W).obj (op m)).obj (op ⦋1⦌)).obj q) :
    x ∈ (coherentArrowSubcomplex ((R W).obj (op m))).obj q ↔
      (((R W).map θ.op).app (op ⦋1⦌)).app q x ∈
        (coherentArrowSubcomplex ((R W).obj (op n))).obj q := by
  let v := JTParameterContraction.parameterVertex n j
  let w := JTParameterContraction.parameterVertex m (θ.toOrderHom j)
  have heval : (R W).map θ.op ≫
      OrdinarySegalCotensorPointEvaluation.evaluation (E n) W v =
        OrdinarySegalCotensorPointEvaluation.evaluation (E m) W w := by
    change OrdinarySegalHorizontalCotensor.pre (GroupoidSimplex.parameter.map θ) W ≫
      OrdinarySegalCotensorPointEvaluation.evaluation (E n) W v =
        OrdinarySegalCotensorPointEvaluation.evaluation (E m) W w
    rw [OrdinarySegalCotensorEvaluationNaturality.evaluation_pre]
    exact congrArg (fun a ↦
      OrdinarySegalCotensorPointEvaluation.evaluation (E m) W a)
      (JTParameterBlocks.parameterVertex_map θ j)
  have hpoint := congrFun
    (NatTrans.congr_app (NatTrans.congr_app heval (op ⦋1⦌)) q) x
  have hpoint' :
      (((OrdinarySegalCotensorPointEvaluation.evaluation (E n) W v).app
        (op ⦋1⦌)).app q)
        ((((R W).map θ.op).app (op ⦋1⦌)).app q x) =
      (((OrdinarySegalCotensorPointEvaluation.evaluation (E m) W w).app
        (op ⦋1⦌)).app q) x := by
    simpa only [NatTrans.comp_app] using hpoint
  have hpoint'' :
      (((OrdinarySegalCotensorPointEvaluation.evaluation (E n) W v).app
        (op ⦋1⦌)).app q)
        (((OrdinarySegalHorizontalCotensor.pre (GroupoidSimplex.parameter.map θ) W).app
          (op ⦋1⦌)).app q x) =
      (((OrdinarySegalCotensorPointEvaluation.evaluation (E m) W w).app
        (op ⦋1⦌)).app q) x := hpoint'
  change x ∈
      (coherentArrowSubcomplex (OrdinarySegalHorizontalCotensor.cotensor (E m) W)).obj
        q ↔
    ((OrdinarySegalHorizontalCotensor.pre (GroupoidSimplex.parameter.map θ) W).app
      (op ⦋1⦌)).app q x ∈
      (coherentArrowSubcomplex (OrdinarySegalHorizontalCotensor.cotensor (E n) W)).obj
        q
  have hm := OrdinaryCoherentCotensorEvaluationReflection.evaluation_reflects_coherent
    W hSegal m (θ.toOrderHom j) q x
  have hn := OrdinaryCoherentCotensorEvaluationReflection.evaluation_reflects_coherent
    W hSegal n j q
      (((OrdinarySegalHorizontalCotensor.pre (GroupoidSimplex.parameter.map θ) W).app
        (op ⦋1⦌)).app q x)
  have hmem := congrArg
    (fun y ↦ y ∈ (coherentArrowSubcomplex W).obj q) hpoint''
  constructor
  · intro hx
    apply hn.mpr
    exact Eq.mp hmem.symm (hm.mp hx)
  · intro hx
    apply hm.mpr
    exact Eq.mp hmem (hn.mp hx)

/-- Pointwise range membership is literally the original coherent-arrow
predicate at the same outer and inner degree. -/
theorem mem_range_iff (W : Space) (q : SimplexCategoryᵒᵖ)
    (x : ((P W).obj (op ⦋1⦌)).obj q) :
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
      x ∈ (coherentArrowSubcomplex ((R W).obj q)).obj q := by
  change (∃ y : (diagonalFunctor.obj (C W)).obj q,
    (diagonalInclusion W).app q y = x) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Membership in the literal range is detected by the original diagonal
first vertex, with both the outer and inner parameter maps retained. -/
theorem range_first_vertex_iff (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategoryᵒᵖ)
    (x : ((P W).obj (op ⦋1⦌)).obj q) :
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
      ((P W).obj (op ⦋1⦌)).map (first q) x ∈
        (SSet.Subcomplex.range (diagonalInclusion W)).obj (op ⦋0⦌) := by
  rw [mem_range_iff W q x,
    mem_range_iff W (op ⦋0⦌) (((P W).obj (op ⦋1⦌)).map (first q) x),
    mem_coherent_first ((R W).obj q) q x]
  have h := transition_reflects_coherent W hSegal
    (SimplexCategory.const ⦋0⦌ q.unop (0 : Fin (q.unop.len + 1))) 0
    (op ⦋0⦌) ((((R W).obj q).obj (op ⦋1⦌)).map (first q) x)
  exact h.trans (by rfl)

#print axioms diagonalInclusion_mono
#print axioms rangeIso
#print axioms range_le_componentImage
#print axioms transition_reflects_coherent
#print axioms range_first_vertex_iff

end

end DaggerModels.PartII.OrdinaryCoherentDiagonalSubcomplex
