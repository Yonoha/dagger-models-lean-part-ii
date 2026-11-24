import DaggerModelsPartII.BoundaryDiagramHom

/-! External tensor with the outer simplex boundary represents the matching object. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance boundaryTensorCoefficientLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance boundaryTensorCoefficientColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- The boundary version of the external-tensor evaluation bijection. -/
def boundaryTensorHomEquiv (n : ℕ) (A : DaggerSSet.{u}) (W : ResolutionDiagram.{u}) :
    ((externalTensorWith (SSet.boundary n).toSSet).obj A ⟶ W) ≃
      (A ⟶ (matchingFunctor n).obj W) :=
  ((externalTensorAdjunction A).homEquiv _ W).trans (boundaryDiagramHomEquiv n A W)

/-- The boundary bijection is calculated by restriction to each proper face. -/
theorem boundaryTensorHomEquiv_π (n : ℕ) {A : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (q : (externalTensorWith (SSet.boundary n).toSSet).obj A ⟶ W) (s : MatchingIndex n) :
    boundaryTensorHomEquiv n A W q ≫ limit.π (matchingProjection n ⋙ W) s =
      ((externalTensorAdjunction A).homEquiv _ W q).app s.obj.right (boundaryFaceSimplex s) := by
  exact boundaryDiagramHomEquiv_π n _ s

/-- Naturality of the boundary bijection in its dagger simplicial set. -/
theorem boundaryTensorHomEquiv_natural_left (n : ℕ)
    {A B : DaggerSSet.{u}} {W : ResolutionDiagram.{u}} (i : A ⟶ B)
    (q : (externalTensorWith (SSet.boundary n).toSSet).obj B ⟶ W) :
    boundaryTensorHomEquiv n A W ((externalTensorWith (SSet.boundary n).toSSet).map i ≫ q) =
      i ≫ boundaryTensorHomEquiv n B W q := by
  apply limit.hom_ext
  intro s
  change _ ≫ limit.π (matchingProjection n ⋙ W) s =
    (i ≫ boundaryTensorHomEquiv n B W q) ≫ limit.π (matchingProjection n ⋙ W) s
  rw [Category.assoc, boundaryTensorHomEquiv_π, boundaryTensorHomEquiv_π]
  exact externalTensorAdjunction_natural_in_dagger i _ W q _ _

/-- Naturality of the boundary bijection in the resolution diagram. -/
theorem boundaryTensorHomEquiv_natural_right (n : ℕ)
    {A : DaggerSSet.{u}} {W V : ResolutionDiagram.{u}}
    (q : (externalTensorWith (SSet.boundary n).toSSet).obj A ⟶ W) (f : W ⟶ V) :
    boundaryTensorHomEquiv n A V (q ≫ f) =
      boundaryTensorHomEquiv n A W q ≫ (matchingFunctor n).map f := by
  apply limit.hom_ext
  intro s
  change _ ≫ limit.π (matchingProjection n ⋙ V) s =
    (_ ≫ limMap (Functor.whiskerLeft (matchingProjection n) f)) ≫
      limit.π (matchingProjection n ⋙ V) s
  rw [Category.assoc, limMap_π]
  change _ ≫ limit.π (matchingProjection n ⋙ V) s =
    (boundaryTensorHomEquiv n A W q) ≫ limit.π (matchingProjection n ⋙ W) s ≫
      f.app s.obj.right
  rw [← Category.assoc, boundaryTensorHomEquiv_π, boundaryTensorHomEquiv_π,
    externalTensorAdjunction_homEquiv_apply, externalTensorAdjunction_homEquiv_apply,
    NatTrans.comp_app, Category.assoc]

/-- Restriction along the outer boundary inclusion is the canonical matching comparison. -/
theorem boundaryTensorHomEquiv_restrict (n : ℕ)
    {A : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (q : (externalTensorWith (Δ[n] : SSet.{u})).obj A ⟶ W) :
    boundaryTensorHomEquiv n A W ((externalTensor A).map (SSet.boundary n).ι ≫ q) =
      evaluationHomEquiv n A W q ≫ (matchingComparison n).app W := by
  change boundaryDiagramHomEquiv n A W
    ((externalTensorAdjunction A).homEquiv _ W ((externalTensor A).map _ ≫ q)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact boundaryDiagramHomEquiv_restrict n _

end

end DaggerModels.PartII
