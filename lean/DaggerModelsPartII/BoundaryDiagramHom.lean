import DaggerModelsPartII.SimplexBoundaryColimit

/-! Maps from the standard simplex and its boundary into a levelwise Hom simplicial set. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- The simplicial set of levelwise morphisms from a fixed coefficient object. -/
def diagramHomSSet (A : C) (W : SimplexCategoryᵒᵖ ⥤ C) : SSet.{v} :=
  W ⋙ coyoneda.obj (op A)

private theorem boundaryYoneda_naturality {Z : SSet.{v}} {s t : SimplexCategoryᵒᵖ}
    (g : s ⟶ t) (q : SSet.stdSimplex.obj s.unop ⟶ Z) :
    Z.map g (SSet.yonedaEquiv q) = SSet.yonedaEquiv (SSet.stdSimplex.map g.unop ≫ q) :=
  uliftYonedaEquiv_naturality q g

private def boundaryCoconeEquivCone (n : ℕ) (A : C) (W : SimplexCategoryᵒᵖ ⥤ C) :
    (boundaryFaceDiagram n ⟶ (Functor.const (MatchingIndex n)ᵒᵖ).obj
      (diagramHomSSet A W)) ≃
      ((Functor.const (MatchingIndex n)).obj A ⟶ matchingProjection n ⋙ W) where
  toFun a :=
    { app := fun s ↦ SSet.yonedaEquiv (a.app (op s))
      naturality := by
        intro s t g
        change 𝟙 A ≫ SSet.yonedaEquiv (a.app (op t)) =
          SSet.yonedaEquiv (a.app (op s)) ≫ W.map g.hom.right
        have h : SSet.stdSimplex.map g.hom.right.unop ≫ a.app (op s) =
            a.app (op t) ≫ 𝟙 _ := a.naturality g.op
        rw [Category.id_comp, Category.comp_id] at *
        exact (congrArg SSet.yonedaEquiv h).symm.trans
          (boundaryYoneda_naturality g.hom.right (a.app (op s))).symm }
  invFun b :=
    { app := fun s ↦ (SSet.yonedaEquiv (X := diagramHomSSet A W)).symm (b.app s.unop)
      naturality := by
        intro s t g
        apply SSet.yonedaEquiv.injective
        change SSet.yonedaEquiv
            (SSet.stdSimplex.map g.unop.hom.right.unop ≫
              (SSet.yonedaEquiv (X := diagramHomSSet A W)).symm (b.app t.unop)) =
          SSet.yonedaEquiv ((SSet.yonedaEquiv (X := diagramHomSSet A W)).symm (b.app s.unop) ≫ 𝟙 _)
        rw [Category.comp_id, ← boundaryYoneda_naturality, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
        have h : 𝟙 A ≫ b.app s.unop = b.app t.unop ≫ W.map g.unop.hom.right :=
          b.naturality g.unop
        exact (Category.id_comp _).symm.trans h |>.symm }
  left_inv a := by
    apply NatTrans.ext
    funext s
    exact Equiv.symm_apply_apply SSet.yonedaEquiv (a.app s)
  right_inv b := by
    apply NatTrans.ext
    funext s
    exact Equiv.apply_symm_apply
      (SSet.yonedaEquiv (X := diagramHomSSet A W)) (b.app s)

/-- Precomposition in the coefficient object acts levelwise on the Hom simplicial set. -/
def diagramHomPrecomp {A B : C} (i : A ⟶ B) (W : SimplexCategoryᵒᵖ ⥤ C) :
    diagramHomSSet B W ⟶ diagramHomSSet A W :=
  Functor.whiskerLeft W (coyoneda.map i.op)

/-- A map of diagrams acts levelwise by postcomposition. -/
def diagramHomPostcomp (A : C) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    diagramHomSSet A W ⟶ diagramHomSSet A V :=
  Functor.whiskerRight f (coyoneda.obj (op A))

variable [HasLimitsOfSize.{0, 0} C]

/-- Maps from the simplex boundary are maps into the matching object. -/
def boundaryDiagramHomEquiv (n : ℕ) (A : C) (W : SimplexCategoryᵒᵖ ⥤ C) :
    ((SSet.boundary n).toSSet ⟶ diagramHomSSet A W) ≃ (A ⟶ (matchingFunctor n).obj W) :=
  (boundaryFaceIsColimit n).homEquiv.trans
    ((boundaryCoconeEquivCone n A W).trans (limit.isLimit _).homEquiv.symm)

/-- The simplex of the boundary specifying a proper face. -/
def boundaryFaceSimplex {n : ℕ} (s : MatchingIndex n) :
    (SSet.boundary.{v} n).toSSet.obj s.obj.right :=
  (boundaryFaceInclusion s).app s.obj.right (SSet.stdSimplex.objEquiv.symm (𝟙 _))

/-- The map into the matching object has the specified restrictions at each proper face. -/
theorem boundaryDiagramHomEquiv_π (n : ℕ) {A : C} {W : SimplexCategoryᵒᵖ ⥤ C}
    (q : (SSet.boundary n).toSSet ⟶ diagramHomSSet A W) (s : MatchingIndex n) :
    boundaryDiagramHomEquiv n A W q ≫ limit.π (matchingProjection n ⋙ W) s =
      q.app s.obj.right (boundaryFaceSimplex s) :=
  (limit.isLimit _).homEquiv_symm_π_app _ _

theorem boundaryDiagramHomEquiv_precomp (n : ℕ) {A B : C} (i : A ⟶ B)
    {W : SimplexCategoryᵒᵖ ⥤ C} (q : (SSet.boundary n).toSSet ⟶ diagramHomSSet B W) :
    boundaryDiagramHomEquiv n A W (q ≫ diagramHomPrecomp i W) =
      i ≫ boundaryDiagramHomEquiv n B W q := by
  apply limit.hom_ext
  intro s
  change _ ≫ limit.π (matchingProjection n ⋙ W) s =
    (i ≫ boundaryDiagramHomEquiv n B W q) ≫ limit.π (matchingProjection n ⋙ W) s
  rw [Category.assoc, boundaryDiagramHomEquiv_π, boundaryDiagramHomEquiv_π]
  rfl

theorem boundaryDiagramHomEquiv_postcomp (n : ℕ) {A : C} {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) (q : (SSet.boundary n).toSSet ⟶ diagramHomSSet A W) :
    boundaryDiagramHomEquiv n A V (q ≫ diagramHomPostcomp A f) =
      boundaryDiagramHomEquiv n A W q ≫ (matchingFunctor n).map f := by
  apply limit.hom_ext
  intro s
  change _ ≫ limit.π (matchingProjection n ⋙ V) s =
    (_ ≫ limMap (Functor.whiskerLeft (matchingProjection n) f)) ≫
      limit.π (matchingProjection n ⋙ V) s
  rw [Category.assoc, limMap_π]
  change _ ≫ limit.π (matchingProjection n ⋙ V) s =
    (boundaryDiagramHomEquiv n A W q) ≫ limit.π (matchingProjection n ⋙ W) s ≫
      f.app s.obj.right
  rw [← Category.assoc, boundaryDiagramHomEquiv_π, boundaryDiagramHomEquiv_π]
  rfl

/-- Restriction from the simplex to its boundary becomes the matching comparison. -/
theorem boundaryDiagramHomEquiv_restrict (n : ℕ) {A : C} {W : SimplexCategoryᵒᵖ ⥤ C}
    (q : (Δ[n] : SSet.{v}) ⟶ diagramHomSSet A W) :
    boundaryDiagramHomEquiv n A W ((SSet.boundary n).ι ≫ q) =
      SSet.yonedaEquiv q ≫ (matchingComparison n).app W := by
  apply limit.hom_ext
  intro s
  change _ ≫ limit.π (matchingProjection n ⋙ W) s =
    (_ ≫ limit.lift _ (matchingCone n W)) ≫ limit.π (matchingProjection n ⋙ W) s
  rw [Category.assoc, limit.lift_π, boundaryDiagramHomEquiv_π]
  change q.app s.obj.right (SSet.stdSimplex.objEquiv.symm (𝟙 _ ≫ s.obj.hom.unop)) =
    (diagramHomSSet A W).map s.obj.hom (SSet.yonedaEquiv q)
  rw [Category.id_comp, ← SSet.stdSimplex.yonedaEquiv_map, ← SSet.yonedaEquiv_comp]
  exact (boundaryYoneda_naturality s.obj.hom q).symm

end

end DaggerModels.PartII
