import DaggerModelsPartII.RelativeDiagramHom
import Mathlib.CategoryTheory.Elements

/-! Restriction of a simplicial diagram along a simplicial set, computed by its elements. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C]

/-- The limit of the diagram over the simplices of the test simplicial set. -/
def diagramRestriction (K : SSet.{v}) (W : SimplexCategoryᵒᵖ ⥤ C) : C :=
  limit (CategoryOfElements.π K ⋙ W)

/-- The restriction of a cone to a simplicial subset or along a general map. -/
def diagramRestrictionPre {K L : SSet.{v}} (j : K ⟶ L)
    (W : SimplexCategoryᵒᵖ ⥤ C) : diagramRestriction L W ⟶ diagramRestriction K W :=
  limit.lift _ ((limit.cone (CategoryOfElements.π L ⋙ W)).whisker (CategoryOfElements.map j))

/-- The induced map of restrictions. -/
def diagramRestrictionPost (K : SSet.{v}) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    diagramRestriction K W ⟶ diagramRestriction K V :=
  limMap (Functor.whiskerLeft (CategoryOfElements.π K) f)

private def diagramRestrictionCone {A : C} {K : SSet.{v}} {W : SimplexCategoryᵒᵖ ⥤ C}
    (q : K ⟶ diagramHomSSet A W) : Cone (CategoryOfElements.π K ⋙ W) where
  pt := A
  π :=
    { app := fun s ↦ q.app s.1 s.2
      naturality := by
        intro s t f
        change 𝟙 A ≫ q.app t.1 t.2 = q.app s.1 s.2 ≫ W.map f.val
        rw [Category.id_comp]
        have h : q.app t.1 (K.map f.val s.2) = q.app s.1 s.2 ≫ W.map f.val :=
          congrFun (q.naturality f.val) s.2
        rwa [f.property] at h }

/-- The restriction represents maps from the test simplicial set into the Hom simplicial set. -/
def diagramRestrictionHomEquiv (K : SSet.{v}) (A : C) (W : SimplexCategoryᵒᵖ ⥤ C) :
    (K ⟶ diagramHomSSet A W) ≃ (A ⟶ diagramRestriction K W) where
  toFun q := limit.lift _ (diagramRestrictionCone q)
  invFun q :=
    { app := fun d x ↦ q ≫ limit.π (CategoryOfElements.π K ⋙ W) ⟨d, x⟩
      naturality := by
        intro s t f
        funext x
        change q ≫ limit.π _ ⟨t, K.map f x⟩ = (q ≫ limit.π _ ⟨s, x⟩) ≫ W.map f
        rw [Category.assoc]
        have h := limit.w (CategoryOfElements.π K ⋙ W)
          (CategoryOfElements.homMk ⟨s, x⟩ ⟨t, K.map f x⟩ f rfl)
        exact congrArg (fun k ↦ q ≫ k) h.symm }
  left_inv q := by
    ext d x : 2
    exact limit.lift_π (diagramRestrictionCone q) ⟨d, x⟩
  right_inv q := by
    apply limit.hom_ext
    intro d
    exact limit.lift_π _ d

@[reassoc]
theorem diagramRestrictionHomEquiv_π {K : SSet.{v}} {A : C} {W : SimplexCategoryᵒᵖ ⥤ C}
    (q : K ⟶ diagramHomSSet A W) (d : K.Elements) :
    diagramRestrictionHomEquiv K A W q ≫ limit.π (CategoryOfElements.π K ⋙ W) d =
      q.app d.1 d.2 :=
  limit.lift_π _ _

@[reassoc]
theorem diagramRestrictionPre_π {K L : SSet.{v}} (j : K ⟶ L)
    (W : SimplexCategoryᵒᵖ ⥤ C) (d : K.Elements) :
    diagramRestrictionPre j W ≫ limit.π (CategoryOfElements.π K ⋙ W) d =
      limit.π (CategoryOfElements.π L ⋙ W) ((CategoryOfElements.map j).obj d) :=
  limit.lift_π _ _

theorem diagramRestrictionHomEquiv_pre {K L : SSet.{v}} (j : K ⟶ L)
    {A : C} {W : SimplexCategoryᵒᵖ ⥤ C} (q : L ⟶ diagramHomSSet A W) :
    diagramRestrictionHomEquiv K A W (j ≫ q) =
      diagramRestrictionHomEquiv L A W q ≫ diagramRestrictionPre j W := by
  apply limit.hom_ext
  intro d
  rw [diagramRestrictionHomEquiv_π, Category.assoc, diagramRestrictionPre_π]
  exact (diagramRestrictionHomEquiv_π q ((CategoryOfElements.map j).obj d)).symm

theorem diagramRestrictionHomEquiv_post (K : SSet.{v}) {A : C}
    {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) (q : K ⟶ diagramHomSSet A W) :
    diagramRestrictionHomEquiv K A V (q ≫ diagramHomPostcomp A f) =
      diagramRestrictionHomEquiv K A W q ≫ diagramRestrictionPost K f := by
  apply limit.hom_ext
  intro d
  rw [diagramRestrictionHomEquiv_π, Category.assoc]
  change _ = _ ≫ limMap _ ≫ limit.π (CategoryOfElements.π K ⋙ V) d
  rw [limMap_π]
  exact (diagramRestrictionHomEquiv_π_assoc q d (f.app d.1)).symm

theorem diagramRestrictionHomEquiv_coeff (K : SSet.{v}) {A B : C} (i : A ⟶ B)
    {W : SimplexCategoryᵒᵖ ⥤ C} (q : K ⟶ diagramHomSSet B W) :
    diagramRestrictionHomEquiv K A W (q ≫ diagramHomPrecomp i W) =
      i ≫ diagramRestrictionHomEquiv K B W q := by
  apply limit.hom_ext
  intro d
  rw [diagramRestrictionHomEquiv_π, Category.assoc, diagramRestrictionHomEquiv_π]
  rfl

/-- Restrictions form a contravariant functor of the test simplicial set. -/
def diagramRestrictionFunctor (W : SimplexCategoryᵒᵖ ⥤ C) : SSet.{v}ᵒᵖ ⥤ C where
  obj K := diagramRestriction K.unop W
  map j := diagramRestrictionPre j.unop W
  map_id K := by
    apply limit.hom_ext
    intro d
    change diagramRestrictionPre (𝟙 K.unop) W ≫ limit.π _ d = _
    rw [diagramRestrictionPre_π, Category.id_comp]
    congr
  map_comp j k := by
    apply limit.hom_ext
    intro d
    change diagramRestrictionPre (k.unop ≫ j.unop) W ≫ limit.π _ d =
      (diagramRestrictionPre j.unop W ≫ diagramRestrictionPre k.unop W) ≫ limit.π _ d
    rw [Category.assoc, diagramRestrictionPre_π, diagramRestrictionPre_π,
      diagramRestrictionPre_π]
    rfl

/-- The restriction functor is right adjoint to the opposite levelwise Hom construction. -/
def diagramRestrictionAdjunction (W : SimplexCategoryᵒᵖ ⥤ C) :
    opOp C ⋙ (coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj W).op ⊣
      diagramRestrictionFunctor W := by
  apply Adjunction.mkOfHomEquiv
  refine ⟨fun A K ↦ (opEquiv _ _).trans (diagramRestrictionHomEquiv K.unop A W), ?_, ?_⟩
  · intro A B K i q
    apply Quiver.Hom.unop_inj
    change (diagramRestrictionHomEquiv K.unop A W).symm (i ≫ q) =
      (diagramRestrictionHomEquiv K.unop B W).symm q ≫ diagramHomPrecomp i W
    apply (diagramRestrictionHomEquiv K.unop A W).injective
    rw [Equiv.apply_symm_apply, diagramRestrictionHomEquiv_coeff, Equiv.apply_symm_apply]
  · intro A K L q j
    exact diagramRestrictionHomEquiv_pre j.unop q.unop

end

end DaggerModels.PartII
