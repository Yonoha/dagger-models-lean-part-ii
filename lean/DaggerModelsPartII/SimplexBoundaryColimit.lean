import DaggerModelsPartII.SimplexReedyFactorization
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! The standard simplex boundary is the colimit of the representables of its proper faces. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

/-- The standard simplices of the proper faces of the outer simplex. -/
def boundaryFaceDiagram (n : ℕ) : (MatchingIndex n)ᵒᵖ ⥤ SSet.{u} :=
  (matchingProjection n).leftOp ⋙ SSet.stdSimplex

private theorem properFace_not_epi {n : ℕ} (s : MatchingIndex n) : ¬ Epi s.obj.hom.unop :=
  fun h ↦ Nat.not_le_of_lt s.property.1 (by
    letI := h
    exact SimplexCategory.len_le_of_epi s.obj.hom.unop)

/-- The inclusion of a proper face into the boundary, through its given map to the simplex. -/
def boundaryFaceInclusion {n : ℕ} (s : MatchingIndex n) :
    SSet.stdSimplex.{u}.obj s.obj.right.unop ⟶ (SSet.boundary n).toSSet :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map s.obj.hom.unop) (by
    rintro t _ ⟨x, rfl⟩
    change ¬ Function.Surjective
      (SSet.stdSimplex.objEquiv x ≫ s.obj.hom.unop).toOrderHom
    intro h
    apply properFace_not_epi s
    rw [SimplexCategory.epi_iff_surjective]
    exact Function.Surjective.of_comp h)

@[reassoc (attr := simp)]
theorem boundaryFaceInclusion_ι {n : ℕ} (s : MatchingIndex n) :
    boundaryFaceInclusion s ≫ (SSet.boundary.{u} n).ι =
      SSet.stdSimplex.map s.obj.hom.unop :=
  SSet.Subcomplex.lift_ι _ _

/-- The boundary receives the proper-face diagram. -/
def boundaryFaceCocone (n : ℕ) : Cocone (boundaryFaceDiagram.{u} n) where
  pt := (SSet.boundary n).toSSet
  ι :=
    { app := fun s ↦ boundaryFaceInclusion s.unop
      naturality := by
        intro s t g
        apply (cancel_mono (SSet.boundary n).ι).mp
        change (SSet.stdSimplex.map g.unop.hom.right.unop ≫
            boundaryFaceInclusion t.unop) ≫ _ =
          (boundaryFaceInclusion s.unop ≫ 𝟙 _) ≫ _
        rw [Category.comp_id, Category.assoc, boundaryFaceInclusion_ι,
          boundaryFaceInclusion_ι, ← SSet.stdSimplex.map_comp]
        exact SSet.stdSimplex.congr_map (congrArg Quiver.Hom.unop (StructuredArrow.w g.unop.hom)) }

noncomputable section

variable {n : ℕ}

private def boundaryImageFace {t : SimplexCategoryᵒᵖ} (a : t.unop ⟶ ⦋n⦌) (ha : ¬ Epi a) :
    MatchingIndex n :=
  ⟨StructuredArrow.mk (image.ι a).op, by
    apply SimplexCategory.len_lt_of_mono (image.ι a)
    intro h
    apply ha
    haveI : IsIso (image.ι a) :=
      (SimplexCategory.isIso_iff_of_mono _).mpr (congrArg SimplexCategory.len h.symm)
    rw [← image.fac a]
    infer_instance, inferInstanceAs (Mono (image.ι a))⟩

private theorem boundarySimplex_not_epi {t : SimplexCategoryᵒᵖ}
    (x : (SSet.boundary.{u} n).toSSet.obj t) : ¬ Epi (SSet.stdSimplex.objEquiv x.val) :=
  fun h ↦ x.property (SimplexCategory.epi_iff_surjective.mp h)

private def boundaryFaceDescApp (c : Cocone (boundaryFaceDiagram.{u} n))
    (t : SimplexCategoryᵒᵖ) (x : (SSet.boundary n).toSSet.obj t) : c.pt.obj t :=
  let a := SSet.stdSimplex.objEquiv x.val
  let s := boundaryImageFace a (boundarySimplex_not_epi x)
  (c.ι.app (op s)).app t (SSet.stdSimplex.objEquiv.symm (factorThruImage a))

private theorem boundaryFaceDescApp_on_face (c : Cocone (boundaryFaceDiagram.{u} n))
    (s : MatchingIndex n) (t : SimplexCategoryᵒᵖ)
    (y : (SSet.stdSimplex.obj s.obj.right.unop).obj t) :
    boundaryFaceDescApp c t ((boundaryFaceInclusion s).app t y) = (c.ι.app (op s)).app t y := by
  let x := (boundaryFaceInclusion s).app t y
  let a := SSet.stdSimplex.objEquiv x.val
  let b := SSet.stdSimplex.objEquiv y
  have e : b ≫ s.obj.hom.unop = a := rfl
  letI := s.property.2
  let F : MonoFactorisation a := ⟨s.obj.right.unop, s.obj.hom.unop, b, e⟩
  let q := boundaryImageFace a (boundarySimplex_not_epi x)
  let g : s ⟶ q :=
    ⟨StructuredArrow.homMk (image.lift F).op
      (Quiver.Hom.unop_inj (image.lift_fac F))⟩
  have h := congrFun (NatTrans.congr_app (c.w g.op) t)
    (SSet.stdSimplex.objEquiv.symm (factorThruImage a))
  change (c.ι.app (op s)).app t
    (SSet.stdSimplex.objEquiv.symm (factorThruImage a ≫ image.lift F)) =
      boundaryFaceDescApp c t x at h
  rw [image.fac_lift F] at h
  exact h.symm

private theorem boundaryImageFace_rep {t : SimplexCategoryᵒᵖ}
    (x : (SSet.boundary.{u} n).toSSet.obj t) :
    (boundaryFaceInclusion
      (boundaryImageFace (SSet.stdSimplex.objEquiv x.val) (boundarySimplex_not_epi x))).app t
        (SSet.stdSimplex.objEquiv.symm (factorThruImage (SSet.stdSimplex.objEquiv x.val))) = x := by
  apply Subtype.ext
  change SSet.stdSimplex.objEquiv.symm
      (factorThruImage (SSet.stdSimplex.objEquiv x.val) ≫ image.ι _) = x.val
  rw [image.fac, Equiv.symm_apply_apply]

private def boundaryFaceDesc (c : Cocone (boundaryFaceDiagram.{u} n)) :
    (SSet.boundary n).toSSet ⟶ c.pt where
  app t := boundaryFaceDescApp c t
  naturality s t g := by
    funext x
    obtain ⟨q, y, rfl⟩ :
        ∃ (q : MatchingIndex n) (y : (SSet.stdSimplex.obj q.obj.right.unop).obj s),
          (boundaryFaceInclusion q).app s y = x :=
      ⟨_, _, boundaryImageFace_rep x⟩
    change boundaryFaceDescApp c t ((SSet.boundary n).toSSet.map g
        ((boundaryFaceInclusion q).app s y)) =
      c.pt.map g (boundaryFaceDescApp c s ((boundaryFaceInclusion q).app s y))
    have h : (boundaryFaceInclusion q).app t
        ((SSet.stdSimplex.obj q.obj.right.unop).map g y) =
        (SSet.boundary n).toSSet.map g ((boundaryFaceInclusion q).app s y) :=
      congrFun ((boundaryFaceInclusion q).naturality g) y
    rw [← h, boundaryFaceDescApp_on_face, boundaryFaceDescApp_on_face]
    exact congrFun ((c.ι.app (op q)).naturality g) y

/-- Part II: the literal simplicial boundary is a colimit of its proper faces. -/
def boundaryFaceIsColimit (n : ℕ) : IsColimit (boundaryFaceCocone.{u} n) where
  desc := boundaryFaceDesc
  fac c s := by
    ext t y : 2
    exact boundaryFaceDescApp_on_face c s.unop t y
  uniq c m hm := by
    ext t x : 2
    let q := boundaryImageFace (SSet.stdSimplex.objEquiv x.val) (boundarySimplex_not_epi x)
    let y := SSet.stdSimplex.objEquiv.symm (factorThruImage (SSet.stdSimplex.objEquiv x.val))
    exact (congrArg (m.app t) (boundaryImageFace_rep x)).symm.trans
      (congrFun (NatTrans.congr_app (hm (op q)) t) y)

end

end DaggerModels.PartII
