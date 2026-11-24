import DaggerModelsPartII.JTCylinderConeComparison
import DaggerModelsPartII.JTEndpointCobase
import DaggerModelsPartII.ReedyMaps
import OriginalCounitRightConeQZeroFaceIntersectionReconciled
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# The literal right-cone latching diagram under its ordered boundary

The proper-face diagram is formed in the original undercategory.  This
retains the shared boundary in degree one, where the two cone faces meet
at both fixed endpoints.  The map below uses the unchanged ordinary
right-cone functor; no rigidified Hom replacement is involved.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace DaggerModels.PartII.JTConeReedy

noncomputable section

open JTCylinderConeComparison
open DaggerOriginalCounitRightCone

/-- Each actual cone coface is split monic. This uses its genuine
cosimplicial map, rather than monicity of the rigidified `Q` coface. -/
theorem coneCoface_mono (n : ℕ) (i : Fin (n + 2)) :
    Mono ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}).map
      (SimplexCategory.δ i)) := by
  infer_instance

/-- The actual proper-face diagram of the ordinary cone under its boundary. -/
def faceDiagram (n : ℕ) :
    (MatchingIndex n)ᵒᵖ ⥤ Under JTXiEndpointCollapse.boundary :=
  (matchingProjection n).leftOp ⋙ coneUnder

/-- The actual proper-face cocone into the cone of degree `n`. -/
def faceCocone (n : ℕ) : Cocone (faceDiagram n) where
  pt := coneUnder.obj ⦋n⦌
  ι :=
    { app := fun s ↦ coneUnder.map s.unop.obj.hom.unop
      naturality := by
        intro s t f
        change coneUnder.map f.unop.hom.right.unop ≫
            coneUnder.map t.unop.obj.hom.unop =
          coneUnder.map s.unop.obj.hom.unop ≫ 𝟙 _
        rw [Category.comp_id, ← coneUnder.map_comp]
        exact coneUnder.congr_map
          (congrArg Quiver.Hom.unop (StructuredArrow.w f.unop.hom)) }

/-- The literal latching arrow in the original ordinary undercategory. -/
def faceLatchingMap (n : ℕ) :
    colimit (faceDiagram n) ⟶ coneUnder.obj ⦋n⦌ :=
  colimit.desc _ (faceCocone n)

/-- Opposite matching objects retain the literal under-boundary latching
colimit in every degree, including the empty zero face category. -/
def coneMatchingIso (n : ℕ) :
    (matchingFunctor n).obj coneUnder.op ≅ op (colimit (faceDiagram n)) :=
  limit.isoLimitCone ⟨coneOfCoconeLeftOp
    (F := matchingProjection n ⋙ coneUnder.op)
    (colimit.cocone (faceDiagram n)),
    isLimitConeOfCoconeLeftOp _ (colimit.isColimit (faceDiagram n))⟩

/-- The native matching comparison is exactly the opposite of the actual
under-boundary latching arrow. -/
theorem coneMatchingIso_comp (n : ℕ) :
    (matchingComparison n).app coneUnder.op ≫
      (coneMatchingIso n).hom = (faceLatchingMap n).op := by
  apply Quiver.Hom.unop_inj
  apply (colimit.isColimit (faceDiagram n)).hom_ext
  intro s
  apply Quiver.Hom.op_inj
  rw [op_comp, op_comp]
  simp only [Quiver.Hom.op_unop]
  have hfac : (colimit.cocone (faceDiagram n)).ι.app s ≫
      faceLatchingMap n = (faceCocone n).ι.app s :=
    colimit.ι_desc (faceCocone n) s
  conv_rhs => rw [← op_comp, hfac]
  change ((matchingComparison n).app coneUnder.op ≫
      (coneMatchingIso n).hom) ≫
      (colimit.ι (faceDiagram n) s).op =
    (coneUnder.map s.unop.obj.hom.unop).op
  rw [Category.assoc]
  have hlim : (coneMatchingIso n).hom ≫
      (colimit.ι (faceDiagram n) s).op =
        limit.π (matchingProjection n ⋙ coneUnder.op) s.unop :=
    limit.isoLimitCone_hom_π
      ⟨coneOfCoconeLeftOp
        (F := matchingProjection n ⋙ coneUnder.op)
        (colimit.cocone (faceDiagram n)),
        isLimitConeOfCoconeLeftOp _ (colimit.isColimit (faceDiagram n))⟩ s.unop
  rw [hlim]
  exact limit.lift_π _ _

/- The collapsed old face is the identity of the terminal zero simplex. -/
private theorem collapse_zero_eq_id :
    collapse.{0} 0 = 𝟙 (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The large-simplex leg is an isomorphism in degree zero, since the
collapsed old face is the identity. -/
private theorem simplexIncl_zero_isIso : IsIso (simplexIncl.{0} 0) := by
  haveI : IsIso (collapse.{0} 0) := by
    rw [collapse_zero_eq_id]
    infer_instance
  exact (IsPushout.of_hasPushout (face.{0} 0) (collapse.{0} 0)).isIso_inl_of_isIso

/-- The literal ordered boundary map at degree zero is the standard
boundary inclusion followed by the original pushout's large-simplex leg. -/
private theorem coneBoundary_zero_factor :
    coneBoundary ⦋0⦌ =
      (SSet.boundary.{0} 1).ι ≫ simplexIncl.{0} 0 := by
  apply SSet.boundary₁.hom_ext
  · rw [coneBoundary_zero, ← Category.assoc, SSet.boundary₁.ι₀_ι]
    change baseIncl.{0} 0 = face.{0} 0 ≫ simplexIncl.{0} 0
    rw [face_eq_collapse, collapse_zero_eq_id, Category.id_comp]
  · rw [coneBoundary_one, ← Category.assoc, SSet.boundary₁.ι₁_ι]
    change omegaMap.{0} 0 = SSet.stdSimplex.δ 0 ≫ simplexIncl.{0} 0
    change lastVertex.{0} 0 ≫ simplexIncl.{0} 0 =
      SSet.stdSimplex.δ 0 ≫ simplexIncl.{0} 0
    congr 1
    rw [lastVertex, SSet.stdSimplex.δ_zero]
    rfl

/-- The actual zero-degree cone boundary is monic in ordinary simplicial
sets. This is the geometric input for the empty Reedy latching index. -/
theorem coneBoundary_zero_mono : Mono (coneBoundary ⦋0⦌) := by
  rw [coneBoundary_zero_factor]
  letI : IsIso (simplexIncl.{0} 0) := simplexIncl_zero_isIso
  infer_instance

end

end DaggerModels.PartII.JTConeReedy
