import DaggerModelsPartII.JTNativeOuterCollapse
import DaggerModelsPartII.JTMixedGraphHorizontalTraversal

/-! Native endpoint padding of an arbitrary necklace and its original-map comparison. -/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeEndpointPadding

noncomputable section

private abbrev A := single 1

/-- Add a fixed one-bead necklace at each endpoint. -/
def pad : NecklaceCode ⥤ NecklaceCode where
  obj T := wedge A (wedge T A)
  map f := wedgeMap (𝟙 A) (wedgeMap f (𝟙 A))
  map_id T := by
    change wedgeMap (Hom.id.{0} A)
      (wedgeMap (Hom.id.{0} T) (Hom.id.{0} A)) = Hom.id.{0} _
    rw [wedgeMap_id, wedgeMap_id]
  map_comp f g := by
    change wedgeMap (Hom.id.{0} A) (wedgeMap (Hom.comp f g) (Hom.id.{0} A)) =
      Hom.comp (wedgeMap (Hom.id.{0} A) (wedgeMap f (Hom.id.{0} A)))
        (wedgeMap (Hom.id.{0} A) (wedgeMap g (Hom.id.{0} A)))
    rw [← wedgeMap_comp, ← wedgeMap_comp]
    rfl

private theorem pad_left {T U : NecklaceCode} (f : T ⟶ U) :
    tripleRightT A T A ≫ (pad.map f).map = tripleRightT A U A := by
  simp only [tripleRightT, pad, wedgeMap_left]
  exact Category.id_comp _

private theorem pad_middle {T U : NecklaceCode} (f : T ⟶ U) :
    tripleRightU A T A ≫ (pad.map f).map = f.map ≫ tripleRightU A U A := by
  unfold tripleRightU pad
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left, Category.assoc]

private theorem pad_right {T U : NecklaceCode} (f : T ⟶ U) :
    tripleRightV A T A ≫ (pad.map f).map = tripleRightV A U A := by
  unfold tripleRightV pad
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_right]
  change (𝟙 A.toSSet ≫ wedgeιRight U A) ≫ wedgeιRight A (wedge U A) = _
  rw [Category.id_comp]

/-- Collapse the added beads and retain the complete original necklace. -/
def collapse : pad ⟶ 𝟭 NecklaceCode where
  app T := NecklaceCode.collapse A T A
  naturality := by
    intro T U f
    apply Hom.ext
    change (pad.map f).map ≫ (NecklaceCode.collapse A U A).map =
      (NecklaceCode.collapse A T A).map ≫ f.map
    apply tripleRight_hom_ext (T := A) (U := T) (V := A)
    · rw [← Category.assoc, pad_left, NecklaceCode.collapse_left,
        ← Category.assoc, NecklaceCode.collapse_left, Category.assoc, pointAt_first_comp]
    · rw [← Category.assoc, pad_middle, Category.assoc,
        NecklaceCode.collapse_middle, ← Category.assoc (tripleRightU A T A),
        NecklaceCode.collapse_middle, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, pad_right, NecklaceCode.collapse_right,
        ← Category.assoc, NecklaceCode.collapse_right, Category.assoc, pointAt_last_comp]

/-- Pad every native arrow into a fixed target, including all arrows between them. -/
def over (Q : NecklaceCode) : Over Q ⥤ Over (pad.obj Q) where
  obj P := Over.mk (pad.map P.hom)
  map {P R} f := Over.homMk (pad.map f.left) (by
    change pad.map f.left ≫ pad.map R.hom = pad.map P.hom
    rw [← pad.map_comp, Over.w f])
  map_id P := by
    apply Over.OverMorphism.ext
    exact pad.map_id P.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact pad.map_comp f.left g.left

/-- Postcomposing a padded native map with collapse recovers the whole original map. -/
theorem over_obj_collapse (Q : NecklaceCode) (P : Over Q) :
    ((over Q).obj P).hom ≫ (collapse.app Q) =
      collapse.app P.left ≫ P.hom := by
  simpa only [Functor.id_obj, Functor.id_map, Over.mk_hom] using
    collapse.naturality P.hom

/-- For a finite or arbitrary diagram, every native map lands in the same padded target. -/
theorem diagram_obj_collapse {J : Type*} [Category J] (Q : NecklaceCode)
    (F : J ⥤ Over Q) (j : J) :
    (((F ⋙ over Q).obj j).hom) ≫ collapse.app Q =
      collapse.app (F.obj j).left ≫ (F.obj j).hom :=
  over_obj_collapse Q (F.obj j)

/-- On a one-bead middle, the general padded target is the existing mixed graph code. -/
theorem pad_single_eq_code (d : ℕ) :
    pad.obj (single d) = MixedGraphCylinderTraversal.code d := rfl

/-- The general collapse specializes to the existing mixed-graph collapse. -/
theorem collapse_single_eq (d : ℕ) :
    collapse.app (single d) = MixedGraphCylinderTraversal.collapseOuter d := by
  apply Hom.ext
  apply tripleRight_hom_ext (T := A) (U := single d) (V := A)
  · exact (NecklaceCode.collapse_left A (single d) A).trans
      (MixedGraphCylinderTraversal.collapseMap_left d).symm
  · exact (NecklaceCode.collapse_middle A (single d) A).trans
      (MixedGraphCylinderTraversal.collapseMap_middle d).symm
  · exact (NecklaceCode.collapse_right A (single d) A).trans
      (MixedGraphCylinderTraversal.collapseMap_right d).symm

/-- The padded map on a one-bead middle is the pre-existing horizontal padding. -/
theorem pad_map_single_eq {d e : ℕ} (f : single d ⟶ single e) :
    pad.map f = JTMixedGraphHorizontalTraversal.padded f := rfl

/-- A diagram of native maps to one bead has the existing mixed-graph comparison target. -/
theorem diagram_single_collapse {J : Type*} [Category J] (d : ℕ)
    (F : J ⥤ Over (single d)) (j : J) :
    ((F ⋙ over (single d)).obj j).hom ≫
        MixedGraphCylinderTraversal.collapseOuter d =
      collapse.app (F.obj j).left ≫ (F.obj j).hom := by
  rw [← collapse_single_eq]
  exact diagram_obj_collapse (single d) F j

end

end DaggerModels.PartII.JTNativeEndpointPadding
