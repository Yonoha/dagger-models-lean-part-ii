import DaggerModelsPartII.ReducedCylinder
import ActualRigidificationRelativeDirectedHomotopy
import OriginalOrdinaryHomRetractsReconciled

/-! A directed contraction of the parameter contracts the actual reduced
cylinder relative to its entire collapsed boundary. -/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerActualRigidificationDirectedIntervalObjects
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ReducedCylinderDirectedContraction

noncomputable section

variable {A B K : SSet.{0}} (j : A ⟶ B)

private abbrev V := (ReducedCylinder.value j).obj K
private abbrev cylinder := (ReducedCylinder.cylinder j).app K
private abbrev boundary := (ReducedCylinder.boundary j).app K

/-- Forget the parameter on the literal reduced cylinder. -/
def augmentation : V (K := K) j ⟶ B :=
  (ReducedCylinder.value_isPushout j).desc (fst B K) j (tensorHom_fst j (𝟙 K))

theorem cylinder_augmentation : cylinder j ≫ augmentation j = fst B K :=
  (ReducedCylinder.value_isPushout j).inl_desc _ _ _

theorem boundary_augmentation : boundary (K := K) j ≫ augmentation j = j :=
  (ReducedCylinder.value_isPushout j).inr_desc _ _ _

variable (v : K.obj (op ⦋0⦌))

/-- Use the specified constant parameter vertex as a pointwise section. -/
def sectionAt : B ⟶ V (K := K) j :=
  lift (𝟙 B) (SSet.const v) ≫ cylinder j

theorem section_augmentation : sectionAt j v ≫ augmentation j = 𝟙 B := by
  rw [sectionAt, Category.assoc, cylinder_augmentation, lift_fst]

theorem boundary_section : j ≫ sectionAt j v = boundary j := by
  apply NatTrans.ext
  funext q a
  exact congrFun (NatTrans.congr_app (ReducedCylinder.value_isPushout j (K := K)).w q)
    (a, (SSet.const v).app q (j.app q a))

private local instance : PreservesColimitsOfSize.{0, 0} (tensorRight (Δ[1] : SSet.{0})) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{0, 0} (tensorLeft (Δ[1] : SSet.{0})) := inferInstance
  exact preservesColimits_of_natIso
    (MonoidalCategory.tensorLeftIsoTensorRight (Δ[1] : SSet.{0}))

variable (H : K ⊗ (Δ[1] : SSet.{0}) ⟶ K)

private def cylinderDeformation : (B ⊗ K) ⊗ (Δ[1] : SSet.{0}) ⟶ V (K := K) j :=
  (α_ B K (Δ[1] : SSet.{0})).hom ≫ (B ◁ H) ≫ cylinder j

private def boundaryDeformation : A ⊗ (Δ[1] : SSet.{0}) ⟶ V (K := K) j :=
  fst A (Δ[1] : SSet.{0}) ≫ boundary j

private def deformation : V (K := K) j ⊗ (Δ[1] : SSet.{0}) ⟶ V (K := K) j :=
  ((ReducedCylinder.value_isPushout j (K := K)).map (tensorRight (Δ[1] : SSet.{0}))).desc
    (cylinderDeformation j H) (boundaryDeformation j) (by
      apply NatTrans.ext
      funext q z
      exact congrFun (NatTrans.congr_app (ReducedCylinder.value_isPushout j (K := K)).w q)
        (z.1.1, H.app q (z.1.2, z.2)))

private theorem deformation_cylinder :
    (cylinder j ▷ (Δ[1] : SSet.{0})) ≫ deformation j H = cylinderDeformation j H :=
  ((ReducedCylinder.value_isPushout j (K := K)).map (tensorRight (Δ[1] : SSet.{0}))).inl_desc
    _ _ _

private theorem deformation_boundary :
    (boundary j ▷ (Δ[1] : SSet.{0})) ≫ deformation j H = boundaryDeformation j :=
  ((ReducedCylinder.value_isPushout j (K := K)).map (tensorRight (Δ[1] : SSet.{0}))).inr_desc
    _ _ _

private theorem deformation_time_zero (h₀ : timeSlice K 0 ≫ H = 𝟙 K) :
    timeSlice (V (K := K) j) 0 ≫ deformation j H = 𝟙 _ := by
  apply (ReducedCylinder.value_isPushout j (K := K)).hom_ext
  · rw [← Category.assoc, timeSlice_naturality, Category.assoc, deformation_cylinder,
      Category.comp_id]
    apply NatTrans.ext
    funext q z
    exact congrArg (fun k ↦ (cylinder j).app q (z.1, k))
      (congrFun (NatTrans.congr_app h₀ q) z.2)
  · rw [← Category.assoc, timeSlice_naturality, Category.assoc, deformation_boundary]
    change timeSlice A 0 ≫ fst A (Δ[1] : SSet.{0}) ≫ boundary (K := K) j = _
    rw [← Category.assoc, DaggerActualRigidificationRelativeDirectedHomotopy.timeSlice_fst,
      Category.id_comp, Category.comp_id]

private theorem deformation_time_one (h₁ : timeSlice K 1 ≫ H = SSet.const v) :
    timeSlice (V (K := K) j) 1 ≫ deformation j H = augmentation j ≫ sectionAt j v := by
  apply (ReducedCylinder.value_isPushout j (K := K)).hom_ext
  · rw [← Category.assoc, timeSlice_naturality, Category.assoc, deformation_cylinder,
      ← Category.assoc, cylinder_augmentation]
    apply NatTrans.ext
    funext q z
    exact congrArg (fun k ↦ (cylinder j).app q (z.1, k))
      (congrFun (NatTrans.congr_app h₁ q) z.2)
  · rw [← Category.assoc, timeSlice_naturality, Category.assoc, deformation_boundary,
      ← Category.assoc]
    change timeSlice A 1 ≫ fst A (Δ[1] : SSet.{0}) ≫ boundary (K := K) j =
      (boundary j ≫ augmentation j) ≫ sectionAt j v
    rw [boundary_augmentation, boundary_section, ← Category.assoc,
      DaggerActualRigidificationRelativeDirectedHomotopy.timeSlice_fst, Category.id_comp]

/-- The original rigidification object corresponding to a collapsed boundary vertex. -/
def boundaryObject (z : A.obj (op ⦋0⦌)) : (rigidification.obj (V (K := K) j)).Obj :=
  vertexEquiv _ ((boundary j).app (op ⦋0⦌) z)

private theorem deformation_boundaryLine (z : A.obj (op ⦋0⦌)) :
    vertexLine (V (K := K) j) (boundaryObject j z) ≫ deformation j H =
      SSet.const ((vertexEquiv (V (K := K) j)).symm (boundaryObject j z)) := by
  let d := boundary (K := K) j
  have hline : vertexLine (V (K := K) j) (boundaryObject j z) =
      vertexLine A (vertexEquiv A z) ≫ (d ▷ (Δ[1] : SSet.{0})) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [vertexLine, boundaryObject, SSet.const_comp, d]
    · simp [vertexLine, boundaryObject]
  rw [hline, Category.assoc, deformation_boundary]
  change (vertexLine A (vertexEquiv A z) ≫ fst A (Δ[1] : SSet.{0})) ≫ d = _
  simp only [vertexLine, lift_fst, SSet.const_comp, boundaryObject, Equiv.symm_apply_apply]
  dsimp only [d]

/-- The literal augmentation of a directedly contractible parameter is
weak on each original rigidification Hom between collapsed boundary vertices. -/
theorem augmentation_endpointHom_weak (h₀ : timeSlice K 0 ≫ H = 𝟙 K)
    (h₁ : timeSlice K 1 ≫ H = SSet.const v) (x y : A.obj (op ⦋0⦌)) :
    WeakEquivalence ((rigidification.map (augmentation (K := K) j)).map
      (boundaryObject j x) (boundaryObject j y)) := by
  have hend := DaggerActualRigidificationRelativeDirectedHomotopy.endomorphism_GW
    (V (K := K) j) (deformation j H) (augmentation j ≫ sectionAt j v)
    (deformation_time_zero j H h₀) (deformation_time_one j v H h₁)
    (boundaryObject j x) (boundaryObject j y)
    (deformation_boundaryLine j H x) (deformation_boundaryLine j H y)
  let r : RetractArrow (augmentation (K := K) j)
      (augmentation (K := K) j ≫ sectionAt j v) :=
    { i := Arrow.homMk (𝟙 _) (sectionAt j v) (by simp)
      r := Arrow.homMk (𝟙 _) (augmentation (K := K) j) (by simp [Category.assoc, section_augmentation])
      retract := by ext <;> simp [section_augmentation] }
  let h := r.map rigidification
  have hi : h.i.left = 𝟙 (rigidification.obj (V (K := K) j)) := rigidification.map_id _
  have hweak : WeakEquivalence
      ((rigidification.map (augmentation j ≫ sectionAt j v)).map
        (h.i.left.obj (boundaryObject j x)) (h.i.left.obj (boundaryObject j y))) := by
    rw [hi]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hend
  exact ⟨MorphismProperty.of_retract
    (DaggerModels.OriginalOrdinaryHomRetracts.homRetract h
      (boundaryObject j x) (boundaryObject j y))
    ((weakEquivalence_iff _).mp hweak)⟩

end

end DaggerModels.PartII.ReducedCylinderDirectedContraction
