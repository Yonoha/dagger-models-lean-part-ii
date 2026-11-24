import DaggerModelsPartII.ReducedGroupoidCylinderAugmentation
import DaggerModelsPartII.JTParameterContraction
import ActualRigidificationRelativeDirectedHomotopy
import DaggerModels.RigidificationVertices
import OriginalOrdinaryHomRetractsReconciled

/-!
# Relative deformation of the general reduced groupoid cylinder

The directed deformation of the SAME reduced-cylinder pushout fixes the
entire collapsed boundary for an arbitrary boundary map. The actual original
rigidification Hom of its augmentation is weak at two chosen boundary
vertices, including when the boundary map is nonmonic.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra MorphismProperty
open Opposite Simplicial
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerActualRigidificationDirectedIntervalObjects
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ReducedCylinderEndpointHomWeak

open ReducedCylinder ReducedGroupoidCylinderAugmentation
open JTParameterContraction

noncomputable section

private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev V {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :=
  (ReducedCylinder.value j).obj (J k)

private local instance : PreservesColimitsOfSize.{0, 0}
    (tensorRight (Δ[1] : SSet.{0})) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{0, 0}
      (tensorLeft (Δ[1] : SSet.{0})) := inferInstance
  exact preservesColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight (Δ[1] : SSet.{0}))

/-- The full parameter map constant at vertex zero factors through the
same pointwise vertex section used by the original augmentation. -/
private theorem constantAt_zero (k : SimplexCategory) :
    constantAt k 0 =
      SSet.stdSimplex.isTerminalObj₀.from (J k) ≫ parameterVertex k 0 := by
  apply NatTrans.ext
  funext q z
  rfl

/-- Contract the groupoid coordinate on the uncollapsed cylinder. -/
private def cylinderDeformation {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    (B ⊗ J k) ⊗ (Δ[1] : SSet.{0}) ⟶ V j k :=
  (α_ B (J k) (Δ[1] : SSet.{0})).hom ≫
    (B ◁ contraction k 0) ≫
      (ReducedCylinder.cylinder j).app (J k)

/-- The collapsed boundary remains fixed at every homotopy time. -/
private def boundaryDeformation {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    A ⊗ (Δ[1] : SSet.{0}) ⟶ V j k :=
  fst A (Δ[1] : SSet.{0}) ≫
    (ReducedCylinder.boundary j).app (J k)

private theorem deformation_compat {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    ((j ⊗ₘ 𝟙 (J k)) ▷ (Δ[1] : SSet.{0})) ≫
        cylinderDeformation j k =
      ((fst A (J k)) ▷ (Δ[1] : SSet.{0})) ≫
        boundaryDeformation j k := by
  apply NatTrans.ext
  funext q z
  have hw := congrFun
    (NatTrans.congr_app (ReducedCylinder.value_isPushout j (K := J k)).w q)
      (z.1.1, (contraction k 0).app q (z.1.2, z.2))
  exact hw

/-- Tensoring the pointwise reduced-cylinder pushout with `Δ[1]` and
descending the two compatible deformation legs. -/
def deformation {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    V j k ⊗ (Δ[1] : SSet.{0}) ⟶ V j k :=
  ((ReducedCylinder.value_isPushout j (K := J k)).map
      (tensorRight (Δ[1] : SSet.{0}))).desc
    (cylinderDeformation j k) (boundaryDeformation j k)
    (deformation_compat j k)

/-- The deformation's entire boundary leg is the constant boundary line. -/
theorem deformation_boundary {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    ((ReducedCylinder.boundary j).app (J k) ▷ (Δ[1] : SSet.{0})) ≫
      deformation j k = boundaryDeformation j k :=
  ((ReducedCylinder.value_isPushout j (K := J k)).map
      (tensorRight (Δ[1] : SSet.{0}))).inr_desc _ _ _

/-- The actual uncollapsed leg of the same deformation. -/
theorem deformation_cylinder {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    ((ReducedCylinder.cylinder j).app (J k) ▷ (Δ[1] : SSet.{0})) ≫
      deformation j k = cylinderDeformation j k :=
  ((ReducedCylinder.value_isPushout j (K := J k)).map
      (tensorRight (Δ[1] : SSet.{0}))).inl_desc _ _ _

private theorem cylinder_time_zero {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    timeSlice (B ⊗ J k) 0 ≫ cylinderDeformation j k =
      (ReducedCylinder.cylinder j).app (J k) := by
  apply NatTrans.ext
  funext q z
  have h := congrFun
    (NatTrans.congr_app (contraction_time_zero k 0) q) z.2
  exact congrArg
    (fun v ↦ ((ReducedCylinder.cylinder j).app (J k)).app q (z.1, v)) h

private theorem cylinder_time_one {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    timeSlice (B ⊗ J k) 1 ≫ cylinderDeformation j k =
      fst B (J k) ≫ vertexSection j k := by
  apply NatTrans.ext
  funext q z
  have h := congrFun
    (NatTrans.congr_app (contraction_time_one k 0) q) z.2
  rw [constantAt_zero k] at h
  have hterminal :
      (SSet.stdSimplex.isTerminalObj₀.from (J k)).app q z.2 =
        (SSet.stdSimplex.isTerminalObj₀.from B).app q z.1 :=
    Subsingleton.elim _ _
  change ((ReducedCylinder.cylinder j).app (J k)).app q
      (z.1, (timeSlice (J k) 1 ≫ contraction k 0).app q z.2) =
    ((ReducedCylinder.cylinder j).app (J k)).app q
      (z.1, (SSet.stdSimplex.isTerminalObj₀.from B ≫ parameterVertex k 0).app q z.1)
  rw [h]
  exact congrArg
    (fun v ↦ ((ReducedCylinder.cylinder j).app (J k)).app q
      (z.1, (parameterVertex k 0).app q v)) hterminal

/-- The directed deformation starts at the literal identity of the
pointwise reduced cylinder. -/
theorem deformation_time_zero {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    timeSlice (V j k) 0 ≫ deformation j k = 𝟙 (V j k) := by
  apply (ReducedCylinder.value_isPushout j (K := J k)).hom_ext
  · rw [← Category.assoc, timeSlice_naturality,
      Category.assoc, deformation_cylinder]
    change timeSlice (B ⊗ J k) 0 ≫ cylinderDeformation j k = _
    rw [cylinder_time_zero, Category.comp_id]
  · rw [← Category.assoc, timeSlice_naturality,
      Category.assoc, deformation_boundary]
    change timeSlice A 0 ≫ fst A (Δ[1] : SSet.{0}) ≫
      (ReducedCylinder.boundary j).app (J k) = _
    rw [← Category.assoc,
      DaggerActualRigidificationRelativeDirectedHomotopy.timeSlice_fst,
      Category.id_comp, Category.comp_id]

/-- At time one the map is exactly augmentation followed by the actual
pointwise vertex section. -/
theorem deformation_time_one {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    timeSlice (V j k) 1 ≫ deformation j k =
      augmentation j k ≫ vertexSection j k := by
  apply (ReducedCylinder.value_isPushout j (K := J k)).hom_ext
  · rw [← Category.assoc, timeSlice_naturality,
      Category.assoc, deformation_cylinder]
    change timeSlice (B ⊗ J k) 1 ≫ cylinderDeformation j k = _
    rw [cylinder_time_one, ← Category.assoc, augmentation_cylinder]
  · rw [← Category.assoc, timeSlice_naturality,
      Category.assoc, deformation_boundary,
      ← Category.assoc, augmentation_boundary]
    change timeSlice A 1 ≫ fst A (Δ[1] : SSet.{0}) ≫
      (ReducedCylinder.boundary j).app (J k) = j ≫ vertexSection j k
    rw [boundary_vertexSection]
    rw [← Category.assoc,
      DaggerActualRigidificationRelativeDirectedHomotopy.timeSlice_fst,
      Category.id_comp]

/-- The actual object of rigidification at a specified collapsed-boundary
vertex. The target object after augmentation is the image of `j` at that
same vertex, with no separate point choice. -/
def boundaryObject {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) (z : A.obj (op ⦋0⦌)) :
    (rigidification.obj (V j k)).Obj :=
  vertexEquiv (V j k) (((ReducedCylinder.boundary j).app (J k)).app (op ⦋0⦌) z)

/-- The relative deformation fixes the whole vertical line through every
specified boundary vertex. This is the precise input of `endomorphism_GW`. -/
theorem deformation_boundaryLine {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) (z : A.obj (op ⦋0⦌)) :
    vertexLine (V j k) (boundaryObject j k z) ≫ deformation j k =
      SSet.const ((vertexEquiv (V j k)).symm (boundaryObject j k z)) := by
  let d := (ReducedCylinder.boundary j).app (J k)
  have hline :
      vertexLine (V j k) (boundaryObject j k z) =
        vertexLine A (vertexEquiv A z) ≫ (d ▷ (Δ[1] : SSet.{0})) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [vertexLine, boundaryObject, SSet.const_comp, d]
    · simp [vertexLine, boundaryObject]
  rw [hline, Category.assoc, deformation_boundary]
  change (vertexLine A (vertexEquiv A z) ≫ fst A (Δ[1] : SSet.{0})) ≫ d = _
  simp only [vertexLine, CartesianMonoidalCategory.lift_fst,
    SSet.const_comp, boundaryObject, Equiv.symm_apply_apply]
  dsimp only [d]

/-- The relative directed deformation makes the actual rigidification
endomorphism weak on the two specified boundary objects. -/
theorem endomorphism_endpointHom_GW {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) (z₀ z₁ : A.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW
      ((rigidification.map (augmentation j k ≫ vertexSection j k)).map
        (boundaryObject j k z₀) (boundaryObject j k z₁)) :=
  DaggerActualRigidificationRelativeDirectedHomotopy.endomorphism_GW
    (V j k) (deformation j k) (augmentation j k ≫ vertexSection j k)
    (deformation_time_zero j k) (deformation_time_one j k)
    (boundaryObject j k z₀) (boundaryObject j k z₁)
    (deformation_boundaryLine j k z₀)
    (deformation_boundaryLine j k z₁)

/-- The augmentation arrow is a retract of its directed-deformation endomorphism.
This arrow retract retains both endpoint transports after rigidification. -/
private def augmentationRetract {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    RetractArrow (augmentation j k) (augmentation j k ≫ vertexSection j k) where
  i := Arrow.homMk (𝟙 _) (vertexSection j k) (by simp)
  r := Arrow.homMk (𝟙 _) (augmentation j k) (by
    simp [Category.assoc, vertexSection_augmentation])
  retract := by
    ext <;> simp [vertexSection_augmentation]

/-- The SAME general reduced-cylinder augmentation is weak on the actual
original rigidification Hom of any two collapsed-boundary vertices. No
monomorphism or fibrancy hypothesis is used. -/
theorem augmentation_endpointHom_weak {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) (z₀ z₁ : A.obj (op ⦋0⦌)) :
    WeakEquivalence
      ((rigidification.map (augmentation j k)).map
        (boundaryObject j k z₀) (boundaryObject j k z₁)) := by
  let h := (augmentationRetract j k).map rigidification
  have hi : h.i.left = 𝟙 (rigidification.obj (V j k)) := by
    change rigidification.map (𝟙 (V j k)) = _
    exact rigidification.map_id _
  have hG : WeakEquivalence
      ((rigidification.map (augmentation j k ≫ vertexSection j k)).map
        (h.i.left.obj (boundaryObject j k z₀))
        (h.i.left.obj (boundaryObject j k z₁))) := by
    rw [hi]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (endomorphism_endpointHom_GW j k z₀ z₁)
  exact ⟨MorphismProperty.of_retract
    (DaggerModels.OriginalOrdinaryHomRetracts.homRetract h
      (boundaryObject j k z₀) (boundaryObject j k z₁))
    ((weakEquivalence_iff _).1 hG)⟩

end

end DaggerModels.PartII.ReducedCylinderEndpointHomWeak
