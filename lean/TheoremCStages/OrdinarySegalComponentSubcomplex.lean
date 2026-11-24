import NativeConstantProjectionSubcomplexFibration
import NativeSubcomplexWeakRestriction
import OriginalFullVertexSubcomplex

/-!
# Component-saturated subcomplexes used for ordinary Segal equivalence arrows

Reuse the existing full-vertex subcomplex, the native constant-projection
fibration theorem, and native right properness. A subset of connected components
selects a literal subcomplex whose inclusion is a Kan fibration, even before
assuming the ambient simplicial set is Kan. Weak maps restrict to weak maps when
the selected source components are exactly the preimage of the target components.

This is infrastructure for Rezk Sections 6 and 11. It does not identify the
components of coherent isomorphisms with the isomorphisms of a Segal homotopy
category, and does not assert the missing CSS-to-DK comparison.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.OrdinarySegalComponentSubcomplex

noncomputable section

/-- Retain precisely the simplices whose vertices lie in the selected components. -/
def selected (X : SSet.{u}) (U : Set X.π₀) : X.Subcomplex :=
  DaggerOriginalFullVertexSubcomplex.fullVertexSubcomplex X
    {x | SSet.π₀.mk x ∈ U}

/-- A single vertex suffices, since all vertices of a simplex have the same component. -/
theorem mem_selected_iff (X : SSet.{u}) (U : Set X.π₀)
    (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    x ∈ (selected X U).obj q ↔ DaggerUnitaryDiscrete.simplexComponent X q x ∈ U := by
  constructor
  · intro h
    exact h (⦋0⦌.const q.unop 0)
  · intro h α
    change SSet.π₀.mk (X.map α.op x) ∈ U
    change SSet.π₀.mk (X.map (⦋0⦌.const q.unop 0).op x) ∈ U at h
    rw [SSet.π₀.congr_mk_map x α (⦋0⦌.const q.unop 0)]
    exact h

/-- The component projection is the existing original map to the constant component set. -/
def componentProjection (X : SSet.{u}) : X ⟶ DaggerUnitaryDiscrete.constSSet X.π₀ :=
  DaggerUnitaryDiscrete.componentsToHom X X.π₀ id

/-- The selected subcomplex is cut out by the actual component projection. -/
theorem mem_selected_projection (X : SSet.{u}) (U : Set X.π₀)
    (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    x ∈ (selected X U).obj q ↔ (componentProjection X).app q x ∈ U :=
  mem_selected_iff X U q x

/-- The inclusion of any union of components is an actual Kan fibration. -/
theorem inclusion_fibration (X : SSet.{u}) (U : Set X.π₀) :
    Fibration (selected X U).ι :=
  DaggerNativeConstantProjectionSubcomplexFibration.fibration
    (selected X U) (componentProjection X) U (mem_selected_projection X U)

/-- A union of components of a Kan complex is itself Kan. -/
theorem selected_isFibrant (X : SSet.{u}) [IsFibrant X] (U : Set X.π₀) :
    IsFibrant (selected X U).toSSet := by
  have : Fibration (selected X U).ι := inclusion_fibration X U
  exact isFibrant_of_fibration (selected X U).ι

/-- Applying a simplicial map commutes with the original simplex-component assignment. -/
theorem simplexComponent_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    DaggerUnitaryDiscrete.simplexComponent Y q (f.app q x) =
      SSet.mapπ₀ f (DaggerUnitaryDiscrete.simplexComponent X q x) := by
  change SSet.π₀.mk (Y.map (⦋0⦌.const q.unop 0).op (f.app q x)) =
    SSet.mapπ₀ f (SSet.π₀.mk (X.map (⦋0⦌.const q.unop 0).op x))
  rw [SSet.mapπ₀_mk]
  exact congrArg SSet.π₀.mk
    (congrFun (f.naturality (⦋0⦌.const q.unop 0).op) x).symm

/-- The restricted map retains the literal original map in every degree. -/
def restrict {X Y : SSet.{u}} (f : X ⟶ Y) (U : Set X.π₀) (V : Set Y.π₀)
    (h : ∀ c ∈ U, SSet.mapπ₀ f c ∈ V) :
    (selected X U).toSSet ⟶ (selected Y V).toSSet :=
  SSet.Subcomplex.lift ((selected X U).ι ≫ f) (by
    intro q y hy
    obtain ⟨x, rfl⟩ := hy
    rw [mem_selected_iff, simplexComponent_map]
    exact h _ ((mem_selected_iff X U q x.val).mp x.property))

/-- Restriction commutes with the actual inclusions, without changing the map. -/
theorem restrict_inclusion {X Y : SSet.{u}} (f : X ⟶ Y)
    (U : Set X.π₀) (V : Set Y.π₀) (h : ∀ c ∈ U, SSet.mapπ₀ f c ∈ V) :
    restrict f U V h ≫ (selected Y V).ι = (selected X U).ι ≫ f :=
  SSet.Subcomplex.lift_ι _ _

/-- Exact preimage components give the strict pullback of the original map. -/
theorem restrict_isPullback {X Y : SSet.{u}} (f : X ⟶ Y) (V : Set Y.π₀) :
    CategoryTheory.IsPullback
      (restrict f (SSet.mapπ₀ f ⁻¹' V) V (fun _ h ↦ h))
      (selected X (SSet.mapπ₀ f ⁻¹' V)).ι (selected Y V).ι f := by
  apply DaggerNativeSubcomplexWeakRestriction.isPullback f
    (selected X (SSet.mapπ₀ f ⁻¹' V)) (selected Y V)
    (restrict f (SSet.mapπ₀ f ⁻¹' V) V (fun _ h ↦ h))
    (restrict_inclusion f _ _ _)
  intro q x
  rw [mem_selected_iff, mem_selected_iff, simplexComponent_map]
  rfl

/-- An actual Kan weak equivalence restricts to any corresponding union of components. -/
theorem restrict_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence f] (V : Set Y.π₀) :
    WeakEquivalence (restrict f (SSet.mapπ₀ f ⁻¹' V) V (fun _ h ↦ h)) := by
  have : Fibration (selected Y V).ι := inclusion_fibration Y V
  exact DaggerSSetRightProper.weakEquivalence_of_isPullback (restrict_isPullback f V)

#print axioms inclusion_fibration
#print axioms selected_isFibrant
#print axioms restrict_isPullback
#print axioms restrict_weakEquivalence

end

end DaggerModels.PartII.OrdinarySegalComponentSubcomplex
