import OrdinarySegalComponentSubcomplex

/-!
# Component image of a simplicial map

The literal map factors through the union of target components it meets. The
factor is surjective on components, and the inclusion of that union is
injective on components. If the original map is a Kan fibration, so is the
factor. No vertex-surjectivity or weak-equivalence assertion is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.OrdinarySegalComponentImage

noncomputable section

open OrdinarySegalComponentSubcomplex

/-- The target components met by the original map. -/
def imageComponents {X Y : SSet.{u}} (f : X ⟶ Y) : Set Y.π₀ :=
  Set.range (SSet.mapπ₀ f)

/-- The component-saturated image inside the original target. -/
def componentImage {X Y : SSet.{u}} (f : X ⟶ Y) : Y.Subcomplex :=
  selected Y (imageComponents f)

/-- At degree zero, selection is exactly membership of the original component. -/
theorem mem_selected_zero (X : SSet.{u}) (U : Set X.π₀)
    (x : X.obj (op ⦋0⦌)) :
    x ∈ (selected X U).obj (op ⦋0⦌) ↔ SSet.π₀.mk x ∈ U := by
  rw [mem_selected_iff]
  change SSet.π₀.mk (X.map (⦋0⦌.const ⦋0⦌ 0).op x) ∈ U ↔ _
  have h : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  simp only [h, op_id, FunctorToTypes.map_id_apply]

/-- The original map lands in the actual component-saturated image. -/
def factor {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ (componentImage f).toSSet :=
  SSet.Subcomplex.lift f (by
    intro q y hy
    obtain ⟨x, rfl⟩ := hy
    rw [componentImage, mem_selected_iff, simplexComponent_map]
    exact ⟨DaggerUnitaryDiscrete.simplexComponent X q x, rfl⟩)

/-- The factor and the literal inclusion recover the original map. -/
theorem factor_inclusion {X Y : SSet.{u}} (f : X ⟶ Y) :
    factor f ≫ (componentImage f).ι = f :=
  SSet.Subcomplex.lift_ι _ _

/-- Inclusion of a union of components is injective on connected components. -/
theorem selected_inclusion_injective (Y : SSet.{u}) (V : Set Y.π₀) :
    Function.Injective (SSet.mapπ₀ (selected Y V).ι) := by
  apply SSet.π₀.subsingleton_π₀_of_subcomplex
  · intro e
    rw [mem_selected_zero, mem_selected_zero]
    rw [SSet.π₀.sound e rfl rfl]
  · intro e hleft _
    rw [mem_selected_iff]
    have hfirst : SSet.π₀.mk (Y.δ 1 e) ∈ V :=
      (mem_selected_zero Y V _).mp hleft
    have hcomponent :
        DaggerUnitaryDiscrete.simplexComponent Y (op ⦋1⦌) e =
          SSet.π₀.mk (Y.δ 1 e) := by
      change SSet.π₀.mk (Y.map (⦋0⦌.const ⦋1⦌ 0).op e) =
        SSet.π₀.mk (Y.map (SimplexCategory.δ (1 : Fin 2)).op e)
      exact SSet.π₀.congr_mk_map e _ _
    rw [hcomponent]
    exact hfirst

/-- The image inclusion is injective on connected components. -/
theorem componentImage_inclusion_injective {X Y : SSet.{u}} (f : X ⟶ Y) :
    Function.Injective (SSet.mapπ₀ (componentImage f).ι) :=
  selected_inclusion_injective Y (imageComponents f)

/-- Every component of the saturated image is met by the factor. -/
theorem factor_surjective_components {X Y : SSet.{u}} (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (factor f)) := by
  intro c
  obtain ⟨⟨y, hy⟩, rfl⟩ := c.mk_surjective
  have hyImage : SSet.π₀.mk y ∈ imageComponents f :=
    (mem_selected_zero Y (imageComponents f) y).mp hy
  obtain ⟨cx, hcx⟩ := hyImage
  obtain ⟨x, rfl⟩ := cx.mk_surjective
  refine ⟨SSet.π₀.mk x, ?_⟩
  apply componentImage_inclusion_injective f
  calc
    SSet.mapπ₀ (componentImage f).ι
        (SSet.mapπ₀ (factor f) (SSet.π₀.mk x)) =
        SSet.mapπ₀ f (SSet.π₀.mk x) := by
          rw [← SSet.mapπ₀_comp_apply, factor_inclusion]
    _ = SSet.π₀.mk y := hcx
    _ = SSet.mapπ₀ (componentImage f).ι
        (SSet.π₀.mk (⟨y, hy⟩ : (componentImage f).toSSet.obj (op ⦋0⦌))) := rfl

/-- A Kan fibration remains a Kan fibration after narrowing its target to its
component-saturated image. The proof uses monicity of the literal inclusion. -/
theorem factor_fibration {X Y : SSet.{u}} (f : X ⟶ Y) [Fibration f] :
    Fibration (factor f) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  have hf : SSet.modelCategoryQuillen.J.rlp f :=
    (SSet.modelCategoryQuillen.fibration_iff f).mp (inferInstance : Fibration f)
  letI : HasLiftingProperty i f := hf i hi
  constructor
  intro a b sq
  let sqY : CommSq a i f (b ≫ (componentImage f).ι) := ⟨by
    calc
      a ≫ f = (a ≫ factor f) ≫ (componentImage f).ι := by
        simp only [Category.assoc, factor_inclusion]
      _ = (i ≫ b) ≫ (componentImage f).ι :=
        congrArg (fun t => t ≫ (componentImage f).ι) sq.w
      _ = i ≫ (b ≫ (componentImage f).ι) := by rw [Category.assoc]⟩
  haveI : sqY.HasLift := inferInstance
  refine CommSq.HasLift.mk' ⟨sqY.lift, sqY.fac_left, ?_⟩
  apply (cancel_mono (componentImage f).ι).mp
  rw [Category.assoc, factor_inclusion]
  exact sqY.fac_right

#print axioms mem_selected_zero
#print axioms factor_inclusion
#print axioms componentImage_inclusion_injective
#print axioms factor_surjective_components
#print axioms factor_fibration

end

end DaggerModels.PartII.OrdinarySegalComponentImage
