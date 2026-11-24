import DaggerModelsPartII.BoundaryNecklaceComma
import ActualRigidificationRelativeDirectedHomotopy
import OriginalOrdinaryHomRetractsReconciled
import ActualNecklaceConeGadgetComparison
import NativeGroupoidCompletionNerveBaseCases

/-! Keep the actual ordered Hom through a relative directed retraction. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open EnrichedCategory HomotopicalAlgebra MorphismProperty DaggerChosenRigidificationNecklace
open DaggerModels.OrdinaryRigidification DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerActualRigidificationDirectedIntervalObjects
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointCoverRigidification

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev zero := op (⦋0⦌ : SimplexCategory)

private abbrev boundaryObject (U : Under B) (z : B.obj zero) :=
  vertexEquiv U.right (U.hom.app zero z)

variable {U V : Under B} (ρ : U ⟶ V) (σ : V ⟶ U)
variable (hσ : σ ≫ ρ = 𝟙 V)
variable (H : U.right ⊗ (Δ[1] : SSet.{0}) ⟶ U.right)
variable (h₀ : timeSlice U.right 0 ≫ H = 𝟙 U.right)
variable (h₁ : timeSlice U.right 1 ≫ H = ρ.right ≫ σ.right)
variable (hB : (U.hom ▷ (Δ[1] : SSet.{0})) ≫ H = fst B (Δ[1] : SSet.{0}) ≫ U.hom)

include hB in
private theorem boundaryLine (z : B.obj zero) :
    vertexLine U.right (boundaryObject U z) ≫ H =
      SSet.const ((vertexEquiv U.right).symm (boundaryObject U z)) := by
  have hline : vertexLine U.right (boundaryObject U z) =
      vertexLine B (vertexEquiv B z) ≫ (U.hom ▷ (Δ[1] : SSet.{0})) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [vertexLine, boundaryObject, SSet.const_comp]
    · simp [vertexLine, boundaryObject]
  rw [hline, Category.assoc, hB]
  change (vertexLine B (vertexEquiv B z) ≫ fst B (Δ[1] : SSet.{0})) ≫ U.hom = _
  simp only [vertexLine, lift_fst, SSet.const_comp, boundaryObject, Equiv.symm_apply_apply]

include hσ h₀ h₁ hB in
/-- A directed retraction fixing the ordered boundary gives a Kan weak
map on the genuine rigidification Hom of its two boundary vertices. -/
theorem endpointHom_weak (z₀ z₁ : B.obj zero) :
    WeakEquivalence ((rigidification.map ρ.right).map
      (boundaryObject U z₀) (boundaryObject U z₁)) := by
  have hs : σ.right ≫ ρ.right = 𝟙 V.right := congrArg (fun f ↦ f.right) hσ
  have hend := DaggerActualRigidificationRelativeDirectedHomotopy.endomorphism_GW
    U.right H (ρ.right ≫ σ.right) h₀ h₁ (boundaryObject U z₀) (boundaryObject U z₁)
    (boundaryLine H hB z₀) (boundaryLine H hB z₁)
  let r : RetractArrow ρ.right (ρ.right ≫ σ.right) :=
    { i := Arrow.homMk (𝟙 _) σ.right (by simp)
      r := Arrow.homMk (𝟙 _) ρ.right (by simp [Category.assoc, hs])
      retract := by ext <;> simp [hs] }
  let h := r.map rigidification
  have hi : h.i.left = 𝟙 (rigidification.obj U.right) := rigidification.map_id _
  have hw : WeakEquivalence
      ((rigidification.map (ρ.right ≫ σ.right)).map
        (h.i.left.obj (boundaryObject U z₀)) (h.i.left.obj (boundaryObject U z₁))) := by
    rw [hi]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hend
  exact ⟨MorphismProperty.of_retract
    (DaggerModels.OriginalOrdinaryHomRetracts.homRetract h (boundaryObject U z₀)
      (boundaryObject U z₁))
    ((weakEquivalence_iff _).mp hw)⟩

private abbrev firstBoundary : B.obj zero := SSet.yonedaEquiv SSet.boundary₁.ι₀
private abbrev lastBoundary : B.obj zero := SSet.yonedaEquiv SSet.boundary₁.ι₁

private theorem boundaryObject_natural (z : B.obj zero) :
    (rigidification.map ρ.right).obj (boundaryObject U z) = boundaryObject V z := by
  have he := congrFun (NatTrans.congr_app (Under.w ρ) zero) z
  exact (vertexEquiv_naturality _ _).trans (congrArg (vertexEquiv V.right) he)

include hσ h₀ h₁ hB in
/-- The internal necklace category of the covered component is weakly
contractible if the actual ordered Hom of the original component is. -/
theorem fiber_point_GW
    (h : GW (pointMap (RV V.right (BoundaryNecklaceComma.first V) ⟶[SSet.{0}]
      RV V.right (BoundaryNecklaceComma.last V)))) :
    GW (pointMap (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder U))) := by
  let f := (rigidification.map ρ.right).map
    (boundaryObject U firstBoundary) (boundaryObject U lastBoundary)
  letI : WeakEquivalence (C := SSet.{0}) f :=
    endpointHom_weak ρ σ hσ H h₀ h₁ hB firstBoundary lastBoundary
  rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq] at h
  letI : WeakEquivalence (C := SSet.{0}) (pointMap
      ((rigidification.map ρ.right).obj (boundaryObject U firstBoundary) ⟶[SSet.{0}]
        (rigidification.map ρ.right).obj (boundaryObject U lastBoundary))) := by
    rw [boundaryObject_natural ρ, boundaryObject_natural ρ]
    exact (weakEquivalence_iff_GW _).mpr h
  have h1 : WeakEquivalence (C := SSet.{0}) (f ≫ pointMap _) := inferInstance
  have h2 : GW (pointMap
      (boundaryObject U firstBoundary ⟶[SSet.{0}] boundaryObject U lastBoundary)) := by
    apply (weakEquivalence_iff_GW _).mp
    rw [← pointIsTerminal.hom_ext (f ≫ pointMap _) (pointMap _)]
    exact h1
  have h3 : GW (pointMap (nerve (NecklacesOver U.right (BoundaryNecklaceComma.first U)
      (BoundaryNecklaceComma.last U)))) := by
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact DaggerActualNecklaceConeGadgetComparison.necklace_point_GW_of_original_hom _ _ _ h2
  let g := nerveMap (BoundaryNecklaceComma.equivalence U).functor
  letI : WeakEquivalence (C := SSet.{0}) g :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  letI : WeakEquivalence (C := SSet.{0}) (pointMap (nerve
      (NecklacesOver U.right (BoundaryNecklaceComma.first U) (BoundaryNecklaceComma.last U)))) :=
    (weakEquivalence_iff_GW _).mpr h3
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (g ≫ pointMap _) (pointMap _)]
  infer_instance

end

end DaggerModels.PartII.JTEndpointCoverRigidification
