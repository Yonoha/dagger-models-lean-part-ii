import SimplicialReplacementBasedPiOperators
import SimplicialReplacementComponents
import BasedPiCartesianProjection
import NativePiKanReedyDiagonal
import NativeReedyRelativeComponentFibration

/-!
# Relative diagonal fibration for the original simplicial replacement

The relative Reedy replacement is applied to the actual original
replacement projection. Component and positive based homotopy-group
conditions are transported through its two rowwise weak units.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerOriginalProductGadget DaggerSSetGluing
open DaggerNativeSimplicialReplacement (replacement projection)
open DaggerNativeReedyRelativeReplacement
open DaggerNativeHorizontalPiSections (rowProjection)
open DaggerNativeComponentMatchingNaturality (componentMap)
open DaggerNativeReedyRelativeComponentFibration (component_fibration_iff)
open DaggerModels.PartII.SimplicialReplacementBasedPiOperators
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialReplacementRelativeDiagonalFibration

noncomputable section

variable {C : Type u} [Category.{u} C]

private def pointDiagram : C ⥤ SSet.{u} :=
  (Functor.const C).obj (Δ[0] : SSet.{u})

private instance pointDiagram_value_fibrant (a : C) :
    IsFibrant ((pointDiagram (C := C)).obj a) := by
  change IsFibrant (Δ[0] : SSet.{u})
  infer_instance

private theorem pointDiagram_map_weak ⦃a b : C⦄ (g : a ⟶ b) :
    WeakEquivalence ((pointDiagram (C := C)).map g) := by
  change WeakEquivalence (𝟙 (Δ[0] : SSet.{u}))
  infer_instance

private theorem pointDiagram_point_weak :
    WeakEquivalence (pointMap (Δ[0] : SSet.{u})) := by
  haveI : IsIso (pointMap (Δ[0] : SSet.{u})) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
      pointIsTerminal _
  infer_instance

private theorem pointDiagram_projection_row_weak (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((projection (pointDiagram (C := C))).app q) := by
  apply (weakEquivalence_iff_GW _).mpr
  apply DaggerNativeSimplicialReplacement.projection_row_GW
  intro c
  change GW (pointMap (Δ[0] : SSet.{u}))
  exact (weakEquivalence_iff_GW _).mp pointDiagram_point_weak

/-- Every operator of the literal vertically constant original nerve
acts bijectively on positive based homotopy groups. -/
theorem base_operator_mapπ_bijective (n : ℕ)
    ⦃q r : SimplexCategoryᵒᵖ⦄ (α : q ⟶ r)
    (x : ((DaggerNerveTheoremA.outerDegreeConstant (nerve C)).obj q) _⦋0⦌) :
    Function.Bijective
      (SSet.KanComplex.mapπ
        ((DaggerNerveTheoremA.outerDegreeConstant (nerve C)).map α)
        (n + 1) x _ rfl) := by
  let G₀ := pointDiagram (C := C)
  letI : ∀ a, IsFibrant (G₀.obj a) := fun a ↦ pointDiagram_value_fibrant a
  letI : ∀ q, IsFibrant ((replacement G₀).obj q) := fun q ↦
    replacementRowFibrant G₀ q
  letI : ∀ q, IsFibrant
      ((DaggerNerveTheoremA.outerDegreeConstant (nerve C)).obj q) := by
    intro q
    change IsFibrant (DaggerUnitaryDiscrete.constSSet ((nerve C).obj q))
    infer_instance
  exact DaggerBasedPiOperatorWeakTransfer.operator_mapπ_bijective
    (projection G₀) (pointDiagram_projection_row_weak (C := C)) (n + 1)
    (by
      intro q r α y
      exact operator_mapπ_bijective_at G₀ n pointDiagram_map_weak α y) α x

variable (G : C ⥤ SSet.{u}) [∀ a, IsFibrant (G.obj a)]
variable (hG : ∀ ⦃a b : C⦄ (g : a ⟶ b), WeakEquivalence (G.map g))

private def originalArrow : Arrow BiSSet.{u} := Arrow.mk (projection G)

private theorem original_total_row_fibrant (q : SimplexCategoryᵒᵖ) :
    IsFibrant ((replacement G).obj q) := replacementRowFibrant G q

private theorem original_base_row_fibrant (q : SimplexCategoryᵒᵖ) :
    IsFibrant ((DaggerNerveTheoremA.outerDegreeConstant (nerve C)).obj q) := by
  change IsFibrant (DaggerUnitaryDiscrete.constSSet ((nerve C).obj q))
  infer_instance

include hG in
/-- Positive based projection fibrations on the total and base of the
actual relative Reedy replacement, with no action-triviality premise. -/
theorem replaced_total_basedProjection_fibration (n : ℕ) :
    Fibration (C := SSet.{u})
      (rowProjection (relativeReplacement.obj (originalArrow G)).left (n + 1)) := by
  let f := originalArrow G
  letI : ∀ q, IsFibrant (f.left.obj q) :=
    fun q ↦ original_total_row_fibrant G q
  letI : ∀ q, IsFibrant ((relativeReplacement.obj f).left.obj q) :=
    fun q ↦ total_rows_Kan f q
  have hw (q : SimplexCategoryᵒᵖ) :
      WeakEquivalence ((totalUnit f).app q) :=
    ((mem_trivialCofibrations_iff _).mp (totalUnit_row_trivial f q)).2
  exact DaggerBasedPiCartesianProjection.target_basedProjection_fibration
    (totalUnit f) hw (n + 1)
    (by
      intro q r α x
      exact operator_mapπ_bijective_at G n hG α x)

omit [∀ a, IsFibrant (G.obj a)] in
theorem replaced_base_basedProjection_fibration (n : ℕ) :
    Fibration (C := SSet.{u})
      (rowProjection (relativeReplacement.obj (originalArrow G)).right (n + 1)) := by
  let f := originalArrow G
  letI : ∀ q, IsFibrant (f.right.obj q) :=
    fun q ↦ original_base_row_fibrant (C := C) q
  letI : ∀ q, IsFibrant ((relativeReplacement.obj f).right.obj q) :=
    fun q ↦ base_rows_Kan f q
  have hw (q : SimplexCategoryᵒᵖ) :
      WeakEquivalence ((baseUnit f).app q) :=
    ((mem_trivialCofibrations_iff _).mp (baseUnit_row_trivial f q)).2
  exact DaggerBasedPiCartesianProjection.target_basedProjection_fibration
    (baseUnit f) hw (n + 1)
    (by
      intro q r α x
      exact base_operator_mapπ_bijective (C := C) n α x)

include hG in
/-- The diagonal of the relative Reedy replacement of the actual
original simplicial-replacement projection is a Kan fibration. -/
theorem relative_diagonal_fibration :
    Fibration (C := SSet.{u})
      (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map
        (relativeReplacement.obj (originalArrow G)).hom) := by
  let f := originalArrow G
  have hc : Fibration (C := SSet.{u})
      (componentMap (relativeReplacement.obj f).hom) :=
    (component_fibration_iff f).mp
      (SimplicialReplacementComponents.projection_componentMap_fibration G hG)
  letI : Fibration (C := SSet.{u})
      (componentMap (relativeReplacement.obj f).hom) := hc
  exact DaggerNativePiKanReedyDiagonal.diagonal_fibration
    (relativeReplacement.obj f).hom (projection_reedy f)
    (total_reedy f) (base_reedy f)
    (fun n ↦ replaced_total_basedProjection_fibration G hG n)
    (fun n ↦ replaced_base_basedProjection_fibration G n)

#print axioms base_operator_mapπ_bijective
#print axioms replaced_total_basedProjection_fibration
#print axioms replaced_base_basedProjection_fibration
#print axioms relative_diagonal_fibration

end
end DaggerModels.PartII.SimplicialReplacementRelativeDiagonalFibration
