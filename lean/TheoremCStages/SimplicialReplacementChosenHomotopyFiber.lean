import SimplicialReplacementChosenFiber
import SimplicialReplacementRelativeDiagonalFibration
import SimplicialReplacementProjectionRows
import NativeRelativeReedyFibreComparisonWeak

/-!
# Chosen fiber of the relative simplicial-replacement projection

The point is the full constant chain in every outer degree. The final
pullback is over an actual Kan fibration supplied by the relative Reedy
replacement, while the comparison retains both original unit maps.
-/

set_option autoImplicit false
set_option warningAsError true
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement projection diagonalProjection)
open DaggerNativeReedyRelativeReplacement
open DaggerNativeRelativeReedyBisimplicialFibres (imageComparison)
open DaggerSimplicialReplacementChosenFiber
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.SimplicialReplacementChosenHomotopyFiber
noncomputable section

variable {C : Type u} [Category.{u} C]

/-- The actual constant outer point diagram, with the zero simplex in each row. -/
def pointBi : BiSSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Δ[0] : SSet.{u})

/-- Its diagonal is the original zero simplex, by identity components. -/
def pointDiagonalIso : diagonalFunctor.obj pointBi.{u} ≅ (Δ[0] : SSet.{u}) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The unchanged native equality between the diagonal of the vertically
discrete outer nerve and the original full nerve. -/
def baseDiagonalIso :
    diagonalFunctor.obj (DaggerNerveTheoremA.outerDegreeConstant (nerve C)) ≅ nerve C :=
  eqToIso (DaggerNerveTheoremA.diag_outerDegreeConstant (nerve C))

/-- The chosen original constant chain in every bisimplicial row and column. -/
def coherentPoint (c : C) : pointBi.{u} ⟶
    DaggerNerveTheoremA.outerDegreeConstant (nerve C) where
  app q :=
    { app k _ := constantChain c q
      naturality k l β := by funext x; rfl }
  naturality q r α := by
    apply NatTrans.ext
    funext k x
    exact (constantChain_map c α).symm

/-- The diagonal of the coherent bisimplicial point is exactly the chosen
ordinary nerve point, with both diagonal identifications displayed. -/
theorem coherentPoint_diagonal (c : C) :
    pointDiagonalIso.inv ≫ diagonalFunctor.map (coherentPoint c) =
      chainPoint c ≫ (baseDiagonalIso (C := C)).inv := by
  apply NatTrans.ext
  funext q x
  rfl

private def originalArrow (G : C ⥤ SSet.{u}) : Arrow BiSSet.{u} :=
  Arrow.mk (projection G)

/-- The exact old strict fiber uses the diagonal of the original projection
and the same coherent bisimplicial point. -/
def originalFiber (G : C ⥤ SSet.{u}) (c : C) : SSet.{u} :=
  pullback (diagonalFunctor.map (projection G))
    (diagonalFunctor.map (coherentPoint c))

/-- The chosen original value is exactly the strict old diagonal fiber,
including the point-diagonal and base-diagonal isomorphisms. -/
def originalFiberIso (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ≅ originalFiber G c := by
  have h : IsPullback (diagonalInclusion G c)
      (zeroMap (G.obj c) ≫ pointDiagonalIso.inv)
      (diagonalFunctor.map (projection G))
      (diagonalFunctor.map (coherentPoint c)) := by
    apply (diagonalInclusion_isPullback G c).of_iso
      (Iso.refl _) (Iso.refl _) pointDiagonalIso.symm
      (baseDiagonalIso (C := C)).symm
    · simp
    · simp
    · calc
        diagonalProjection G ≫ (baseDiagonalIso (C := C)).inv =
            (diagonalFunctor.map (projection G) ≫
              (baseDiagonalIso (C := C)).hom) ≫
              (baseDiagonalIso (C := C)).inv := rfl
        _ = diagonalFunctor.map (projection G) := by simp
    · exact (coherentPoint_diagonal c).symm
  exact h.isoPullback

/-- The actual strict chosen fiber of the diagonal relative Reedy fibration. -/
def relativeFiber (G : C ⥤ SSet.{u}) (c : C) : SSet.{u} :=
  pullback
    (diagonalFunctor.map (relativeReplacement.obj (originalArrow G)).hom)
    (diagonalFunctor.map (coherentPoint c ≫ baseUnit (originalArrow G)))

/-- This map keeps the original total and base units and the same chosen
point on both sides of the fiber comparison. -/
def chosenFiberComparison (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ⟶ relativeFiber G c :=
  (originalFiberIso G c).hom ≫
    imageComparison diagonalFunctor (originalArrow G) (coherentPoint c)

variable (G : C ⥤ SSet.{u}) [∀ a, IsFibrant (G.obj a)]

/-- The chosen strict-to-relative-fiber map is a weak equivalence. -/
theorem chosenFiberComparison_weak (c : C) :
    WeakEquivalence (chosenFiberComparison G c) := by
  have hr (q : SimplexCategoryᵒᵖ) :
      Fibration ((projection G).app q) :=
    SimplicialReplacementProjectionRows.projection_row_fibration G q
  have hc : WeakEquivalence
      (imageComparison diagonalFunctor (originalArrow G) (coherentPoint c)) :=
    DaggerNativeRelativeReedyFibreComparisonWeak.diagonalComparison_weak
      (originalArrow G) hr (coherentPoint c)
  have : WeakEquivalence
      (imageComparison diagonalFunctor (originalArrow G) (coherentPoint c)) := hc
  change WeakEquivalence
    ((originalFiberIso G c).hom ≫
      imageComparison diagonalFunctor (originalArrow G) (coherentPoint c))
  infer_instance

variable (hG : ∀ ⦃a b : C⦄ (g : a ⟶ b), WeakEquivalence (G.map g))

include hG in
/-- The target of the chosen comparison is a strict fiber of this actual
Kan fibration, so it represents the chosen derived fiber. -/
theorem relative_diagonal_fibration :
    Fibration (diagonalFunctor.map
      (relativeReplacement.obj (originalArrow G)).hom) :=
  SimplicialReplacementRelativeDiagonalFibration.relative_diagonal_fibration G hG

omit [∀ a, IsFibrant (G.obj a)] in
/-- The total unit is weak after diagonalizing its original rowwise weak maps. -/
theorem total_diagonal_unit_weak :
    WeakEquivalence (diagonalFunctor.map (totalUnit (originalArrow G))) := by
  apply DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
  intro q
  exact ((mem_trivialCofibrations_iff _).mp
    (totalUnit_row_trivial (originalArrow G) q)).2

omit [∀ a, IsFibrant (G.obj a)] in
/-- The base unit is weak after diagonalizing its original rowwise weak maps. -/
theorem base_diagonal_unit_weak :
    WeakEquivalence (diagonalFunctor.map (baseUnit (originalArrow G))) := by
  apply DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
  intro q
  exact ((mem_trivialCofibrations_iff _).mp
    (baseUnit_row_trivial (originalArrow G) q)).2

#print axioms chosenFiberComparison_weak
#print axioms relative_diagonal_fibration
#print axioms total_diagonal_unit_weak
#print axioms base_diagonal_unit_weak

end
end DaggerModels.PartII.SimplicialReplacementChosenHomotopyFiber
