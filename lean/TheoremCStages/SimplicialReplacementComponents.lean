import NativeSimplicialReplacement
import NativePiZeroFamilyEquivalence
import NativeRowwiseWeakEvaluation
import OriginalUnitaryDiscreteConstantRecovered
import OriginalSimplicialPiZeroWeakEquivalence
import SimplicialSetLocalSystemFibration

/-!
# Components of the full simplicial replacement

Each original replacement row has components indexed by an entire base
chain and a component of the value at its initial object. These row
equivalences are natural for every horizontal operator and identify the
actual component projection with the local-system projection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerNativeSimplicialReplacementCells (first initialArrow family horizontal)
open DaggerNativePiZeroFamilyEquivalence
open DaggerUnitaryDiscrete (constSSet constPiZeroEquiv)

universe u

namespace DaggerModels.PartII.SimplicialReplacementComponents

open SimplicialSetLocalSystem
open DaggerNativeSimplicialReplacement (replacement projection)
open DaggerNativeRowwiseWeakEvaluation (componentMap)

noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})

/-- The original rowwise component equivalence, keeping every complete
base chain and the component of its first-object value. -/
def rowEquiv (q : SimplexCategoryᵒᵖ) :
    ((replacement G).obj q).π₀ ≃
      (localSystem (G ⋙ SSet.π₀Functor)).obj q :=
  familyComponentsEquiv _ (family G q)

/-- All row equivalences commute with the original horizontal
replacement operators, including their initial-arrow transports. -/
def replacementComponentsIso :
    (replacement G ⋙ SSet.π₀Functor : SSet.{u}) ≅
      localSystem (G ⋙ SSet.π₀Functor) :=
  NatIso.ofComponents (fun q ↦ (rowEquiv G q).toIso) (by
    intro q r α
    funext z
    obtain ⟨⟨c, x⟩, rfl⟩ := SSet.π₀.mk_surjective z
    change (rowEquiv G r)
        (SSet.mapπ₀ ((replacement G).map α) (SSet.π₀.mk ⟨c, x⟩)) =
      (localSystem (G ⋙ SSet.π₀Functor)).map α
        ((rowEquiv G q) (SSet.π₀.mk ⟨c, x⟩))
    rw [SSet.mapπ₀_mk]
    rfl)

/-- Components of the vertically constant original nerve row are the
same original set of base chains. -/
def targetRowEquiv (q : SimplexCategoryᵒᵖ) :
    ((DaggerNerveTheoremA.outerDegreeConstant (nerve C)).obj q).π₀ ≃
      (nerve C).obj q := by
  change (constSSet ((nerve C).obj q)).π₀ ≃ (nerve C).obj q
  exact constPiZeroEquiv _

/-- The target component equivalences preserve all original chain
restrictions, including degeneracies. -/
def targetComponentsIso :
    (DaggerNerveTheoremA.outerDegreeConstant (nerve C) ⋙
      SSet.π₀Functor : SSet.{u}) ≅ nerve C :=
  NatIso.ofComponents (fun q ↦ (targetRowEquiv (C := C) q).toIso) (by
    intro q r α
    funext z
    obtain ⟨c, rfl⟩ := SSet.π₀.mk_surjective z
    rfl)

/-- Under the two exact component isomorphisms, the actual original
replacement projection is the local-system projection. -/
theorem projection_components_square :
    (replacementComponentsIso G).hom ≫ projection (G ⋙ SSet.π₀Functor) =
      componentMap (DaggerNativeSimplicialReplacement.projection G) ≫
        (targetComponentsIso (C := C)).hom := by
  apply NatTrans.ext
  funext q z
  obtain ⟨⟨c, x⟩, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

/-- Weak value transports give bijective component transports and hence
a fibration for the actual component map of the original projection. -/
theorem projection_componentMap_fibration
    (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b), WeakEquivalence (G.map f)) :
    Fibration (C := SSet.{u})
      (componentMap (DaggerNativeSimplicialReplacement.projection G)) := by
  have hL : ∀ ⦃a b : C⦄ (f : a ⟶ b),
      Function.Bijective ((G ⋙ SSet.π₀Functor).map f) := by
    intro a b f
    change Function.Bijective (SSet.mapπ₀ (G.map f))
    have : WeakEquivalence (G.map f) := hG f
    exact DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero _
  let a : Arrow.mk (componentMap (DaggerNativeSimplicialReplacement.projection G)) ≅
      Arrow.mk (projection (G ⋙ SSet.π₀Functor)) :=
    Arrow.isoMk (replacementComponentsIso G) (targetComponentsIso (C := C))
      (projection_components_square G)
  have hp : Fibration (projection (G ⋙ SSet.π₀Functor)) :=
    SimplicialSetLocalSystemFibration.projection_fibration
      (G ⋙ SSet.π₀Functor) hL
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff a).mpr ((fibration_iff _).mp hp))

#print axioms replacementComponentsIso
#print axioms targetComponentsIso
#print axioms projection_components_square
#print axioms projection_componentMap_fibration

end
end DaggerModels.PartII.SimplicialReplacementComponents
