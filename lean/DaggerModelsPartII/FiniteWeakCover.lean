import DaggerModelsPartII.FiniteFactorContractibility
import OriginalStandardSSetCylinderRecovered
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-! Finite nullhomotopies can be proved on a weakly equivalent resolution. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteWeakCover

noncomputable section

universe u

private abbrev R : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

/-- Singular realization preserves the Kan weak equivalences. -/
theorem weak_singular {X Y : SSet.{u}} (p : X ⟶ Y) [WeakEquivalence p] :
    WeakEquivalence (R.map p) := by
  have h := (sSetTopAdj.unit.naturality p).symm
  change sSetTopAdj.unit.app X ≫ R.map p = p ≫ sSetTopAdj.unit.app Y at h
  exact weakEquivalence_of_precomp_of_fac h

/-- Precomposition by a weak equivalence detects simplicial homotopy
when the target is Kan. -/
def homotopyOfPrecomp {K A Z : SSet.{u}} [IsFibrant Z]
    (p : K ⟶ A) [WeakEquivalence p] {f g : A ⟶ Z}
    (h : SSet.Homotopy (p ≫ f) (p ≫ g)) : SSet.Homotopy f g := by
  have h' := ((DaggerStandardSSetCylinder.model_iff_literal _ _).mpr ⟨h⟩).rightHomotopyRel
  apply DaggerStandardSSetCylinder.literalOfModel
  apply RightHomotopyRel.leftHomotopyRel
  apply (RightHomotopyClass.mk_eq_mk_iff _ _).mp
  apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z p).injective
  simpa only [RightHomotopyClass.precomp_mk] using (RightHomotopyClass.mk_eq_mk_iff _ _).mpr h'

/-- In the finite-subcomplex criterion, a different weak cover may be
used for each subcomplex. The homotopy on the cover uses the same vertex in X. -/
theorem point_GW_of_finite_weak_cover (X : SSet.{u})
    (h : ∀ A : X.Subcomplex, A.toSSet.IsFinite →
      ∃ (K : SSet.{u}) (p : K ⟶ A.toSSet) (_ : WeakEquivalence p)
        (v : (Δ[0] : SSet.{u}) ⟶ X),
        Nonempty (SSet.Homotopy
          (R.map (p ≫ A.ι))
          (R.map (p ≫ SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v)))) :
    GW (SSet.stdSimplex.isTerminalObj₀.from X) := by
  apply FiniteFactorContractibility.point_GW_of_finite_nullhomotopy
  intro A hA
  obtain ⟨K, p, hp, v, ⟨H⟩⟩ := h A hA
  haveI : WeakEquivalence (R.map p) := weak_singular p
  refine ⟨v, ⟨homotopyOfPrecomp (R.map p) ?_⟩⟩
  simpa only [Functor.map_comp] using H

end

end DaggerModels.PartII.FiniteWeakCover
