import NativeAmbientDaggerFibrancy
import ActualDaggerFibrantCounitReduction
import DaggerModelsPartII.OrdinaryDwyerKanCore

/-!
# A pointwise object-preserving fibrant replacement

For each original dagger simplicial category, factor its terminal map in the
native fixed-object model.  This construction fixes the object type and the
object function of the unit.  It does not assert functoriality across varying
object types.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels
open DaggerOriginalFixedObjectDaggerCategories
open DaggerNativeFixedDaggerCompletionWeakBridge
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel

universe u

namespace DaggerModels.PartII.JTObjectPreservingReplacement

noncomputable section

private local instance : ModelCategory DaggerSimplicialCat.{u, u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- The chosen factorization stays inside the original fixed-object category. -/
def replacementData (C : DaggerSimplicialCat.{u, u}) :=
  factorizationData (trivialCofibrations (FixedDaggerCategory C.Obj))
    (fibrations (FixedDaggerCategory C.Obj))
    (terminal.from (fixedOfDagger C))

/-- The replacement has exactly the same object type as `C`. -/
def Robj (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  originalDagger (replacementData C).Z

/-- The replacement unit is a fixed-object dagger functor. -/
def r (C : DaggerSimplicialCat.{u, u}) : C ⟶ Robj C :=
  originalDaggerHom (replacementData C).i

/-- The literal object function of the unit is the identity. -/
theorem r_obj (C : DaggerSimplicialCat.{u, u}) (x : C.Obj) :
    (r C).obj x = x := rfl

/-- The fixed-object unit is a weak equivalence on every original enriched Hom. -/
theorem r_hom_weak (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    WeakEquivalence ((r C).map x y) := by
  have hfixed : WeakEquivalence (replacementData C).i :=
    (weakEquivalence_iff _).mpr (replacementData C).hi.2
  exact (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original
    (replacementData C).i).mp hfixed x y

/-- The replacement is fibrant in the original global dagger model. -/
theorem Robj_fibrant (C : DaggerSimplicialCat.{u, u}) : IsFibrant (Robj C) := by
  have hfixed : IsFibrant (replacementData C).Z := by
    exact (isFibrant_iff_of_isTerminal (replacementData C).p
      (Limits.terminalIsTerminal : IsTerminal (⊤_ FixedDaggerCategory C.Obj))).mpr
      ((fibration_iff _).mpr (replacementData C).hp)
  apply (DaggerActualFibrantCounitReduction.fibrant_iff_localKan (Robj C)).mpr
  intro x y
  exact (DaggerNativeAmbientDaggerFibrancy.fibrant_iff_homs
    (replacementData C).Z).mp hfixed x y

/-- The fixed-object unit is an original dagger DK equivalence. -/
theorem r_daggerDK (C : DaggerSimplicialCat.{u, u}) :
    DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement (r C) := by
  have hobj : Function.Surjective (r C).obj := by
    intro y
    exact ⟨y, r_obj C y⟩
  have hlocal : DaggerGlobalDK.LocalGeometricWeakEquivalence (r C) := by
    intro x y
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp (r_hom_weak C x y)
  exact DaggerGlobalDK.daggerDK_of_surjective_local
    DaggerUnitaryInvariance.standardReplacement (r C) hobj hlocal

/-- The same unit lies in the weak class of the original global model. -/
theorem r_weak (C : DaggerSimplicialCat.{u, u}) : WeakEquivalence (r C) := by
  apply (weakEquivalence_iff _).mpr
  rw [DaggerActualRigidificationQuillen.target_weak]
  exact r_daggerDK C

end

end DaggerModels.PartII.JTObjectPreservingReplacement
