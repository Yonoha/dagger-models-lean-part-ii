import TopCatModelCategory.SSet.Evaluation
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.SSet.Finite
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite-subcomplex presentation of a simplicial set

The index consists of actual finite subcomplexes, including the empty
subcomplex, and the cocone legs are their literal inclusions. Native filtered
colimit preservation by the subcomplex functor gives the universal property.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial

namespace DaggerModels.PartII.FiniteSubcomplexPresentation

noncomputable section

/-- The poset of finite subcomplexes of the given simplicial set. -/
abbrev FiniteSubcomplex (X : SSet.{0}) :=
  {A : X.Subcomplex // SSet.IsFinite (A : SSet.{0})}

private theorem finite_bot (X : SSet.{0}) :
    SSet.IsFinite ((⊥ : X.Subcomplex) : SSet.{0}) := by
  have h : SSet.IsFinite
      ((⨆ _ : Empty, (⊥ : X.Subcomplex) : X.Subcomplex) : SSet.{0}) :=
    (SSet.isFinite_iSup_iff
      (fun _ : Empty ↦ (⊥ : X.Subcomplex))).2 (fun i ↦ isEmptyElim i)
  simpa using h

private theorem finite_sup (X : SSet.{0}) {A B : X.Subcomplex}
    (hA : SSet.IsFinite (A : SSet.{0}))
    (hB : SSet.IsFinite (B : SSet.{0})) :
    SSet.IsFinite ((A ⊔ B : X.Subcomplex) : SSet.{0}) := by
  have h : SSet.IsFinite
      ((⨆ b : Bool, cond b A B : X.Subcomplex) : SSet.{0}) :=
    (SSet.isFinite_iSup_iff (fun b : Bool ↦ cond b A B)).2 (by
      intro b
      cases b
      · exact hB
      · exact hA)
  simpa only [iSup_bool_eq, Bool.cond_true, Bool.cond_false] using h

instance (X : SSet.{0}) : Nonempty (FiniteSubcomplex X) :=
  ⟨⟨⊥, finite_bot X⟩⟩

instance (X : SSet.{0}) : SemilatticeSup (FiniteSubcomplex X) :=
  Subtype.semilatticeSup (fun _ _ hA hB ↦ finite_sup X hA hB)

/-- The inclusion of finite subcomplexes into the complete lattice of all subcomplexes. -/
def inclusion (X : SSet.{0}) : FiniteSubcomplex X ⥤ X.Subcomplex where
  obj A := A.1
  map f := homOfLE (leOfHom f)
  map_id := by intro A; rfl
  map_comp := by intro A B C f g; rfl

/-- The actual finite subcomplexes and the maps induced by inclusion. -/
def diagram (X : SSet.{0}) : FiniteSubcomplex X ⥤ SSet.{0} :=
  inclusion X ⋙ SSet.Subcomplex.toPresheafFunctor

/-- Literal inclusions of finite subcomplexes into the original simplicial set. -/
def cocone (X : SSet.{0}) : Cocone (diagram X) where
  pt := X
  ι :=
    { app := fun A ↦ A.1.ι
      naturality := by
        intro A B f
        simp [diagram, inclusion] }

/-- Every simplex lies in a finite generated subcomplex; hence finite subcomplexes cover X. -/
theorem iSup_eq_top (X : SSet.{0}) :
    (⨆ A : FiniteSubcomplex X, A.1) = ⊤ := by
  apply le_antisymm (le_top)
  rintro ⟨q⟩
  induction q using SimplexCategory.rec with
  | _ n =>
    intro x _
    exact (le_iSup (fun A : FiniteSubcomplex X ↦ A.1)
      ⟨SSet.Subcomplex.ofSimplex x, inferInstance⟩) _
      (SSet.Subcomplex.mem_ofSimplex_obj x)

/-- The canonical finite-subcomplex cocone is a filtered colimit. -/
def isColimit (X : SSet.{0}) : IsColimit (cocone X) := by
  letI : IsFilteredOrEmpty (FiniteSubcomplex X) := inferInstance
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves SSet.Subcomplex.toPresheafFunctor
      ((CompleteLattice.colimitCocone (inclusion X)).isColimit))
    (Cocones.ext
      ((SSet.Subcomplex.isoOfEq (iSup_eq_top X)) ≪≫ SSet.Subcomplex.topIso X)
      (fun _ ↦ by rfl))

end

end DaggerModels.PartII.FiniteSubcomplexPresentation
