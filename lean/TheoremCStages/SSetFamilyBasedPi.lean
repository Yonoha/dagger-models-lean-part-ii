import NativeCoproductHomotopy
import NativeTotalBasedPiFunctor

/-! Positive based homotopy groups of a simplicial family retain their original index. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerOriginalProductGadget DaggerNativeCoproductHomotopy
open scoped SSet.modelCategoryQuillen

universe u
namespace DaggerSSetFamilyBasedPi
noncomputable section

private theorem familySigmaIso_vertex {I : Type u} (X : I → SSet.{u}) (i : I)
    (x : (X i) _⦋0⦌) :
    (familySigmaIso X).hom.app (op ⦋0⦌) ((Sigma.ι X i).app (op ⦋0⦌) x) =
      ⟨i, x⟩ := by
  have h := congrFun (NatTrans.congr_app (familySigmaIso_ι X i) (op ⦋0⦌)) x
  exact h

/-- The original summand inclusion identifies every positive based homotopy group with the
corresponding based homotopy group of the full simplicial family. -/
def familyPiEquiv {I : Type u} (X : I → SSet.{u}) [∀ i, IsFibrant (X i)]
    (i : I) (x : (X i) _⦋0⦌) (n : ℕ) :
    π (n + 1) (X i) x ≃ π (n + 1) (familySSet X) ⟨i, x⟩ :=
  (summandPiEquiv X i x n).trans
    (mapπEquivOfIso (familySigmaIso X) (n + 1)
      ((Sigma.ι X i).app (op ⦋0⦌) x) ⟨i, x⟩ (familySigmaIso_vertex X i x))

theorem familyPiEquiv_apply {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) (x : (X i) _⦋0⦌) (n : ℕ)
    (s : π (n + 1) (X i) x) :
    familyPiEquiv X i x n s =
      mapπ (familyInclusion X i) (n + 1) x ⟨i, x⟩ rfl s := by
  change mapπ (familySigmaIso X).hom (n + 1)
      ((Sigma.ι X i).app (op ⦋0⦌) x) ⟨i, x⟩ (familySigmaIso_vertex X i x)
      (mapπ (Sigma.ι X i) (n + 1) x _ rfl s) = _
  simpa only [familySigmaIso_ι] using
    (mapπ_mapπ (Sigma.ι X i) (n + 1) x _ rfl
      (familySigmaIso X).hom ⟨i, x⟩ (familySigmaIso_vertex X i x) s)

/-- The total positive based homotopy group of a family is the indexed family of its
original total positive based homotopy groups. -/
def familyTotalPiEquiv {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (n : ℕ) :
    (Σ i, Σ x : (X i) _⦋0⦌, π (n + 1) (X i) x) ≃
      (Σ z : (familySSet X) _⦋0⦌, π (n + 1) (familySSet X) z) :=
  (Equiv.sigmaCongrRight fun i ↦
    Equiv.sigmaCongrRight fun x ↦ familyPiEquiv X i x n).trans
    (Equiv.sigmaAssoc (fun i x ↦ π (n + 1) (familySSet X) ⟨i, x⟩)).symm

theorem familyTotalPiEquiv_apply {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (n : ℕ) (i : I) (x : (X i) _⦋0⦌)
    (s : π (n + 1) (X i) x) :
    familyTotalPiEquiv X n ⟨i, x, s⟩ =
      ⟨⟨i, x⟩, mapπ (familyInclusion X i) (n + 1) x ⟨i, x⟩ rfl s⟩ := by
  change (⟨⟨i, x⟩, familyPiEquiv X i x n s⟩ :
    Σ z : (familySSet X) _⦋0⦌, π (n + 1) (familySSet X) z) = _
  rw [familyPiEquiv_apply]

#print axioms familyPiEquiv
#print axioms familyPiEquiv_apply
#print axioms familyTotalPiEquiv_apply

end
end DaggerSSetFamilyBasedPi
