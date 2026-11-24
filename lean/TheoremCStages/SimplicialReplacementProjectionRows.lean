import NativeCoproductDescFibration
import CartesianSimplicialMapFibration
import NativeSimplicialReplacement
import NativeFamilyLoopAction

/-!
# Kan fibrations of the original replacement rows

The projection of a family of Kan simplicial sets to its discrete
index set is a Kan fibration. The proof retains the original family
projection and the original sigma-family isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerOriginalProductGadget (familySSet familyInclusion familySigmaIso
  familySigmaIso_ι familyProjection)
open DaggerNativeSimplicialReplacementCells (family first)
open DaggerOriginalFlagFlankification (constantSSet)
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialReplacementProjectionRows

noncomputable section

/-- The strict inclusion of one discrete index, with the whole zero
simplex as source. -/
def pointInclusion {I : Type u} (i : I) :
    (Δ[0] : SSet.{u}) ⟶ constantSSet I where
  app _ _ := i
  naturality _ _ _ := by funext x; rfl

/-- A point inclusion into a constant simplicial set has cartesian
naturality squares in every simplicial degree. -/
theorem pointInclusion_isPullback {I : Type u} (i : I)
    ⦃q r : SimplexCategoryᵒᵖ⦄ (α : q ⟶ r) :
    IsPullback ((Δ[0] : SSet.{u}).map α) ((pointInclusion i).app q)
      ((pointInclusion i).app r) ((constantSSet I).map α) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨(pointInclusion i).naturality α, ?_, ?_⟩
  · intro x y h
    exact Subsingleton.elim x y
  · intro x y h
    refine ⟨default, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact h

theorem pointInclusion_fibration {I : Type u} (i : I) :
    Fibration (pointInclusion i) :=
  DaggerCartesianSimplicialMapFibration.fibration_of_cartesian_naturality
    (pointInclusion i) (by
      intro q r α
      exact pointInclusion_isPullback i α)

/-- The map from one summand to the unchanged discrete index set. -/
def summandProjection {I : Type u} (X : I → SSet.{u}) (i : I) :
    X i ⟶ constantSSet I :=
  SSet.stdSimplex.isTerminalObj₀.from (X i) ≫ pointInclusion i

theorem summandProjection_fibration {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) :
    Fibration (summandProjection X i) := by
  have h₀ : Fibration (SSet.stdSimplex.isTerminalObj₀.from (X i)) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  have h₁ : Fibration (pointInclusion i) := pointInclusion_fibration i
  letI := h₀
  letI := h₁
  change Fibration
    (SSet.stdSimplex.isTerminalObj₀.from (X i) ≫ pointInclusion i)
  infer_instance

/-- The original family projection agrees, on every entire summand,
with the coproduct map of the actual summand projections. -/
theorem familyProjection_sigmaDesc {I : Type u} (X : I → SSet.{u}) :
    (familySigmaIso X).hom ≫ familyProjection X =
      Limits.Sigma.desc (summandProjection X) := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, familySigmaIso_ι, Limits.Sigma.ι_desc]
  apply NatTrans.ext
  rfl

/-- The original family projection of arbitrary Kan summands is a
Kan fibration over the unchanged discrete index simplicial set. -/
theorem familyProjection_fibration {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] :
    Fibration (familyProjection X) := by
  letI : ∀ i, Fibration (summandProjection X i) :=
    fun i ↦ summandProjection_fibration X i
  have hσ : Fibration (Limits.Sigma.desc (summandProjection X)) :=
    DaggerNativeCoproductDescFibration.sigma_desc_fibration
      (summandProjection X)
  let a : Arrow.mk (Limits.Sigma.desc (summandProjection X)) ≅
      Arrow.mk (familyProjection X) :=
    Arrow.isoMk (familySigmaIso X) (Iso.refl _) (by
      change (familySigmaIso X).hom ≫ familyProjection X =
        Limits.Sigma.desc (summandProjection X) ≫ 𝟙 _
      rw [Category.comp_id]
      exact familyProjection_sigmaDesc X)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
      ((fibration_iff _).mp hσ))

/-- Every literal row of the original simplicial replacement projects
by a Kan fibration when its original values are Kan. -/
theorem projection_row_fibration {C : Type u} [Category.{u} C]
    (G : C ⥤ SSet.{u}) [∀ c, IsFibrant (G.obj c)]
    (q : SimplexCategoryᵒᵖ) :
    Fibration ((DaggerNativeSimplicialReplacement.projection G).app q) := by
  letI : ∀ c : (nerve C).obj q, IsFibrant ((family G q) c) :=
    fun c ↦ show IsFibrant (G.obj (first c)) from inferInstance
  change Fibration (familyProjection (family G q))
  exact familyProjection_fibration (family G q)

#print axioms pointInclusion_fibration
#print axioms familyProjection_sigmaDesc
#print axioms familyProjection_fibration
#print axioms projection_row_fibration

end
end DaggerModels.PartII.SimplicialReplacementProjectionRows
