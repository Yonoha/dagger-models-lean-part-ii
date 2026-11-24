import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.FunctorialCofibrantArrowResolution

/-!
# The functorial projective replacement and the strictification mate

The replacement below is obtained from the actual boundary-generator small-object
argument for the original projective Kan model. The final maps take explicit
`g` and `r` as inputs: the free-inner factorization and object-preserving
Bergner fibrant replacement required by the manuscript are separate inputs.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open DaggerModels

namespace DaggerModels.PartII.JTStrictificationMaps

open DaggerJTRealization
open OrdinaryRigidification.DaggerRigidification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The actual projective cofibration/trivial-fibration factorization obtained
from the boundary generators of reversal diagrams. -/
private def projectiveFactorization :
    letI : ModelCategory Source :=
      ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    FunctorialFactorizationData (cofibrations Source)
      (trivialFibrations Source) := by
  letI : ModelCategory Source :=
    ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsLocallyPresentable.{0} Source :=
    ProjectiveKanDiagram.locallyPresentable ReverseSimplexᵒᵖ
  have hcof : cofibrations Source =
      (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ).rlp.llp :=
    ProjectiveKanDiagram.model_cofibrations ReverseSimplexᵒᵖ
  have htriv : trivialFibrations Source =
      (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ).rlp := by
    change ProjectiveKanDiagram.fibrations ReverseSimplexᵒᵖ ⊓
      ProjectiveKanDiagram.weakEquivalences ReverseSimplexᵒᵖ = _
    rw [ProjectiveKanDiagram.fibrations_inf_weakEquivalences]
    exact (ProjectiveKanDiagram.boundaryGenerators_rlp ReverseSimplexᵒᵖ).symm
  rw [hcof, htriv]
  exact DaggerSmithSolutionSet.soaFactorization
    (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ)

/-- The arrow from the initial projective diagram, natural in its target. -/
private def initialArrow : Source ⥤ Arrow Source where
  obj W := Arrow.mk (initial.to W)
  map f := Arrow.homMk (𝟙 _) f (by simp)
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- The actual functorial projective cofibrant replacement of a reversal
dagger space. -/
def Qproj : Source ⥤ Source := initialArrow ⋙ projectiveFactorization.Z

/-- The natural projective trivial fibration from the replacement. -/
def p : Qproj ⟶ 𝟭 Source where
  app W := projectiveFactorization.p.app (initialArrow.obj W)
  naturality W V f := by
    exact projectiveFactorization.p.naturality (initialArrow.map f)

/-- Each replacement object is cofibrant in the original projective Kan
model structure. -/
theorem Qproj_cofibrant (W : Source) :
    letI : ModelCategory Source :=
      ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    IsCofibrant (Qproj.obj W) := by
  letI : ModelCategory Source :=
    ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  change IsCofibrant (projectiveFactorization.Z.obj (initialArrow.obj W))
  apply (isCofibrant_iff_of_isInitial
    (projectiveFactorization.i.app (initialArrow.obj W)) initialIsInitial).mpr
  exact (cofibration_iff _).mpr
    (projectiveFactorization.hi (initialArrow.obj W))

/-- The comparison map is a projective trivial fibration, as required in
the manuscript's choice of `Q_{\mathrm{proj}} W`. -/
theorem p_trivialFibration (W : Source) :
    letI : ModelCategory Source :=
      ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    trivialFibrations Source (p.app W) := by
  letI : ModelCategory Source :=
    ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  exact projectiveFactorization.hp (initialArrow.obj W)

/-- The actual rigidified map assembled from a supplied free-inner map `g`
and a supplied target replacement map `r`. -/
def a (W : Source) {T : DaggerSSet.{0}}
    (g : daggerRealization.obj (Qproj.obj W) ⟶ T)
    {C : DaggerSimplicialCat.{0, 0}}
    (r : daggerRigidification.obj T ⟶ C) :
    daggerRigidification.obj (daggerRealization.obj (Qproj.obj W)) ⟶ C :=
  daggerRigidification.map g ≫ r

/-- The transpose of the assembled map under the original composite
dagger JT and rigidification adjunction. -/
def aFlat (W : Source) {T : DaggerSSet.{0}}
    (g : daggerRealization.obj (Qproj.obj W) ⟶ T)
    {C : DaggerSimplicialCat.{0, 0}}
    (r : daggerRigidification.obj T ⟶ C) :
    Qproj.obj W ⟶ JTCoendMate.compositeNerve.obj C :=
  JTCoendMate.compositeAdjunction.homEquiv (Qproj.obj W) C (a W g r)

/-- The literal unit-comparison composite in the frame adjunction. -/
def psi (W : Source) {T : DaggerSSet.{0}}
    (g : daggerRealization.obj (Qproj.obj W) ⟶ T)
    {C : DaggerSimplicialCat.{0, 0}}
    (r : daggerRigidification.obj T ⟶ C) :
    Qproj.obj W ⟶ JTFrameAdjunction.frameNerve.obj C :=
  JTFrameAdjunction.adjunction.unit.app (Qproj.obj W) ≫
    JTFrameAdjunction.frameNerve.map
      (JTCoendComparison.comparison.app (Qproj.obj W) ≫ a W g r)

/-- The original right mate identifies the two literal constructions of
the strictification map, for the supplied `g` and `r`. -/
theorem psi_eq_aFlat_rightMate (W : Source) {T : DaggerSSet.{0}}
    (g : daggerRealization.obj (Qproj.obj W) ⟶ T)
    {C : DaggerSimplicialCat.{0, 0}}
    (r : daggerRigidification.obj T ⟶ C) :
    psi W g r = aFlat W g r ≫ JTCoendMate.rightMate.app C := by
  change JTFrameAdjunction.adjunction.unit.app (Qproj.obj W) ≫
      JTFrameAdjunction.frameNerve.map
        (JTCoendComparison.comparison.app (Qproj.obj W) ≫ a W g r) =
    JTCoendMate.compositeAdjunction.homEquiv (Qproj.obj W) C (a W g r) ≫
      JTCoendMate.rightMate.app C
  simpa only [Adjunction.homEquiv_unit] using
    (JTCoendMateFormula.rightMate_homEquiv (Qproj.obj W) C (a W g r))

end

end DaggerModels.PartII.JTStrictificationMaps
