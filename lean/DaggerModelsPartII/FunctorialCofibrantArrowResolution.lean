import DaggerModelsPartII.CofibrantLocalizingFamily
import DaggerModelsPartII.ProjectiveKanDiagram
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-! A functorial cofibrant resolution of arrows in a model category. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

namespace FunctorialCofibrantArrowResolution

private def data : FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  functorialFactorizationData _ _

/-- The arrow from an initial object to each object, natural in that object. -/
private def initialArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (initial.to X)
  map f := Arrow.homMk (𝟙 _) f (by simp)
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- Functorial cofibrant replacement of the source of an arrow. -/
private def sourceReplacement : C ⥤ C := initialArrow ⋙ (data (C := C)).Z

/-- The natural trivial fibration from the source replacement. -/
private def sourceComparison : sourceReplacement (C := C) ⟶ 𝟭 C where
  app X := (data (C := C)).p.app (initialArrow.obj X)
  naturality X Y f := by
    exact (data (C := C)).p.naturality (initialArrow.map f)

/-- Replace the source of an arrow before factoring the resulting arrow. -/
private def sourceReplacedArrow : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (sourceComparison.app f.left ≫ f.hom)
  map {f g} φ := Arrow.homMk (sourceReplacement.map φ.left) φ.right (by
    have h := sourceComparison.naturality φ.left
    simp only [Functor.id_map] at h
    have hw : φ.left ≫ g.hom = f.hom ≫ φ.right := φ.w
    calc
      sourceReplacement.map φ.left ≫ (sourceComparison.app g.left ≫ g.hom)
          = (sourceComparison.app f.left ≫ φ.left) ≫ g.hom := by
              rw [← Category.assoc, h]
      _ = sourceComparison.app f.left ≫ (φ.left ≫ g.hom) := by rw [Category.assoc]
      _ = sourceComparison.app f.left ≫ (f.hom ≫ φ.right) := by rw [hw]
      _ = (sourceComparison.app f.left ≫ f.hom) ≫ φ.right := by rw [Category.assoc])
  map_id f := by apply Arrow.hom_ext <;> simp
  map_comp φ ψ := by apply Arrow.hom_ext <;> simp

/-- The functorial cofibration between cofibrant objects resolving each arrow. -/
def QArrow : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk ((data (C := C)).i.app (sourceReplacedArrow.obj f))
  map {f g} φ := Arrow.homMk (sourceReplacedArrow.map φ).left
    ((data (C := C)).Z.map (sourceReplacedArrow.map φ))
    (by simpa only [Arrow.leftFunc_map] using
      (data (C := C)).i.naturality (sourceReplacedArrow.map φ))
  map_id f := by apply Arrow.hom_ext <;> simp
  map_comp φ ψ := by apply Arrow.hom_ext <;> simp

/-- The natural comparison from the resolved arrow to the original arrow. -/
def comparison : QArrow (C := C) ⟶ 𝟭 (Arrow C) where
  app f := Arrow.homMk (sourceComparison.app f.left)
    ((data (C := C)).p.app (sourceReplacedArrow.obj f)) (by
      exact ((data (C := C)).fac_app (f := sourceReplacedArrow.obj f)).symm)
  naturality f g φ := by
    apply Arrow.hom_ext
    · exact sourceComparison.naturality φ.left
    · exact (data (C := C)).p.naturality (sourceReplacedArrow.map φ)

omit [HasLimitsOfSize.{0, 0} C] in
theorem cofibration (f : Arrow C) : cofibrations C (QArrow.obj f).hom :=
  (data (C := C)).hi (sourceReplacedArrow.obj f)

omit [HasLimitsOfSize.{0, 0} C] in
theorem source_cofibrant (f : Arrow C) : IsCofibrant (QArrow.obj f).left := by
  change IsCofibrant ((data (C := C)).Z.obj (initialArrow.obj f.left))
  apply (isCofibrant_iff_of_isInitial
    ((data (C := C)).i.app (initialArrow.obj f.left)) initialIsInitial).mpr
  exact (cofibration_iff _).mpr ((data (C := C)).hi (initialArrow.obj f.left))

omit [HasLimitsOfSize.{0, 0} C] in
theorem target_cofibrant (f : Arrow C) : IsCofibrant (QArrow.obj f).right := by
  letI : IsCofibrant ((𝟭 C).obj (QArrow.obj f).left) := source_cofibrant f
  letI : Cofibration (QArrow.obj f).hom := (cofibration_iff _).mpr (cofibration f)
  exact isCofibrant_of_cofibration (QArrow.obj f).hom

omit [HasLimitsOfSize.{0, 0} C] in
theorem source_weak (f : Arrow C) :
    WeakEquivalence (comparison.app f).left :=
  (weakEquivalence_iff _).mpr ((data (C := C)).hp (initialArrow.obj f.left)).2

omit [HasLimitsOfSize.{0, 0} C] in
theorem target_weak (f : Arrow C) :
    WeakEquivalence (comparison.app f).right :=
  (weakEquivalence_iff _).mpr ((data (C := C)).hp (sourceReplacedArrow.obj f)).2

/-- Each component satisfies the earlier pointwise resolution specification. -/
def component {X Y : C} (s : X ⟶ Y) : CofibrantArrowResolution s where
  source := (QArrow.obj (Arrow.mk s)).left
  target := (QArrow.obj (Arrow.mk s)).right
  hom := (QArrow.obj (Arrow.mk s)).hom
  comparison := comparison.app (Arrow.mk s)
  cofibration := (cofibration_iff _).mpr (cofibration (Arrow.mk s))
  source_cofibrant := source_cofibrant (Arrow.mk s)
  target_cofibrant := target_cofibrant (Arrow.mk s)
  source_weak := source_weak (Arrow.mk s)
  target_weak := target_weak (Arrow.mk s)

namespace Projective

variable (D : Type) [SmallCategory D]

/-- The boundary generators provide the functorial factorization required by
the projective Kan diagram model at universe level zero. -/
private def factorization :
    letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
    FunctorialFactorizationData (cofibrations (Dᵒᵖ ⥤ SSet.{0}))
      (trivialFibrations (Dᵒᵖ ⥤ SSet.{0})) := by
  letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
  letI : IsLocallyPresentable.{0} (Dᵒᵖ ⥤ SSet.{0}) :=
    ProjectiveKanDiagram.locallyPresentable Dᵒᵖ
  have hcof : cofibrations (Dᵒᵖ ⥤ SSet.{0}) =
      (ProjectiveKanDiagram.boundaryGenerators Dᵒᵖ).rlp.llp :=
    ProjectiveKanDiagram.model_cofibrations Dᵒᵖ
  have htriv : trivialFibrations (Dᵒᵖ ⥤ SSet.{0}) =
      (ProjectiveKanDiagram.boundaryGenerators Dᵒᵖ).rlp := by
    change ProjectiveKanDiagram.fibrations Dᵒᵖ ⊓
      ProjectiveKanDiagram.weakEquivalences Dᵒᵖ = _
    rw [ProjectiveKanDiagram.fibrations_inf_weakEquivalences]
    exact (ProjectiveKanDiagram.boundaryGenerators_rlp Dᵒᵖ).symm
  rw [hcof, htriv]
  exact DaggerSmithSolutionSet.soaFactorization
    (ProjectiveKanDiagram.boundaryGenerators Dᵒᵖ)

/-- The functorial arrow resolution for projective reversal or dagger spaces. -/
def QArrow : Arrow (Dᵒᵖ ⥤ SSet.{0}) ⥤ Arrow (Dᵒᵖ ⥤ SSet.{0}) := by
  letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
  letI : HasFunctorialFactorization (cofibrations (Dᵒᵖ ⥤ SSet.{0}))
      (trivialFibrations (Dᵒᵖ ⥤ SSet.{0})) := ⟨⟨factorization D⟩⟩
  exact FunctorialCofibrantArrowResolution.QArrow

/-- The projective arrow resolution compares naturally to the original arrows. -/
def comparison : QArrow D ⟶ 𝟭 (Arrow (Dᵒᵖ ⥤ SSet.{0})) := by
  letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
  letI : HasFunctorialFactorization (cofibrations (Dᵒᵖ ⥤ SSet.{0}))
      (trivialFibrations (Dᵒᵖ ⥤ SSet.{0})) := ⟨⟨factorization D⟩⟩
  exact FunctorialCofibrantArrowResolution.comparison

/-- Each projective component is a cofibrant arrow resolution, compatible with
the natural projective comparison. -/
def component {X Y : Dᵒᵖ ⥤ SSet.{0}} (s : X ⟶ Y) :
    letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
    CofibrantArrowResolution s := by
  letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
  letI : HasFunctorialFactorization (cofibrations (Dᵒᵖ ⥤ SSet.{0}))
      (trivialFibrations (Dᵒᵖ ⥤ SSet.{0})) := ⟨⟨factorization D⟩⟩
  exact FunctorialCofibrantArrowResolution.component s

theorem component_hom {X Y : Dᵒᵖ ⥤ SSet.{0}} (s : X ⟶ Y) :
    letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
    (component D s).hom = ((QArrow D).obj (Arrow.mk s)).hom := rfl

theorem component_comparison {X Y : Dᵒᵖ ⥤ SSet.{0}} (s : X ⟶ Y) :
    letI : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) := ProjectiveKanDiagram.modelCategory Dᵒᵖ
    (component D s).comparison = (comparison D).app (Arrow.mk s) := rfl

end Projective

end FunctorialCofibrantArrowResolution

end

end DaggerModels.PartII
