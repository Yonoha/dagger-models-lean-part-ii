import DaggerModelsPartII.JTOrdinaryEndpointFibration
import DaggerModelsPartII.ReducedCylinder

/-!
# Colimits and projective cofibrations for the ordinary JT arrow tensor

The existing arrow tensor of an arbitrary simplicial map preserves colimits.
For two monomorphisms, its value on the second map is a projective Arrow
cofibration in the original Joyal model.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
  HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinaryJTArrowTensor

noncomputable section

open JTOrdinaryEndpointFibration

private local instance (A : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

private def leftCocone {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} (c : Cocone K) :
    Cocone ((K ⋙ tensorArrowFunctor u) ⋙ Arrow.leftFunc) :=
  (tensorLeft A).mapCocone c

private def rightCocone {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} (c : Cocone K) :
    Cocone ((K ⋙ tensorArrowFunctor u) ⋙ Arrow.rightFunc) :=
  (tensorLeft B).mapCocone c

private def leftIsColimit {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) : IsColimit (leftCocone u c) :=
  isColimitOfPreserves (tensorLeft A) hc

private def rightIsColimit {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) : IsColimit (rightCocone u c) :=
  isColimitOfPreserves (tensorLeft B) hc

private def arrowCocone {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) : Cocone (K ⋙ tensorArrowFunctor u) :=
  Comma.coconeOfPreserves (K ⋙ tensorArrowFunctor u)
    (leftIsColimit u hc) (rightCocone u c)

private def arrowIsColimit {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) : IsColimit (arrowCocone u hc) :=
  Comma.coconeOfPreservesIsColimit (K ⋙ tensorArrowFunctor u)
    (leftIsColimit u hc) (rightIsColimit u hc)

private theorem arrowCocone_hom {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) :
    (arrowCocone u hc).pt.hom = u ▷ c.pt := by
  apply (leftIsColimit u hc).hom_ext
  intro j
  have hj := Arrow.w ((arrowCocone u hc).ι.app j)
  change (A ◁ c.ι.app j) ≫ (arrowCocone u hc).pt.hom =
    (u ▷ K.obj j) ≫ (B ◁ c.ι.app j) at hj
  exact hj.trans (MonoidalCategory.whisker_exchange u (c.ι.app j)).symm

private def arrowCoconePointIso {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) :
    (arrowCocone u hc).pt ≅ (tensorArrowFunctor u).obj c.pt :=
  Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
    exact (arrowCocone_hom u hc).symm)

private def arrowCoconeIso {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) :
    arrowCocone u hc ≅ (tensorArrowFunctor u).mapCocone c :=
  Cocones.ext (arrowCoconePointIso u hc) (by
    intro j
    apply Arrow.hom_ext
    · rfl
    · rfl)

private def arrowMappedIsColimit {A B : SSet.{0}} (u : A ⟶ B)
    {J : Type} [Category J] {K : J ⥤ SSet.{0}} {c : Cocone K}
    (hc : IsColimit c) :
    IsColimit ((tensorArrowFunctor u).mapCocone c) :=
  (arrowIsColimit u hc).ofIsoColimit (arrowCoconeIso u hc)

/-- The ordinary arrow tensor preserves every small colimit, for arbitrary
`u`; no monomorphism assumption is needed. -/
instance preservesColimits {A B : SSet.{0}} (u : A ⟶ B) :
    PreservesColimitsOfSize.{0, 0} (tensorArrowFunctor u) where
  preservesColimitsOfShape :=
    { preservesColimit := fun {_} =>
        { preserves := fun {_} hc => ⟨arrowMappedIsColimit u hc⟩ } }

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel

private theorem corner_eq_tensorSquare {A B K L : SSet.{0}}
    (u : A ⟶ B) (f : K ⟶ L) :
    ProjectiveArrowFactorization.corner ((tensorArrowFunctor u).map f) =
      (ReducedCylinder.tensorSquare u f).ι := by
  let t := ReducedCylinder.tensorSquare u f
  apply pushout.hom_ext
  · change pushout.inl (u ▷ K) (A ◁ f) ≫
        ProjectiveArrowFactorization.corner ((tensorArrowFunctor u).map f) =
      t.inl ≫ t.ι
    rw [ProjectiveArrowFactorization.corner, pushout.inl_desc]
    exact t.inl_ι.symm
  · change pushout.inr (u ▷ K) (A ◁ f) ≫
        ProjectiveArrowFactorization.corner ((tensorArrowFunctor u).map f) =
      t.inr ≫ t.ι
    rw [ProjectiveArrowFactorization.corner, pushout.inr_desc]
    exact t.inr_ι.symm

/-- The tensor image of a mono is a projective Arrow cofibration whenever
the fixed simplicial map is also mono. Both cofibration conditions use the
original Joyal model and its monomorphism characterization. -/
theorem projective_of_mono {A B K L : SSet.{0}}
    (u : A ⟶ B) (f : K ⟶ L) [Mono u] [Mono f] :
    ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((tensorArrowFunctor u).map f) := by
  constructor
  · change cofibrations SSet.{0} (A ◁ f)
    change
     (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
        (A ◁ f)
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof]
    exact DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono A f
  · rw [corner_eq_tensorSquare]
    change
     (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
        (ReducedCylinder.tensorSquare u f).ι
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof]
    exact DaggerNativeSimplicialPushoutTensorMono.mono_ι u f
      (ReducedCylinder.tensorSquare u f)

#print axioms preservesColimits
#print axioms projective_of_mono

end

end DaggerModels.PartII.OrdinaryJTArrowTensor
