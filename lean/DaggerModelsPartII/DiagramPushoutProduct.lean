import DaggerModelsPartII.InjectiveKanModel
import NativeSimplicialPushoutTensorMono
import SSetSM7

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

/-- Diagramwise product with a simplicial set, functorial in both variables. -/
def curriedDiagramTensor : (C ⥤ SSet.{u}) ⥤ SSet.{u} ⥤ (C ⥤ SSet.{u}) where
  obj A := diagramTensor A
  map {A B} i := {
    app K := Functor.whiskerRight i (tensorRight K)
    naturality K L j := by
      apply NatTrans.ext
      funext c
      exact whisker_exchange (i.app c) j }
  map_id A := by
    ext K c
    rfl
  map_comp i j := by
    ext K c
    rfl

/-- The actual diagram pushout-product of a diagram map and a simplicial map. -/
def diagramPushoutProduct {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) :
    Functor.PushoutObjObj (curriedDiagramTensor C) i j :=
  Functor.PushoutObjObj.ofHasPushout _ _ _


/-- Evaluation identifies the diagram pushout square with the ordinary
simplicial-set pushout square. -/
def diagramPushoutProductAt {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) (c : C) :
    SSet.PushoutTensor (i.app c) j where
  pt := sq.pt.obj c
  inl := sq.inl.app c
  inr := sq.inr.app c
  isPushout := by
    convert IsPushout.map ((evaluation C SSet.{u}).obj c) sq.isPushout using 1

/-- The ordinary pushout tensor inclusion is the evaluation of the diagram
pushout-product inclusion. -/
theorem diagramPushoutProductAt_ι {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) (c : C) :
    (diagramPushoutProductAt C i j sq c).ι = sq.ι.app c := by
  apply (diagramPushoutProductAt C i j sq c).isPushout.hom_ext
  · exact (diagramPushoutProductAt C i j sq c).inl_ι.trans
      (congrArg (fun f => f.app c) sq.inl_ι).symm
  · exact (diagramPushoutProductAt C i j sq c).inr_ι.trans
      (congrArg (fun f => f.app c) sq.inr_ι).symm


/-- A pushout-product of a diagram mono and a simplicial mono is a diagram mono. -/
theorem diagramPushoutProduct_mono {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) [Mono i] [Mono j]
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) : Mono sq.ι := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro c
  rw [← diagramPushoutProductAt_ι C i j sq c]
  haveI : Mono (i.app c) := inferInstance
  exact DaggerNativeSimplicialPushoutTensorMono.mono_ι
    (i.app c) j (diagramPushoutProductAt C i j sq c)


/-- A trivial injective diagram cofibration remains trivial after taking its
pushout-product with a simplicial monomorphism. -/
theorem diagramPushoutProduct_trivial_left {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) [Mono j]
    (hi : trivialCofibrations C i)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    trivialCofibrations C sq.ι := by
  rw [trivialCofibrations_eq]
  intro c
  rw [← diagramPushoutProductAt_ι C i j sq c]
  have hic : HomotopicalAlgebra.trivialCofibrations SSet.{u} (i.app c) := by
    rw [trivialCofibrations_eq] at hi
    exact hi c
  have ha : SSet.anodyneExtensions (i.app c) :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mpr hic
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
    (SSet.anodyneExtensions.pushoutTensorι₁
      (diagramPushoutProductAt C i j sq c) ha)

/-- A trivial simplicial cofibration remains trivial after taking its
pushout-product with a diagram monomorphism. -/
theorem diagramPushoutProduct_trivial_right {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) [Mono i]
    (hj : HomotopicalAlgebra.trivialCofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    trivialCofibrations C sq.ι := by
  rw [trivialCofibrations_eq]
  intro c
  rw [← diagramPushoutProductAt_ι C i j sq c]
  haveI : Mono (i.app c) := inferInstance
  have ha : SSet.anodyneExtensions j :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mpr hj
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
    (SSet.anodyneExtensions.pushoutTensorι₂
      (diagramPushoutProductAt C i j sq c) ha)

end
end DaggerModels.PartII.InjectiveKanDiagram
