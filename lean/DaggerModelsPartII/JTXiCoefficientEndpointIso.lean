import DaggerModelsPartII.JTXiStrictEndpointIso
import DaggerModelsPartII.JTXiEndpointRigidification
import OriginalActualDaggerFreeComparisonRecovered

/-!
# The strict Xi endpoint collapse after original rigidification

The coefficient cobase is first identified with the rigidified actual raw
collapse. The strict raw-to-free-CE isomorphism and the fixed Part I free
comparison then identify it with the manuscript's ordinary-free-dagger
coefficient. The original ordered boundary map is retained throughout.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DaggerModels
open OrdinaryRigidification.DaggerRigidification
open OrdinaryRigidification.DaggerFreeComparison

namespace DaggerModels.PartII.JTXiCoefficientEndpointIso

open JTXiEndpointCollapse JTXiEndpointRigidification
open JTXiStrictEndpointIso JTEndpointHom JTEndpointObjects
open JTRelativeReedyFrame JTActualCosimplicialFrame

noncomputable section

private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : HomotopicalAlgebra.ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual coefficient Xi cobase, with the original ordered boundary. -/
def coefficientXi : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0} :=
  collapsedFrame XiAugmentationCurried

/-- The first strict comparison, to the dagger rigidification of the
specified free CE diagram. -/
def coefficientRawCEIso :
    coefficientXi ≅ CEFree ⋙ daggerRigidification :=
  coefficientRawIso ≪≫
    Functor.isoWhiskerRight rawXiCollapseIso daggerRigidification

/-- The manuscript's ordinary rigidification followed by ordinary free
dagger, evaluated on the actual endpoint-collapsed CE diagram. -/
def paperCE : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0} :=
  CE ⋙ (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor)

/-- Part I's fixed natural free comparison, whiskered by the literal CE
diagram. Its source is the original free-dagger rigidification. -/
def freeCEComparisonIso :
    CEFree ⋙ daggerRigidification ≅ paperCE :=
  (Functor.associator CE freeDagger daggerRigidification) ≪≫
    Functor.isoWhiskerLeft CE canonicalFreeComparison

/-- The actual coefficient cobase is the paper's CE coefficient diagram.
This is the composite of the calibrated raw isomorphism and the original
Part I free comparison. -/
def coefficientXiCollapseIso : coefficientXi ≅ paperCE :=
  coefficientRawCEIso ≪≫ freeCEComparisonIso

/-- The original boundary inclusion of the Xi coefficient cobase. -/
def coefficientBoundary :
    (Functor.const SimplexCategory).obj Bdagger ⟶ coefficientXi :=
  JTEndpointCobase.endpointCobase_inl (endpointFaces XiCurried)
    Bdagger (endpointCollapse XiAugmentationCurried)

/-- The paper CE boundary is based at the original `Bdagger`. Its value
at `k` is literally the Part I free comparison at `boundary`, followed
by the image of the original `CE_boundary.app k`. -/
def paperBoundary :
    (Functor.const SimplexCategory).obj Bdagger ⟶ paperCE where
  app k := (canonicalFreeComparison.app JTXiEndpointCollapse.boundary).hom ≫
    (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
      (CE_boundary.app k)
  naturality {_ _} θ := by
    change 𝟙 Bdagger ≫
        ((canonicalFreeComparison.app JTXiEndpointCollapse.boundary).hom ≫
          (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
            (CE_boundary.app _)) =
      ((canonicalFreeComparison.app JTXiEndpointCollapse.boundary).hom ≫
        (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
          (CE_boundary.app _)) ≫
        (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
          (CE.map θ)
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    have h := CE_boundary.naturality θ
    change 𝟙 JTXiEndpointCollapse.boundary ≫ CE_boundary.app _ =
      CE_boundary.app _ ≫ CE.map θ at h
    rw [Category.id_comp] at h
    rw [h]

/-- The boundary at a fixed parameter is the prescribed Part I comparison
and the original ordered CE boundary map. -/
theorem paperBoundary_app (k : SimplexCategory) :
    paperBoundary.app k =
      (canonicalFreeComparison.app JTXiEndpointCollapse.boundary).hom ≫
      (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
        (CE_boundary.app k) := rfl

/-- The composite strict isomorphism carries the actual coefficient
boundary to the paper's ordered boundary, with source `Bdagger`. -/
theorem boundary_coefficientXiCollapseIso :
    coefficientBoundary ≫ coefficientXiCollapseIso.hom = paperBoundary := by
  apply NatTrans.ext
  funext k
  have hRaw : coefficientBoundary.app k ≫ coefficientToRaw.app k =
      rawRigidifiedBoundary.app k := by
    simpa only [coefficientBoundary, NatTrans.comp_app] using
      NatTrans.congr_app boundary_coefficientToRaw k
  have hFree : rawBoundary.app k ≫ rawXiCollapseIso.hom.app k =
      CEFreeBoundary.app k := by
    exact NatTrans.congr_app rawBoundary_rawXiCollapseIso k
  change ((coefficientBoundary.app k ≫ coefficientToRaw.app k) ≫
      daggerRigidification.map (rawXiCollapseIso.hom.app k)) ≫
        (canonicalFreeComparison.app (CE.obj k)).hom = paperBoundary.app k
  rw [hRaw]
  change (daggerRigidification.map (rawBoundary.app k) ≫
      daggerRigidification.map (rawXiCollapseIso.hom.app k)) ≫
        (canonicalFreeComparison.app (CE.obj k)).hom = paperBoundary.app k
  rw [← Functor.map_comp, hFree]
  change daggerRigidification.map (freeDagger.map (CE_boundary.app k)) ≫
      (canonicalFreeComparison.app (CE.obj k)).hom =
        (canonicalFreeComparison.app JTXiEndpointCollapse.boundary).hom ≫
          (OrdinaryRigidification.rigidification ⋙ OrdinaryFreeDagger.functor).map
            (CE_boundary.app k)
  exact canonicalFreeComparison.hom.naturality (CE_boundary.app k)

end

end DaggerModels.PartII.JTXiCoefficientEndpointIso
