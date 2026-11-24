import DaggerModelsPartII.OrdinaryPointCoproduct
import OriginalOrdinaryHomRetractsReconciled
import TopCatModelCategory.CommSq

/-!
# Local comparison across an actual ordinary object cell

The explicit ordinary coproduct with an identity-only point is compared with
arbitrary supplied pushout apexes. The Homwise local geometric comparison is
transported through the canonical enriched apex isomorphisms.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryPointCellComparison

open OrdinaryPointCoproduct

noncomputable section

private def emptyIsInitial : IsInitial OrdinaryBergnerGenerators.empty.{u} := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{u, u} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  exact DaggerDiscreteObjects.emptyIsInitial.isInitialObj
    DaggerSimplicialCat.forget DaggerDiscreteObjects.empty

variable {C PC : SimplicialCat.{u, u}}
  {a : OrdinaryBergnerGenerators.empty.{u} ⟶ C}
  (i : C ⟶ PC) (g : OrdinaryBergnerGenerators.point.{u} ⟶ PC)
  (sq : IsPushout a OrdinaryBergnerGenerators.emptyToPoint i g)

include sq in
/-- The explicit ordinary point sum and any original object-cell pushout
apex are canonically isomorphic. -/
def apexIso : OrdinaryPointCoproduct.cat C ≅ PC :=
  IsColimit.coconePointUniqueUpToIso
    (OrdinaryPointCoproduct.isColimit C)
    (sq.isColimitBinaryCofan emptyIsInitial)

include sq in
theorem inOld_apexIso :
    OrdinaryPointCoproduct.inOld C ≫ (apexIso i g sq).hom = i := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (OrdinaryPointCoproduct.isColimit C)
    (sq.isColimitBinaryCofan emptyIsInitial) ⟨WalkingPair.left⟩

include sq in
theorem inPoint_apexIso :
    OrdinaryPointCoproduct.inPoint C ≫ (apexIso i g sq).hom = g := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (OrdinaryPointCoproduct.isColimit C)
    (sq.isColimitBinaryCofan emptyIsInitial) ⟨WalkingPair.right⟩

include sq in
/-- Every supplied ordinary object-cell pushout has monic original Hom
maps, transported from the explicit old-object inclusion. -/
theorem supplied_old_hom_mono (x y : C.Obj) : Mono (i.map x y) := by
  let e : Arrow.mk (OrdinaryPointCoproduct.inOld C) ≅ Arrow.mk i :=
    Arrow.isoMk (Iso.refl C) (apexIso i g sq) (by
      simpa only [Category.id_comp] using inOld_apexIso i g sq)
  have hCan : OriginalOrdinaryHomRetracts.localHomProperty
      (MorphismProperty.monomorphisms SSet.{u})
      (OrdinaryPointCoproduct.inOld C) := by
    intro a b
    exact (OrdinaryPointCoproduct.inOld_embedding C).2 a b
  have hSup : OriginalOrdinaryHomRetracts.localHomProperty
      (MorphismProperty.monomorphisms SSet.{u}) i :=
    (OriginalOrdinaryHomRetracts.localHomProperty
      (MorphismProperty.monomorphisms SSet.{u})).of_retract
        (Retract.ofIso e.symm) hCan
  exact hSup x y

variable {D PD : SimplicialCat.{u, u}} (F : C ⟶ D)
  {a' : OrdinaryBergnerGenerators.empty.{u} ⟶ D}
  (j : D ⟶ PD) (gD : OrdinaryBergnerGenerators.point.{u} ⟶ PD)
  (sqD : IsPushout a' OrdinaryBergnerGenerators.emptyToPoint j gD)
  (Fplus : PC ⟶ PD)
  (hOld : i ≫ Fplus = F ≫ j)
  (hPoint : g ≫ Fplus = gD)

include sq sqD hOld hPoint in
/-- The supplied comparison is exactly the explicit point extension,
conjugated by the canonical source and target apex isomorphisms. -/
theorem comparison_conjugate :
    (apexIso i g sq).hom ≫ Fplus =
      OrdinaryPointCoproduct.extension F ≫ (apexIso j gD sqD).hom := by
  apply BinaryCofan.IsColimit.hom_ext (OrdinaryPointCoproduct.isColimit C)
  · calc
      OrdinaryPointCoproduct.inOld C ≫ ((apexIso i g sq).hom ≫ Fplus) =
          i ≫ Fplus := by rw [← Category.assoc, inOld_apexIso]
      _ = F ≫ j := hOld
      _ = OrdinaryPointCoproduct.inOld C ≫
          (OrdinaryPointCoproduct.extension F ≫ (apexIso j gD sqD).hom) := by
            rw [← Category.assoc, OrdinaryPointCoproduct.extension_old,
              Category.assoc, inOld_apexIso]
  · calc
      OrdinaryPointCoproduct.inPoint C ≫ ((apexIso i g sq).hom ≫ Fplus) =
          g ≫ Fplus := by rw [← Category.assoc, inPoint_apexIso]
      _ = gD := hPoint
      _ = OrdinaryPointCoproduct.inPoint C ≫
          (OrdinaryPointCoproduct.extension F ≫ (apexIso j gD sqD).hom) := by
            rw [← Category.assoc, OrdinaryPointCoproduct.extension_point,
              inPoint_apexIso]

include sq sqD hOld hPoint in
/-- The actual ordinary pushout-apex comparison is locally geometric whenever
the original ordinary comparison is. -/
theorem supplied_comparison_local
    (hF : ∀ x y : C.Obj,
      DaggerOrdinaryCellComparisonGeometric.GW (F.map x y))
    (p q : PC.Obj) :
    DaggerOrdinaryCellComparisonGeometric.GW (Fplus.map p q) := by
  let e : Arrow.mk (OrdinaryPointCoproduct.extension F) ≅ Arrow.mk Fplus :=
    Arrow.isoMk (apexIso i g sq) (apexIso j gD sqD)
      (comparison_conjugate i g sq F j gD sqD Fplus hOld hPoint)
  have hExt : OriginalOrdinaryHomRetracts.localHomProperty
      (weakEquivalences SSet.{u}) (OrdinaryPointCoproduct.extension F) := by
    intro x y
    exact (weakEquivalence_iff _).mp
      ((KanQuillenReuse.weakEquivalence_iff_geometric _).mpr
        (OrdinaryPointCoproduct.extension_local F hF x y))
  have hSup : OriginalOrdinaryHomRetracts.localHomProperty
      (weakEquivalences SSet.{u}) Fplus :=
    (OriginalOrdinaryHomRetracts.localHomProperty
      (weakEquivalences SSet.{u})).of_retract
        (Retract.ofIso e.symm) hExt
  exact (KanQuillenReuse.weakEquivalence_iff_geometric _).mp
    ((weakEquivalence_iff _).mpr (hSup p q))

/-- A cobase change of a local geometric weak equivalence along the actual
ordinary object-cell pushout is locally geometric on every target Hom. -/
theorem point_cell_cobase_local
    {C D PC PD : SimplicialCat.{u, u}}
    {a : OrdinaryBergnerGenerators.empty.{u} ⟶ C}
    (i : C ⟶ PC)
    (g : OrdinaryBergnerGenerators.point.{u} ⟶ PC)
    (sqC : IsPushout a OrdinaryBergnerGenerators.emptyToPoint i g)
    (F : C ⟶ D) (j : D ⟶ PD) (Fplus : PC ⟶ PD)
    (sq : IsPushout F i j Fplus)
    (hF : ∀ x y : C.Obj,
      DaggerOrdinaryCellComparisonGeometric.GW (F.map x y))
    (p q : PC.Obj) :
    DaggerOrdinaryCellComparisonGeometric.GW (Fplus.map p q) := by
  have sqD : IsPushout (a ≫ F) OrdinaryBergnerGenerators.emptyToPoint
      j (g ≫ Fplus) := sqC.paste_horiz sq
  exact supplied_comparison_local i g sqC F j (g ≫ Fplus) sqD
    Fplus sq.w.symm rfl hF p q

end

end DaggerModels.OrdinaryPointCellComparison
