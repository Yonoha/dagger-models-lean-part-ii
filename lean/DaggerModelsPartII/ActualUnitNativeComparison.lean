import DaggerModelsPartII.DaggerNerveLengthOne

/-!
# The representable change-of-index unit and the native free simplex map

The comparison is stated as an equality of natural transformations on the
actual reversal-simplex diagram, after the chosen representable isomorphisms.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexPartIIndex
open DaggerModels.PartII.DaggerSimplexNerveRepresentable
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.SegalRepresentables
open DaggerModels.PartII.ActualIndexProjectiveModel
open DaggerModels.PartII.DaggerSimplexNerveNaturality
open DaggerModels.PartII.DaggerNerveLengthOne

namespace DaggerModels.PartII.ActualUnitNativeComparison

noncomputable section

/-- The actual change-of-index unit, transported to the chosen free dagger
simplex and native nerve presentations. -/
def actualUnitNativeMap (n : ℕ) :
    daggerSimplex.{0} n ⟶
      discreteDagger.obj
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex n)) :=
  (freeSimplexRepresentable.{0} n).hom ≫
    ((actualLeftAdjunction.{0}).unit.app
      ((simplicialYoneda.{0, 0} ReverseSimplex).obj (ReverseSimplex.mk n))) ≫
    (actualRestriction.{0}).map
      ((actualLeftExtension_simplicialYoneda.{0}).hom.app
        (ReverseSimplex.mk n)) ≫
    (actualRepresentableNativeDaggerSpaceIso n).hom

theorem freeSimplexRepresentable_unit_apply {k n : ℕ}
    (q : SimplexCategoryᵒᵖ) (f : ⦋k⦌ ⟶ ⦋n⦌) :
    ((freeSimplexRepresentable.{0} n).hom.app
      (op (ReverseSimplex.mk k))).app q
        ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
          (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)) =
      ULift.up (ReverseSimplex.inclusion.map f) := by
  change ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{0}
    ReverseSimplex.inclusion).inv.app ⦋n⦌).app
      (op (ReverseSimplex.inclusion.obj ⦋k⦌))
    ((ReverseSimplex.inclusion.op.lanUnit.app
      ((uliftYoneda.{0, 0}).obj ⦋n⦌)).app (op ⦋k⦌)
      (ULift.up f)) = ULift.up (ReverseSimplex.inclusion.map f)
  exact (congr_fun (Functor.descOfIsLeftKanExtension_fac_app _
    (ReverseSimplex.inclusion.op.lanUnit.app
      ((uliftYoneda.{0, 0}).obj ⦋n⦌)) _
    (uliftYonedaMap.{0} ReverseSimplex.inclusion ⦋n⦌)
    (op ⦋k⦌)) (ULift.up f)).trans (by rfl)

theorem actualHomNativeNerveEquiv_actualU {k n : ℕ}
    (α : ReverseSimplex.mk k ⟶ ReverseSimplex.mk n) :
    actualHomNativeNerveEquiv k n (actualU.map α) =
      pathHomChainEquiv k n (u.map α) := by
  change pathHomChainEquiv k n
    ((actualHomEquiv ⟨k⟩ ⟨n⟩).symm
      ((actualHomEquiv ⟨k⟩ ⟨n⟩) (u.map α))) = _
  rw [Equiv.symm_apply_apply]

/-- On every ordinary simplex generator, the transported actual unit and
the canonical free dagger map have the same native chain value. -/
theorem actualUnitNativeMap_unit_apply {k n : ℕ}
    (q : SimplexCategoryᵒᵖ) (f : ⦋k⦌ ⟶ ⦋n⦌) :
    ((actualUnitNativeMap n).app (op (ReverseSimplex.mk k))).app q
      ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
        (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)) =
    ((discreteDagger.map (canonicalDaggerMap n)).app
      (op (ReverseSimplex.mk k))).app q
      ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
        (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)) := by
  rw [show ((actualUnitNativeMap n).app (op (ReverseSimplex.mk k))).app q
      ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
        (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)) =
      actualHomNativeNerveEquiv k n
        (actualU.map (ReverseSimplex.inclusion.map f)) by
    change ((actualRepresentableNativeDaggerSpaceIso n).hom.app
      (op (ReverseSimplex.mk k))).app q
      ((((actualLeftAdjunction.{0}).unit.app
        ((simplicialYoneda.{0, 0} ReverseSimplex).obj (ReverseSimplex.mk n)) ≫
        (actualRestriction.{0}).map
          ((actualLeftExtension_simplicialYoneda.{0}).hom.app
            (ReverseSimplex.mk n))).app (op (ReverseSimplex.mk k))).app q
        (((freeSimplexRepresentable.{0} n).hom.app
          (op (ReverseSimplex.mk k))).app q
            ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
              (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)))) = _
    rw [freeSimplexRepresentable_unit_apply]
    exact actualUnit_native_chain_apply
      (ReverseSimplex.mk k) (ReverseSimplex.mk n) q
      (ReverseSimplex.inclusion.map f)]
  rw [actualHomNativeNerveEquiv_actualU]
  change pathHomChainEquiv k n (u.map (ReverseSimplex.inclusion.map f)) =
    (canonicalDaggerMap n).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
        (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f))
  have h := congrFun (NatTrans.congr_app (canonicalDaggerMap_unit n)
    (op ⦋k⦌)) (SSet.stdSimplex.objEquiv.symm f)
  change (canonicalDaggerMap n).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
        (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm f)) =
      (canonicalSimplex n).app (op ⦋k⦌)
        (SSet.stdSimplex.objEquiv.symm f) at h
  exact (h.trans (canonicalSimplex_apply f)).symm

/-- The free dagger unit on the identity ordinary simplex is the chosen
generator of the reversal representable. -/
theorem freeSimplexRepresentable_unit_id (n : ℕ)
    (q : SimplexCategoryᵒᵖ) :
    ((freeSimplexRepresentable.{0} n).hom.app
      (op (ReverseSimplex.mk n))).app q
        ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
          (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      ULift.up (𝟙 (ReverseSimplex.mk n)) := by
  simpa only [Functor.map_id] using
    freeSimplexRepresentable_unit_apply q (𝟙 ⦋n⦌)

/-- Two maps from the free dagger representable agree if they agree on its
ordinary identity generator. -/
theorem freeSimplex_hom_ext (n : ℕ)
    {Y : ReverseDaggerSpace.{0}} (g h : daggerSimplex.{0} n ⟶ Y)
    (hgen : ∀ q : SimplexCategoryᵒᵖ,
      (g.app (op (ReverseSimplex.mk n))).app q
          ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
            (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
        (h.app (op (ReverseSimplex.mk n))).app q
          ((freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
            (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) :
    g = h := by
  ext m q x
  let e := freeSimplexRepresentable.{0} n
  let α : m.unop ⟶ ReverseSimplex.mk n :=
    (((e.hom.app m).app q) x).down
  let x₀ := (freeDaggerAdjunction.{0}.unit.app (Δ[n] : SSet.{0})).app
    (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
  have he₀ : ((e.hom.app (op (ReverseSimplex.mk n))).app q) x₀ =
      ULift.up (𝟙 (ReverseSimplex.mk n)) :=
    freeSimplexRepresentable_unit_id n q
  have hx : x = ((daggerSimplex.{0} n).map α.op).app q x₀ := by
    have heinj : Function.Injective ((e.hom.app m).app q) := by
      exact (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (e.hom.app m)).mp inferInstance q)
    apply heinj
    have hnat := congrFun
      (NatTrans.congr_app (e.hom.naturality α.op) q) x₀
    change ((e.hom.app m).app q)
        (((daggerSimplex.{0} n).map α.op).app q x₀) =
      (((simplicialYoneda.{0, 0} ReverseSimplex).obj
        (ReverseSimplex.mk n)).map α.op).app q
          (((e.hom.app (op (ReverseSimplex.mk n))).app q) x₀) at hnat
    rw [he₀] at hnat
    simpa only [α] using hnat.symm
  rw [hx]
  have hg := congrFun (NatTrans.congr_app (g.naturality α.op) q) x₀
  have hh := congrFun (NatTrans.congr_app (h.naturality α.op) q) x₀
  change (g.app m).app q (((daggerSimplex.{0} n).map α.op).app q x₀) =
    (Y.map α.op).app q ((g.app (op (ReverseSimplex.mk n))).app q x₀) at hg
  change (h.app m).app q (((daggerSimplex.{0} n).map α.op).app q x₀) =
    (Y.map α.op).app q ((h.app (op (ReverseSimplex.mk n))).app q x₀) at hh
  rw [hg, hh, hgen q]

/-- The actual representable change-of-index unit is exactly the canonical
map from the free dagger simplex into the discrete native nerve, after the
chosen source and target representable isomorphisms. -/
theorem actualUnitNativeMap_eq_canonicalDaggerMap (n : ℕ) :
    actualUnitNativeMap n =
      discreteDagger.map (canonicalDaggerMap n) := by
  apply freeSimplex_hom_ext n
  intro q
  exact actualUnitNativeMap_unit_apply q (𝟙 ⦋n⦌)

end

end DaggerModels.PartII.ActualUnitNativeComparison
