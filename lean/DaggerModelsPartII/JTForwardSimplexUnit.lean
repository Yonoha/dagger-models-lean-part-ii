import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModelsPartII.ActualUnitNativeComparison

/-!
# The actual forward simplex map retains the original free-dagger unit

The concrete pushout comparison carries its first coprojection to the original
free-dagger unit. The chosen reversal representable comparison then computes
the forward copy directly by the native representable/Lan unit equation.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTForwardSimplexUnit

open DaggerJTFrameUnderlying JTXiEndpointCollapseBoundary

noncomputable section

/-- The literal forward map is the original free-dagger unit followed by
the inverse chosen reversal-simplex comparison, after forgetting dagger. -/
theorem forwardSimplexNat_app (m : SimplexCategory) :
    forwardSimplexNat.app m =
      freeDaggerAdjunction.unit.app (SSet.stdSimplex.obj m) ≫
        (reversalSimplexFreeIso.inv.app m).hom := by
  change (𝟙 _ ≫ FreeDaggerPushout.inl (SSet.stdSimplex.obj m) ≫ 𝟙 _ ≫
    (FreeDaggerPushout.isoFreeDagger.hom.app (SSet.stdSimplex.obj m)).hom ≫
      (reversalSimplexFreeIso.inv.app m).hom ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]
  have hu : FreeDaggerPushout.inl (SSet.stdSimplex.obj m) ≫
      (FreeDaggerPushout.isoFreeDagger.hom.app (SSet.stdSimplex.obj m)).hom =
      freeDaggerAdjunction.unit.app (SSet.stdSimplex.obj m) :=
    FreeDaggerPushout.inl_isoFreeDagger_hom (SSet.stdSimplex.obj m)
  rw [← Category.assoc, hu]

/-- Every ordinary simplex generator maps to its actual included reversal
map, under the original chosen forward-copy construction. -/
theorem forwardSimplexNat_apply {m n : SimplexCategory} (f : m ⟶ n) :
    (forwardSimplexNat.app n).app (op m) (SSet.stdSimplex.objEquiv.symm f) =
      ULift.up (ReverseSimplex.inclusion.map f) := by
  rw [forwardSimplexNat_app]
  change ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{0}
    ReverseSimplex.inclusion).inv.app n).app
      (op (ReverseSimplex.inclusion.obj m))
    ((ReverseSimplex.inclusion.op.lanUnit.app
      ((uliftYoneda.{0, 0}).obj n)).app (op m)
      (ULift.up f)) = ULift.up (ReverseSimplex.inclusion.map f)
  exact (congr_fun (Functor.descOfIsLeftKanExtension_fac_app _
    (ReverseSimplex.inclusion.op.lanUnit.app
      ((uliftYoneda.{0, 0}).obj n)) _
    (uliftYonedaMap.{0} ReverseSimplex.inclusion n)
    (op m)) (ULift.up f)).trans (by rfl)

/-- The actual forward simplex sends the ordinary identity to the identity
of the represented reversal simplex. -/
theorem forwardSimplexNat_identity (m : SimplexCategory) :
    SSet.yonedaEquiv (forwardSimplexNat.app m) =
      ULift.up (𝟙 (ReverseSimplex.inclusion.obj m)) := by
  simpa only [Functor.map_id] using forwardSimplexNat_apply (𝟙 m)

end

end DaggerModels.PartII.JTForwardSimplexUnit
