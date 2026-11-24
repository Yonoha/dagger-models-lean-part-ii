import OrdinaryCSSWalkingRestrictions
import ActualFreeWalkingIsoIntegerObstructionReconciled
import ActualWalkingIsoCategoricalCylinder

/-!
# Calibration of the CSS walking parameter with the original Joyal interval

The groupoid-completed one-simplex and the retained native walking interval
are identified through the codiscrete groupoid on their two original vertices.
The selected zero vertex is preserved exactly, so lifting tests transfer
without replacing a map by an uncalibrated equivalent interval.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingParameterCalibration

noncomputable section

private abbrev Walking := DaggerModels.OriginalWalkingIsoIntegerObstruction.walkingIso.{0}
private abbrev J := DaggerActualFreeWalkingIsoIntegerObstruction.J.{0}

private def toFinite : Walking ⥤ Codiscrete (Fin 2) where
  obj x := ⟨if (ULift.down x).as then 1 else 0⟩
  map _ := ⟨⟩

private def fromFinite : Codiscrete (Fin 2) ⥤ Walking where
  obj x := DaggerActualWalkingIsoCategoricalCylinder.parameterObject (decide (x.as = 1))
  map _ := ⟨⟨⟩⟩

private def walkingCodiscreteIso : Cat.of Walking ≅ Cat.of (Codiscrete (Fin 2)) where
  hom := toFinite.toCatHom
  inv := fromFinite.toCatHom
  hom_inv_id := by
    apply Cat.ext
    change toFinite ⋙ fromFinite = 𝟭 _
    have ho : ∀ x, (toFinite ⋙ fromFinite).obj x = (𝟭 Walking).obj x := by
      intro x
      rcases x with ⟨⟨x⟩⟩
      cases x <;> rfl
    exact CategoryTheory.Functor.ext ho (by intros; exact Subsingleton.elim _ _)
  inv_hom_id := by
    apply Cat.ext
    change fromFinite ⋙ toFinite = 𝟭 _
    have ho : ∀ x, (fromFinite ⋙ toFinite).obj x = (𝟭 (Codiscrete (Fin 2))).obj x := by
      intro x
      rcases x with ⟨x⟩
      have h : x = 0 ∨ x = 1 := by omega
      rcases h with rfl | rfl <;> rfl
    exact CategoryTheory.Functor.ext ho (by intros; exact Subsingleton.elim _ _)

/-- The completed one-simplex is the actual retained ordinary walking interval. -/
def parameterWalkingIso : GroupoidSimplex.parameter.obj ⦋1⦌ ≅ J :=
  GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌ ≪≫
    (nerveFunctor.mapIso walkingCodiscreteIso).symm

/-- The isomorphism preserves the actual registered zero vertex on the nose. -/
theorem parameterVertex_comp :
    JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ parameterWalkingIso.hom =
      DaggerActualFreeWalkingIsoIntegerObstruction.zeroInclusion.{0} := by
  apply NatTrans.ext
  funext q x
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- The two literal selected-vertex arrows are isomorphic with fixed source. -/
def vertexArrowIso : Arrow.mk (JTParameterContraction.parameterVertex ⦋1⦌ 0) ≅
    Arrow.mk DaggerActualFreeWalkingIsoIntegerObstruction.zeroInclusion.{0} :=
  Arrow.isoMk (Iso.refl _) parameterWalkingIso (by simpa using parameterVertex_comp.symm)

/-- Every original vertical monomorphism restriction of a CSS-fibrant target
lifts against the zero vertex of the native Joyal walking interval. -/
theorem restriction_nativeWalking_lifting (W : OrdinaryCSSLocalization.Space)
    (hW : @HomotopicalAlgebra.IsFibrant OrdinaryCSSLocalization.Space _
      OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] :
    HasLiftingProperty DaggerActualFreeWalkingIsoIntegerObstruction.zeroInclusion.{0}
      (diagramRestrictionPre v W.flip) :=
  (HasLiftingProperty.iff_of_arrow_iso_left vertexArrowIso _).mp
    (OrdinaryCSSWalkingRestrictions.restriction_walking_lifting W hW v)

#print axioms parameterWalkingIso
#print axioms parameterVertex_comp
#print axioms vertexArrowIso
#print axioms restriction_nativeWalking_lifting

end
end DaggerModels.PartII.OrdinaryWalkingParameterCalibration
