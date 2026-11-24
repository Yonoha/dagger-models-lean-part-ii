import OrdinaryJTCurriedAdjunction
import OrdinaryJTPlainMapReedy
import DaggerModelsPartII.RelativeArrows

/-!
# Relative Reedy fibrations of the actual ordinary JT right adjoint

The two-index restricted-Yoneda nerve is retained literally. Its curried
map is compared with the plain mapping-row map through the checked native
row isomorphism. Functoriality of relative matching arrows then transports
the full Reedy fibration property.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTNativeMapReedy

open OrdinaryJTCurriedAdjunction OrdinaryJTNativeRightNerveReedy
open OrdinaryJTRightNerveReedy OrdinaryJTPlainMapReedy
open OrdinaryJTMappingCornerFibration

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private theorem rowMappingIso_hom_app (X : SSet.{0})
    (m k : SimplexCategory)
    (z : (JTRightAdjointOrderedFiber.ordinaryRow X m).obj (op k)) :
    ((OrdinaryJTRightNerveSegal.rowMappingIso X m).hom.app (op k)) z =
      z.down := by
  dsimp [OrdinaryJTRightNerveSegal.rowMappingIso,
    JTRightAdjointOrderedFiber.ordinaryRowHomIso]
  rw [CategoryTheory.eqToHom_app]
  rfl

/-- The actual curried restricted-Yoneda map commutes with the full native
row-to-mapping-row isomorphism, in both simplicial indices. -/
theorem nativePlainIso_naturality {X Y : SSet.{0}} (p : X ⟶ Y) :
    right.map p ≫ (nativePlainIso Y).hom =
      (nativePlainIso X).hom ≫ plainMap p := by
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext k z
  change ((OrdinaryJTRightNerveSegal.rowMappingIso Y m.unop).hom.app k)
      (((right.map p).app m).app k z) =
    ((mappingPost p (SSet.stdSimplex.obj m.unop)).app k)
      (((OrdinaryJTRightNerveSegal.rowMappingIso X m.unop).hom.app k) z)
  rw [rowMappingIso_hom_app, rowMappingIso_hom_app]
  change (((OrdinaryJTRealization.nerve.map p).app
      (op (m.unop, k.unop))) z).down = z.down ≫ p
  rfl

/-- The actual right-adjoint arrow and its ordinary mapping-row arrow are
isomorphic in the arrow category of full simplicial diagrams. -/
def rightPlainMapArrowIso {X Y : SSet.{0}} (p : X ⟶ Y) :
    Arrow.mk (right.map p) ≅ Arrow.mk (plainMap p) :=
  Arrow.isoMk (nativePlainIso X) (nativePlainIso Y)
    (nativePlainIso_naturality p).symm

/-- An original Joyal fibration is sent by the actual curried ordinary JT
right adjoint to a native Kan Reedy fibration. -/
theorem right_map_relativeReedyFibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : ordinaryJoyalModel.categoryWithFibrations.fibrations p) :
    reedyMatchingProperty (fibrations SSet.{0}) (right.map p) := by
  intro n
  let e := (relativeMatchingArrows (matchingComparison n)).mapIso
    (rightPlainMapArrowIso p)
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff e).mpr
    (plainMap_relativeReedyFibration p hp n)

#print axioms nativePlainIso_naturality
#print axioms rightPlainMapArrowIso
#print axioms right_map_relativeReedyFibration

end
end DaggerModels.PartII.OrdinaryJTNativeMapReedy
