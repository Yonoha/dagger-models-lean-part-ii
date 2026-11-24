import OrdinaryJTRightNerveReedy
import OrdinaryJTRightNerveSegal
import DaggerModelsPartII.JTRealizationDiagonal

/-!
# Reedy fibrancy of the literal ordinary JT right nerve

The original two-index nerve is curried in its first simplicial index.
Its rows are naturally the already checked ordinary mapping spaces of the
standard simplices. This transfers full Reedy fibrancy to the native rows.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
  MonoidalCategory DaggerModels
open scoped SSet.modelCategoryQuillen
open scoped Prod

namespace DaggerModels.PartII.OrdinaryJTNativeRightNerveReedy

noncomputable section

/-- The literal ordinary JT right nerve, curried from the actual two-index
restricted Yoneda functor. -/
def nativeSpace (X : SSet.{0}) : SimplexCategoryᵒᵖ ⥤ SSet.{0} :=
  JTRealizationDiagonal.ordinaryCurry.obj (OrdinaryJTRealization.nerve.obj X)

/-- Each object of the native diagram is the original ordinary row. -/
theorem nativeSpace_obj (X : SSet.{0}) (m : SimplexCategory) :
    (nativeSpace X).obj (op m) = JTRightAdjointOrderedFiber.ordinaryRow X m := rfl

/-- The horizontal operator is the original first-index operator of the
two-index right nerve. -/
theorem nativeSpace_map_app (X : SSet.{0})
    {r q : SimplexCategory} (δ : r ⟶ q) (k : SimplexCategory) :
    ((nativeSpace X).map δ.op).app (op k) =
      (OrdinaryJTRealization.nerve.obj X).map (δ ×ₘ 𝟙 k).op :=
  JTRealizationDiagonal.ordinaryCurry_obj_map_app
    (OrdinaryJTRealization.nerve.obj X) δ k

private theorem rowMappingIso_hom_app (X : SSet.{0})
    (m k : SimplexCategory)
    (z : (JTRightAdjointOrderedFiber.ordinaryRow X m).obj (op k)) :
    ((OrdinaryJTRightNerveSegal.rowMappingIso X m).hom.app (op k)) z =
      z.down := by
  dsimp [OrdinaryJTRightNerveSegal.rowMappingIso,
    JTRightAdjointOrderedFiber.ordinaryRowHomIso]
  rw [CategoryTheory.eqToHom_app]
  rfl

/-- The native rows are naturally the full ordinary JT mapping spaces of
the standard simplices, with their original horizontal operators. -/
def nativePlainIso (X : SSet.{0}) :
    nativeSpace X ≅ OrdinaryJTRightNerveReedy.plainSpace X :=
  NatIso.ofComponents
    (fun m ↦ OrdinaryJTRightNerveSegal.rowMappingIso X m.unop)
    (by
      intro m n θ
      apply NatTrans.ext
      funext k
      change ((nativeSpace X).map θ).app k ≫
          (OrdinaryJTRightNerveSegal.rowMappingIso X n.unop).hom.app k =
        (OrdinaryJTRightNerveSegal.rowMappingIso X m.unop).hom.app k ≫
          ((OrdinaryJTRightNerveReedy.plainSpace X).map θ).app k
      funext z
      have hnative : ((nativeSpace X).map θ).app k =
          (OrdinaryJTRealization.nerve.obj X).map
            (θ.unop ×ₘ 𝟙 k.unop).op :=
        nativeSpace_map_app X θ.unop k.unop
      rw [hnative]
      change
        ((OrdinaryJTRightNerveSegal.rowMappingIso X n.unop).hom.app k)
            (((OrdinaryJTRealization.nerve.obj X).map
              (θ.unop ×ₘ 𝟙 k.unop).op) z) =
          ((OrdinaryJTRightNerveReedy.plainSpace X).map θ).app k
            (((OrdinaryJTRightNerveSegal.rowMappingIso X m.unop).hom.app k) z)
      rw [rowMappingIso_hom_app, rowMappingIso_hom_app]
      change
        (OrdinaryJTRealization.tFunctor.map (θ.unop ×ₘ 𝟙 k.unop)) ≫ z.down =
          (SSet.stdSimplex.map θ.unop ▷
            GroupoidSimplex.parameter.obj k.unop) ≫ z.down
      rw [OrdinaryJTRealization.tFunctor_map,
        GroupoidSimplex.parameter.map_id,
        MonoidalCategory.tensorHom_id])

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  simplicialReedyModelCategory SSet.{0}

/-- The literal native ordinary JT right nerve is Reedy fibrant over every
quasicategory, with the whole horizontal simplicial diagram retained. -/
theorem nativeSpace_reedyFibrant (X : SSet.{0}) [X.Quasicategory] :
    IsFibrant (nativeSpace X) := by
  letI : IsFibrant (OrdinaryJTRightNerveReedy.plainSpace X) :=
    OrdinaryJTRightNerveReedy.plainSpace_reedyFibrant X
  rw [isFibrant_iff]
  rw [Subsingleton.elim (terminal.from (nativeSpace X))
    ((nativePlainIso X).hom ≫
      terminal.from (OrdinaryJTRightNerveReedy.plainSpace X))]
  infer_instance

#print axioms nativeSpace_obj
#print axioms nativeSpace_map_app
#print axioms nativePlainIso
#print axioms nativeSpace_reedyFibrant

end

end DaggerModels.PartII.OrdinaryJTNativeRightNerveReedy
