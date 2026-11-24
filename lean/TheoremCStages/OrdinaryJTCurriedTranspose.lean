import OrdinaryJTCurriedAdjunction

/-!
# Transpose comparison for the original ordinary JT adjunction

The transpose after currying is the image under the literal curry functor
of the original two-index transpose. The source morphism uses the inverse
of the actual equivalence unit, so no alternate raw nerve or unit is
introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryJTCurriedTranspose

noncomputable section

/-- Transporting an adjunction across an equivalence carries the transpose
of an inverse-unit-precomposed map to the functor image of the original
transpose. -/
private theorem transpose_comp_equivalence
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (L : C ⥤ E) (R : E ⥤ C) (a : L ⊣ R)
    (B : C) (X : E) (f : L.obj B ⟶ X) :
    ((e.symm.toAdjunction.comp a).homEquiv (e.functor.obj B) X)
        (L.map (e.unitIso.inv.app B) ≫ f) =
      e.functor.map ((a.homEquiv B X) f) := by
  rw [Adjunction.comp_homEquiv]
  change (e.symm.toAdjunction.homEquiv (e.functor.obj B) (R.obj X))
      ((a.homEquiv (e.inverse.obj (e.functor.obj B)) X)
        (L.map (e.unitInv.app B) ≫ f)) = _
  rw [a.homEquiv_naturality_left]
  rw [e.symm.toAdjunction.homEquiv_unit]
  change e.counitInv.app (e.functor.obj B) ≫
      e.functor.map (e.unitInv.app B ≫ (a.homEquiv B X) f) = _
  rw [e.functor.map_comp, ← Category.assoc, e.counitInv_functor_comp]
  exact Category.id_comp _

/-- The curried transpose of the actual original-realization morphism is
the curry of its original two-index restricted-Yoneda transpose. -/
theorem realization_transpose_curry
    (B : OrdinaryJTRealization.BiPresheaf) (X : SSet.{0})
    (f : OrdinaryJTRealization.realization.obj B ⟶ X) :
    (OrdinaryJTCurriedAdjunction.adjunction.homEquiv
        (OrdinaryJTCurriedAdjunction.curryEquivalence.functor.obj B) X)
        (OrdinaryJTRealization.realization.map
          (OrdinaryJTCurriedAdjunction.curryEquivalence.unitIso.inv.app B) ≫ f) =
      JTRealizationDiagonal.ordinaryCurry.map
        ((OrdinaryJTRealization.realizationNerveAdjunction.homEquiv B X) f) := by
  exact transpose_comp_equivalence
    OrdinaryJTCurriedAdjunction.curryEquivalence
    OrdinaryJTRealization.realization OrdinaryJTRealization.nerve
    OrdinaryJTRealization.realizationNerveAdjunction B X f

#print axioms realization_transpose_curry

end
end DaggerModels.PartII.OrdinaryJTCurriedTranspose
