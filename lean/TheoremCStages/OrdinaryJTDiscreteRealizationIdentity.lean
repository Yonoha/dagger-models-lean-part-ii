import OrdinaryJTConstantRealizationIdentity
import OrdinaryJTCurriedAdjunction
import OrdinaryCSSLocalization

/-!
# Ordinary JT realization of a horizontally discrete simplicial set

The CSS discrete functor is the first-index constant bisimplicial functor
after the checked currying equivalence. The equivalence unit removes the
currying and uncurrying pair. The checked constant-realization identity then
gives an isomorphism of the actual composite left adjoint with the identity.
No model-category or weak-equivalence assumption enters this identity.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial

namespace DaggerModels.PartII.OrdinaryJTDiscreteRealizationIdentity

open OrdinaryCSSLocalization OrdinaryJTCurriedAdjunction
open OrdinaryJTConstantRealizationIdentity

noncomputable section

/-- At each horizontal degree, the two vertical simplicial sets have the
same simplices and the same vertical operators. -/
private def rowIso (X : SSet.{0}) (q : SimplexCategoryᵒᵖ) :
    (discrete.obj X).obj q ≅
      ((p1Constant ⋙ curryEquivalence.functor).obj X).obj q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro k l θ
    simp [discrete, p1Constant, curryEquivalence, firstProjection])

/-- The rowwise identity maps respect every horizontal operator. -/
private def objectIso (X : SSet.{0}) :
    discrete.obj X ≅ (p1Constant ⋙ curryEquivalence.functor).obj X :=
  NatIso.ofComponents (rowIso X) (by
    intro q r θ
    apply NatTrans.ext
    funext k
    simp [rowIso, discrete, p1Constant, curryEquivalence, firstProjection])

/-- Literal horizontal discreteness is naturally isomorphic to first-index
constancy followed by the existing currying equivalence. -/
def discreteConstantCurryIso :
    discrete ≅ p1Constant ⋙ curryEquivalence.functor :=
  NatIso.ofComponents objectIso (by
    intro X Y f
    apply NatTrans.ext
    funext q
    apply NatTrans.ext
    funext k
    simp [objectIso, rowIso, discrete, p1Constant, curryEquivalence,
      firstProjection])

/-- Uncurrying a horizontally discrete object recovers the actual
first-index constant bisimplicial object, naturally in its input. -/
def discreteUncurryIso :
    discrete ⋙ curryEquivalence.inverse ≅ p1Constant :=
  (Functor.isoWhiskerRight discreteConstantCurryIso curryEquivalence.inverse) ≪≫
    Functor.associator p1Constant curryEquivalence.functor
      curryEquivalence.inverse ≪≫
    Functor.isoWhiskerLeft p1Constant curryEquivalence.unitIso.symm ≪≫
    p1Constant.rightUnitor

/-- The literal CSS discrete functor followed by the original curried JT
left adjoint is naturally isomorphic to the identity on simplicial sets. -/
def discreteRealizationIdentityIso : discrete ⋙ left ≅ 𝟭 SSet.{0} :=
  (Functor.associator discrete curryEquivalence.inverse
      OrdinaryJTRealization.realization).symm ≪≫
    Functor.isoWhiskerRight discreteUncurryIso
      OrdinaryJTRealization.realization ≪≫
    realizationIdentityIso

#print axioms discreteConstantCurryIso
#print axioms discreteUncurryIso
#print axioms discreteRealizationIdentityIso

end

end DaggerModels.PartII.OrdinaryJTDiscreteRealizationIdentity
