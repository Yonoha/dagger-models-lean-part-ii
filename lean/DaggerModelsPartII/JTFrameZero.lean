import DaggerModelsPartII.DaggerJTFrameUnderlying
import DaggerModelsPartII.DaggerJTConstantRealization
import DaggerModelsPartII.IndexKanExtensions
import DaggerModelsPartII.ConstantVertexAdjunction

/-!
# Degree-zero normalization of the dagger JT frame

The represented pair at vertical degree zero is the constant simplicial
diagram on the reversal representable. The constant-realization isomorphism
then identifies the resulting dagger frame with the native represented
dagger simplex, naturally in the full reversal simplex index.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTFrameZero

open SegalLocalizers DaggerJTAdjunction DaggerJTRepresentedFrames
open DaggerJTFrameUnderlying DaggerJTRealization

noncomputable section

/-- Hold the ordinary JT simplex index at zero. -/
def zeroSection : ReverseSimplex ⥤ DaggerIndex :=
  CategoryTheory.Prod.sectL ReverseSimplex ⦋0⦌

/-- The degree-zero represented pair before dagger realization. -/
def zeroRepresentedPair : ReverseSimplex ⥤ ReverseDaggerSpace.{0} :=
  zeroSection ⋙ representedPair

/-- At each bidegree, discard the unique simplex of `Δ[0]`. -/
def zeroRepresentedPointEquiv (m d : ReverseSimplex)
    (n : SimplexCategory) :
    ((zeroRepresentedPair.obj m).obj (op d)).obj (op n) ≃
      (((uliftYoneda.{0} ⋙ discretePresheaf.{0, 0} ReverseSimplex).obj m).obj
        (op d)).obj (op n) where
  toFun x := ULift.up x.down.1
  invFun x := ULift.up (x.down, SimplexCategory.isTerminalZero.from n)
  left_inv x := by
    rcases x with ⟨⟨a, b⟩⟩
    have hb : SimplexCategory.isTerminalZero.from n = b :=
      SimplexCategory.isTerminalZero.hom_ext _ _
    cases hb
    rfl
  right_inv x := by cases x; rfl

/-- The degree-zero pair is the vertical constant diagram on Yoneda. -/
def zeroRepresentedPairIso (m : ReverseSimplex) :
    zeroRepresentedPair.obj m ≅
      (discretePresheaf.{0, 0} ReverseSimplex).obj (uliftYoneda.{0}.obj m) :=
  NatIso.ofComponents
    (fun d => NatIso.ofComponents
      (fun n => (zeroRepresentedPointEquiv m d.unop n.unop).toIso)
      (by intro n n' f; ext x; rfl))
    (by intro d d' f; apply NatTrans.ext; funext n x; rfl)

/-- The zero-pair identification is natural in every reversal-simplex map. -/
def zeroRepresentedPairNatIso :
    zeroRepresentedPair ≅
      uliftYoneda.{0} ⋙ discretePresheaf.{0, 0} ReverseSimplex :=
  NatIso.ofComponents zeroRepresentedPairIso (by
    intro m m' f
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext n x
    rfl)

/-- The dagger JT frame at ordinary degree zero is the native reversal
simplex, as a natural isomorphism of dagger simplicial sets. -/
def frameZeroIso :
    zeroSection ⋙ frame ≅ reversalSimplex :=
  Functor.isoWhiskerLeft zeroSection
    (Functor.associator uliftYoneda sourceEquivalence.inverse
      daggerRealization).symm ≪≫
  (Functor.associator zeroSection representedPair daggerRealization).symm ≪≫
  Functor.isoWhiskerRight zeroRepresentedPairNatIso daggerRealization ≪≫
  Functor.associator uliftYoneda (discretePresheaf ReverseSimplex)
    daggerRealization ≪≫
  Functor.isoWhiskerLeft uliftYoneda
    DaggerJTConstantRealization.constantRealizationIso

/-- The original constant-vertex dagger realization recovers each dagger
simplicial set, naturally in the source. -/
def deltaRealizationIso :
    ConstantVertexAdjunction.delta ⋙ daggerRealization ≅
      𝟭 DaggerSSet.{0} :=
  Functor.associator DaggerSSet.toPresheaf
    (discretePresheaf ReverseSimplex) daggerRealization ≪≫
  Functor.isoWhiskerLeft DaggerSSet.toPresheaf
    DaggerJTConstantRealization.constantRealizationIso ≪≫
  DaggerSSet.unitIso.symm

end

end DaggerModels.PartII.JTFrameZero
