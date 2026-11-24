import DaggerModelsPartII.DaggerJTRepresentedFrames
import DaggerModelsPartII.JTRealizationBox

/-!
# Underlying simplicial sets of the represented dagger JT frames

The product-Yoneda comparison and ordinary JT box formula identify the
underlying represented frames, naturally in both reversal and ordinary
simplex indices. The reversal-simplex diagram is the native dagger
restriction of Yoneda and agrees with the free dagger standard simplices.
-/

set_option autoImplicit false

open CategoryTheory Opposite MonoidalCategory DaggerModels

namespace DaggerModels.PartII.DaggerJTFrameUnderlying

open DaggerJTAdjunction DaggerJTRealization DaggerJTRepresentedFrames
open JTReversalInput JTRealizationBox

noncomputable section

/-- The native dagger simplex represented by each reversal index. -/
def reversalSimplex : ReverseSimplex ⥤ DaggerSSet.{0} :=
  uliftYoneda.{0} ⋙ ReversePresheaf.toDaggerSSet

/-- The same represented simplex after forgetting dagger. -/
def underlyingSimplex : ReverseSimplex ⥤ SSet.{0} :=
  reversalSimplex ⋙ DaggerSSet.forget

/-- Restricting the represented tensor to ordinary indices is literally
the external box for the underlying represented dagger simplex. -/
def representedOrdinaryBoxIso :
    representedTensorPair ⋙ ordinaryInput ≅
      (underlyingSimplex.prod (𝟭 SimplexCategory)) ⋙ boxStandard :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro p q f; rfl)

/-- The original product parameter, with the native reversal simplex in
its first variable. -/
def frameParameter : DaggerIndex ⥤ SSet.{0} :=
  (underlyingSimplex.prod GroupoidSimplex.parameter) ⋙
    MonoidalCategory.tensor SSet.{0}

/-- The actual represented dagger frame has the ordinary product formula,
jointly naturally in the full reversal index and the ordinary parameter. -/
def frameUnderlyingIso : frame ⋙ DaggerSSet.forget ≅ frameParameter :=
  Functor.isoWhiskerRight frameRepresentation DaggerSSet.forget ≪≫
    Functor.associator representedTensorPair daggerRealization DaggerSSet.forget ≪≫
    Functor.isoWhiskerLeft representedTensorPair (eqToIso daggerRealization_underlying) ≪≫
    (Functor.associator representedTensorPair ordinaryInput
      OrdinaryJTRealization.realization).symm ≪≫
    Functor.isoWhiskerRight representedOrdinaryBoxIso OrdinaryJTRealization.realization ≪≫
    Functor.associator (underlyingSimplex.prod (𝟭 SimplexCategory)) boxStandard
      OrdinaryJTRealization.realization ≪≫
    Functor.isoWhiskerLeft (underlyingSimplex.prod (𝟭 SimplexCategory)) realizationBoxIso

/-- On ordinary simplex maps, the native reversal-simplex diagram is the
original free dagger functor on standard simplices. -/
def reversalSimplexFreeIso :
    ReverseSimplex.inclusion ⋙ reversalSimplex ≅ SSet.stdSimplex.{0} ⋙ freeDagger :=
  (Functor.associator ReverseSimplex.inclusion uliftYoneda
    ReversePresheaf.toDaggerSSet).symm ≪≫
    Functor.isoWhiskerRight
      (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{0} ReverseSimplex.inclusion)
      ReversePresheaf.toDaggerSSet ≪≫
    Functor.associator SSet.stdSimplex ReverseSimplex.inclusion.op.lan
      ReversePresheaf.toDaggerSSet

end

end DaggerModels.PartII.DaggerJTFrameUnderlying
