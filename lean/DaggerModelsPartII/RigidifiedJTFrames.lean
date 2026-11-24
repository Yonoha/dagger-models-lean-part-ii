import DaggerModelsPartII.DaggerJTFrameUnderlying
import DaggerModelsPartII.JTFrameZero
import DaggerModelsPartII.ResolutionGeneratorCofibrancy
import ActualDaggerRigidificationQuillen

/-!
# Literal rigidified represented JT frames

The Part I rigidification is applied to the represented dagger JT frames.
The ordinary underlying comparison and the degree-zero identification are
natural in their indices.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial DaggerModels

namespace DaggerModels.PartII.RigidifiedJTFrames

open DaggerJTAdjunction DaggerJTFrameUnderlying
open DaggerJTRepresentedFrames DaggerJTRealization
open JTFrameZero
open OrdinaryRigidification
open OrdinaryRigidification.DaggerRigidification

noncomputable section

local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}

local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The rigidified represented frame, jointly functorial in both indices. -/
def Xi : DaggerIndex ⥤ DaggerSimplicialCat.{0, 0} :=
  frame ⋙ daggerRigidification

/-- The rigidified native reversal simplex. -/
def A : ReverseSimplex ⥤ DaggerSimplicialCat.{0, 0} :=
  reversalSimplex ⋙ daggerRigidification

/-- The represented formula for the actual rigidified dagger JT frame. -/
def XiRepresentedIso :
    Xi ≅ (representedTensorPair ⋙ daggerRealization) ⋙ daggerRigidification :=
  Functor.isoWhiskerRight frameRepresentation daggerRigidification

/-- At vertical degree zero the rigidified frame is the rigidified
reversal simplex, naturally in the full reversal index. -/
def XiZeroIso : zeroSection ⋙ Xi ≅ A :=
  Functor.associator zeroSection frame daggerRigidification ≪≫
    Functor.isoWhiskerRight frameZeroIso daggerRigidification

/-- The original ordinary rigidification is the strict underlying functor of
the literal dagger rigidification, applied to the represented JT frame. -/
def XiUnderlyingIso :
    Xi ⋙ DaggerSimplicialCat.forget ≅
      frameParameter ⋙ rigidification :=
  Functor.associator frame daggerRigidification
    DaggerSimplicialCat.forget ≪≫
  Functor.isoWhiskerLeft frame (eqToIso daggerRigidification_forget) ≪≫
  (Functor.associator frame DaggerSSet.forget rigidification).symm ≪≫
  Functor.isoWhiskerRight frameUnderlyingIso rigidification

/-- The represented reversal simplex is cofibrant in the original dagger
Joyal model, by the free-dagger comparison. -/
theorem reversalSimplex_isCofibrant (m : ReverseSimplex) :
    IsCofibrant (reversalSimplex.obj m) := by
  rcases m with ⟨n⟩
  let i := reversalSimplexFreeIso.app ⦋n⦌
  haveI : IsCofibrant ((SSet.stdSimplex ⋙ freeDagger).obj ⦋n⦌) := by
    exact freeDagger_isCofibrant _
  haveI : Cofibration i.inv := inferInstance
  exact isCofibrant_of_cofibration i.inv

/-- The Part I left Quillen rigidification sends each represented reversal
simplex to a cofibrant dagger simplicial category. -/
theorem A_isCofibrant (m : ReverseSimplex) :
    IsCofibrant (A.obj m) := by
  letI : daggerRigidification.{0}.PreservesCofibrations :=
    DaggerActualRigidificationQuillen.preservesCofibrations
  letI : PreservesColimits daggerRigidification.{0} :=
    DaggerActualRigidificationQuillen.adjunction.leftAdjoint_preservesColimits
  letI : IsCofibrant (reversalSimplex.obj m) := reversalSimplex_isCofibrant m
  change IsCofibrant (daggerRigidification.obj (reversalSimplex.obj m))
  apply (isCofibrant_iff_of_isInitial
    (daggerRigidification.map (initial.to (reversalSimplex.obj m)))
    (initialIsInitial.isInitialObj daggerRigidification _)).mpr
  infer_instance

end

end DaggerModels.PartII.RigidifiedJTFrames
