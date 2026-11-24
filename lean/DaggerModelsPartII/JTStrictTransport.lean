import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.JTFrameZero
import DaggerModelsPartII.JTActualCosimplicialFrame
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Strict `jt.lem.transport` comparison

The actual coend comparison is an isomorphism on vertically constant input.
The represented-generator calculation at degree zero and presheaf density
prove this for every dagger simplicial set. Conjugating the strict
comparison gives the corresponding zero-vertex nerve isomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial DaggerModels

namespace DaggerModels.PartII.JTStrictTransport

open ConstantVertexAdjunction JTFrameAdjunction JTCoendComparison JTFrameZero
open SegalLocalizers
open OrdinaryRigidification.DaggerRigidification
open OrdinaryRigidification.DaggerNerve

noncomputable section

local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The literal capital Lambda, restricted along delta and followed by the
already proved vertical-constant dagger JT realization isomorphism. -/
def thetaHom : delta ⋙ frameRealization ⟶ daggerRigidification :=
  Functor.whiskerLeft delta comparison ≫
    (Functor.associator delta DaggerJTRealization.daggerRealization
      daggerRigidification).symm.hom ≫
    (Functor.isoWhiskerRight deltaRealizationIso daggerRigidification).hom ≫
    daggerRigidification.leftUnitor.hom

/-- The degree-zero input comparison is assembled from two already natural
isomorphisms and is therefore canonical in the reversal index. -/
private def zeroRepresentableInputIso (m : ReverseSimplex) :
    delta.obj (DaggerJTFrameUnderlying.reversalSimplex.obj m) ≅
      zeroRepresentedPair.obj m :=
  (discretePresheaf.{0, 0} ReverseSimplex).mapIso
      (ReversePresheaf.counitIso.app (uliftYoneda.{0}.obj m)) ≪≫
    (zeroRepresentedPairNatIso.app m).symm

/-- The capital Lambda is invertible on every reversal representable
because its actual represented-generator value is the identity at zero. -/
private theorem thetaHom_representable_isIso (m : ReverseSimplex) :
    IsIso (thetaHom.app (DaggerJTFrameUnderlying.reversalSimplex.obj m)) := by
  let p : DaggerJTAdjunction.DaggerIndex := (m, ⦋0⦌)
  have hgenerator : JTCoendMateFormula.frameGenerator p ≫
      comparison.app (JTCoendMateFormula.representedInput p) = 𝟙 _ := by
    rw [JTCoendMateFormula.frameGenerator_comparison]
    change parameterComparison.app (m, ⦋0⦌) =
      𝟙 (RigidifiedJTFrames.Xi.obj (m, ⦋0⦌))
    exact parameterComparison_zero m
  have hcomp : IsIso (comparison.app (JTCoendMateFormula.representedInput p)) := by
    haveI : IsIso (JTCoendMateFormula.frameGenerator p ≫
        comparison.app (JTCoendMateFormula.representedInput p)) := by
      rw [hgenerator]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (JTCoendMateFormula.frameGenerator p)
      (comparison.app (JTCoendMateFormula.representedInput p))
  let i := zeroRepresentableInputIso m
  have htransport : IsIso (comparison.app
      (delta.obj (DaggerJTFrameUnderlying.reversalSimplex.obj m))) := by
    have hi : IsIso (frameRealization.map i.hom ≫
        comparison.app (JTCoendMateFormula.representedInput p)) := by
      exact inferInstance
    have hn := comparison.naturality i.hom
    change frameRealization.map i.hom ≫
      comparison.app (JTCoendMateFormula.representedInput p) =
        comparison.app (delta.obj (DaggerJTFrameUnderlying.reversalSimplex.obj m)) ≫
          (DaggerJTRealization.daggerRealization ⋙ daggerRigidification).map i.hom at hn
    rw [hn] at hi
    exact IsIso.of_isIso_comp_right
      (comparison.app (delta.obj
        (DaggerJTFrameUnderlying.reversalSimplex.obj m)))
      ((DaggerJTRealization.daggerRealization ⋙ daggerRigidification).map i.hom)
  dsimp only [thetaHom, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- Presheaf density extends the represented calculation to every dagger
simplicial set. Both sides preserve colimits as composites of left adjoints.
The native API is `Presheaf.isLeftKanExtension_along_uliftYoneda_iff`
and `Functor.isLeftKanExtension_iff_isIso`, not a new cell induction. -/
private theorem thetaHom_isIso : IsIso thetaHom := by
  let R := ReversePresheaf.toDaggerSSet.{0}
  let L := R ⋙ (delta ⋙ frameRealization)
  let M := R ⋙ daggerRigidification
  let α : L ⟶ M := Functor.whiskerLeft R thetaHom
  haveI : PreservesColimitsOfSize.{0, 0} R :=
    daggerSSetEquivalencePresheaf.symm.toAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfSize.{0, 0} delta :=
    ConstantVertexAdjunction.adjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfSize.{0, 0} frameRealization :=
    JTFrameAdjunction.adjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfSize.{0, 0} daggerRigidification :=
    DaggerActualRigidificationQuillen.adjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfSize.{0, 0} L := inferInstance
  haveI : PreservesColimitsOfSize.{0, 0} M := inferInstance
  haveI hrepresentables :
      ∀ m : ReverseSimplex,
        IsIso ((Functor.whiskerLeft uliftYoneda.{0} α).app m) := by
    intro m
    change IsIso (thetaHom.app (DaggerJTFrameUnderlying.reversalSimplex.obj m))
    exact thetaHom_representable_isIso m
  haveI : IsIso (Functor.whiskerLeft uliftYoneda.{0} α) :=
    NatIso.isIso_of_isIso_app _
  letI : L.IsLeftKanExtension (𝟙 (uliftYoneda.{0} ⋙ L)) :=
    (Presheaf.isLeftKanExtension_along_uliftYoneda_iff.{0} _ _).2
      ⟨inferInstance, inferInstance⟩
  letI : M.IsLeftKanExtension (Functor.whiskerLeft uliftYoneda.{0} α) :=
    (Presheaf.isLeftKanExtension_along_uliftYoneda_iff.{0} _ _).2
      ⟨inferInstance, inferInstance⟩
  have hα : IsIso α :=
    (Functor.isLeftKanExtension_iff_isIso α
      (𝟙 (uliftYoneda.{0} ⋙ L))
      (Functor.whiskerLeft uliftYoneda.{0} α) (by simp)).1 inferInstance
  let e : (DaggerSSet.{0} ⥤ DaggerSimplicialCat.{0, 0}) ≌
      ((ReverseSimplexᵒᵖ ⥤ Type) ⥤ DaggerSimplicialCat.{0, 0}) :=
    daggerSSetEquivalencePresheaf.congrLeft
  have hmap : IsIso (e.functor.map thetaHom) := by
    change IsIso α
    exact hα
  exact e.fullyFaithfulFunctor.isIso_of_isIso_map thetaHom

/-- The strict transport comparison, with hom definitionally tied to Lambda. -/
def Theta : delta ⋙ frameRealization ≅ daggerRigidification :=
  have : IsIso thetaHom := thetaHom_isIso
  asIso thetaHom

/-- The forward strict transport map is exactly the prescribed capital
Lambda after vertical-constant realization, with no extra comparison choice. -/
theorem Theta_hom : Theta.hom =
    Functor.whiskerLeft delta comparison ≫
      (Functor.associator delta DaggerJTRealization.daggerRealization
        daggerRigidification).symm.hom ≫
      (Functor.isoWhiskerRight deltaRealizationIso daggerRigidification).hom ≫
      daggerRigidification.leftUnitor.hom := rfl

/-- The actual composite adjunction on the left side of strict transport. -/
def frameVertexAdjunction :
    delta ⋙ frameRealization ⊣ frameNerve ⋙ vertex :=
  ConstantVertexAdjunction.adjunction.comp JTFrameAdjunction.adjunction

/-- The mate of Theta points from the Part I nerve to the zero-vertex
actual frame nerve. -/
def OmegaInv : daggerCoherentNerve ≅ frameNerve ⋙ vertex :=
  conjugateIsoEquiv DaggerActualRigidificationQuillen.adjunction
    frameVertexAdjunction Theta

/-- The manuscript's vartheta, oriented from the zero-vertex frame nerve to
the original Part I coherent dagger nerve. -/
def Omega : frameNerve ⋙ vertex ≅ daggerCoherentNerve :=
  OmegaInv.symm

/-- The inverse of the zero-vertex nerve isomorphism is the actual mate of
the specified strict Lambda transport map. -/
theorem Omega_inv_mate :
    conjugateEquiv DaggerActualRigidificationQuillen.adjunction
      frameVertexAdjunction Theta.hom = Omega.inv := rfl

end

end DaggerModels.PartII.JTStrictTransport
