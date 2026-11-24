import DaggerModelsPartII.JTTargetCommaNativeFibers

/-! Compare the exact lift categories for all factorizations of the same native map. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeLiftRawComparison

open JTProjectiveOrderedFiberComparison (row)
open JTTargetCommaNativeFibers (lifts)
open JTTargetCommaPullback (diagram fst snd map_fst targetMap)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev I (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  DecoratedNecklaceHomDiagram.Index W x y

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (P : Over Q.code)

private abbrev mapRaw := necklaceUnder.map P.hom ≫ targetMap W x y Q

/-- The full raw equation, formulated as a map in the slice under the ordered boundary. -/
def rawLifts : I W x y ⥤ Type :=
  Over.lift (underDiagram W x y) (underCocone W x y) ⋙
    coyoneda.obj (op (Over.mk (mapRaw Q P)))

private def liftEquiv (i : I W x y) :
    (lifts Q P).obj i ≃ (rawLifts Q P).obj i where
  toFun u := Over.homMk (u.left ≫ fst W x y Q i) (by
    change (u.left ≫ fst W x y Q i) ≫ (underCocone W x y).app i = mapRaw Q P
    have hw : u.left ≫ snd W x y Q i = necklaceUnder.map P.hom := Over.w u
    rw [Category.assoc, JTTargetCommaPullback.condition, ← Category.assoc, hw])
  invFun v := Over.homMk
    (pullback.lift v.left (necklaceUnder.map P.hom) (Over.w v)) (pullback.lift_snd _ _ _)
  left_inv u := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext (f := (underCocone W x y).app i) (g := targetMap W x y Q)
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w u).symm
  right_inv u := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- Pairing the full raw map with the original native map is natural in every label. -/
def rawLiftsIso : lifts Q P ≅ rawLifts Q P :=
  NatIso.ofComponents (fun i ↦ (liftEquiv Q P i).toIso) (by
    intro i j f
    funext u
    apply Over.OverMorphism.ext
    change (u.left ≫ (diagram W x y Q).map f) ≫ fst W x y Q j =
      (u.left ≫ fst W x y Q i) ≫ (underDiagram W x y).map f
    rw [Category.assoc, map_fst, Category.assoc])

/-- The exact source equipped with its full composite map to the raw realization. -/
def composedTarget : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) where
  code := P.left
  map := P.hom.map ≫ Q.map
  first := (congrArg (Q.map.app _) P.hom.first).trans Q.first
  last := (congrArg (Q.map.app _) P.hom.last).trans Q.last

private theorem raw_identity :
    rawLifts Q P = rawLifts (composedTarget Q P)
      (Over.mk (𝟙 (composedTarget Q P).code)) := by
  have h : mapRaw Q P =
      mapRaw (composedTarget Q P) (Over.mk (𝟙 (composedTarget Q P).code)) := by
    apply Under.UnderMorphism.ext
    change P.hom.map ≫ Q.map = (𝟙 P.left.toSSet) ≫ (P.hom.map ≫ Q.map)
    exact (Category.id_comp _).symm
  exact congrArg (fun a ↦ Over.lift (underDiagram W x y) (underCocone W x y) ⋙
    coyoneda.obj (op (Over.mk a))) h

/-- It is enough to contract exact lifts of the identity of each original native code. -/
def reduceToIdentity : lifts Q P ≅
    lifts (composedTarget Q P) (Over.mk (𝟙 (composedTarget Q P).code)) :=
  rawLiftsIso Q P ≪≫ eqToIso (raw_identity Q P) ≪≫ (rawLiftsIso _ _).symm

/-- Weak contractibility for the identity native maps implies the original Theorem C. -/
theorem theoremC_of_identity_lifts
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
        (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)),
        GW (pointMap (nerve (lifts Q (Over.mk (𝟙 Q.code))).Elements))) :
    TheoremCStatement.statement := by
  apply JTTargetCommaNativeFibers.theoremC_of_native_lifts
  intro W hW x y Q P
  let e := Cat.equivOfIso (Functor.elementsFunctor.mapIso (reduceToIdentity Q P))
  let f := nerveMap e.functor
  let t := pointMap (nerve (lifts (composedTarget Q P)
    (Over.mk (𝟙 (composedTarget Q P).code))).Elements)
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence t := (weakEquivalence_iff_GW _).mpr (h W hW x y (composedTarget Q P))
  have ht : f ≫ t = pointMap (nerve (lifts Q P).Elements) := pointIsTerminal.hom_ext _ _
  exact (weakEquivalence_iff_GW _).mp (ht ▸ inferInstanceAs (WeakEquivalence (f ≫ t)))

end
end DaggerModels.PartII.JTNativeLiftRawComparison
