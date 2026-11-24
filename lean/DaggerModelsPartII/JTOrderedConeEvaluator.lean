import DaggerModelsPartII.JTOrderedFrameHomBar
import ActualGeneralRightConeRigidificationWeak
import ActualQWeightedResolutionNaturality
import DaggerModelsPartII.OrderedLabelNaturalWeakSpans

/-! Compare the ordered-frame right-cone evaluation with the original Part I augmentation. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualGeneralRightConeMapping
open DaggerActualGeneralRightConeRigidificationLeg
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementReindex
open DaggerNativeSimplicialReplacementWeightsChange DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedConeEvaluator

open JTConeMappingPresentation (targetUnder coneMappingIso coneBoundary_pair)
open JTCylinderConeComparison (coneUnder)
open JTOrderedFrameHomBar

noncomputable section

variable (X : SSet.{0}) (x y : X.obj (op ⦋0⦌))

private abbrev U := targetUnder X x y
private abbrev M := rightMapping X x y
private abbrev W := DaggerActualWeightedConeCompositeChallenge.diagram (M X x y)

private def toNativeIndex :
    Index coneUnder (U X x y) ⥤ DaggerActualWeightedConeCompositeChallenge.Index (M X x y) :=
  (NatTrans.mapElements (coneMappingIso X x y).hom).op ⋙
    (CategoryOfElements.costructuredArrowULiftYonedaEquivalence (M X x y)).functor ⋙
      ULiftHom.up

private theorem cone_first (k : SimplexCategory) :
    BoundaryNecklaceComma.first (coneUnder.obj k) = alpha.{0} k.len := by
  have h := congrArg Prod.fst (coneBoundary_pair (cone.{0} k.len) k (𝟙 _))
  simpa only [Category.comp_id] using h

private theorem cone_last (k : SimplexCategory) :
    BoundaryNecklaceComma.last (coneUnder.obj k) = omega.{0} k.len := by
  have h := congrArg Prod.snd (coneBoundary_pair (cone.{0} k.len) k (𝟙 _))
  simpa only [Category.comp_id] using h

private theorem target_first : BoundaryNecklaceComma.first (U X x y) = x :=
  congrArg Prod.fst ((JTEndpointObjects.boundaryHomEquiv X).apply_symm_apply (x, y))

private theorem target_last : BoundaryNecklaceComma.last (U X x y) = y :=
  congrArg Prod.snd ((JTEndpointObjects.boundaryHomEquiv X).apply_symm_apply (x, y))

private def homIso (C : SimplicialCat.{0, 0}) {a a' b b' : C.Obj}
    (ha : a = a') (hb : b = b') : C.enriched.Hom a b ≅ C.enriched.Hom a' b' :=
  eqToIso (by rw [ha, hb])

private theorem homIso_natural {C D : SimplicialCat.{0, 0}} (f : C ⟶ D)
    {a a' b b' : C.Obj} {c c' d d' : D.Obj}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (fa : f.obj a = c) (fb : f.obj b = d)
    (fa' : f.obj a' = c') (fb' : f.obj b' = d') :
    castMap f a b c d fa fb ≫ (homIso D hc hd).hom =
      (homIso C ha hb).hom ≫ castMap f a' b' c' d' fa' fb' := by
  subst a'
  subst b'
  subst c'
  subst d'
  simp [homIso]

/-- The actual ordered frame endpoints recover the original Part I weight. -/
def coefficientIso (k : SimplexCategory) :
    (coneUnder ⋙ orderedHom).obj k ≅ Q.{0} k.len :=
  homIso (rigidification.obj (cone.{0} k.len))
    (congrArg (vertexEquiv _) (cone_first k))
    (congrArg (vertexEquiv _) (cone_last k))

/-- The actual target endpoints recover the original Part I rigidified Hom. -/
def targetIso : orderedHom.obj (U X x y) ≅ originalHom X x y :=
  homIso (rigidification.obj X)
    (congrArg (vertexEquiv X) (target_first X x y))
    (congrArg (vertexEquiv X) (target_last X x y))

/-- The coefficient comparison is natural in every original simplex operator. -/
def coefficientComparison : coneUnder ⋙ orderedHom ≅ QFunctor.{0} :=
  NatIso.ofComponents coefficientIso (by
    intro k l f
    change orderedHom.map (coneUnder.map f) ≫ (coefficientIso l).hom =
      (coefficientIso k).hom ≫ Qmap f
    rw [orderedHom_map]
    exact homIso_natural (rigidification.map (coneMap f)) _ _ _ _ _ _ _ _)

/-- The reindexing uses exactly the degree of the original full cone map. -/
def weightComparison : weights coneUnder (U X x y) ≅ toNativeIndex X x y ⋙ W X x y :=
  Functor.isoWhiskerLeft (degree coneUnder (U X x y)) coefficientComparison

private def nativeCocone : W X x y ⟶
    (Functor.const (DaggerActualWeightedConeCompositeChallenge.Index (M X x y))).obj
      (originalHom X x y) :=
  DaggerActualWeightedConeCompositeChallenge.augmentation (M X x y) ≫
    { app _ := DaggerActualGeneralRightConeRigidificationComparison.toRealization X x y }

theorem cocone_comparison :
    cocone coneUnder (U X x y) ≫
      (Functor.const (Index coneUnder (U X x y))).map (targetIso X x y).hom =
        (weightComparison X x y).hom ≫
          Functor.whiskerLeft (toNativeIndex X x y) (nativeCocone X x y) := by
  apply NatTrans.ext
  funext i
  let k := (degree coneUnder (U X x y)).obj i
  let f : coneUnder.obj k ⟶ U X x y := i.unop.2
  let σ := (coneMappingIso X x y).hom.app (op k) f
  change orderedHom.map f ≫ (targetIso X x y).hom =
    (coefficientIso k).hom ≫
      ((realizationUnit.app k ≫ realization.map (uliftYonedaEquiv.symm σ)) ≫
        DaggerActualGeneralRightConeRigidificationComparison.toRealization X x y)
  rw [Category.assoc, DaggerActualGeneralRightConeRigidificationComparison.toRealization_on_simplex,
    orderedHom_map]
  exact homIso_natural (rigidification.map f.right) _ _ _ _ _ _ _ _


private theorem toNativeIndex_weak : WeakEquivalence (nerveMap (toNativeIndex X x y)) := by
  let e := CategoryOfElements.costructuredArrowULiftYonedaEquivalence (M X x y)
  let E : SimplexIndex (M X x y) ≌ ULiftHom (SimplexIndex (M X x y)) := ULiftHom.equiv
  let f := (NatTrans.mapElements (coneMappingIso X x y).hom).op
  haveI : WeakEquivalence (nerveMap f) :=
    (TotalElementsWeakComparison.elementsOpposite_weak_iff _).mpr inferInstance
  haveI : WeakEquivalence (nerveMap (e.trans E).functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (nerveFunctor.map (f.toCatHom ≫ (e.trans E).functor.toCatHom))
  rw [nerveFunctor.map_comp]
  change WeakEquivalence (nerveMap f ≫ nerveMap (e.trans E).functor)
  infer_instance

/-- The full map from the Part II right-cone bar into the original Part I Q bar. -/
def toNativeBar : bar coneUnder (U X x y) ⟶
    DaggerBisimplicialDiagonal.diag (replacement (W X x y)) :=
  diagonalChange (weightComparison X x y).hom ≫
    diagonalReindex (toNativeIndex X x y) (W X x y)

theorem toNativeBar_weak : WeakEquivalence (toNativeBar X x y) := by
  haveI : WeakEquivalence (diagonalChange (weightComparison X x y).hom) :=
    OrderedLabelNaturalWeakSpans.diagonalChange_weak _ (fun _ ↦ inferInstance)
  haveI : WeakEquivalence (diagonalReindex (toNativeIndex X x y) (W X x y)) :=
    (weakEquivalence_iff_GW _).mpr (diagonalReindex_GW _ _
      ((weakEquivalence_iff_GW _).mp (toNativeIndex_weak X x y))
      (DaggerActualQWeightedResolutionNaturality.weights_point_GW (M X x y)))
  exact inferInstanceAs (WeakEquivalence (_ ≫ _))

theorem evaluator_square :
    evaluator coneUnder (U X x y) ≫ (targetIso X x y).hom =
      toNativeBar X x y ≫
        (DaggerActualWeightedConeCompositeChallenge.toRealization (M X x y) ≫
          DaggerActualGeneralRightConeRigidificationComparison.toRealization X x y) := by
  change diagonalAugmentation (weights coneUnder (U X x y))
      (cocone coneUnder (U X x y) ≫
        (Functor.const (Index coneUnder (U X x y))).map (targetIso X x y).hom) =
    (diagonalChange (weightComparison X x y).hom ≫
        diagonalReindex (toNativeIndex X x y) (W X x y)) ≫
      diagonalAugmentation (W X x y) (nativeCocone X x y)
  rw [Category.assoc, DaggerNativeSimplicialReplacementReindex.augmentation_square,
    DaggerNativeSimplicialReplacementWeightsChange.augmentation_square, cocone_comparison]

/-- The actual right-cone ordered evaluator is weak by the original Part I proof. -/
theorem evaluator_weak [X.Quasicategory] :
    WeakEquivalence (evaluator coneUnder (U X x y)) := by
  haveI := toNativeBar_weak X x y
  haveI : WeakEquivalence (DaggerActualWeightedConeCompositeChallenge.toRealization (M X x y)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualQWeightedAugmentationSkeletonInduction.augmentation_GW (M X x y))
  haveI := DaggerActualGeneralRightConeRigidificationWeak.toRealization_weak X x y
  apply (weakEquivalence_postcomp_iff _ (targetIso X x y).hom).mp
  rw [evaluator_square]
  infer_instance

end

end DaggerModels.PartII.JTOrderedConeEvaluator
