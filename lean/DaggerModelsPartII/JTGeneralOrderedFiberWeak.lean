import DaggerModelsPartII.JTCEOrdinaryFiber
import DaggerModelsPartII.JTConeLatchingMono
import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import DaggerModelsPartII.JTOrdinaryEndpointFibration

/-!
# Naturality and weak transport for the original ordered ordinary fiber

The literal original pullback map is calibrated to target postcomposition
on CE and right-cone mapping spaces. For a map between underlying
quasi-categories, weakness on the original right-cone mapping space implies
weakness on that same strict ordered fiber. No whole Joyal weakness of the
map, and no dagger-Joyal fibrancy, is required.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTGeneralOrderedFiberWeak

open JTXiEndpointCollapse JTEndpointObjects JTUnderlyingOrderedFibers
open JTRightAdjointOrderedFiber JTCEOrdinaryFiber JTCEPlainMappingTarget

noncomputable section

/-- The original ordered boundary is natural for every target map. -/
theorem orderedBoundary_natural {X Y : SSet.{0}} (f : X ⟶ Y)
    (x y : X.obj (op ⦋0⦌)) :
    JTConeMappingPresentation.orderedBoundary X x y ≫ f =
      JTConeMappingPresentation.orderedBoundary Y
        (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  apply (boundaryHomEquiv Y).injective
  simp only [JTConeMappingPresentation.orderedBoundary, Equiv.apply_symm_apply]
  apply Prod.ext
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₀ ≫
          (JTConeMappingPresentation.orderedBoundary X x y ≫ f)) = _
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact congrArg (f.app (op ⦋0⦌))
      (congrArg Prod.fst ((boundaryHomEquiv X).apply_symm_apply (x, y)))
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₁ ≫
          (JTConeMappingPresentation.orderedBoundary X x y ≫ f)) = _
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact congrArg (f.app (op ⦋0⦌))
      (congrArg Prod.snd ((boundaryHomEquiv X).apply_symm_apply (x, y)))

/-- The same target map under its two actual endpoint images. -/
def targetUnderMap {X Y : SSet.{0}} (f : X ⟶ Y)
    (x y : X.obj (op ⦋0⦌)) :
    JTConeMappingPresentation.targetUnder X x y ⟶
      JTConeMappingPresentation.targetUnder Y
        (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  Under.homMk f (orderedBoundary_natural f x y)

/-- The cone comparison is natural for the actual endpoint-preserving map. -/
theorem coneMappingIso_natural {X Y : SSet.{0}} (f : X ⟶ Y)
    (x y : X.obj (op ⦋0⦌)) :
    JTCylinderMappingSpan.postcompose JTCylinderConeComparison.coneUnder
        (targetUnderMap f x y) ≫
      (JTConeMappingPresentation.coneMappingIso Y
        (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).hom =
    (JTConeMappingPresentation.coneMappingIso X x y).hom ≫
      DaggerActualGeneralRightConeMapping.map f x y := by
  apply NatTrans.ext
  funext q g
  apply Subtype.ext
  rfl

private theorem rowMap_endpoint_i {X Y : SSet.{0}} (f : X ⟶ Y) (i : Fin 2) :
    ordinaryRowEndpoint X i ≫ originalRowMap f ⦋0⦌ =
      originalRowMap f ⦋1⦌ ≫ ordinaryRowEndpoint Y i := by
  apply NatTrans.ext
  funext k z
  exact congrFun ((OrdinaryJTRealization.nerve.map f).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i, 𝟙 k.unop)))) z

/-- The original ordered row endpoint square, in its original order. -/
theorem rowMap_endpoint {X Y : SSet.{0}} (f : X ⟶ Y) :
    ordinaryEndpointArrow X ≫
        prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌) =
      originalRowMap f ⦋1⦌ ≫ ordinaryEndpointArrow Y := by
  apply prod.hom_ext
  · simpa only [ordinaryEndpointArrow, prod.lift_fst,
      prod.lift_fst_assoc, prod.map_fst, Category.assoc] using rowMap_endpoint_i f 0
  · simpa only [ordinaryEndpointArrow, prod.lift_snd,
      prod.lift_snd_assoc, prod.map_snd, Category.assoc] using rowMap_endpoint_i f 1

private theorem vertexPoint_natural {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    ordinaryVertexPoint X x y i ≫ originalRowMap f ⦋0⦌ =
      ordinaryVertexPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) i := by
  apply NatTrans.ext
  funext k z
  change ULift.up
      ((CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (GroupoidSimplex.parameter.obj k.unop) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary X x y) ≫ f) =
    ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
      (GroupoidSimplex.parameter.obj k.unop) ≫ JTEndpointObjects.boundaryVertexMap i ≫
        ordinaryBoundary Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
  have h := orderedBoundary_natural f x y
  change ordinaryBoundary X x y ≫ f =
    ordinaryBoundary Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) at h
  simp only [Category.assoc]
  rw [h]

/-- The original constant endpoint point is sent to its actual image. -/
theorem endpointPoint_natural {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint X x y ≫
        prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌) =
      ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_fst]
    exact vertexPoint_natural f x y 0
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_snd]
    exact vertexPoint_natural f x y 1

/-- The literal pullback map on the original ordinary endpoint fibers. -/
def strictFiberMap {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedFiber X x y ⟶
      ordinaryOrderedFiber Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  pullback.map (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y)
    (ordinaryEndpointArrow Y.toSSet)
    (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
    (originalRowMap f ⦋1⦌) (𝟙 (Δ[0] : SSet.{0}))
    (prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌))
    (rowMap_endpoint f)
    (by simpa only [Category.id_comp] using endpointPoint_natural f x y)

/-- Its total projection is the actual map of the original outer-one row. -/
theorem strictFiberMap_fst {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    strictFiberMap f x y ≫
        pullback.fst (ordinaryEndpointArrow Y.toSSet)
          (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) =
      pullback.fst (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y) ≫
        originalRowMap f ⦋1⦌ := by
  simp only [strictFiberMap, pullback.map, pullback.lift_fst]

private def spanMap {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedSpanSSet X x y ⟶
      ordinaryOrderedSpanSSet Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) where
  app k g := ⟨g.val ≫ f, by
    rw [← Category.assoc, g.property, Category.assoc]
    exact congrArg (fun h ↦ cylinderProjection.app k.unop ≫ h)
      (orderedBoundary_natural f x y)⟩
  naturality {_ _} _ := by
    funext g
    apply Subtype.ext
    exact Category.assoc _ _ _

private theorem ceSpanIso_natural {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    plainCEHomMap (targetUnderMap f x y) ≫
        (ceSpanIso Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).hom =
      (ceSpanIso X x y).hom ≫ spanMap f x y := by
  apply NatTrans.ext
  funext k g
  apply Subtype.ext
  change CE_interval.app k.unop ≫ (g.right ≫ f) =
    (CE_interval.app k.unop ≫ g.right) ≫ f
  exact (Category.assoc _ _ _).symm

private theorem fiberIso_natural {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    strictFiberMap f x y ≫
        (ordinaryOrderedFiberIso Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).hom =
      (ordinaryOrderedFiberIso X x y).hom ≫ spanMap f x y := by
  apply NatTrans.ext
  funext k z
  apply Subtype.ext
  change ((ordinaryOrderedFiberIso Y _ _).hom.app k
      ((strictFiberMap f x y).app k z)).val =
    ((ordinaryOrderedFiberIso X x y).hom.app k z).val ≫ f
  rw [ordinaryOrderedFiberIso_hom_val, ordinaryOrderedFiberIso_hom_val]
  have h := congrFun (NatTrans.congr_app (strictFiberMap_fst f x y) k) z
  change ((pullback.fst (ordinaryEndpointArrow Y.toSSet)
    (ordinaryEndpointPoint Y _ _)).app k ((strictFiberMap f x y).app k z)) =
      (originalRowMap f ⦋1⦌).app k
        ((pullback.fst (ordinaryEndpointArrow X.toSSet)
          (ordinaryEndpointPoint X x y)).app k z) at h
  rw [h]
  rfl

/-- The literal pullback map is the CE postcomposition map after the
original calibrated isomorphisms, for every target map. -/
theorem strictFiberMap_ce {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    strictFiberMap f x y ≫
        (originalFiberCEIso Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).hom =
      (originalFiberCEIso X x y).hom ≫ plainCEHomMap (targetUnderMap f x y) := by
  apply (cancel_mono (ceSpanIso Y
    (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).hom).1
  simp only [originalFiberCEIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id, ceSpanIso_natural]
  simp only [Iso.inv_hom_id_assoc]
  exact fiberIso_natural f x y

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : ModelCategory (Under JTXiEndpointCollapse.boundary) :=
  JTEndpointCobase.underModel JTXiEndpointCollapse.boundary

private theorem targetUnder_fibrant (X : SSet.{0}) [X.Quasicategory]
    (x y : X.obj (op ⦋0⦌)) :
    IsFibrant (JTConeMappingPresentation.targetUnder X x y) := by
  apply (UnderReedyCriterion.under_isFibrant_iff JTXiEndpointCollapse.boundary _).2
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

/-- Weakness of the original right-cone map implies weakness of actual CE
postcomposition, with no whole ordinary Joyal weakness premise. -/
theorem ceMap_weak_of_rightMapping_weak {X Y : SSet.{0}}
    [X.Quasicategory] [Y.Quasicategory] (f : X ⟶ Y)
    (x y : X.obj (op ⦋0⦌))
    (hf : DaggerSSetGluing.GW (DaggerActualGeneralRightConeMapping.map f x y)) :
    DaggerSSetGluing.GW (plainCEHomMap (targetUnderMap f x y)) := by
  let S := JTConeMappingPresentation.targetUnder X x y
  let T := JTConeMappingPresentation.targetUnder Y
    (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
  have hS : IsFibrant S := targetUnder_fibrant X x y
  have hT : IsFibrant T := targetUnder_fibrant Y _ _
  have hCX := @JTCylinderMappingWeak.fromCone_GW S hS
    JTCylinderAugmentationWeak.augmentation_weak JTConeLatchingMono.coneUnder_op_isFibrant
  have hCY := @JTCylinderMappingWeak.fromCone_GW T hT
    JTCylinderAugmentationWeak.augmentation_weak JTConeLatchingMono.coneUnder_op_isFibrant
  have hEX := @JTCylinderMappingWeak.fromCE_GW S hS
    JTCylinderAugmentationWeak.augmentation_weak
  have hEY := @JTCylinderMappingWeak.fromCE_GW T hT
    JTCylinderAugmentationWeak.augmentation_weak
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have hcone : WeakEquivalence
      (JTCylinderMappingSpan.postcompose JTCylinderConeComparison.coneUnder
        (targetUnderMap f x y)) := by
    let e : Arrow.mk
        (JTCylinderMappingSpan.postcompose JTCylinderConeComparison.coneUnder
          (targetUnderMap f x y)) ≅
        Arrow.mk (DaggerActualGeneralRightConeMapping.map f x y) :=
      Arrow.isoMk (JTConeMappingPresentation.coneMappingIso X x y)
      (JTConeMappingPresentation.coneMappingIso Y
        (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
      (coneMappingIso_natural f x y).symm
    apply (weakEquivalence_iff _).2
    exact ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).2
      ((weakEquivalence_iff _).1 ((DaggerSSetGluing.weakEquivalence_iff_GW _).2 hf))
  have : WeakEquivalence (JTCylinderMappingSpan.fromCone S) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hCX
  have : WeakEquivalence (JTCylinderMappingSpan.fromCone T) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hCY
  have : WeakEquivalence
      (JTCylinderMappingSpan.postcompose JTCylinderFrame.under (targetUnderMap f x y)) :=
    weakEquivalence_of_precomp_of_fac
      (JTCylinderMappingSpan.fromCone_naturality (targetUnderMap f x y)).symm
  have : WeakEquivalence (JTCylinderMappingSpan.fromCE S) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hEX
  have : WeakEquivalence (JTCylinderMappingSpan.fromCE T) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hEY
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp_of_fac
      (JTCylinderMappingSpan.fromCE_naturality (targetUnderMap f x y)))

/-- The same literal original strict fiber map is Kan weak whenever its
original right-cone action is weak between underlying quasi-categories. -/
theorem strictFiberMap_weak_of_rightMapping_weak {X Y : DaggerSSet.{0}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌))
    (hf : DaggerSSetGluing.GW (DaggerActualGeneralRightConeMapping.map f x y)) :
    DaggerSSetGluing.GW (strictFiberMap f x y) := by
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  let e : Arrow.mk (strictFiberMap f x y) ≅
      Arrow.mk (plainCEHomMap (targetUnderMap f x y)) :=
    Arrow.isoMk (originalFiberCEIso X x y)
    (originalFiberCEIso Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
    (strictFiberMap_ce f x y).symm
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  apply (weakEquivalence_iff _).2
  exact ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).2
    ((weakEquivalence_iff _).1 ((DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (ceMap_weak_of_rightMapping_weak f x y hf)))

/-- The original chosen-to-chosen fiber action of the same pointed square. -/
def chosenFiberMap {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ChosenHomotopyFiberComparison.chosenFiber
        (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y) ⟶
      ChosenHomotopyFiberComparison.chosenFiber (ordinaryEndpointArrow Y.toSSet)
        (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :=
  ChosenHomotopyFiberFunctor.chosenMap
    (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointArrow Y.toSSet)
    (originalRowMap f ⦋1⦌)
    (prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌))
    (rowMap_endpoint f) (ordinaryEndpointPoint X x y)
    (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
    (endpointPoint_natural f x y)

/-- The strict and chosen maps retain the SAME actual inclusion triangle. -/
theorem chosenFiberMap_inclusion {X Y : DaggerSSet.{0}} (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ChosenHomotopyFiberTriangle.inclusion
        (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y) ≫
        chosenFiberMap f x y =
      strictFiberMap f x y ≫ ChosenHomotopyFiberTriangle.inclusion
        (ordinaryEndpointArrow Y.toSSet)
        (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) := by
  rw [chosenFiberMap, ChosenHomotopyFiberFunctor.inclusion_chosenMap]
  congr 1

/-- For quasi-category targets the same original chosen action is weak;
this uses the actual original endpoint fibrations and strict-to-chosen maps. -/
theorem chosenFiberMap_weak_of_rightMapping_weak {X Y : DaggerSSet.{0}}
    [X.toSSet.Quasicategory] [Y.toSSet.Quasicategory] (f : X.toSSet ⟶ Y.toSSet)
    (x y : X.toSSet.obj (op ⦋0⦌))
    (hf : DaggerSSetGluing.GW (DaggerActualGeneralRightConeMapping.map f x y)) :
    DaggerSSetGluing.GW (chosenFiberMap f x y) := by
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have : Fibration (ordinaryEndpointArrow X.toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration X.toSSet
  have : Fibration (ordinaryEndpointArrow Y.toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration Y.toSSet
  have he : DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointArrow Y.toSSet)
      (originalRowMap f ⦋1⦌)
      (prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌))
      (rowMap_endpoint f) (ordinaryEndpointPoint X x y)
      (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
      (endpointPoint_natural f x y) = strictFiberMap f x y := by
    apply pullback.hom_ext <;>
      simp [DaggerNativeSSetFibrationSquareFibreWeak.fibreMap, strictFiberMap]
  have : WeakEquivalence
      (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointArrow Y.toSSet)
        (originalRowMap f ⦋1⦌)
        (prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌))
        (rowMap_endpoint f) (ordinaryEndpointPoint X x y)
        (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
        (endpointPoint_natural f x y)) := by
    rw [he]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (strictFiberMap_weak_of_rightMapping_weak f x y hf)
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    (ChosenHomotopyFiberFunctor.chosenMap_weak_of_strict_weak
      (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointArrow Y.toSSet)
      (originalRowMap f ⦋1⦌)
      (prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌))
      (rowMap_endpoint f) (ordinaryEndpointPoint X x y)
      (ordinaryEndpointPoint Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
      (endpointPoint_natural f x y))

end

end DaggerModels.PartII.JTGeneralOrderedFiberWeak
