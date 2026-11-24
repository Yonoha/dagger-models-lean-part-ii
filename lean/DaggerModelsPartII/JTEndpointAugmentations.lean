import DaggerModelsPartII.CoproductWeakOnCofibrant
import DaggerModelsPartII.JTEndpointArrowWeak
import DaggerModelsPartII.JTEndpointCofibrancy
import DaggerModelsPartII.ReedyFibrantDiagrams

/-!
# The original endpoint arrow augmentations and their weak components

The actual Gamma/Xi augmentations define maps of endpoint arrows to the
original iota. Gamma's two-zero-frame augmentation is weak by the retained
cofibrant Brown lemma; Xi follows from the actual comparison square. The
zero-fixed replacement maps inherit these exact augmentations, without
assuming Xi objects cofibrant.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTEndpointAugmentations

open JTRelativeReedyFrame RigidifiedJTFrames JTActualCosimplicialFrame
open JTEndpointHom JTEndpointMateUnder JTEndpointArrowReplacement
open JTEndpointObjects JTZeroObjects JTOrderedFrameMate JTEndpointCofibrancy

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ

private def intervalInputIso : A.obj oneIndex ≅ Jdagger :=
  daggerRigidification.mapIso (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌)

private theorem boundaryVertexMap_inclusion (i : Fin 2) :
    boundaryVertexMap i ≫ (SSet.boundary 1).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

private theorem endpoint_interval (i : Fin 2) :
    A.map (vertex i) ≫ intervalInputIso.hom = endpointMap i ≫ iota := by
  have h := DaggerJTFrameUnderlying.reversalSimplexFreeIso.hom.naturality
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)
  change DaggerJTFrameUnderlying.reversalSimplex.map (vertex i) ≫
      (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋1⦌).hom =
    (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋0⦌).hom ≫
      freeDagger.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)) at h
  rw [← boundaryVertexMap_inclusion i, freeDagger.map_comp] at h
  simpa only [Functor.comp_map, A, endpointMap, zeroInputIso, iota, intervalInputIso,
    Functor.mapIso_hom, daggerRigidification.map_comp, Category.assoc] using
      congrArg daggerRigidification.map h

/-- The target augmentation to the original rigidified free interval. -/
def targetAugmentation {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA) :
    F ⋙ (evaluation ReverseSimplex Coefficient).obj oneIndex ⟶
      (Functor.const SimplexCategory).obj Jdagger where
  app k := (a.app k).app oneIndex ≫ intervalInputIso.hom
  naturality {j k} θ := by
    have h := congrArg (fun t ↦ t.app oneIndex) (a.naturality θ)
    have hc : (constantA.map θ).app oneIndex = 𝟙 _ := by simp [constantA]
    simp only [NatTrans.comp_app, hc, Category.comp_id] at h
    change (F.map θ).app oneIndex ≫ ((a.app k).app oneIndex ≫ _) =
      ((a.app j).app oneIndex ≫ _) ≫ 𝟙 _
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun t ↦ t ≫ intervalInputIso.hom) h

/-- The original augmentation is a square with the same ordered iota. -/
theorem faces_targetAugmentation {F : SimplexCategory ⥤ OuterDiagram}
    (a : F ⟶ constantA) :
    endpointFaces F ≫ targetAugmentation a =
      endpointCollapse a ≫ (Functor.const SimplexCategory).map iota := by
  apply NatTrans.ext
  funext k
  apply coprod.hom_ext
  · have h := (a.app k).naturality (vertex 0)
    change (F.obj k).map (vertex 0) ≫ (a.app k).app oneIndex =
      (a.app k).app zeroIndex ≫ A.map (vertex 0) at h
    simp only [endpointFaces, endpointCollapse, targetAugmentation,
      NatTrans.comp_app, coprod.inl_desc_assoc, Functor.const_map_app]
    rw [← Category.assoc, h, Category.assoc, endpoint_interval]
    exact (Category.assoc _ _ _).symm
  · have h := (a.app k).naturality (vertex 1)
    change (F.obj k).map (vertex 1) ≫ (a.app k).app oneIndex =
      (a.app k).app zeroIndex ≫ A.map (vertex 1) at h
    simp only [endpointFaces, endpointCollapse, targetAugmentation,
      NatTrans.comp_app, coprod.inr_desc_assoc, Functor.const_map_app]
    rw [← Category.assoc, h, Category.assoc, endpoint_interval]
    exact (Category.assoc _ _ _).symm

/-- The exact natural map from the ordered arrow diagram to constant iota. -/
def arrowAugmentation {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA) :
    arrowsOf (endpointFaces F) ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota) where
  app k := Arrow.homMk ((endpointCollapse a).app k) ((targetAugmentation a).app k) (by
    exact (NatTrans.congr_app (faces_targetAugmentation a) k).symm)
  naturality {j k} θ := by
    apply Arrow.hom_ext
    · exact (endpointCollapse a).naturality θ
    · exact (targetAugmentation a).naturality θ

/-- Every actual Gamma frame value is cofibrant in the original dagger model. -/
theorem gamma_object_isCofibrant (m : ReverseSimplex) (k : SimplexCategory) :
    IsCofibrant ((Gamma.obj k).obj m) := by
  letI : IsFibrant (GammaOuter.obj m).op := GammaOuter_op_isFibrant m
  letI := reedyFibrant_obj (GammaOuter.obj m).op (op k)
  let p := terminal.from ((GammaOuter.obj m).op.obj (op k))
  have h := mem_fibrations p
  rw [fibrations_op] at h
  exact (isCofibrant_iff_of_isInitial p.unop (initialUnopOfTerminal terminalIsTerminal)).mpr
    ((cofibration_iff _).mpr h)

/-- The actual two-endpoint Gamma source augmentation is original weak. -/
theorem gamma_source_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((endpointCollapse augmentation).app k) := by
  letI : IsCofibrant ((Gamma.obj k).obj zeroIndex) := gamma_object_isCofibrant zeroIndex k
  letI : IsCofibrant (A.obj zeroIndex) := A_isCofibrant zeroIndex
  let f : (Gamma.obj k).obj zeroIndex ⟶ A.obj zeroIndex :=
    (augmentation.app k).app zeroIndex
  have hf : weakEquivalences Coefficient f := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, ⦋n⦌ = k := ⟨k.len, SimplexCategory.ext _ _ rfl⟩
    exact augmentation_component_weak zeroIndex n
  have hsum := CoproductWeakOnCofibrant.map_weak f f hf hf
  have h := (weakEquivalences Coefficient).comp_mem _ _ hsum
    ((weakEquivalences Coefficient).of_isIso endpointCoproductIso.hom)
  change weakEquivalences Coefficient
    (coprod.desc (f ≫ endpointMap 0) (f ≫ endpointMap 1))
  simpa only [endpointCoproductIso, coprod.map_desc] using h

/-- Xi's source augmentation is weak by the original comparison equation. -/
theorem xi_source_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((endpointCollapse XiAugmentationCurried).app k) := by
  have h := NatTrans.congr_app comparison_collapse k
  change (endpointCollapse augmentation).app k =
    comparisonSource.app k ≫ (endpointCollapse XiAugmentationCurried).app k at h
  apply (weakEquivalences Coefficient).of_precomp (comparisonSource.app k) _
    (JTEndpointArrowWeak.comparisonSource_weak k)
  rw [← h]
  exact gamma_source_weak k

/-- The actual Gamma target augmentation is weak. -/
theorem gamma_target_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((targetAugmentation augmentation).app k) := by
  change weakEquivalences Coefficient ((augmentation.app k).app oneIndex ≫ _)
  apply (weakEquivalences Coefficient).comp_mem
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, ⦋n⦌ = k := ⟨k.len, SimplexCategory.ext _ _ rfl⟩
    exact augmentation_component_weak oneIndex n
  · exact (weakEquivalences Coefficient).of_isIso intervalInputIso.hom

/-- The actual Xi target augmentation is weak. -/
theorem xi_target_weak (k : SimplexCategory) :
    weakEquivalences Coefficient ((targetAugmentation XiAugmentationCurried).app k) := by
  change weakEquivalences Coefficient
    (JTFrameProjection.XiAugmentation.app (oneIndex, k) ≫ _)
  exact (weakEquivalences Coefficient).comp_mem _ _
    (JTFrameProjection.XiAugmentation_weak oneIndex k)
    ((weakEquivalences Coefficient).of_isIso intervalInputIso.hom)

/-- The original lambda respects the exact augmentation to iota. -/
theorem lambda_augmentation :
    lambda ≫ arrowAugmentation XiAugmentationCurried = arrowAugmentation augmentation := by
  apply NatTrans.ext
  funext k
  apply Arrow.hom_ext
  · exact (NatTrans.congr_app comparison_collapse k).symm
  · change (comparison.app k).app oneIndex ≫
        ((XiAugmentationCurried.app k).app oneIndex ≫ intervalInputIso.hom) =
      (augmentation.app k).app oneIndex ≫ intervalInputIso.hom
    simp only [augmentation, NatTrans.comp_app, Category.assoc]

/-- The actual first replacement inherits the original augmentation. -/
def QGaugmentation :
    QG ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota) :=
  qG ≫ arrowAugmentation augmentation

/-- The actual second replacement inherits the original augmentation. -/
def QXaugmentation :
    QX ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota) :=
  qX ≫ arrowAugmentation XiAugmentationCurried

/-- The literal replacement comparison is augmentation compatible. -/
theorem Qlambda_augmentation : Qlambda ≫ QXaugmentation = QGaugmentation := by
  simp only [QXaugmentation, QGaugmentation, ← Category.assoc, Qlambda_square]
  rw [Category.assoc, lambda_augmentation]

/-- Both components of the actual QG augmentation are weak in every degree. -/
theorem QGaugmentation_weak (n : ℕ) :
    weakEquivalences Coefficient (QGaugmentation.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (QGaugmentation.app ⦋n⦌).right := by
  exact ⟨(weakEquivalences Coefficient).comp_mem _ _ (qG_pointwiseWeak n).1
      (gamma_source_weak ⦋n⦌),
    (weakEquivalences Coefficient).comp_mem _ _ (qG_pointwiseWeak n).2
      (gamma_target_weak ⦋n⦌)⟩

/-- Both components of the actual QX augmentation are weak in every degree. -/
theorem QXaugmentation_weak (n : ℕ) :
    weakEquivalences Coefficient (QXaugmentation.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (QXaugmentation.app ⦋n⦌).right := by
  exact ⟨(weakEquivalences Coefficient).comp_mem _ _ (qX_pointwiseWeak n).1
      (xi_source_weak ⦋n⦌),
    (weakEquivalences Coefficient).comp_mem _ _ (qX_pointwiseWeak n).2
      (xi_target_weak ⦋n⦌)⟩

end

end DaggerModels.PartII.JTEndpointAugmentations
