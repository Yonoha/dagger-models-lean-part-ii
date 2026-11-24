import DaggerModelsPartII.JTGtildeOrderedFiberAction
import DaggerModelsPartII.JTCEOrdinaryFiber
import DaggerModelsPartII.JTRightEndpointCartesian
import DaggerModelsPartII.JTChosenCEUnitBoundary
import DaggerModelsPartII.ChosenHomotopyFiberFunctor
import DaggerModelsPartII.JTEtaChosenFiber

/-!
# The chosen composite adjoint on literal ordered endpoint arrows

The actual chosen dagger adjoint restricts to the original ordinary source
rows. Its target is the original dagger JT right-adjoint endpoint arrow.
The degree-zero image point is identified with the original constant point
at the two actual images under the chosen ordinary adjoints. The checked
global underlying-adjoint identity then becomes a pointed-arrow square.
No weakness of the chosen map is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTAFlatOrderedFiberAction

open JTChosenOrdinaryAdjoint JTStrictificationCoefficients
open JTGtildeOrderedFiberAction JTRightAdjointOrderedFiber
open JTCEOrdinaryFiber JTChosenCEUnitBoundary
open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open DaggerJTAdjunction JTUnderlyingOrderedFibers
open DaggerJTFrameUnderlying

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev C (W : Source) := rigidCoefficient (chosenT W)
private abbrev X (W : Source) :=
  OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj (C W)

private theorem sourceRow_map (W : Source) (m : SimplexCategory)
    {k l : SimplexCategoryᵒᵖ} (θ : k ⟶ l) :
    (sourceRow W m).map θ =
      (JTReversalInput.ordinaryInput.obj (JTStrictificationMaps.Qproj.obj W)).map
        (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop))) := by
  exact JTRealizationDiagonal.ordinaryCurry_obj_obj_map
    (JTReversalInput.ordinaryInput.obj (JTStrictificationMaps.Qproj.obj W))
    m θ.unop

private theorem targetRow_map (W : Source) (m : SimplexCategory)
    {k l : SimplexCategoryᵒᵖ} (θ : k ⟶ l) :
    (daggerRow (X W) (ReverseSimplex.inclusion.obj m)).map θ =
      (JTReversalInput.ordinaryInput.obj (JTCoendMate.compositeNerve.obj (C W))).map
        (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop))) := by
  simp [daggerRow, JTReversalInput.ordinaryInput,
    JTCoendMate.compositeNerve]

private theorem sourceEndpoint_app (W : Source) (i : Fin 2)
    (k : SimplexCategoryᵒᵖ) :
    (sourceEndpoint W i).app k =
      ((JTStrictificationMaps.Qproj.obj W).map
        (ReverseSimplex.inclusion.map
          (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)).op).app k := by
  calc
    (sourceEndpoint W i).app k =
        (JTReversalInput.ordinaryInput.obj
          (JTStrictificationMaps.Qproj.obj W)).map
            (op (JTXiEndpointCollapseBoundary.ordinaryEndpoint i,
              𝟙 k.unop)) :=
      JTRealizationDiagonal.ordinaryCurry_obj_map_app
        (JTReversalInput.ordinaryInput.obj
          (JTStrictificationMaps.Qproj.obj W))
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint i) k.unop
    _ = _ := by
      simp [JTReversalInput.ordinaryInput, Functor.uncurry]

/-- The actual chosen composite adjoint, restricted to each ordinary row. -/
def aRow (W : Source) (m : SimplexCategory) :
    sourceRow W m ⟶ daggerRow (X W) (ReverseSimplex.inclusion.obj m) where
  app k := (JTReversalInput.ordinaryInput.map (chosenAFlat W)).app
    (op (m, k.unop))
  naturality {k l} θ := by
    rw [sourceRow_map, targetRow_map]
    exact (JTReversalInput.ordinaryInput.map (chosenAFlat W)).naturality
      (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))

/-- The two literal cofaces commute with the chosen composite adjoint. -/
theorem aRow_endpoint (W : Source) (i : Fin 2) :
    sourceEndpoint W i ≫ aRow W ⦋0⦌ =
      aRow W ⦋1⦌ ≫
        ((DaggerJTAdjunction.daggerNerve.obj (X W)).map
          (JTOrderedFrameMate.vertex i).op) := by
  apply NatTrans.ext
  funext k z
  have h := congrFun
    (NatTrans.congr_app ((chosenAFlat W).naturality
      (op (ReverseSimplex.inclusion.map
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)))) k) z
  change ((aRow W ⦋0⦌).app k)
      (((sourceEndpoint W i).app k) z) =
    (((DaggerJTAdjunction.daggerNerve.obj (X W)).map
      (JTOrderedFrameMate.vertex i).op).app k)
      (((aRow W ⦋1⦌).app k) z)
  simpa only [sourceEndpoint_app, aRow,
    JTReversalInput.ordinaryInput_map_app,
    JTOrderedFrameMate.vertex,
    JTXiEndpointCollapseBoundary.ordinaryEndpoint] using h

/-- The exact ordered base map induced by `chosenAFlat W`. -/
def aBase (W : Source) :
    sourceRow W ⦋0⦌ ⨯ sourceRow W ⦋0⦌ ⟶
      daggerRow (X W) JTZeroObjects.zeroIndex ⨯
        daggerRow (X W) JTZeroObjects.zeroIndex :=
  prod.map (aRow W ⦋0⦌) (aRow W ⦋0⦌)

/-- The chosen adjoint gives a square of the original endpoint arrows. -/
theorem aArrow_square (W : Source) :
    sourceEndpointArrow W ≫ aBase W =
      aRow W ⦋1⦌ ≫ daggerEndpointArrow (X W) := by
  apply prod.hom_ext
  · simpa only [sourceEndpointArrow, aBase, daggerEndpointArrow,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        aRow_endpoint W 0
  · simpa only [sourceEndpointArrow, aBase, daggerEndpointArrow,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        aRow_endpoint W 1

/-- The global original adjoint identity, evaluated on one literal row. -/
theorem aRow_comparison (W : Source) (m : SimplexCategory) :
    aRow W m ≫ comparisonRow (X W) m =
      gRow W m ≫ originalRowMap (etaOrdinary W) m := by
  apply NatTrans.ext
  funext k z
  exact congrFun
    (NatTrans.congr_app
      (chosen_underlying_adjoint_compatibility W) (op (m, k.unop))) z

/-- The dagger comparison map on the ordered product of zero rows. -/
def comparisonBase (W : Source) :
    daggerRow (X W) JTZeroObjects.zeroIndex ⨯
        daggerRow (X W) JTZeroObjects.zeroIndex ⟶
      ordinaryRow (X W).toSSet ⦋0⦌ ⨯
        ordinaryRow (X W).toSSet ⦋0⦌ :=
  prod.map (comparisonRow (X W) ⦋0⦌) (comparisonRow (X W) ⦋0⦌)

private def zeroFrameUnderlyingIsTerminal :
    IsTerminal (DaggerJTFrameUnderlying.underlyingSimplex.obj m0) := by
  letI : PreservesLimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesLimits
  have h : IsTerminal ((freeDagger.obj (Δ[0] : SSet.{0})).toSSet) :=
    JTWalkingUnitaryWeak.freeZeroIsTerminal.isTerminalObj
      DaggerSSet.forget _
  exact IsTerminal.ofIso h
    (DaggerSSet.forget.mapIso
      (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋0⦌)).symm

private theorem forwardFrame0_isIso (k : SimplexCategory) :
    IsIso (forwardFrame0.app k) := by
  haveI : IsIso (JTXiEndpointCollapseBoundary.forwardSimplexNat.app ⦋0⦌) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
      zeroFrameUnderlyingIsTerminal _
  haveI : IsIso (JTXiEndpointCollapseBoundary.forwardParameter0.app k) := by
    change IsIso
      ((JTXiEndpointCollapseBoundary.forwardSimplexNat.app ⦋0⦌) ⊗ₘ
        (𝟙 (GroupoidSimplex.parameter.obj k)))
    infer_instance
  dsimp only [forwardFrame0, NatTrans.comp_app]
  infer_instance

private theorem comparisonRow_forward (Y : DaggerSSet.{0})
    (k : SimplexCategory) (f : frame0.obj k ⟶ Y) :
    (((comparisonRow Y ⦋0⦌).app (op k)) (ULift.up f)).down =
      forwardFrame0.app k ≫ f.hom := by
  have h := JTRightAdjointForwardNormalization.comparison_on_represented_forward
    Y ⦋0⦌ k f
  rw [JTRightAdjointNativeRow.daggerGeneratorEquiv_eq_native] at h
  change (((comparisonRow Y ⦋0⦌).app (op k)) (ULift.up f)).down = _ at h
  exact h

/-- Only monicity is needed: no global zero-row comparison isomorphism
is claimed. It follows from the checked forward-copy isomorphism and the
faithfulness of the underlying dagger-simplicial-set functor. -/
private theorem comparisonRow_zero_mono (Y : DaggerSSet.{0}) :
    Mono (comparisonRow Y ⦋0⦌) := by
  apply (NatTrans.mono_iff_mono_app (comparisonRow Y ⦋0⦌)).2
  intro k
  apply (mono_iff_injective _).2
  rintro ⟨f⟩ ⟨g⟩ h
  have hf := comparisonRow_forward Y k.unop f
  have hg := comparisonRow_forward Y k.unop g
  have hp : forwardFrame0.app k.unop ≫ f.hom =
      forwardFrame0.app k.unop ≫ g.hom := by
    calc
      _ = (((comparisonRow Y ⦋0⦌).app k) (ULift.up f)).down := hf.symm
      _ = (((comparisonRow Y ⦋0⦌).app k) (ULift.up g)).down :=
        congrArg ULift.down h
      _ = _ := hg
  letI : IsIso (forwardFrame0.app k.unop) := forwardFrame0_isIso k.unop
  have hfg : f = g := by
    apply DaggerSSet.forget.map_injective
    exact (cancel_epi (forwardFrame0.app k.unop)).1 hp
  cases hfg
  rfl

private def orderedBoundaryVertex (i : Fin 2) :
    (Δ[0] : SSet.{0}) ⟶ JTEndpointObjects.boundary :=
  if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁

private theorem orderedBoundaryVertex_eq (i : Fin 2) :
    orderedBoundaryVertex i = JTEndpointObjects.boundaryVertexMap i := by
  fin_cases i
  · change SSet.boundary₁.ι₀ = JTEndpointObjects.boundaryVertexMap 0
    apply (cancel_mono (SSet.boundary 1).ι).mp
    apply SSet.yonedaEquiv.injective
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    simp only [SSet.yonedaEquiv_comp,
      JTEndpointObjects.boundaryVertexMap, Equiv.apply_symm_apply]
    rfl
  · change SSet.boundary₁.ι₁ = JTEndpointObjects.boundaryVertexMap 1
    apply (cancel_mono (SSet.boundary 1).ι).mp
    apply SSet.yonedaEquiv.injective
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    simp only [SSet.yonedaEquiv_comp,
      JTEndpointObjects.boundaryVertexMap, Equiv.apply_symm_apply]
    rfl

private theorem ordinaryPoint_boundary (Y : DaggerSSet.{0})
    (u v : Y.toSSet.obj (op ⦋0⦌)) (i : Fin 2)
    (k : SimplexCategory) :
    (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
      cylinderProjection.app k ≫ ordinaryBoundary Y u v =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj k) ≫
          JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary Y u v := by
  have h := CartesianMonoidalCategory.whiskerRight_fst
    (orderedBoundaryVertex i) (GroupoidSimplex.parameter.obj k)
  change (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
    CartesianMonoidalCategory.fst JTEndpointObjects.boundary
      (GroupoidSimplex.parameter.obj k) ≫ ordinaryBoundary Y u v = _
  rw [orderedBoundaryVertex_eq i]
  rw [orderedBoundaryVertex_eq i] at h
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ ordinaryBoundary Y u v) h

private theorem comparisonVertexPoint (Y : DaggerSSet.{0})
    (u v : Y.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    daggerVertexPoint Y u v i ≫ comparisonRow Y ⦋0⦌ =
      ordinaryVertexPoint Y u v i := by
  apply NatTrans.ext
  funext k z
  have h := comparisonRow_forward Y k.unop
    ((endpointCollapse i).app k.unop ≫ daggerBoundary Y u v)
  have hp := JTXiEndpointCollapseBoundary.projectionEndpointSquare i k.unop
  have hb := daggerBoundary_transpose Y u v
  rw [Adjunction.homEquiv_unit] at hb
  change freeDaggerAdjunction.unit.app boundary ≫
    (daggerBoundary Y u v).hom = ordinaryBoundary Y u v at hb
  change ULift.up (((comparisonRow Y ⦋0⦌).app k)
      (ULift.up ((endpointCollapse i).app k.unop ≫ daggerBoundary Y u v))).down =
    ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
      (GroupoidSimplex.parameter.obj k.unop) ≫
      JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary Y u v)
  apply congrArg ULift.up
  rw [h]
  change forwardFrame0.app k.unop ≫
    (DaggerSSet.forget.map ((endpointCollapse i).app k.unop) ≫
      (daggerBoundary Y u v).hom) = _
  rw [← Category.assoc, ← hp]
  simp only [Category.assoc]
  rw [hb]
  exact ordinaryPoint_boundary Y u v i k.unop

private theorem comparisonEndpointPoint (Y : DaggerSSet.{0})
    (u v : Y.toSSet.obj (op ⦋0⦌)) :
    daggerEndpointPoint Y u v ≫
      prod.map (comparisonRow Y ⦋0⦌) (comparisonRow Y ⦋0⦌) =
        ordinaryEndpointPoint Y u v := by
  apply prod.hom_ext
  · simpa only [daggerEndpointPoint, ordinaryEndpointPoint,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        comparisonVertexPoint Y u v 0
  · simpa only [daggerEndpointPoint, ordinaryEndpointPoint,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        comparisonVertexPoint Y u v 1

/-- The chosen dagger adjoint's literal image of the source pair. -/
def aPoint (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      daggerRow (X W) JTZeroObjects.zeroIndex ⨯
        daggerRow (X W) JTZeroObjects.zeroIndex :=
  sourcePoint W x y ≫ aBase W

/-- The chosen adjoint lands at the ORIGINAL dagger endpoint point for
its actual image vertices. The degree-zero comparison is only used
through its monicity, not inverted as a global row isomorphism. -/
theorem aPoint_eq_original (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    aPoint W x y = daggerEndpointPoint (X W)
      (chosenVertices W (targetVertices W x y).1
        (targetVertices W x y).2).1
      (chosenVertices W (targetVertices W x y).1
        (targetVertices W x y).2).2 := by
  let u := (targetVertices W x y).1
  let v := (targetVertices W x y).2
  let I := prod.map (comparisonRow (X W) ⦋0⦌)
    (comparisonRow (X W) ⦋0⦌)
  letI : Mono (comparisonRow (X W) ⦋0⦌) := comparisonRow_zero_mono (X W)
  haveI : Mono I := inferInstance
  apply (cancel_mono I).mp
  calc
    aPoint W x y ≫ I =
        sourcePoint W x y ≫
          prod.map (aRow W ⦋0⦌ ≫ comparisonRow (X W) ⦋0⦌)
            (aRow W ⦋0⦌ ≫ comparisonRow (X W) ⦋0⦌) := by
              simp only [aPoint, aBase, I, Category.assoc, prod.map_map]
    _ = sourcePoint W x y ≫
          prod.map (gRow W ⦋0⦌ ≫ originalRowMap (etaOrdinary W) ⦋0⦌)
            (gRow W ⦋0⦌ ≫ originalRowMap (etaOrdinary W) ⦋0⦌) := by
              rw [aRow_comparison]
    _ = imagePoint W x y ≫
          prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
            (originalRowMap (etaOrdinary W) ⦋0⦌) := by
              simp only [imagePoint, gBase, Category.assoc, prod.map_map]
    _ = ordinaryEndpointPoint (X W)
          (chosenVertices W u v).1 (chosenVertices W u v).2 := by
              rw [imagePoint_eq_ordinaryEndpointPoint]
              exact JTEtaChosenFiber.endpoint_point_square W u v
    _ = daggerEndpointPoint (X W)
          (chosenVertices W u v).1 (chosenVertices W u v).2 ≫ I := by
              exact (comparisonEndpointPoint (X W)
                (chosenVertices W u v).1
                (chosenVertices W u v).2).symm

/-- The actual chosen-fiber action of `chosenAFlat W`, at the same
original ordered endpoints as the manuscript. -/
def chosenFiberMap (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    ChosenHomotopyFiberComparison.chosenFiber
        (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      ChosenHomotopyFiberComparison.chosenFiber
        (daggerEndpointArrow (X W))
        (daggerEndpointPoint (X W)
          (chosenVertices W (targetVertices W x y).1
            (targetVertices W x y).2).1
          (chosenVertices W (targetVertices W x y).1
            (targetVertices W x y).2).2) :=
  ChosenHomotopyFiberFunctor.chosenMap
    (sourceEndpointArrow W) (daggerEndpointArrow (X W))
    (aRow W ⦋1⦌) (aBase W) (aArrow_square W)
    (sourcePoint W x y)
    (daggerEndpointPoint (X W)
      (chosenVertices W (targetVertices W x y).1
        (targetVertices W x y).2).1
      (chosenVertices W (targetVertices W x y).1
        (targetVertices W x y).2).2)
    (aPoint_eq_original W x y)

/-- The original dagger-to-ordinary right-comparison action at the same
chosen vertices, using the actual ordered endpoint square. -/
def comparisonChosenMap (W : Source)
    (u v : (X W).toSSet.obj (op ⦋0⦌)) :
    ChosenHomotopyFiberComparison.chosenFiber
        (daggerEndpointArrow (X W)) (daggerEndpointPoint (X W) u v) ⟶
      ChosenHomotopyFiberComparison.chosenFiber
        (ordinaryEndpointArrow (X W).toSSet)
        (ordinaryEndpointPoint (X W) u v) :=
  ChosenHomotopyFiberFunctor.chosenMap
    (daggerEndpointArrow (X W))
    (ordinaryEndpointArrow (X W).toSSet)
    (comparisonRow (X W) ⦋1⦌) (comparisonBase W)
    (JTRightEndpointCartesian.endpoint_square (X W))
    (daggerEndpointPoint (X W) u v)
    (ordinaryEndpointPoint (X W) u v)
    (comparisonEndpointPoint (X W) u v)

/-- The actual chosen `a_W^flat` fiber action followed by the original
right comparison equals the actual `gTilde_W` action followed by the
chosen ordinary unit action, after Kan localization. No weakness of the
`gTilde_W` action is inferred from this square. -/
theorem chosenFiberMap_localized_square (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (weakEquivalences SSet.{0}).Q.map (chosenFiberMap W x y) ≫
        (weakEquivalences SSet.{0}).Q.map
          (comparisonChosenMap W
            (chosenVertices W (targetVertices W x y).1
              (targetVertices W x y).2).1
            (chosenVertices W (targetVertices W x y).1
              (targetVertices W x y).2).2) =
      (weakEquivalences SSet.{0}).Q.map
          (JTGtildeOrderedFiberAction.chosenFiberMap W x y) ≫
        (weakEquivalences SSet.{0}).Q.map
          (JTEtaChosenFiber.etaChosenFiberMap W
            (targetVertices W x y).1 (targetVertices W x y).2) := by
  let u := (targetVertices W x y).1
  let v := (targetVertices W x y).2
  let u' := (chosenVertices W u v).1
  let v' := (chosenVertices W u v).2
  have hTotal : aRow W ⦋1⦌ ≫ comparisonRow (X W) ⦋1⦌ =
      gRow W ⦋1⦌ ≫ originalRowMap (etaOrdinary W) ⦋1⦌ :=
    aRow_comparison W ⦋1⦌
  have hBase : aBase W ≫ comparisonBase W =
      gBase W ≫
        prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
          (originalRowMap (etaOrdinary W) ⦋0⦌) := by
    simp only [aBase, comparisonBase, gBase, prod.map_map]
    rw [aRow_comparison W ⦋0⦌]
  have hLeft := ChosenHomotopyFiberFunctor.chosenMap_comp
    (sourceEndpointArrow W) (daggerEndpointArrow (X W))
    (ordinaryEndpointArrow (X W).toSSet)
    (aRow W ⦋1⦌) (aBase W) (aArrow_square W)
    (comparisonRow (X W) ⦋1⦌) (comparisonBase W)
    (JTRightEndpointCartesian.endpoint_square (X W))
    (sourcePoint W x y) (daggerEndpointPoint (X W) u' v')
    (ordinaryEndpointPoint (X W) u' v')
    (aPoint_eq_original W x y)
    (comparisonEndpointPoint (X W) u' v')
  have hRight := ChosenHomotopyFiberFunctor.chosenMap_comp
    (sourceEndpointArrow W)
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointArrow (X W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (originalRowMap (etaOrdinary W) ⦋1⦌)
    (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
      (originalRowMap (etaOrdinary W) ⦋0⦌))
    (JTEtaChosenFiber.endpoint_square W)
    (sourcePoint W x y)
    (ordinaryEndpointPoint (chosenT W) u v)
    (ordinaryEndpointPoint (X W) u' v')
    (imagePoint_eq_ordinaryEndpointPoint W x y)
    (JTEtaChosenFiber.endpoint_point_square W u v)
  calc
    _ = _ := hLeft
    _ = _ := by
      simp only [hTotal, hBase]
    _ = _ := hRight.symm

end

end DaggerModels.PartII.JTAFlatOrderedFiberAction
