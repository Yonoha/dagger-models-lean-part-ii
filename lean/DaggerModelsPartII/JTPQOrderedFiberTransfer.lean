import DaggerModelsPartII.JTChosenPsiOrderedFiber
import DaggerModelsPartII.JTChosenPsiVertices
import DaggerModelsPartII.JTFirstRowWeakRecognition
import DaggerModelsPartII.JTInjectiveFrameNerveTests

/-! Ordered endpoint squares for the two replacement maps in the
literal strictification span. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTPQOrderedFiberTransfer

open JTProjectiveOrderedFiberComparison JTFirstRowWeakRecognition
open JTChosenPsiOrderedFiber JTInjectiveFrameNerveTests
open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor
open JTStrictificationCoefficients
open JTGammaRowEndpoints JTGammaDerivedFiber

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The actual row map of any reversal-diagram arrow preserves both
ordered outer cofaces. -/
theorem rowMap_endpoint {V Z : Source} (f : V ⟶ Z) (i : Fin 2) :
    endpoint V i ≫ rowMap f ⦋0⦌ =
      rowMap f ⦋1⦌ ≫ endpoint Z i :=
  (JTRealizationDiagonal.ordinaryCurry.map
    (JTReversalInput.ordinaryInput.map f)).naturality
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op

/-- The literal ordered endpoint square, with no reindexing of its
two factors. -/
theorem endpoint_square {V Z : Source} (f : V ⟶ Z) :
    endpointArrow V ≫ prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) =
      rowMap f ⦋1⦌ ≫ endpointArrow Z := by
  apply prod.hom_ext
  · simpa only [endpointArrow, prod.lift_fst, prod.lift_fst_assoc,
      prod.map_fst, Category.assoc] using rowMap_endpoint f 0
  · simpa only [endpointArrow, prod.lift_snd, prod.lift_snd_assoc,
      prod.map_snd, Category.assoc] using rowMap_endpoint f 1

/-- The ordered point maps to its literal image pair. -/
theorem point_square {V Z : Source} (f : V ⟶ Z)
    (x y : (row V ⦋0⦌).obj (op ⦋0⦌)) :
    point V x y ≫ prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) =
      point Z ((rowMap f ⦋0⦌).app (op ⦋0⦌) x)
        ((rowMap f ⦋0⦌).app (op ⦋0⦌) y) := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc]
    simp only [point, prod.lift_fst]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, vertexPoint,
      Equiv.apply_symm_apply]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    simp only [point, prod.lift_snd]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, vertexPoint,
      Equiv.apply_symm_apply]

/-- The chosen-fiber action of an actual reversal-diagram arrow, over
the corresponding ordered pair of original vertices. -/
def fiberMap {V Z : Source} (f : V ⟶ Z)
    (x y : (row V ⦋0⦌).obj (op ⦋0⦌)) :
    chosenFiber (endpointArrow V) (point V x y) ⟶
      chosenFiber (endpointArrow Z)
        (point Z ((rowMap f ⦋0⦌).app (op ⦋0⦌) x)
          ((rowMap f ⦋0⦌).app (op ⦋0⦌) y)) :=
  chosenMap (endpointArrow V) (endpointArrow Z)
    (rowMap f ⦋1⦌)
    (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌))
    (endpoint_square f)
    (point V x y)
    (point Z ((rowMap f ⦋0⦌).app (op ⦋0⦌) x)
      ((rowMap f ⦋0⦌).app (op ⦋0⦌) y))
    (point_square f x y)

private theorem prod_diagonal_weak {A B : SSet.{0}} (f : A ⟶ B)
    [IsFibrant A] [IsFibrant B] [WeakEquivalence f] :
    WeakEquivalence (prod.map f f) := by
  haveI : WeakEquivalence (prod.map f (𝟙 A)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f A).flip
  haveI : WeakEquivalence (prod.map f (𝟙 B)) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_prod_fst_with_id f B).flip
  have h : prod.map (𝟙 B) f =
      (prod.braiding B A).hom ≫ prod.map f (𝟙 B) ≫
        (prod.braiding B B).hom := by
    apply prod.hom_ext <;> simp
  haveI : WeakEquivalence (prod.map (𝟙 B) f) := by
    rw [h]
    infer_instance
  have hcomp : prod.map f (𝟙 A) ≫ prod.map (𝟙 B) f =
      prod.map f f := by
    simp only [prod.map_map, Category.comp_id, Category.id_comp]
  rw [← hcomp]
  infer_instance

/-- Rowwise weakness gives weakness on the chosen ordered fibers,
provided the zero rows are Kan complexes. -/
theorem fiberMap_weak_of_rows {V Z : Source} (f : V ⟶ Z)
    (x y : (row V ⦋0⦌).obj (op ⦋0⦌))
    [IsFibrant (row V ⦋0⦌)] [IsFibrant (row Z ⦋0⦌)]
    [WeakEquivalence (rowMap f ⦋0⦌)]
    [WeakEquivalence (rowMap f ⦋1⦌)] :
    WeakEquivalence (fiberMap f x y) := by
  letI : WeakEquivalence
      (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌)) :=
    prod_diagonal_weak (rowMap f ⦋0⦌)
  letI : Fibration (replacement (endpointArrow Z)).p :=
    (fibration_iff _).mpr (replacement (endpointArrow Z)).hp
  letI : WeakEquivalence (replacement (endpointArrow Z)).i :=
    (weakEquivalence_iff _).mpr (replacement (endpointArrow Z)).hi.2
  have htotal : WeakEquivalence
      (rowMap f ⦋1⦌ ≫ (replacement (endpointArrow Z)).i) :=
    inferInstance
  have hsquare : endpointArrow V ≫
      prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) =
      (rowMap f ⦋1⦌ ≫ (replacement (endpointArrow Z)).i) ≫
        (replacement (endpointArrow Z)).p := by
    rw [Category.assoc, (replacement (endpointArrow Z)).fac]
    exact endpoint_square f
  change WeakEquivalence
    (comparison (endpointArrow V) (replacement (endpointArrow Z)).p
      (rowMap f ⦋1⦌ ≫ (replacement (endpointArrow Z)).i)
      (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌))
      hsquare (point V x y)
      (point Z ((rowMap f ⦋0⦌).app (op ⦋0⦌) x)
        ((rowMap f ⦋0⦌).app (op ⦋0⦌) y))
      (point_square f x y))
  exact comparison_weak _ _ _ _ _ _ _ _

/-- A projective rowwise weak equivalence induces a weak equivalence on
each original ordinary row. -/
theorem rowMap_weak_of_projective {V Z : Source} (f : V ⟶ Z)
    (hf : ProjectiveKanDiagram.weakEquivalences ReverseSimplexᵒᵖ f)
    (m : SimplexCategory) :
    WeakEquivalence (rowMap f m) := by
  let ea : Arrow.mk (rowMap f m) ≅
      Arrow.mk (f.app (op (ReverseSimplex.inclusion.obj m))) :=
    Arrow.isoMk (rowRestrictionIso V m)
      (rowRestrictionIso Z m) (show _ = _ by ext k x; rfl)
  have hlevel := hf (op (ReverseSimplex.inclusion.obj m))
  exact (weakEquivalence_iff _).mpr
    (((HomotopicalAlgebra.weakEquivalences SSet.{0}).arrow_mk_iso_iff ea).2
      hlevel)

private theorem row_fibrant_of_projective (V : Source)
    (hV : @IsFibrant Source _
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithFibrations
      _ V) (m : SimplexCategory) : IsFibrant (row V m) := by
  haveI : IsFibrant
      (V.obj (op (ReverseSimplex.inclusion.obj m))) :=
    (ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ V).mp hV
      (op (ReverseSimplex.inclusion.obj m))
  exact (isFibrant_iff_of_isTerminal
    ((rowRestrictionIso V m).hom ≫ terminal.from _) terminalIsTerminal).mpr
      inferInstance

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The injective-local replacement of the actual frame nerve, kept as
the literal map selected by FrameNerveTest. -/
def q (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C] :
    JTFrameAdjunction.frameNerve.obj C ⟶ (frameNerveTest C).target :=
  (frameNerveTest C).map

/-- Its chosen action on the original ordered endpoint fibers. -/
def qFiberMap (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C]
    (x y : (row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).obj (op ⦋0⦌)) :
    chosenFiber (endpointArrow (JTFrameAdjunction.frameNerve.obj C))
      (point (JTFrameAdjunction.frameNerve.obj C) x y) ⟶
      chosenFiber (endpointArrow (frameNerveTest C).target)
        (point (frameNerveTest C).target
          ((rowMap (q C) ⦋0⦌).app (op ⦋0⦌) x)
          ((rowMap (q C) ⦋0⦌).app (op ⦋0⦌) y)) :=
  fiberMap (q C) x y

/-- The exact q endpoint square is weak on all chosen ordered fibers.
Its zero and one row maps are the actual rowwise weak replacement. -/
theorem qFiberMap_weak (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C]
    (x y : (row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (qFiberMap C x y) := by
  let V := JTFrameAdjunction.frameNerve.obj C
  let Z := (frameNerveTest C).target
  have hV : @IsFibrant Source _
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithFibrations
      _ V := JTSegalFrameLocality.frameNerve_obj_isFibrant C
  letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hZinj : IsFibrant Z := (frameNerveTest C).localObject.1
  have hZ : @IsFibrant Source _
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithFibrations
      _ Z :=
    ProjectiveInjectiveComparison.isFibrant_projective ReverseSimplexᵒᵖ Z hZinj
  letI : IsFibrant (row V ⦋0⦌) :=
    row_fibrant_of_projective V hV ⦋0⦌
  letI : IsFibrant (row Z ⦋0⦌) :=
    row_fibrant_of_projective Z hZ ⦋0⦌
  have hq : ProjectiveKanDiagram.weakEquivalences ReverseSimplexᵒᵖ (q C) :=
    (frameNerveTest C).rowwiseWeak
  letI : WeakEquivalence (rowMap (q C) ⦋0⦌) :=
    rowMap_weak_of_projective (q C) hq ⦋0⦌
  letI : WeakEquivalence (rowMap (q C) ⦋1⦌) :=
    rowMap_weak_of_projective (q C) hq ⦋1⦌
  exact fiberMap_weak_of_rows (q C) x y

/-- The selected q comparison applies to the exact two images under
the original chosenPsi, in the same endpoint order. -/
theorem q_after_chosenPsi_fiber_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence
      (@qFiberMap (rigidCoefficient (chosenT W))
        (rigidCoefficient_fibrant (chosenT W))
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y)) := by
  letI : IsFibrant (rigidCoefficient (chosenT W)) :=
    rigidCoefficient_fibrant (chosenT W)
  exact qFiberMap_weak (rigidCoefficient (chosenT W)) _ _

/-- The p, literal chosenPsi, and q maps are each weak on the
specified ordered fibers, under the remaining raw JT fiber hypothesis. -/
theorem replacement_span_fibers_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (JTProjectiveOrderedFiberComparison.chosenFiberMap W x y) ∧
      WeakEquivalence (psiChosenMap W x y) ∧
      WeakEquivalence
        (@qFiberMap (rigidCoefficient (chosenT W))
          (rigidCoefficient_fibrant (chosenT W))
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y)) := by
  exact ⟨JTProjectiveOrderedFiberComparison.chosenFiberMap_weak W x y,
    psiChosenMap_weak_of_raw W x y hraw,
    q_after_chosenPsi_fiber_weak W x y⟩

private theorem gammaZeroRow_map (C : DaggerSimplicialCat.{0, 0})
    {j k : SimplexCategoryᵒᵖ} (θ : j ⟶ k)
    (z : (row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).obj j) :
    (row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).map θ z =
      (JTRelativeReedyFrame.Gamma.map θ.unop).app
        JTZeroObjects.zeroIndex ≫ z := by
  have h := congrFun ((rowRestrictionIso
    (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).hom.naturality θ) z
  change (row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).map θ z =
    ((JTFrameAdjunction.frameNerve.obj C).obj (op JTZeroObjects.zeroIndex)).map θ z at h
  rw [h]
  change JTFrameAdjunction.frameParameter.map
    (show (JTZeroObjects.zeroIndex, k.unop) ⟶
      (JTZeroObjects.zeroIndex, j.unop) from (𝟙 _, θ.unop)) ≫ z = _
  rw [JTFrameAdjunction.frameParameter_vertical_map]
  rfl

private def zeroPairFst (C : DaggerSimplicialCat.{0, 0}) :
    zeroPairRow C ⟶ row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ where
  app _ := Prod.fst
  naturality {j k} θ := by
    ext z
    exact (gammaZeroRow_map C θ z.1).symm

private def zeroPairSnd (C : DaggerSimplicialCat.{0, 0}) :
    zeroPairRow C ⟶ row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ where
  app _ := Prod.snd
  naturality {j k} θ := by
    ext z
    exact (gammaZeroRow_map C θ z.2).symm

private def productToZeroPair (C : DaggerSimplicialCat.{0, 0}) :
    row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶ zeroPairRow C where
  app k z := ((prod.fst : _ ⟶ row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k z,
    (prod.snd : _ ⟶ row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k z)
  naturality {j k} θ := by
    ext z
    apply Prod.ext
    · have h := congrFun ((prod.fst :
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
            row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
              row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).naturality θ) z
      exact h.trans (gammaZeroRow_map C θ _)
    · have h := congrFun ((prod.snd :
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
            row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
              row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).naturality θ) z
      exact h.trans (gammaZeroRow_map C θ _)

/-- The original Gamma boundary Hom row is the ordered product of the
two literal zero rows of the frame nerve. -/
def gammaProductIso (C : DaggerSimplicialCat.{0, 0}) :
    endpointSourceRow C ≅
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ :=
  endpointSourceRowIso C ≪≫
    { hom := prod.lift (zeroPairFst C) (zeroPairSnd C)
      inv := productToZeroPair C
      hom_inv_id := by
        apply NatTrans.ext
        funext k z
        apply Prod.ext
        · have h := congrFun (NatTrans.congr_app
            (prod.lift_fst (zeroPairFst C) (zeroPairSnd C)) k) z
          simpa only [NatTrans.comp_app, types_comp_apply, zeroPairFst,
            productToZeroPair] using h
        · have h := congrFun (NatTrans.congr_app
            (prod.lift_snd (zeroPairFst C) (zeroPairSnd C)) k) z
          simpa only [NatTrans.comp_app, types_comp_apply, zeroPairSnd,
            productToZeroPair] using h
      inv_hom_id := by
        apply prod.hom_ext <;> ext k z <;>
          simp [zeroPairFst, zeroPairSnd, productToZeroPair] }

/-- Identify the Gamma outer-one Hom row with the original ordinary
restriction row. -/
def gammaOneIso (C : DaggerSimplicialCat.{0, 0}) :
    JTGammaRowEndpoints.gammaRow C JTOrderedFrameMate.oneIndex ≅
      row (JTFrameAdjunction.frameNerve.obj C) ⦋1⦌ :=
  (rowRestrictionIso (JTFrameAdjunction.frameNerve.obj C) ⦋1⦌).symm

private theorem frameNerve_endpoint_val (C : DaggerSimplicialCat.{0, 0})
    (i : Fin 2) (k : SimplexCategoryᵒᵖ)
    (z : (gammaRow C JTOrderedFrameMate.oneIndex).obj k) :
    (endpoint (JTFrameAdjunction.frameNerve.obj C) i).app k z =
      (JTRelativeReedyFrame.Gamma.obj k.unop).map
        (JTOrderedFrameMate.vertex i) ≫ z := by
  change ((JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj (JTFrameAdjunction.frameNerve.obj C))).map
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i).op).app k z = _
  rw [JTRealizationDiagonal.ordinaryCurry_obj_map_app]
  simp [JTReversalInput.ordinaryInput, JTFrameAdjunction.frameNerve,
    JTFrameAdjunction.rawPresheafNerve, DaggerJTAdjunction.sourceEquivalence,
    JTFrameAdjunction.frameParameter, JTRelativeReedyFrame.GammaOuter,
    JTOrderedFrameMate.vertex, JTXiEndpointCollapseBoundary.ordinaryEndpoint,
    Functor.uncurry]

private theorem gammaProductIso_fst_app (C : DaggerSimplicialCat.{0, 0})
    (k : SimplexCategoryᵒᵖ) (z : (endpointSourceRow C).obj k) :
    (prod.fst :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
        ((gammaProductIso C).hom.app k z) =
      ((endpointSourceRowIso C).hom.app k z).1 := by
  change ((gammaProductIso C).hom ≫ prod.fst).app k z = _
  simp only [gammaProductIso, Iso.trans_hom, Category.assoc,
    prod.lift_fst, zeroPairFst]
  rfl

private theorem gammaProductIso_snd_app (C : DaggerSimplicialCat.{0, 0})
    (k : SimplexCategoryᵒᵖ) (z : (endpointSourceRow C).obj k) :
    (prod.snd :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
        ((gammaProductIso C).hom.app k z) =
      ((endpointSourceRowIso C).hom.app k z).2 := by
  change ((gammaProductIso C).hom ≫ prod.snd).app k z = _
  simp only [gammaProductIso, Iso.trans_hom, Category.assoc,
    prod.lift_snd, zeroPairSnd]
  rfl

/-- The Gamma endpoint arrow is the ordinary frame-nerve endpoint
arrow after the explicit ordered coproduct/product identification. -/
theorem gamma_arrow_product (C : DaggerSimplicialCat.{0, 0}) :
    rawArrow C ≫ (gammaProductIso C).hom =
      (gammaOneIso C).hom ≫
        endpointArrow (JTFrameAdjunction.frameNerve.obj C) := by
  apply prod.hom_ext
  · apply NatTrans.ext
    funext k z
    simp only [Category.assoc, endpointArrow, prod.lift_fst]
    change (prod.fst :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
        ((gammaProductIso C).hom.app k ((rawArrow C).app k z)) =
      (endpoint (JTFrameAdjunction.frameNerve.obj C) 0).app k
        ((gammaOneIso C).hom.app k z)
    rw [gammaProductIso_fst_app]
    change ((endpointSourceRowIso C).hom.app k
      ((gammaEndpointArrow C).app k z)).1 = _
    rw [congrArg Prod.fst (gammaEndpointArrow_val C k.unop z)]
    exact (frameNerve_endpoint_val C 0 k z).symm
  · apply NatTrans.ext
    funext k z
    simp only [Category.assoc, endpointArrow, prod.lift_snd]
    change (prod.snd :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
        ((gammaProductIso C).hom.app k ((rawArrow C).app k z)) =
      (endpoint (JTFrameAdjunction.frameNerve.obj C) 1).app k
        ((gammaOneIso C).hom.app k z)
    rw [gammaProductIso_snd_app]
    change ((endpointSourceRowIso C).hom.app k
      ((gammaEndpointArrow C).app k z)).2 = _
    rw [congrArg Prod.snd (gammaEndpointArrow_val C k.unop z)]
    exact (frameNerve_endpoint_val C 1 k z).symm

/-- On the outer-one row, the original psiRow is literally the
ordinary restriction of chosenPsi after the Gamma row identification. -/
theorem psi_row_one_product (W : Source) :
    psiRow W ≫
      (gammaOneIso (rigidCoefficient (chosenT W))).hom =
        rowMap (chosenPsi W) ⦋1⦌ := by
  apply NatTrans.ext
  funext k z
  change ((gammaOneIso (rigidCoefficient (chosenT W))).hom.app k)
    ((psiRow W).app k z) = (rowMap (chosenPsi W) ⦋1⦌).app k z
  rw [show (psiRow W).app k =
      ((chosenPsi W).app (op JTOrderedFrameMate.oneIndex)).app k from
        psiRow_app W k]
  rfl

/-- The original psi zero row, before taking its ordered product. -/
theorem psi_row_zero_product (W : Source) :
    JTAFlatOrderedFiberAction.aRow W ⦋0⦌ ≫
        ((JTCoendMate.rightMate.app
          (rigidCoefficient (chosenT W))).app (op JTZeroObjects.zeroIndex)) ≫
        (rowRestrictionIso
          (JTFrameAdjunction.frameNerve.obj (rigidCoefficient (chosenT W)))
          ⦋0⦌).inv =
      rowMap (chosenPsi W) ⦋0⦌ := by
  apply NatTrans.ext
  funext k z
  rw [chosenPsi_eq_chosenAFlat_rightMate]
  rfl

/-- The mate's original Gamma boundary map becomes the ordered product
of its two zero-row components. -/
theorem mate_base_product (C : DaggerSimplicialCat.{0, 0}) :
    JTRightMateOrderedFiber.mateBase C ≫ (gammaProductIso C).hom =
      prod.map
        (((JTCoendMate.rightMate.app C).app (op JTZeroObjects.zeroIndex)) ≫
          (rowRestrictionIso (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).inv)
        (((JTCoendMate.rightMate.app C).app (op JTZeroObjects.zeroIndex)) ≫
          (rowRestrictionIso (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).inv) := by
  apply prod.hom_ext
  · apply NatTrans.ext
    funext k z
    simp only [Category.assoc, prod.map_fst]
    change (prod.fst :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
          ((gammaProductIso C).hom.app k
            ((JTRightMateOrderedFiber.mateBase C).app k z)) = _
    rw [gammaProductIso_fst_app]
    exact congrArg Prod.fst (JTRightMateOrderedFiber.mateBase_val C k z)
  · apply NatTrans.ext
    funext k z
    simp only [Category.assoc, prod.map_snd]
    change (prod.snd :
      row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⨯
        row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌ ⟶
          row (JTFrameAdjunction.frameNerve.obj C) ⦋0⦌).app k
          ((gammaProductIso C).hom.app k
            ((JTRightMateOrderedFiber.mateBase C).app k z)) = _
    rw [gammaProductIso_snd_app]
    exact congrArg Prod.snd (JTRightMateOrderedFiber.mateBase_val C k z)

/-- The original psiBase is exactly the ordered product of the
outer-zero components of chosenPsi. -/
theorem psi_base_product (W : Source) :
    psiBase W ≫
        (gammaProductIso (rigidCoefficient (chosenT W))).hom =
      prod.map (rowMap (chosenPsi W) ⦋0⦌)
        (rowMap (chosenPsi W) ⦋0⦌) := by
  rw [psiBase, Category.assoc, mate_base_product]
  change prod.map (JTAFlatOrderedFiberAction.aRow W ⦋0⦌)
      (JTAFlatOrderedFiberAction.aRow W ⦋0⦌) ≫
      prod.map
        (((JTCoendMate.rightMate.app
          (rigidCoefficient (chosenT W))).app (op JTZeroObjects.zeroIndex)) ≫
          (rowRestrictionIso
            (JTFrameAdjunction.frameNerve.obj (rigidCoefficient (chosenT W)))
            ⦋0⦌).inv)
        (((JTCoendMate.rightMate.app
          (rigidCoefficient (chosenT W))).app (op JTZeroObjects.zeroIndex)) ≫
          (rowRestrictionIso
            (JTFrameAdjunction.frameNerve.obj (rigidCoefficient (chosenT W)))
            ⦋0⦌).inv) = _
  rw [prod.map_map]
  rw [psi_row_zero_product]

/-- Publicly expose the actual point square of the chosen strictification
map for transfer through q. -/
theorem psi_point_square (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    JTGtildeOrderedFiberAction.sourcePoint W x y ≫ psiBase W =
      rawPoint (rigidCoefficient (chosenT W))
        (coefficientVertices W x y).1 (coefficientVertices W x y).2 := by
  have ha : JTGtildeOrderedFiberAction.sourcePoint W x y ≫
      JTAFlatOrderedFiberAction.aBase W =
      JTXiRowEndpoints.boundaryPoint (rigidCoefficient (chosenT W))
        (coefficientVertices W x y).1 (coefficientVertices W x y).2 :=
    (JTAFlatOrderedFiberAction.aPoint_eq_original W x y).trans
      (JTXiOrderedPointCalibration.daggerEndpointPoint_eq_boundaryPoint
        (rigidCoefficient (chosenT W)) _ _)
  rw [psiBase, ← Category.assoc, ha, JTRightMateOrderedFiber.matePoint]

/-- After normalizing the Gamma boundary, the exact psi point is the
ordered pair of literal chosenPsi vertex images. -/
theorem psi_point_product (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    rawPoint (rigidCoefficient (chosenT W))
        (coefficientVertices W x y).1 (coefficientVertices W x y).2 ≫
      (gammaProductIso (rigidCoefficient (chosenT W))).hom =
    point (JTFrameAdjunction.frameNerve.obj
      (rigidCoefficient (chosenT W)))
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y) := by
  rw [← psi_point_square W x y, Category.assoc, psi_base_product]
  exact point_square (chosenPsi W) x y

/-- The chosen map of the exact Gamma-to-product endpoint isomorphism,
based at the literal pair of chosenPsi images. -/
def gammaChosenBridge (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    gammaHomotopyFiber (rigidCoefficient (chosenT W))
      (coefficientVertices W x y).1 (coefficientVertices W x y).2 ⟶
    chosenFiber (endpointArrow
      (JTFrameAdjunction.frameNerve.obj (rigidCoefficient (chosenT W))))
      (point (JTFrameAdjunction.frameNerve.obj (rigidCoefficient (chosenT W)))
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y)) :=
  chosenMap (rawArrow (rigidCoefficient (chosenT W)))
    (endpointArrow (JTFrameAdjunction.frameNerve.obj
      (rigidCoefficient (chosenT W))))
    (gammaOneIso (rigidCoefficient (chosenT W))).hom
    (gammaProductIso (rigidCoefficient (chosenT W))).hom
    (gamma_arrow_product (rigidCoefficient (chosenT W)))
    (rawPoint (rigidCoefficient (chosenT W))
      (coefficientVertices W x y).1 (coefficientVertices W x y).2)
    (point (JTFrameAdjunction.frameNerve.obj
      (rigidCoefficient (chosenT W)))
      (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
      (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
    (psi_point_product W x y)

/-- The Γ-to-product presentation change is weak on the selected
homotopy fibers, since both of its original row maps are isomorphisms. -/
theorem gammaChosenBridge_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (gammaChosenBridge W x y) := by
  let C := rigidCoefficient (chosenT W)
  letI : WeakEquivalence (gammaOneIso C).hom := inferInstance
  letI : WeakEquivalence (gammaProductIso C).hom := inferInstance
  letI : Fibration (replacement
      (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).p :=
    (fibration_iff _).mpr
      (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).hp
  letI : WeakEquivalence (replacement
      (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).i :=
    (weakEquivalence_iff _).mpr
      (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).hi.2
  have htotal : WeakEquivalence
      ((gammaOneIso C).hom ≫
        (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).i) :=
    inferInstance
  have hsquare : rawArrow C ≫ (gammaProductIso C).hom =
      ((gammaOneIso C).hom ≫
        (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).i) ≫
          (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).p := by
    rw [Category.assoc, (replacement
      (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).fac]
    exact gamma_arrow_product C
  change WeakEquivalence
    (comparison (rawArrow C)
      (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).p
      ((gammaOneIso C).hom ≫
        (replacement (endpointArrow (JTFrameAdjunction.frameNerve.obj C))).i)
      (gammaProductIso C).hom hsquare
      (rawPoint C (coefficientVertices W x y).1
        (coefficientVertices W x y).2)
      (point (JTFrameAdjunction.frameNerve.obj C)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
      (psi_point_product W x y))
  exact comparison_weak _ _ _ _ _ _ _ _

/-- The original, unnormalized chosenPsi endpoint square. -/
theorem psi_square_public (W : Source) :
    JTGtildeOrderedFiberAction.sourceEndpointArrow W ≫ psiBase W =
      psiRow W ≫ rawArrow (rigidCoefficient (chosenT W)) := by
  dsimp only [psiBase, psiRow]
  rw [← Category.assoc, JTAFlatOrderedFiberAction.aArrow_square, Category.assoc]
  have h := JTRightMateOrderedFiber.mateSquare (rigidCoefficient (chosenT W))
  change JTRightAdjointOrderedFiber.daggerEndpointArrow
    (OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj
      (rigidCoefficient (chosenT W))) ≫
        JTRightMateOrderedFiber.mateBase (rigidCoefficient (chosenT W)) =
      JTRightMateOrderedFiber.mateRow (rigidCoefficient (chosenT W)) ≫
        rawArrow (rigidCoefficient (chosenT W)) at h
  rw [h, Category.assoc]

private theorem chosenMap_congr_square
    {X Y B D K : SSet.{0}} (p : X ⟶ B) (q : Y ⟶ D)
    {f f' : X ⟶ Y} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g')
    (h : p ≫ g = f ≫ q) (h' : p ≫ g' = f' ≫ q)
    (b : K ⟶ B) (d : K ⟶ D)
    (hb : b ≫ g = d) (hb' : b ≫ g' = d) :
    chosenMap p q f g h b d hb =
      chosenMap p q f' g' h' b d hb' := by
  cases hf
  cases hg
  rfl

/-- The chosen-map composition theorem identifies the original Gamma
fiber action with the literal chosenPsi fiber action after Kan localization. -/
theorem psi_fiberMap_localized_eq (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (weakEquivalences SSet.{0}).Q.map (psiChosenMap W x y) ≫
        (weakEquivalences SSet.{0}).Q.map (gammaChosenBridge W x y) =
      (weakEquivalences SSet.{0}).Q.map (fiberMap (chosenPsi W) x y) := by
  let C := rigidCoefficient (chosenT W)
  let N := JTFrameAdjunction.frameNerve.obj C
  let v := coefficientVertices W x y
  have h := ChosenHomotopyFiberFunctor.chosenMap_comp
    (JTGtildeOrderedFiberAction.sourceEndpointArrow W)
    (rawArrow C) (endpointArrow N)
    (psiRow W) (psiBase W) (psi_square_public W)
    (gammaOneIso C).hom (gammaProductIso C).hom (gamma_arrow_product C)
    (JTGtildeOrderedFiberAction.sourcePoint W x y)
    (rawPoint C v.1 v.2)
    (point N
      (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
      (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
    (psi_point_square W x y) (psi_point_product W x y)
  change (weakEquivalences SSet.{0}).Q.map (psiChosenMap W x y) ≫
      (weakEquivalences SSet.{0}).Q.map (gammaChosenBridge W x y) =
    (weakEquivalences SSet.{0}).Q.map
      (chosenMap (JTGtildeOrderedFiberAction.sourceEndpointArrow W)
        (endpointArrow N)
        (psiRow W ≫ (gammaOneIso C).hom)
        (psiBase W ≫ (gammaProductIso C).hom) _
        (JTGtildeOrderedFiberAction.sourcePoint W x y)
        (point N
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
        _) at h
  have hs : JTGtildeOrderedFiberAction.sourceEndpointArrow W ≫
      (psiBase W ≫ (gammaProductIso C).hom) =
      (psiRow W ≫ (gammaOneIso C).hom) ≫ endpointArrow N := by
    rw [← Category.assoc, psi_square_public, Category.assoc,
      gamma_arrow_product]
    rfl
  have hp : JTGtildeOrderedFiberAction.sourcePoint W x y ≫
      (psiBase W ≫ (gammaProductIso C).hom) =
      point N
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y) := by
    rw [← Category.assoc, psi_point_square, psi_point_product]
  have hmap :
      chosenMap (JTGtildeOrderedFiberAction.sourceEndpointArrow W)
        (endpointArrow N)
        (psiRow W ≫ (gammaOneIso C).hom)
        (psiBase W ≫ (gammaProductIso C).hom) hs
        (JTGtildeOrderedFiberAction.sourcePoint W x y)
        (point N
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
        hp = fiberMap (chosenPsi W) x y := by
    change chosenMap (JTGtildeOrderedFiberAction.sourceEndpointArrow W)
      (endpointArrow N)
      (psiRow W ≫ (gammaOneIso C).hom)
      (psiBase W ≫ (gammaProductIso C).hom) hs
      (JTGtildeOrderedFiberAction.sourcePoint W x y)
      (point N
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
        (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
      hp =
      chosenMap (JTGtildeOrderedFiberAction.sourceEndpointArrow W)
        (endpointArrow N) (rowMap (chosenPsi W) ⦋1⦌)
        (prod.map (rowMap (chosenPsi W) ⦋0⦌)
          (rowMap (chosenPsi W) ⦋0⦌))
        (endpoint_square (chosenPsi W))
        (JTGtildeOrderedFiberAction.sourcePoint W x y)
        (point N
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) x)
          (((chosenPsi W).app (op JTZeroObjects.zeroIndex)).app (op ⦋0⦌) y))
        (point_square (chosenPsi W) x y)
    exact chosenMap_congr_square _ _ (psi_row_one_product W)
      (psi_base_product W) hs (endpoint_square (chosenPsi W))
      _ _ hp (point_square (chosenPsi W) x y)
  exact h.trans (congrArg (weakEquivalences SSet.{0}).Q.map hmap)

/-- The actual chosenPsi map is weak on its ordinary ordered fibers,
using the original raw JT input. -/
theorem chosenPsi_fiberMap_weak_of_raw (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (fiberMap (chosenPsi W) x y) := by
  let Q := (weakEquivalences SSet.{0}).Q
  haveI : WeakEquivalence (psiChosenMap W x y) :=
    psiChosenMap_weak_of_raw W x y hraw
  haveI : WeakEquivalence (gammaChosenBridge W x y) :=
    gammaChosenBridge_weak W x y
  haveI : IsIso (Q.map (psiChosenMap W x y)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _
      (mem_weakEquivalences _)
  haveI : IsIso (Q.map (gammaChosenBridge W x y)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _
      (mem_weakEquivalences _)
  apply (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q (fiberMap (chosenPsi W) x y)).2
  rw [← psi_fiberMap_localized_eq]
  infer_instance

private theorem rowMap_comp {V Y Z : Source} (f : V ⟶ Y)
    (g : Y ⟶ Z) (m : SimplexCategory) :
    rowMap (f ≫ g) m = rowMap f m ≫ rowMap g m := by
  apply NatTrans.ext
  funext k z
  rfl

/-- The original rowwise pointed-arrow assignment respects actual
composition after Kan localization. -/
theorem fiberMap_localized_comp {V Y Z : Source}
    (f : V ⟶ Y) (g : Y ⟶ Z)
    (x y : (row V ⦋0⦌).obj (op ⦋0⦌)) :
    (weakEquivalences SSet.{0}).Q.map (fiberMap f x y) ≫
        (weakEquivalences SSet.{0}).Q.map
          (fiberMap g
            ((rowMap f ⦋0⦌).app (op ⦋0⦌) x)
            ((rowMap f ⦋0⦌).app (op ⦋0⦌) y)) =
      (weakEquivalences SSet.{0}).Q.map (fiberMap (f ≫ g) x y) := by
  let xf := (rowMap f ⦋0⦌).app (op ⦋0⦌) x
  let yf := (rowMap f ⦋0⦌).app (op ⦋0⦌) y
  have h := ChosenHomotopyFiberFunctor.chosenMap_comp
    (endpointArrow V) (endpointArrow Y) (endpointArrow Z)
    (rowMap f ⦋1⦌)
    (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌))
    (endpoint_square f)
    (rowMap g ⦋1⦌)
    (prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌))
    (endpoint_square g)
    (point V x y) (point Y xf yf)
    (point Z ((rowMap g ⦋0⦌).app (op ⦋0⦌) xf)
      ((rowMap g ⦋0⦌).app (op ⦋0⦌) yf))
    (point_square f x y) (point_square g xf yf)
  have hf : rowMap f ⦋1⦌ ≫ rowMap g ⦋1⦌ =
      rowMap (f ≫ g) ⦋1⦌ := (rowMap_comp f g ⦋1⦌).symm
  have hg : prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) ≫
        prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌) =
      prod.map (rowMap (f ≫ g) ⦋0⦌)
        (rowMap (f ≫ g) ⦋0⦌) := by
    rw [prod.map_map, ← rowMap_comp]
  have hs : endpointArrow V ≫
      (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) ≫
        prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)) =
      (rowMap f ⦋1⦌ ≫ rowMap g ⦋1⦌) ≫ endpointArrow Z := by
    rw [← Category.assoc, endpoint_square f, Category.assoc,
      endpoint_square g]
    rfl
  have hp : point V x y ≫
      (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) ≫
        prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)) =
      point Z ((rowMap g ⦋0⦌).app (op ⦋0⦌) xf)
        ((rowMap g ⦋0⦌).app (op ⦋0⦌) yf) := by
    rw [← Category.assoc, point_square f, point_square g]
  have hmap := chosenMap_congr_square
    (endpointArrow V) (endpointArrow Z) hf hg hs
    (endpoint_square (f ≫ g)) (point V x y)
    (point Z ((rowMap g ⦋0⦌).app (op ⦋0⦌) xf)
      ((rowMap g ⦋0⦌).app (op ⦋0⦌) yf)) hp
    (point_square (f ≫ g) x y)
  change (weakEquivalences SSet.{0}).Q.map (fiberMap f x y) ≫
      (weakEquivalences SSet.{0}).Q.map (fiberMap g xf yf) =
    (weakEquivalences SSet.{0}).Q.map
      (chosenMap (endpointArrow V) (endpointArrow Z)
        (rowMap f ⦋1⦌ ≫ rowMap g ⦋1⦌)
        (prod.map (rowMap f ⦋0⦌) (rowMap f ⦋0⦌) ≫
          prod.map (rowMap g ⦋0⦌) (rowMap g ⦋0⦌)) _
        (point V x y)
        (point Z ((rowMap g ⦋0⦌).app (op ⦋0⦌) xf)
          ((rowMap g ⦋0⦌).app (op ⦋0⦌) yf)) _) at h
  exact h.trans (congrArg (weakEquivalences SSet.{0}).Q.map hmap)

/-- The literal q after the literal chosenPsi, with its original
projective-resolution source. -/
def chosenComposite (W : Source) :
    JTStrictificationMaps.Qproj.obj W ⟶
      (@frameNerveTest (rigidCoefficient (chosenT W))
        (rigidCoefficient_fibrant (chosenT W))).target :=
  chosenPsi W ≫
    @q (rigidCoefficient (chosenT W))
      (rigidCoefficient_fibrant (chosenT W))

/-- The actual composite preserves the zero--one ordered endpoint square. -/
theorem chosenComposite_endpoint_square (W : Source) :
    endpointArrow (JTStrictificationMaps.Qproj.obj W) ≫
        prod.map (rowMap (chosenComposite W) ⦋0⦌)
          (rowMap (chosenComposite W) ⦋0⦌) =
      rowMap (chosenComposite W) ⦋1⦌ ≫
        endpointArrow
          (@frameNerveTest (rigidCoefficient (chosenT W))
            (rigidCoefficient_fibrant (chosenT W))).target :=
  endpoint_square (chosenComposite W)

/-- Its specified ordered source pair maps to the actual composite
image pair, without changing or exchanging endpoints. -/
theorem chosenComposite_point_square (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    point (JTStrictificationMaps.Qproj.obj W) x y ≫
        prod.map (rowMap (chosenComposite W) ⦋0⦌)
          (rowMap (chosenComposite W) ⦋0⦌) =
      point
        (@frameNerveTest (rigidCoefficient (chosenT W))
          (rigidCoefficient_fibrant (chosenT W))).target
        ((rowMap (chosenComposite W) ⦋0⦌).app (op ⦋0⦌) x)
        ((rowMap (chosenComposite W) ⦋0⦌).app (op ⦋0⦌) y) :=
  point_square (chosenComposite W) x y

/-- The chosen ordered-fiber map induced by the actual composite
q ∘ chosenPsi, based at the original x,y. -/
def compositeFiberMap (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  fiberMap (chosenComposite W) x y

/-- Under the original raw JT ordered-fiber input, the literal
q ∘ chosenPsi is weak on each chosen ordered endpoint fiber. -/
theorem compositeFiberMap_weak_of_raw (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (compositeFiberMap W x y) := by
  let C := rigidCoefficient (chosenT W)
  let qW := @q C (rigidCoefficient_fibrant (chosenT W))
  let Q := (weakEquivalences SSet.{0}).Q
  haveI : WeakEquivalence (fiberMap (chosenPsi W) x y) :=
    chosenPsi_fiberMap_weak_of_raw W x y hraw
  haveI : WeakEquivalence
      (fiberMap qW
        ((rowMap (chosenPsi W) ⦋0⦌).app (op ⦋0⦌) x)
        ((rowMap (chosenPsi W) ⦋0⦌).app (op ⦋0⦌) y)) := by
    exact q_after_chosenPsi_fiber_weak W x y
  haveI : IsIso (Q.map (fiberMap (chosenPsi W) x y)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _
      (mem_weakEquivalences _)
  haveI : IsIso (Q.map
      (fiberMap qW
        ((rowMap (chosenPsi W) ⦋0⦌).app (op ⦋0⦌) x)
        ((rowMap (chosenPsi W) ⦋0⦌).app (op ⦋0⦌) y))) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _
      (mem_weakEquivalences _)
  apply (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q (compositeFiberMap W x y)).2
  change IsIso (Q.map (fiberMap (chosenPsi W ≫ qW) x y))
  rw [← fiberMap_localized_comp]
  infer_instance

end

end DaggerModels.PartII.JTPQOrderedFiberTransfer
