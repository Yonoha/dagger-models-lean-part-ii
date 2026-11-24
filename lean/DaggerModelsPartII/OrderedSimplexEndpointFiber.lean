import DaggerModelsPartII.OrderedNecklaceVertexPoints
import DaggerModelsPartII.NecklaceSimplexCompletion
import DaggerModelsPartII.DiagramMappingRepresentable
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration

/-!
# The actual single-edge ordered label fiber

Tensor--Yoneda assembles into mapping isomorphisms natural in the representing
object. The two original cofaces and the actual boundary point calibrate the
single-edge label fiber to the unchanged raw endpoint fiber of W. No chosen
right-adjoint-uniqueness evaluation formula or replacement fiber is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerModels

namespace DaggerModels.PartII.OrderedSimplexEndpointFiber

open SegalLocalizers ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison OrderedNecklaceLabelDiagram
open OrderedNecklaceVertexPoints JTXiEndpointCollapseBoundary

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}

/-- The retained tensor--Yoneda equivalence assembled in all inner degrees. -/
def tensorYonedaMappingIso {C : Type} [SmallCategory C] (W : Cᵒᵖ ⥤ SSet.{0})
    (c : C) :
    diagramMappingSpace
        ((simplicialYoneda.{0, 0} C).obj c) W ≅ W.obj (op c) :=
  NatIso.ofComponents
    (fun q ↦ ((representableTensorHomEquiv c
      (SSet.stdSimplex.obj q.unop) W).trans SSet.yonedaEquiv).toIso)
    (by
      intro q r g
      funext η
      have h := congrFun ((η.app (op c)).naturality g)
        (ULift.up (𝟙 c),
          SSet.stdSimplex.objEquiv.symm (𝟙 q.unop))
      simpa [diagramMappingSpace, diagramTensor,
        representableTensorHomEquiv, representableTensorHomTo,
        SSet.yonedaEquiv, SSet.stdSimplex.map_apply] using h)

/-- The explicit isomorphism evaluates a transformation at the identity
of the representing reversal object and the identity simplex. -/
theorem tensorYonedaMappingIso_apply {C : Type} [SmallCategory C] (W : Cᵒᵖ ⥤ SSet.{0})
    (c : C) (q : SimplexCategory)
    (η : (diagramMappingSpace
      ((simplicialYoneda.{0, 0} C).obj c) W).obj (op q)) :
    ((tensorYonedaMappingIso W c).hom.app
      (op q)) η =
      (η.app (op c)).app (op q)
        (ULift.up (𝟙 c),
          SSet.stdSimplex.objEquiv.symm (𝟙 q)) := by
  rfl

/-- Enriched Yoneda is natural in the original reversal representing
object; no discrete free-dagger comparison is involved in this step. -/
theorem tensorYonedaMappingIso_natural {C : Type} [SmallCategory C] (W : Cᵒᵖ ⥤ SSet.{0})
    {c d : C} (f : c ⟶ d) :
    diagramMappingPrecomp
        ((simplicialYoneda.{0, 0} C).map f) W ≫
        (tensorYonedaMappingIso W c).hom =
      (tensorYonedaMappingIso W d).hom ≫
        W.map f.op := by
  apply NatTrans.ext
  funext q
  cases q with
  | op q =>
    funext η
    change ((tensorYonedaMappingIso W c).hom.app
        (op q)) ((diagramMappingPrecomp
          ((simplicialYoneda.{0, 0} C).map f) W).app
            (op q) η) =
      (W.map f.op).app (op q)
        (((tensorYonedaMappingIso W d).hom.app
          (op q)) η)
    rw [tensorYonedaMappingIso_apply W c q,
      tensorYonedaMappingIso_apply W d q]
    have h := congrFun
      (NatTrans.congr_app (η.naturality f.op) (op q))
      (ULift.up (𝟙 d), SSet.stdSimplex.objEquiv.symm (𝟙 q))
    simpa [diagramMappingPrecomp, diagramTensor, simplicialYoneda,
      discretePresheaf, uliftYoneda] using h

def freeMappingIso (W : Source) (n : ℕ) :
    diagramMappingSpace (daggerSimplex n) W ≅ W.obj (op (⟨n⟩ : ReverseSimplex)) :=
  ((diagramMappingSource W).mapIso
    (SegalRepresentables.freeSimplexRepresentable n).op).symm ≪≫
      tensorYonedaMappingIso W ⟨n⟩

theorem freeSimplexMappingIso_natural (W : Source)
    {m n : SimplexCategory} (f : m ⟶ n) :
    diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
        (freeMappingIso W m.len).hom =
      (freeMappingIso W n.len).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op := by
  let e := SegalRepresentables.freeSimplicesRepresentable.{0}
  have hnat := e.inv.naturality f
  have hpre :
      diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
        diagramMappingPrecomp (e.inv.app m) W =
      diagramMappingPrecomp (e.inv.app n) W ≫
        diagramMappingPrecomp
          ((ReverseSimplex.inclusion ⋙
            simplicialYoneda.{0, 0} ReverseSimplex).map f) W := by
    rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
    exact congrArg (fun z ↦ diagramMappingPrecomp z W) hnat.symm
  change diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
      diagramMappingPrecomp (e.inv.app m) W ≫
        (tensorYonedaMappingIso W (ReverseSimplex.inclusion.obj m)).hom =
    diagramMappingPrecomp (e.inv.app n) W ≫
      (tensorYonedaMappingIso W (ReverseSimplex.inclusion.obj n)).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op
  rw [← Category.assoc, hpre]
  have hrep := tensorYonedaMappingIso_natural W
    (ReverseSimplex.inclusion.map f)
  change diagramMappingPrecomp
      ((ReverseSimplex.inclusion ⋙
        simplicialYoneda.{0, 0} ReverseSimplex).map f) W ≫
        (tensorYonedaMappingIso W
          (ReverseSimplex.inclusion.obj m)).hom =
      (tensorYonedaMappingIso W
        (ReverseSimplex.inclusion.obj n)).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op at hrep
  simpa only [Category.assoc] using congrArg
    (fun z ↦ diagramMappingPrecomp (e.inv.app n) W ≫ z) hrep

theorem rowRestriction_endpoint (W : Source) (i : Fin 2) :
    (rowRestrictionIso W ⦋1⦌).inv ≫ endpoint W i =
      W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint i)).op ≫
        (rowRestrictionIso W ⦋0⦌).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [rowRestrictionIso, endpoint, row,
    JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
  simp

/-- The chosen free-simplex mapping isomorphism followed by the raw-row
restriction isomorphism. -/
def freeSimplexRowIso (W : Source) (n : ℕ) :
    diagramMappingSpace (daggerSimplex n) W ≅ row W ⦋n⦌ :=
  freeMappingIso W n ≪≫ (rowRestrictionIso W ⦋n⦌).symm


/-- The literal free-zero point is recovered at its original raw vertex. -/
theorem freeMappingIso_zeroLabel (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    ((freeMappingIso W 0).hom.app (op ⦋0⦌)) (zeroLabel W x) =
      ((rowRestrictionIso W ⦋0⦌).hom.app (op ⦋0⦌)) x := by
  change SSet.yonedaEquiv
    (representableTensorHomTo (ReverseSimplex.inclusion.obj ⦋0⦌)
      (Functor.whiskerRight (SegalRepresentables.freeSimplexRepresentable 0).inv
        (tensorRight (Δ[0] : SSet.{0})) ≫ zeroLabel W x)) = _
  rw [zeroLabel_tensorYoneda, SSet.yonedaEquiv_comp]
  simp only [vertexPoint, Equiv.apply_symm_apply]

/-- The SAME zero point, after free-simplex row transport, is the original point. -/
theorem freeSimplexRowIso_zeroPoint (W : Source)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    zeroPoint W x ≫ (freeSimplexRowIso W 0).hom = vertexPoint W x := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [zeroPoint, vertexPoint, Equiv.apply_symm_apply]
  change ((rowRestrictionIso W ⦋0⦌).inv.app (op ⦋0⦌))
    (((freeMappingIso W 0).hom.app (op ⦋0⦌)) (zeroLabel W x)) = x
  rw [freeMappingIso_zeroLabel]
  exact congrFun (NatTrans.congr_app (rowRestrictionIso W ⦋0⦌).hom_inv_id (op ⦋0⦌)) x

/-- The two actual outer cofaces are transported without reversing their order. -/
theorem freeSimplexRowIso_endpoint (W : Source) (i : Fin 2) :
    diagramMappingPrecomp
        (SegalRepresentables.freeSimplices.map (ordinaryEndpoint i)) W ≫
      (freeSimplexRowIso W 0).hom =
        (freeSimplexRowIso W 1).hom ≫ endpoint W i := by
  have hn := freeSimplexMappingIso_natural W (ordinaryEndpoint i)
  change diagramMappingPrecomp
      (SegalRepresentables.freeSimplices.map (ordinaryEndpoint i)) W ≫
        (freeMappingIso W 0).hom =
      (freeMappingIso W 1).hom ≫
        W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint i)).op at hn
  simpa only [freeSimplexRowIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, rowRestriction_endpoint] using
    congrArg (fun z ↦ z ≫ (rowRestrictionIso W ⦋0⦌).inv) hn

/-- The common boundary-label space as the original ordered raw-row product. -/
def boundaryRowIso (W : Source) :
    boundaryLabels W ≅ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  boundaryMappingIso W ≪≫
    prod.mapIso (freeSimplexRowIso W 0) (freeSimplexRowIso W 0)

/-- The original ordered vertex point is preserved by boundary transport. -/
theorem boundaryPoint_row (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    boundaryPoint W x y ≫ (boundaryRowIso W).hom = point W x y := by
  apply prod.hom_ext
  · simp only [boundaryRowIso, Iso.trans_hom, prod.mapIso_hom, Category.assoc,
      prod.map_fst, point, prod.lift_fst]
    rw [← Category.assoc (boundaryMappingIso W).hom prod.fst,
      boundaryMappingIso_fst, ← Category.assoc, boundaryPoint_first,
      freeSimplexRowIso_zeroPoint]
  · simp only [boundaryRowIso, Iso.trans_hom, prod.mapIso_hom, Category.assoc,
      prod.map_snd, point, prod.lift_snd]
    rw [← Category.assoc (boundaryMappingIso W).hom prod.snd,
      boundaryMappingIso_snd, ← Category.assoc, boundaryPoint_last,
      freeSimplexRowIso_zeroPoint]

/-- The first boundary leg of the single-edge simplex is its original zero coface. -/
theorem singleBoundary_first :
    (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) =
      SegalRepresentables.freeSimplices.map (ordinaryEndpoint 0) := by
  simp only [boundarySimplex, boundaryNecklace, coprod.inl_desc_assoc]
  rw [← F.map_comp]
  change F.map _ = F.map (SSet.stdSimplex.map (ordinaryEndpoint 0))
  congr 1

/-- The second boundary leg of the single-edge simplex is its original one coface. -/
theorem singleBoundary_last :
    (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) =
      SegalRepresentables.freeSimplices.map (ordinaryEndpoint 1) := by
  simp only [boundarySimplex, boundaryNecklace, coprod.inr_desc_assoc]
  rw [← F.map_comp]
  change F.map _ = F.map (SSet.stdSimplex.map (ordinaryEndpoint 1))
  congr 1

/-- The actual single-edge boundary restriction, with both raw cofaces calibrated. -/
def singleEndpointArrowIso (W : Source) :
    Arrow.mk (diagramMappingPrecomp
      (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W) ≅
        Arrow.mk (endpointArrow W) :=
  Arrow.isoMk (freeSimplexRowIso W 1) (boundaryRowIso W) (by
    apply prod.hom_ext
    · change ((freeSimplexRowIso W 1).hom ≫ endpointArrow W) ≫ prod.fst =
        (diagramMappingPrecomp
          (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W ≫
            (boundaryRowIso W).hom) ≫ prod.fst
      simp only [Category.assoc, endpointArrow, prod.lift_fst,
        boundaryRowIso, Iso.trans_hom, prod.mapIso_hom, prod.map_fst]
      rw [← Category.assoc (boundaryMappingIso W).hom prod.fst
        (freeSimplexRowIso W 0).hom, boundaryMappingIso_fst]
      rw [← Category.assoc
        (diagramMappingPrecomp
          (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W)
        (diagramMappingPrecomp coprod.inl W)
        (freeSimplexRowIso W 0).hom,
        ← diagramMappingPrecomp_comp, singleBoundary_first]
      exact (freeSimplexRowIso_endpoint W 0).symm
    · change ((freeSimplexRowIso W 1).hom ≫ endpointArrow W) ≫ prod.snd =
        (diagramMappingPrecomp
          (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W ≫
            (boundaryRowIso W).hom) ≫ prod.snd
      simp only [Category.assoc, endpointArrow, prod.lift_snd,
        boundaryRowIso, Iso.trans_hom, prod.mapIso_hom, prod.map_snd]
      rw [← Category.assoc (boundaryMappingIso W).hom prod.snd
        (freeSimplexRowIso W 0).hom, boundaryMappingIso_snd]
      rw [← Category.assoc
        (diagramMappingPrecomp
          (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W)
        (diagramMappingPrecomp coprod.inr W)
        (freeSimplexRowIso W 0).hom,
        ← diagramMappingPrecomp_comp, singleBoundary_last]
      exact (freeSimplexRowIso_endpoint W 1).symm)

/-- The actual single-edge ordered label fiber IS the original strict endpoint
fiber, preserving the specified original points, with no fibrancy premise. -/
def orderedSingleFiberIso (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (orderedSimplexLabels W (boundaryPoint W x y)).obj
        (op (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) ≅
      pullback (endpointArrow W) (point W x y) := by
  let p := diagramMappingPrecomp
    (boundarySimplex (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) W
  have h₁ : p ≫ (boundaryRowIso W).hom =
      (freeSimplexRowIso W 1).hom ≫ endpointArrow W :=
    (singleEndpointArrowIso W).hom.w.symm
  have h₂ : boundaryPoint W x y ≫ (boundaryRowIso W).hom =
      (𝟙 (Δ[0] : SSet.{0})) ≫ point W x y := by
    simpa only [Category.id_comp] using boundaryPoint_row W x y
  exact asIso (pullback.map p (boundaryPoint W x y)
    (endpointArrow W) (point W x y)
    (freeSimplexRowIso W 1).hom (𝟙 _) (boundaryRowIso W).hom h₁ h₂)

/-- The same isomorphism retains the total projection to the original one-row. -/
theorem orderedSingleFiberIso_fst (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (orderedSingleFiberIso W x y).hom ≫ pullback.fst (endpointArrow W) (point W x y) =
      pullback.fst _ _ ≫ (freeSimplexRowIso W 1).hom := by
  simp only [orderedSingleFiberIso, asIso_hom, pullback.map, pullback.lift_fst,
    simplexBoundaryRestriction]

/-- Canonical passage from the actual single-edge ordered label value to the
chosen homotopy fiber of the original raw endpoint arrow. -/
def orderedSingleToChosenFiber (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (orderedSimplexLabels W (boundaryPoint W x y)).obj
        (op (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) ⟶
      ChosenHomotopyFiberComparison.chosenFiber (endpointArrow W) (point W x y) :=
  (orderedSingleFiberIso W x y).hom ≫
    ChosenHomotopyFiberTriangle.inclusion (endpointArrow W) (point W x y)

/-- Original injective Kan fibrancy suffices for this SAME canonical map to
be weak; Segal or ordinary-completeness hypotheses are not required here. -/
theorem orderedSingleToChosenFiber_weak (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (orderedSingleToChosenFiber W x y) := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  haveI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion (endpointArrow W) (point W x y)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  dsimp only [orderedSingleToChosenFiber]
  infer_instance

end

end DaggerModels.PartII.OrderedSimplexEndpointFiber
