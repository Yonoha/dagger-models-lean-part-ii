import OrdinarySegalVerticalPrecompletion
import OrdinarySegalOrderedMappingMaps
import OrdinarySegalConstantGroupoidSimplexFullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Ordered mapping fibers along the vertical groupoid-simplex resolution

This file keeps a fixed pair of vertices of `W`. The outer simplicial degree
varies through `E[q]`; the strict fiber in each row is taken at the actual
constant-section images of that pair. No fibrancy of the eventual diagonal
precompletion is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalResolutionMappingFibers

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint mappingFiber)
open OrdinarySegalOrderedMappingMaps

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev R (W : Space) := OrdinarySegalPrecompletion.resolution W

/-- The horizontal `n`-row of the outer cotensor resolution. -/
def rowResolution (W : Space) (n : ℕ) : BiSSet.{0} :=
  R W ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋n⦌)

/-- The checked constant section, assembled at one horizontal row. -/
def rowUnit (W : Space) (n : ℕ) :
    (Functor.const SimplexCategoryᵒᵖ).obj (W.obj (op ⦋n⦌)) ⟶
      rowResolution W n :=
  Functor.whiskerRight (OrdinarySegalPrecompletion.resolutionUnit W)
    ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋n⦌))

/-- Evaluation transports the chosen product of outer diagrams to the
chosen product of the evaluated horizontal rows. -/
def rowBaseIso (W : Space) (q : SimplexCategoryᵒᵖ) :
    (rowResolution W 0 ⨯ rowResolution W 0).obj q ≅
      ((R W).obj q).obj (op ⦋0⦌) ⨯
        ((R W).obj q).obj (op ⦋0⦌) :=
  PreservesLimitPair.iso
    ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
    (rowResolution W 0) (rowResolution W 0)

/-- One of the two original horizontal faces, natural in the parameter. -/
def faceResolution (W : Space) (i : Fin 2) :
    rowResolution W 1 ⟶ rowResolution W 0 where
  app q := ((R W).obj q).map (SimplexCategory.δ i).op
  naturality := by
    intro q r θ
    exact ((R W).map θ).naturality (SimplexCategory.δ i).op

/-- The endpoint arrow in every outer groupoid-simplex degree. -/
def endpointResolution (W : Space) :
    rowResolution W 1 ⟶ rowResolution W 0 ⨯ rowResolution W 0 :=
  prod.lift (faceResolution W (1 : Fin 2))
    (faceResolution W (0 : Fin 2))

/-- The evaluated endpoint map has exactly the original ordered faces
after the canonical chosen-product isomorphism. -/
theorem endpointResolution_app (W : Space) (q : SimplexCategoryᵒᵖ) :
    (endpointResolution W).app q ≫ (rowBaseIso W q).hom =
      endpointArrow ((R W).obj q) := by
  apply prod.hom_ext
  · rw [Category.assoc]
    change (endpointResolution W).app q ≫
      prodComparison ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.fst = _
    rw [prodComparison_fst]
    change (endpointResolution W ≫ prod.fst).app q = _
    rw [endpointResolution, prod.lift_fst]
    exact (OrdinarySegalOrderedMappingFibres.endpointArrow_fst ((R W).obj q)).symm
  · rw [Category.assoc]
    change (endpointResolution W).app q ≫
      prodComparison ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.snd = _
    rw [prodComparison_snd]
    change (endpointResolution W ≫ prod.snd).app q = _
    rw [endpointResolution, prod.lift_snd]
    exact (OrdinarySegalOrderedMappingFibres.endpointArrow_snd ((R W).obj q)).symm

/-- The original vertex, followed by the actual constant section in each row. -/
def vertexResolution (W : Space)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (Functor.const SimplexCategoryᵒᵖ).obj (Δ[0] : SSet.{0}) ⟶
      rowResolution W 0 :=
  ((Functor.const SimplexCategoryᵒᵖ).map (SSet.yonedaEquiv.symm x)) ≫
    rowUnit W 0

/-- The ordered pair is constant at its source and follows the row unit. -/
def pointResolution (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (Functor.const SimplexCategoryᵒᵖ).obj (Δ[0] : SSet.{0}) ⟶
      rowResolution W 0 ⨯ rowResolution W 0 :=
  prod.lift (vertexResolution W x) (vertexResolution W y)

/-- The row point is the original boundary point followed by the actual map. -/
theorem pointResolution_app_from_source (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (pointResolution W x y).app q ≫ (rowBaseIso W q).hom =
      endpointPoint W x y ≫
        endpointMap ((OrdinarySegalPrecompletion.resolutionUnit W).app q) := by
  apply prod.hom_ext
  · rw [Category.assoc]
    change (pointResolution W x y).app q ≫
      prodComparison ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.fst = _
    rw [prodComparison_fst]
    change (pointResolution W x y ≫ prod.fst).app q = _
    rw [pointResolution, prod.lift_fst]
    rw [Category.assoc, endpointMap, prod.map_fst, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointPoint_fst]
    rfl
  · rw [Category.assoc]
    change (pointResolution W x y).app q ≫
      prodComparison ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
        (rowResolution W 0) (rowResolution W 0) ≫ prod.snd = _
    rw [prodComparison_snd]
    change (pointResolution W x y ≫ prod.snd).app q = _
    rw [pointResolution, prod.lift_snd]
    rw [Category.assoc, endpointMap, prod.map_snd, ← Category.assoc,
      OrdinarySegalOrderedMappingFibres.endpointPoint_snd]
    rfl

/-- Each point is exactly the ordered pair used by the strict row fiber. -/
theorem pointResolution_app (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (pointResolution W x y).app q ≫ (rowBaseIso W q).hom =
      endpointPoint ((R W).obj q)
        ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
          (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
          (op ⦋0⦌)).app (op ⦋0⦌) y) := by
  rw [pointResolution_app_from_source]
  exact point_naturality
    ((OrdinarySegalPrecompletion.resolutionUnit W).app q) x y

/-- The strict ordered mapping fibers form an outer simplicial diagram. -/
def fiberResolution (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) : BiSSet.{0} :=
  pullback (endpointResolution W) (pointResolution W x y)

/-- The constant original fiber maps into the strict resolution fibers. -/
def constantFiberComparison (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (Functor.const SimplexCategoryᵒᵖ).obj (mappingFiber W x y) ⟶
      fiberResolution W x y :=
  pullback.lift
    (((Functor.const SimplexCategoryᵒᵖ).map
      (pullback.fst (endpointArrow W) (endpointPoint W x y))) ≫
        rowUnit W 1)
    ((Functor.const SimplexCategoryᵒᵖ).map
      (pullback.snd (endpointArrow W) (endpointPoint W x y)))
    (by
      apply NatTrans.ext
      funext q
      change (pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
          ((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
            (op ⦋1⦌)) ≫ (endpointResolution W).app q =
        pullback.snd (endpointArrow W) (endpointPoint W x y) ≫
          (pointResolution W x y).app q
      apply (cancel_mono (rowBaseIso W q).hom).mp
      simp only [Category.assoc]
      rw [endpointResolution_app, pointResolution_app_from_source]
      rw [← endpoint_naturality]
      change pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
          endpointArrow W ≫
            endpointMap ((OrdinarySegalPrecompletion.resolutionUnit W).app q) = _
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ endpointMap
          ((OrdinarySegalPrecompletion.resolutionUnit W).app q))
        (pullback.condition (f := endpointArrow W) (g := endpointPoint W x y)))

/-- The first coordinate of the global comparison is the literal row unit. -/
theorem constantFiberComparison_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    constantFiberComparison W x y ≫
        pullback.fst (endpointResolution W) (pointResolution W x y) =
      ((Functor.const SimplexCategoryᵒᵖ).map
        (pullback.fst (endpointArrow W) (endpointPoint W x y))) ≫
          rowUnit W 1 :=
  pullback.lift_fst _ _ _

/-- The point coordinate stays the original standard zero-simplex. -/
theorem constantFiberComparison_snd (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    constantFiberComparison W x y ≫
        pullback.snd (endpointResolution W) (pointResolution W x y) =
      (Functor.const SimplexCategoryᵒᵖ).map
        (pullback.snd (endpointArrow W) (endpointPoint W x y)) :=
  pullback.lift_snd _ _ _

/-- Evaluation identifies a row of the global pullback with its strict
pointwise pullback. -/
def rowFiberIso (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (fiberResolution W x y).obj q ≅
      pullback ((endpointResolution W).app q)
        ((pointResolution W x y).app q) :=
  PreservesPullback.iso
    ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
    (endpointResolution W) (pointResolution W x y)

/-- Explicitly identify the evaluated global fiber with the literal row
mapping fiber, including the actual constant-section endpoint images. -/
def rowMappingFiberIso (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (fiberResolution W x y).obj q ≅
      mappingFiber ((R W).obj q)
        ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
          (op ⦋0⦌)).app (op ⦋0⦌) x)
        ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
          (op ⦋0⦌)).app (op ⦋0⦌) y) := by
  refine rowFiberIso W x y q ≪≫ ?_
  exact asIso (pullback.map
    ((endpointResolution W).app q) ((pointResolution W x y).app q)
    (endpointArrow ((R W).obj q))
    (endpointPoint ((R W).obj q)
      ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
        (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
        (op ⦋0⦌)).app (op ⦋0⦌) y))
    (𝟙 _) (𝟙 _) (rowBaseIso W q).hom
    (by simpa only [Category.id_comp] using endpointResolution_app W q)
    (by simpa only [Category.id_comp] using pointResolution_app W x y q))

theorem rowMappingFiberIso_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (rowMappingFiberIso W x y q).hom ≫
        pullback.fst (endpointArrow ((R W).obj q))
          (endpointPoint ((R W).obj q)
            ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
              (op ⦋0⦌)).app (op ⦋0⦌) x)
            ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
              (op ⦋0⦌)).app (op ⦋0⦌) y)) =
      (pullback.fst (endpointResolution W) (pointResolution W x y)).app q := by
  dsimp only [rowMappingFiberIso, Iso.trans_hom, asIso_hom, pullback.map]
  rw [Category.assoc, pullback.lift_fst, Category.comp_id]
  exact PreservesPullback.iso_hom_fst
    ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
    (endpointResolution W) (pointResolution W x y)

theorem rowMappingFiberIso_snd (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (rowMappingFiberIso W x y q).hom ≫
        pullback.snd (endpointArrow ((R W).obj q))
          (endpointPoint ((R W).obj q)
            ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
              (op ⦋0⦌)).app (op ⦋0⦌) x)
            ((((OrdinarySegalPrecompletion.resolutionUnit W).app q).app
              (op ⦋0⦌)).app (op ⦋0⦌) y)) =
      (pullback.snd (endpointResolution W) (pointResolution W x y)).app q := by
  dsimp only [rowMappingFiberIso, Iso.trans_hom, asIso_hom, pullback.map]
  rw [Category.assoc, pullback.lift_snd, Category.comp_id]
  exact PreservesPullback.iso_hom_snd
    ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj q)
    (endpointResolution W) (pointResolution W x y)

/-- The row comparison is precisely the pre-existing ordered mapping map. -/
theorem rowComparison_eq_mappingMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    (constantFiberComparison W x y).app q ≫
        (rowMappingFiberIso W x y q).hom =
      mappingMap ((OrdinarySegalPrecompletion.resolutionUnit W).app q) x y := by
  apply pullback.hom_ext
  · rw [Category.assoc, rowMappingFiberIso_fst]
    have h := congrArg (fun f ↦ f.app q)
      (constantFiberComparison_fst W x y)
    simpa only [NatTrans.comp_app, rowUnit] using
      h.trans (mappingMap_fst
        ((OrdinarySegalPrecompletion.resolutionUnit W).app q) x y).symm
  · rw [Category.assoc, rowMappingFiberIso_snd]
    have h := congrArg (fun f ↦ f.app q)
      (constantFiberComparison_snd W x y)
    simpa only [NatTrans.comp_app] using
      h.trans (mappingMap_snd
        ((OrdinarySegalPrecompletion.resolutionUnit W).app q) x y).symm

/-- Every fixed-pair row comparison is weak by the checked whole
groupoid-simplex constant-section theorem. -/
theorem rowComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((constantFiberComparison W x y).app q) := by
  have h : WeakEquivalence
      (mappingMap ((OrdinarySegalPrecompletion.resolutionUnit W).app q) x y) :=
    OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak W
      hSegal q.unop ⟨0, Nat.zero_lt_succ _⟩ x y
  haveI : WeakEquivalence ((rowMappingFiberIso W x y q).hom) := inferInstance
  have hc : WeakEquivalence
      ((constantFiberComparison W x y).app q ≫
        (rowMappingFiberIso W x y q).hom) := by
    rw [rowComparison_eq_mappingMap]
    exact h
  haveI := hc
  exact weakEquivalence_of_postcomp
    ((constantFiberComparison W x y).app q) (rowMappingFiberIso W x y q).hom

#print axioms pointResolution_app
#print axioms rowComparison_eq_mappingMap
#print axioms rowComparison_weak

end

end DaggerModels.PartII.OrdinarySegalResolutionMappingFibers
