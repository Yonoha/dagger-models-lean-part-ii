import OrdinarySegalResolutionMappingFibers
import NativeBisimplicialDiagonalWeak
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Fixed-pair strict mapping fibers of the vertical precompletion unit

The diagonal of the fixed-pair resolution fiber is compared with the strict
ordered mapping fiber of the corrected vertical precompletion. The comparison
uses the actual images of the original vertices under the corrected unit.
No fibrancy of the precompletion, homotopy-fiber comparison, or completeness
statement is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionFiberComparison

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint mappingFiber)
open OrdinarySegalOrderedMappingMaps (endpointMap point_naturality mappingMap)
open OrdinarySegalResolutionMappingFibers
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W

/-- A constant outer simplicial diagram has its original inner diagonal. -/
def constantDiagonalIso (X : SSet.{0}) :
    diagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Diagonalizing a constant map is the original map under this isomorphism. -/
theorem constantDiagonal_map {X Y : SSet.{0}} (f : X ⟶ Y) :
    diagonalFunctor.map ((Functor.const SimplexCategoryᵒᵖ).map f) ≫
        (constantDiagonalIso Y).hom =
      (constantDiagonalIso X).hom ≫ f := by
  apply NatTrans.ext
  funext q
  rfl

/-- The diagonal of the row unit is the actual corrected unit component. -/
theorem diagonal_rowUnit (W : Space) (n : ℕ) :
    diagonalFunctor.map (rowUnit W n) =
      (constantDiagonalIso (W.obj (op ⦋n⦌))).hom ≫
        (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋n⦌) := by
  apply NatTrans.ext
  funext q
  exact (OrdinarySegalVerticalPrecompletion.unit_app_app W
    (op ⦋n⦌) q).symm

theorem diagonal_faceResolution (W : Space) (i : Fin 2) :
    diagonalFunctor.map (faceResolution W i) =
      (P W).map (SimplexCategory.δ i).op := by
  apply NatTrans.ext
  funext q
  rfl

theorem diagonal_vertexResolution (W : Space)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    diagonalFunctor.map (vertexResolution W x) =
      (constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
        SSet.yonedaEquiv.symm x ≫
          (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋0⦌) := by
  rw [vertexResolution, diagonalFunctor.map_comp, diagonal_rowUnit]
  rw [← Category.assoc, constantDiagonal_map, Category.assoc]

/-- The diagonal preserves the pair of horizontal endpoint objects. -/
def baseProductIso (W : Space) :
    diagonalFunctor.obj
        (rowResolution W 0 ⨯ rowResolution W 0) ≅
      (P W).obj (op ⦋0⦌) ⨯ (P W).obj (op ⦋0⦌) :=
  PreservesLimitPair.iso diagonalFunctor (rowResolution W 0)
    (rowResolution W 0)

/-- The diagonal endpoint map is the literal ordered endpoint arrow of
the corrected precompletion, after the canonical product isomorphism. -/
theorem endpoint_diagonal (W : Space) :
    diagonalFunctor.map (endpointResolution W) ≫ (baseProductIso W).hom =
      endpointArrow (P W) := by
  apply prod.hom_ext
  · calc
      (diagonalFunctor.map (endpointResolution W) ≫
          (baseProductIso W).hom) ≫ prod.fst =
        diagonalFunctor.map
          (endpointResolution W ≫ prod.fst) := by
            change (diagonalFunctor.map (endpointResolution W) ≫
              prodComparison diagonalFunctor (rowResolution W 0)
                (rowResolution W 0)) ≫ prod.fst = _
            rw [Category.assoc,
              prodComparison_fst diagonalFunctor
                (rowResolution W 0) (rowResolution W 0),
              ← diagonalFunctor.map_comp]
      _ = (P W).map (SimplexCategory.δ (1 : Fin 2)).op := by
            rw [endpointResolution, prod.lift_fst,
              diagonal_faceResolution]
      _ = endpointArrow (P W) ≫ prod.fst :=
        (OrdinarySegalOrderedMappingFibres.endpointArrow_fst (P W)).symm
  · calc
      (diagonalFunctor.map (endpointResolution W) ≫
          (baseProductIso W).hom) ≫ prod.snd =
        diagonalFunctor.map
          (endpointResolution W ≫ prod.snd) := by
            change (diagonalFunctor.map (endpointResolution W) ≫
              prodComparison diagonalFunctor (rowResolution W 0)
                (rowResolution W 0)) ≫ prod.snd = _
            rw [Category.assoc,
              prodComparison_snd diagonalFunctor
                (rowResolution W 0) (rowResolution W 0),
              ← diagonalFunctor.map_comp]
      _ = (P W).map (SimplexCategory.δ (0 : Fin 2)).op := by
            rw [endpointResolution, prod.lift_snd,
              diagonal_faceResolution]
      _ = endpointArrow (P W) ≫ prod.snd :=
        (OrdinarySegalOrderedMappingFibres.endpointArrow_snd (P W)).symm

/-- The exact vertex in the precompletion is the image under its unit. -/
def unitVertex (W : Space)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ((P W).obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
  (((OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋0⦌)).app
    (op ⦋0⦌)) x

/-- The diagonal boundary point is the literal ordered pair of unit images. -/
theorem point_diagonal (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    diagonalFunctor.map (pointResolution W x y) ≫
        (baseProductIso W).hom =
      (constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
        endpointPoint (P W) (unitVertex W x) (unitVertex W y) := by
  have h : endpointPoint W x y ≫
      endpointMap (OrdinarySegalVerticalPrecompletion.unit W) =
        endpointPoint (P W) (unitVertex W x) (unitVertex W y) :=
    point_naturality (OrdinarySegalVerticalPrecompletion.unit W) x y
  rw [← h]
  apply prod.hom_ext
  · calc
      (diagonalFunctor.map (pointResolution W x y) ≫
          (baseProductIso W).hom) ≫ prod.fst =
        diagonalFunctor.map (vertexResolution W x) := by
            change (diagonalFunctor.map (pointResolution W x y) ≫
              prodComparison diagonalFunctor (rowResolution W 0)
                (rowResolution W 0)) ≫ prod.fst = _
            rw [Category.assoc,
              prodComparison_fst diagonalFunctor
                (rowResolution W 0) (rowResolution W 0),
              ← diagonalFunctor.map_comp,
              pointResolution, prod.lift_fst]
      _ = (constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
          SSet.yonedaEquiv.symm x ≫
            (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋0⦌) :=
        diagonal_vertexResolution W x
      _ = ((constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
          endpointPoint W x y ≫
            endpointMap (OrdinarySegalVerticalPrecompletion.unit W)) ≫
              prod.fst := by
            simp only [Category.assoc, endpointMap, prod.map_fst,
              endpointPoint, prod.lift_fst_assoc]
  · calc
      (diagonalFunctor.map (pointResolution W x y) ≫
          (baseProductIso W).hom) ≫ prod.snd =
        diagonalFunctor.map (vertexResolution W y) := by
            change (diagonalFunctor.map (pointResolution W x y) ≫
              prodComparison diagonalFunctor (rowResolution W 0)
                (rowResolution W 0)) ≫ prod.snd = _
            rw [Category.assoc,
              prodComparison_snd diagonalFunctor
                (rowResolution W 0) (rowResolution W 0),
              ← diagonalFunctor.map_comp,
              pointResolution, prod.lift_snd]
      _ = (constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
          SSet.yonedaEquiv.symm y ≫
            (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋0⦌) :=
        diagonal_vertexResolution W y
      _ = ((constantDiagonalIso (Δ[0] : SSet.{0})).hom ≫
          endpointPoint W x y ≫
            endpointMap (OrdinarySegalVerticalPrecompletion.unit W)) ≫
              prod.snd := by
            simp only [Category.assoc, endpointMap, prod.map_snd,
              endpointPoint, prod.lift_snd_assoc]

/-- Diagonalization preserves the global pullback; the three comparison
objects are then transported by the total identity, the constant-point
isomorphism, and the chosen-product isomorphism. -/
def diagonalFiberIso (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    diagonalFunctor.obj (fiberResolution W x y) ≅
      mappingFiber (P W) (unitVertex W x) (unitVertex W y) :=
  PreservesPullback.iso diagonalFunctor (endpointResolution W)
    (pointResolution W x y) ≪≫
      asIso (pullback.map
        (diagonalFunctor.map (endpointResolution W))
        (diagonalFunctor.map (pointResolution W x y))
        (endpointArrow (P W))
        (endpointPoint (P W) (unitVertex W x) (unitVertex W y))
        (𝟙 _) (constantDiagonalIso (Δ[0] : SSet.{0})).hom
        (baseProductIso W).hom
        (by simpa only [Category.id_comp] using endpoint_diagonal W)
        (point_diagonal W x y))

/-- The total coordinate of the diagonal fiber is unchanged. -/
theorem diagonalFiberIso_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (diagonalFiberIso W x y).hom ≫
        pullback.fst (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      diagonalFunctor.map
        (pullback.fst (endpointResolution W) (pointResolution W x y)) := by
  dsimp only [diagonalFiberIso, Iso.trans_hom, asIso_hom, pullback.map]
  rw [Category.assoc, pullback.lift_fst, Category.comp_id,
    PreservesPullback.iso_hom_fst]

/-- The point coordinate is identified through the constant-diagonal iso. -/
theorem diagonalFiberIso_snd (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (diagonalFiberIso W x y).hom ≫
        pullback.snd (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      diagonalFunctor.map
          (pullback.snd (endpointResolution W) (pointResolution W x y)) ≫
        (constantDiagonalIso (Δ[0] : SSet.{0})).hom := by
  dsimp only [diagonalFiberIso, Iso.trans_hom, asIso_hom, pullback.map]
  rw [Category.assoc, pullback.lift_snd]
  exact congrArg
    (fun k ↦ k ≫ (constantDiagonalIso (Δ[0] : SSet.{0})).hom)
    (PreservesPullback.iso_hom_snd diagonalFunctor
      (endpointResolution W) (pointResolution W x y))

/-- The diagonal of the constant fixed-pair comparison, expressed on the
original source fiber and the actual precompletion target fiber. -/
def strictUnitFiberComparison (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶
      mappingFiber (P W) (unitVertex W x) (unitVertex W y) :=
  (constantDiagonalIso (mappingFiber W x y)).inv ≫
    diagonalFunctor.map (constantFiberComparison W x y) ≫
      (diagonalFiberIso W x y).hom

/-- Its first coordinate is the actual horizontal degree-one unit map. -/
theorem strictUnitFiberComparison_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictUnitFiberComparison W x y ≫
        pullback.fst (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
        (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌) := by
  calc
    strictUnitFiberComparison W x y ≫
        pullback.fst (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      (constantDiagonalIso (mappingFiber W x y)).inv ≫
        (diagonalFunctor.map
          ((Functor.const SimplexCategoryᵒᵖ).map
            (pullback.fst (endpointArrow W) (endpointPoint W x y))) ≫
          (constantDiagonalIso (W.obj (op ⦋1⦌))).hom) ≫
            (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌) := by
              simp only [strictUnitFiberComparison, Category.assoc]
              rw [diagonalFiberIso_fst, ← diagonalFunctor.map_comp,
                constantFiberComparison_fst, diagonalFunctor.map_comp,
                diagonal_rowUnit]
    _ = pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
          (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌) := by
            have h := congrArg
              (fun k ↦ (constantDiagonalIso (mappingFiber W x y)).inv ≫
                k ≫ (OrdinarySegalVerticalPrecompletion.unit W).app
                  (op ⦋1⦌))
              (constantDiagonal_map
                (pullback.fst (endpointArrow W) (endpointPoint W x y)))
            simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- Its second coordinate is still the original standard zero-simplex. -/
theorem strictUnitFiberComparison_snd (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictUnitFiberComparison W x y ≫
        pullback.snd (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      pullback.snd (endpointArrow W) (endpointPoint W x y) := by
  calc
    strictUnitFiberComparison W x y ≫
        pullback.snd (endpointArrow (P W))
          (endpointPoint (P W) (unitVertex W x) (unitVertex W y)) =
      (constantDiagonalIso (mappingFiber W x y)).inv ≫
        (diagonalFunctor.map
          ((Functor.const SimplexCategoryᵒᵖ).map
            (pullback.snd (endpointArrow W) (endpointPoint W x y))) ≫
          (constantDiagonalIso (Δ[0] : SSet.{0})).hom) := by
            simp only [strictUnitFiberComparison, Category.assoc]
            rw [diagonalFiberIso_snd]
            have h := congrArg
              (fun k ↦ (constantDiagonalIso (mappingFiber W x y)).inv ≫
                diagonalFunctor.map k ≫
                  (constantDiagonalIso (Δ[0] : SSet.{0})).hom)
              (constantFiberComparison_snd W x y)
            simpa only [Functor.map_comp, Category.assoc] using h
    _ = pullback.snd (endpointArrow W) (endpointPoint W x y) := by
          have h := congrArg
            (fun k ↦ (constantDiagonalIso (mappingFiber W x y)).inv ≫ k)
            (constantDiagonal_map
              (pullback.snd (endpointArrow W) (endpointPoint W x y)))
          simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The diagonal comparison is the literal ordered mapping-fiber map
of the corrected vertical precompletion unit. -/
theorem strictUnitFiberComparison_eq_mappingMap (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    strictUnitFiberComparison W x y =
      mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y := by
  apply pullback.hom_ext
  · exact (strictUnitFiberComparison_fst W x y).trans
      (OrdinarySegalOrderedMappingMaps.mappingMap_fst
        (OrdinarySegalVerticalPrecompletion.unit W) x y).symm
  · exact (strictUnitFiberComparison_snd W x y).trans
      (OrdinarySegalOrderedMappingMaps.mappingMap_snd
        (OrdinarySegalVerticalPrecompletion.unit W) x y).symm

/-- Strict ordered mapping fibers at the original fixed pair are weakly
equivalent under the corrected vertical precompletion unit. -/
theorem mappingMap_unit_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (OrdinarySegalVerticalPrecompletion.unit W) x y) := by
  haveI : WeakEquivalence
      (diagonalFunctor.map (constantFiberComparison W x y)) :=
    DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
      (constantFiberComparison W x y) (rowComparison_weak W hSegal x y)
  have h : WeakEquivalence (strictUnitFiberComparison W x y) := by
    unfold strictUnitFiberComparison
    infer_instance
  rw [strictUnitFiberComparison_eq_mappingMap] at h
  exact h

#print axioms endpoint_diagonal
#print axioms point_diagonal
#print axioms strictUnitFiberComparison_eq_mappingMap
#print axioms mappingMap_unit_weak

end

end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionFiberComparison
