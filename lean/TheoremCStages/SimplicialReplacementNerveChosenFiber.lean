import SimplicialReplacementValueChosenFiber
import SSetWeakPullbackComparison

/-!
# Chosen fiber at the literal nerve point

The original diagonal projection to `nerve C` and the actual point
`chainPoint c : Δ[0] ⟶ nerve C` are retained. The point and base
identifications from the bisimplicial comparison carry the already
checked weak value comparison to this literal chosen fiber.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (projection diagonalProjection)
open DaggerNativeReedyRelativeReplacement
open DaggerSimplicialReplacementChosenFiber
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SimplicialReplacementNerveChosenFiber

universe u

noncomputable section

variable {C : Type u} [Category.{u} C]

private abbrev A (G : C ⥤ SSet.{u}) : Arrow BiSSet.{u} := Arrow.mk (projection G)
private abbrev r (G : C ⥤ SSet.{u}) :=
  diagonalFunctor.map (relativeReplacement.obj (A G)).hom
private abbrev f (G : C ⥤ SSet.{u}) := diagonalFunctor.map (totalUnit (A G))
private abbrev g (G : C ⥤ SSet.{u}) :=
  (SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso (C := C)).inv ≫
    diagonalFunctor.map (baseUnit (A G))
private abbrev b (c : C) := chainPoint c
private abbrev d (G : C ⥤ SSet.{u}) (c : C) := b c ≫ g G
private abbrev oldPoint (c : C) :=
  diagonalFunctor.map (SimplicialReplacementChosenHomotopyFiber.coherentPoint c)
private abbrev relativeOldPoint (G : C ⥤ SSet.{u}) (c : C) :=
  diagonalFunctor.map
    (SimplicialReplacementChosenHomotopyFiber.coherentPoint c ≫ baseUnit (A G))
private abbrev pointIso :=
  SimplicialReplacementChosenHomotopyFiber.pointDiagonalIso.{u}

/-- The canonical strict-fiber inclusion at the literal nerve projection
and literal zero-simplex point. -/
def nerveValueToChosen (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ⟶ ChosenHomotopyFiberComparison.chosenFiber
      (diagonalProjection G) (chainPoint c) :=
  (chosenFiberIso G c).hom ≫
    ChosenHomotopyFiberTriangle.inclusion (diagonalProjection G) (chainPoint c)

private theorem square (G : C ⥤ SSet.{u}) :
    diagonalProjection G ≫ g G = f G ≫ r G := by
  dsimp only [g]
  rw [← Category.assoc]
  have hb : diagonalProjection G ≫
      (SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso (C := C)).inv =
      diagonalFunctor.map (projection G) := by
    dsimp only [diagonalProjection,
      SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso]
    simp
    rfl
  rw [hb, ← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp,
    unit_square]
  rfl

private theorem point_factor (G : C ⥤ SSet.{u}) (c : C) :
    relativeOldPoint G c = pointIso.hom ≫ d G c := by
  have hc := SimplicialReplacementChosenHomotopyFiber.coherentPoint_diagonal c
  have hcoherent : oldPoint c = pointIso.hom ≫ b c ≫
      (SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso (C := C)).inv := by
    calc
      oldPoint c = pointIso.hom ≫ (pointIso.inv ≫ oldPoint c) := by simp
      _ = pointIso.hom ≫
          (b c ≫ (SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso
            (C := C)).inv) := by rw [hc]
      _ = pointIso.hom ≫ b c ≫
          (SimplicialReplacementChosenHomotopyFiber.baseDiagonalIso
            (C := C)).inv := by rfl
  dsimp only [relativeOldPoint]
  rw [diagonalFunctor.map_comp]
  change oldPoint c ≫ diagonalFunctor.map (baseUnit (A G)) = pointIso.hom ≫ d G c
  rw [hcoherent]
  simp only [d, g, Category.assoc]

private def pointChange (G : C ⥤ SSet.{u}) (c : C) :
    SimplicialReplacementChosenHomotopyFiber.relativeFiber G c ⟶
      pullback (r G) (d G c) :=
  SSetWeakPullbackComparison.pointMap (r G)
    (relativeOldPoint G c) (d G c) pointIso.hom (point_factor G c)

private theorem originalFiberIso_fst (G : C ⥤ SSet.{u}) (c : C) :
    (SimplicialReplacementChosenHomotopyFiber.originalFiberIso G c).hom ≫
        pullback.fst (diagonalFunctor.map (projection G)) (oldPoint c) =
      diagonalInclusion G c := by
  simp only [SimplicialReplacementChosenHomotopyFiber.originalFiberIso,
    IsPullback.isoPullback_hom_fst]

private theorem originalFiberIso_snd (G : C ⥤ SSet.{u}) (c : C) :
    (SimplicialReplacementChosenHomotopyFiber.originalFiberIso G c).hom ≫
        pullback.snd (diagonalFunctor.map (projection G)) (oldPoint c) =
      zeroMap (G.obj c) ≫ pointIso.inv := by
  simp only [SimplicialReplacementChosenHomotopyFiber.originalFiberIso,
    IsPullback.isoPullback_hom_snd]

private theorem chosenComparison_fst (G : C ⥤ SSet.{u}) (c : C) :
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
        pullback.fst (r G) (relativeOldPoint G c) =
      diagonalInclusion G c ≫ f G := by
  have hf :
      DaggerNativeRelativeReedyBisimplicialFibres.imageComparison
          diagonalFunctor (A G)
            (SimplicialReplacementChosenHomotopyFiber.coherentPoint c) ≫
          pullback.fst (r G) (relativeOldPoint G c) =
        pullback.fst (diagonalFunctor.map (projection G)) (oldPoint c) ≫ f G := by
    dsimp only [DaggerNativeRelativeReedyBisimplicialFibres.imageComparison]
    exact DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst _ _ _ _ _ _ _ _
  change ((SimplicialReplacementChosenHomotopyFiber.originalFiberIso G c).hom ≫
      DaggerNativeRelativeReedyBisimplicialFibres.imageComparison
        diagonalFunctor (A G)
          (SimplicialReplacementChosenHomotopyFiber.coherentPoint c)) ≫
      pullback.fst (r G) (relativeOldPoint G c) = _
  rw [Category.assoc, hf, ← Category.assoc, originalFiberIso_fst]

private theorem chosenComparison_snd (G : C ⥤ SSet.{u}) (c : C) :
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
        pullback.snd (r G) (relativeOldPoint G c) =
      zeroMap (G.obj c) ≫ pointIso.inv := by
  have hs :
      DaggerNativeRelativeReedyBisimplicialFibres.imageComparison
          diagonalFunctor (A G)
            (SimplicialReplacementChosenHomotopyFiber.coherentPoint c) ≫
          pullback.snd (r G) (relativeOldPoint G c) =
        pullback.snd (diagonalFunctor.map (projection G)) (oldPoint c) := by
    dsimp only [DaggerNativeRelativeReedyBisimplicialFibres.imageComparison]
    exact DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd _ _ _ _ _ _ _ _
  change ((SimplicialReplacementChosenHomotopyFiber.originalFiberIso G c).hom ≫
      DaggerNativeRelativeReedyBisimplicialFibres.imageComparison
        diagonalFunctor (A G)
          (SimplicialReplacementChosenHomotopyFiber.coherentPoint c)) ≫
      pullback.snd (r G) (relativeOldPoint G c) = _
  rw [Category.assoc, hs, originalFiberIso_snd]

private theorem strict_comparison_triangle (G : C ⥤ SSet.{u}) (c : C) :
    (chosenFiberIso G c).hom ≫
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
          (diagonalProjection G) (r G) (f G) (g G) (square G)
          (b c) (d G c) rfl =
      SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
        pointChange G c := by
  dsimp only [pointChange]
  apply pullback.hom_ext
  · calc
      ((chosenFiberIso G c).hom ≫
          DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
            (diagonalProjection G) (r G) (f G) (g G) (square G)
            (b c) (d G c) rfl) ≫ pullback.fst (r G) (d G c) =
          ((chosenFiberIso G c).hom ≫
            pullback.fst (diagonalProjection G) (b c)) ≫ f G := by
            rw [Category.assoc,
              DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
              ← Category.assoc]
      _ = diagonalInclusion G c ≫ f G := by
        exact congrArg (fun m ↦ m ≫ f G)
          (diagonalInclusion_isPullback G c).isoPullback_hom_fst
      _ = (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
          pointChange G c) ≫ pullback.fst (r G) (d G c) := by
        dsimp only [pointChange]
        rw [Category.assoc, SSetWeakPullbackComparison.pointMap_fst]
        exact (chosenComparison_fst G c).symm
  · calc
      ((chosenFiberIso G c).hom ≫
          DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
            (diagonalProjection G) (r G) (f G) (g G) (square G)
            (b c) (d G c) rfl) ≫ pullback.snd (r G) (d G c) =
          (chosenFiberIso G c).hom ≫
            pullback.snd (diagonalProjection G) (b c) := by
            rw [Category.assoc,
              DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
      _ = zeroMap (G.obj c) :=
        (diagonalInclusion_isPullback G c).isoPullback_hom_snd
      _ = (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
          pointChange G c) ≫ pullback.snd (r G) (d G c) := by
        dsimp only [pointChange]
        rw [Category.assoc, SSetWeakPullbackComparison.pointMap_snd,
          ← Category.assoc, chosenComparison_snd]
        simp

variable (G : C ⥤ SSet.{u}) [∀ a, IsFibrant (G.obj a)]
variable (hG : ∀ ⦃a b : C⦄ (h : a ⟶ b), WeakEquivalence (G.map h))

include hG in
/-- The canonical value map to the chosen fiber at `chainPoint c` is weak. -/
theorem nerveValueToChosen_weak (c : C) :
    WeakEquivalence (nerveValueToChosen G c) := by
  haveI : Fibration (r G) :=
    SimplicialReplacementChosenHomotopyFiber.relative_diagonal_fibration G hG
  haveI : WeakEquivalence (f G) :=
    SimplicialReplacementChosenHomotopyFiber.total_diagonal_unit_weak G
  haveI : WeakEquivalence (g G) := by
    have : WeakEquivalence (diagonalFunctor.map (baseUnit (A G))) :=
      SimplicialReplacementChosenHomotopyFiber.base_diagonal_unit_weak G
    dsimp only [g]
    infer_instance
  haveI : WeakEquivalence pointIso.hom := by infer_instance
  haveI : WeakEquivalence (pointChange G c) :=
    SSetWeakPullbackComparison.pointMap_weak
      (r G) (relativeOldPoint G c) (d G c)
        pointIso.hom (point_factor G c)
  haveI : WeakEquivalence
      (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c) :=
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison_weak G c
  haveI : WeakEquivalence
      (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
        pointChange G c) := inferInstance
  let comparison := ChosenHomotopyFiberComparison.comparison
    (diagonalProjection G) (r G) (f G) (g G) (square G)
    (b c) (d G c) rfl
  haveI : WeakEquivalence comparison :=
    ChosenHomotopyFiberComparison.comparison_weak
      (diagonalProjection G) (r G) (f G) (g G) (square G)
      (b c) (d G c) rfl
  have htriangle : nerveValueToChosen G c ≫ comparison =
      SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c ≫
        pointChange G c := by
    unfold nerveValueToChosen
    rw [Category.assoc,
      ChosenHomotopyFiberTriangle.inclusion_comparison
        (diagonalProjection G) (r G) (f G) (g G) (square G)
        (b c) (d G c) rfl]
    exact strict_comparison_triangle G c
  exact weakEquivalence_of_postcomp_of_fac htriangle

#print axioms nerveValueToChosen
#print axioms nerveValueToChosen_weak

end

end DaggerModels.PartII.SimplicialReplacementNerveChosenFiber
