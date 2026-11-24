import OrdinaryAllVertexStrictFibreMap
import OrdinaryRelativeSegalRecognitionReduction
import DaggerModelsPartII.DiagonalRecognition
import NativeFinitePiWeak

/-!
# All-vertex comparisons after an injective rowwise replacement

The corrected precompletion unit and the actual replacement map are retained.
Weakness of the canonical unit map into each chosen tuple fiber is an explicit
hypothesis. No Segal condition on the precompletion or its replacement is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexReplacementComparison

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinaryAllVertexSquareComparison (vertexComparison)
open OrdinaryAllVertexStrictFibreMap (tupleMap)
open ChosenHomotopyFiberTriangle (inclusion)
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks (mapOver mapOver_fst)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev P (W : Space) :=
  OrdinarySegalVerticalPrecompletion.precompletion W

/-- Covariant target composition for the exact diagram mapping space. -/
private theorem postcomp_comp {W X Y : Space}
    (A : Space) (f : W ⟶ X) (g : X ⟶ Y) :
    diagramMappingPostcomp A (f ≫ g) =
      diagramMappingPostcomp A f ≫ diagramMappingPostcomp A g := by
  change (diagramMappingTarget A).map (f ≫ g) =
    (diagramMappingTarget A).map f ≫ (diagramMappingTarget A).map g
  exact (diagramMappingTarget A).map_comp f g

/-- The complete ordered-vertex base of a rowwise weak map is weak, even
when the domain has no injective fibrancy instance. -/
theorem vertexBaseMap_weak_of_rowZero_weak {X Y : Space}
    (i : X ⟶ Y) (n : ℕ)
    (hi : WeakEquivalence (i.app (op ⦋0⦌))) :
    WeakEquivalence (diagramMappingPostcomp (discrete.obj (vertices n)) i) := by
  have hpi : WeakEquivalence
      (DaggerNativeFinitePiWeak.piMap
        (fun _ : Fin (n + 1) ↦ i.app (op ⦋0⦌))) :=
    DaggerNativeFinitePiWeak.piMap_weak _ (fun _ ↦ hi)
  letI := hpi
  have hcomp : WeakEquivalence
      ((OrdinaryZeroCoskeletonVertexTuple.mappingVertexPiIso X n).hom ≫
        DaggerNativeFinitePiWeak.piMap
          (fun _ : Fin (n + 1) ↦ i.app (op ⦋0⦌))) := inferInstance
  letI := hcomp
  exact weakEquivalence_of_postcomp_of_fac
    (OrdinaryZeroCoskeletonVertexTuple.mappingVertexPiIso_natural i n)

/-- The literal full-tuple strict-fiber action composes through the actual
intermediate tuple point. -/
private theorem tupleMap_comp {W X Y : Space}
    (f : W ⟶ X) (g : X ⟶ Y) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶
      diagramMappingSpace (discrete.obj (vertices n)) W) :
    tupleMap f n b ≫
        tupleMap g n
          (b ≫ diagramMappingPostcomp (discrete.obj (vertices n)) f) =
      tupleMap (f ≫ g) n b := by
  change DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (vertexMap W n) (vertexMap X n) (f.app (op ⦋n⦌))
        (diagramMappingPostcomp (discrete.obj (vertices n)) f) _ _ _ _ ≫
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        (vertexMap X n) (vertexMap Y n) (g.app (op ⦋n⦌))
          (diagramMappingPostcomp (discrete.obj (vertices n)) g) _ _ _ _ =
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (vertexMap W n) (vertexMap Y n)
        (f.app (op ⦋n⦌) ≫ g.app (op ⦋n⦌))
        (diagramMappingPostcomp (discrete.obj (vertices n)) f ≫
          diagramMappingPostcomp (discrete.obj (vertices n)) g) _ _ _ _
  exact ChosenHomotopyFiberFunctor.fibreMap_comp _ _ _ _ _ _ _ _ _
    _ _ _ _ _

/-- The chosen map of the actual replacement square is weak on each tuple,
using only its rowwise weak property. -/
theorem replacementChosenMap_weak {X R : Space}
    (i : X ⟶ R) (n : ℕ)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (b : (Δ[0] : SSet.{0}) ⟶
      diagramMappingSpace (discrete.obj (vertices n)) X) :
    WeakEquivalence
      (ChosenHomotopyFiberFunctor.chosenMap (vertexMap X n) (vertexMap R n)
        (i.app (op ⦋n⦌))
        (diagramMappingPostcomp (discrete.obj (vertices n)) i)
        ((OrdinarySegalAllVertexResolution.vertexRestriction n).naturality i).symm
        b (b ≫ diagramMappingPostcomp (discrete.obj (vertices n)) i) rfl) := by
  letI : WeakEquivalence (i.app (op ⦋n⦌)) := hi (op ⦋n⦌)
  letI : WeakEquivalence
      (diagramMappingPostcomp (discrete.obj (vertices n)) i) :=
    vertexBaseMap_weak_of_rowZero_weak i n (hi (op ⦋0⦌))
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

/-- The derived tuple hypothesis for the corrected unit passes through the
rowwise weak replacement to the literal strict fiber of the replacement. -/
theorem replacement_tupleMap_weak
    (W : Space) [IsFibrant W] (R : Space) [IsFibrant R]
    (i : P W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (hDerived : ∀ (n : ℕ)
      (b : (Δ[0] : SSet.{0}) ⟶
        diagramMappingSpace (discrete.obj (vertices n)) W),
      WeakEquivalence
        (tupleMap (OrdinarySegalVerticalPrecompletion.unit W) n b ≫
          inclusion (vertexMap (P W) n)
            (b ≫ diagramMappingPostcomp (discrete.obj (vertices n))
              (OrdinarySegalVerticalPrecompletion.unit W))))
    (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶
      diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence
      (tupleMap (OrdinarySegalVerticalPrecompletion.unit W ≫ i) n b) := by
  let u := OrdinarySegalVerticalPrecompletion.unit W
  let bP := b ≫ diagramMappingPostcomp (discrete.obj (vertices n)) u
  let bR := bP ≫ diagramMappingPostcomp (discrete.obj (vertices n)) i
  let c := ChosenHomotopyFiberFunctor.chosenMap
    (vertexMap (P W) n) (vertexMap R n)
    (i.app (op ⦋n⦌))
    (diagramMappingPostcomp (discrete.obj (vertices n)) i)
    ((OrdinarySegalAllVertexResolution.vertexRestriction n).naturality i).symm
    bP bR rfl
  have hc : WeakEquivalence c := replacementChosenMap_weak i n hi bP
  have hu : WeakEquivalence
      (tupleMap u n b ≫ inclusion (vertexMap (P W) n) bP) := hDerived n b
  have htarget : Fibration (vertexMap R n) :=
    OrdinarySegalVertexTupleFibres.vertexMap_fibration R n
  letI := htarget
  have hr : WeakEquivalence (inclusion (vertexMap R n) bR) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  have hnat : inclusion (vertexMap (P W) n) bP ≫ c =
      tupleMap i n bP ≫ inclusion (vertexMap R n) bR :=
    ChosenHomotopyFiberFunctor.inclusion_chosenMap _ _ _ _ _ _ _ _
  have hcomp : tupleMap u n b ≫ tupleMap i n bP = tupleMap (u ≫ i) n b :=
    tupleMap_comp u i n b
  have hweak : WeakEquivalence
      (tupleMap (u ≫ i) n b ≫ inclusion (vertexMap R n) bR) := by
    have heq : (tupleMap u n b ≫ tupleMap i n bP) ≫
        inclusion (vertexMap R n) bR =
        (tupleMap u n b ≫ inclusion (vertexMap (P W) n) bP) ≫ c := by
      calc
        _ = tupleMap u n b ≫
            (tupleMap i n bP ≫ inclusion (vertexMap R n) bR) :=
              Category.assoc _ _ _
        _ = tupleMap u n b ≫
            (inclusion (vertexMap (P W) n) bP ≫ c) := by rw [← hnat]
        _ = _ := (Category.assoc _ _ _).symm
    rw [← hcomp, heq]
    letI := hu
    letI := hc
    infer_instance
  letI := hweak
  letI := hr
  exact weakEquivalence_of_postcomp
    (tupleMap (u ≫ i) n b) (inclusion (vertexMap R n) bR)

/-- Weakness of all literal tuple fibers recognizes the all-vertex square
for the source and target vertex fibrations, with no target Segal premise. -/
theorem vertexComparison_weak_of_tupleMaps {W R : Space}
    [IsFibrant W] [IsFibrant R] (f : W ⟶ R) (n : ℕ)
    (hf : ∀ b : (Δ[0] : SSet.{0}) ⟶
      diagramMappingSpace (discrete.obj (vertices n)) W,
      WeakEquivalence (tupleMap f n b)) :
    WeakEquivalence (vertexComparison f n) := by
  let p := vertexMap W n
  let q := vertexMap R n
  let g := diagramMappingPostcomp (discrete.obj (vertices n)) f
  let k := pullback.snd q g
  let t := pullback.fst q g
  let a := vertexComparison f n
  have ha : a ≫ k = p := by
    dsimp only [a, k, p]
    unfold vertexComparison
    exact pullback.lift_snd _ _ _
  have : Fibration p := OrdinarySegalVertexTupleFibres.vertexMap_fibration W n
  have : Fibration q := OrdinarySegalVertexTupleFibres.vertexMap_fibration R n
  have : Fibration k := inferInstance
  apply DaggerNativeFibrewiseWeakRecognition.weak_of_vertex_base_changes p k a ha
  intro b
  let v := mapOver p k a ha b
  have sq : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b)
      q (b ≫ g) := by
    simpa only [k, t] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := sq.isoPullback
  have hcal : v ≫ e.hom = tupleMap f n b := by
    apply pullback.hom_ext
    · rw [Category.assoc, sq.isoPullback_hom_fst, ← Category.assoc,
        mapOver_fst, Category.assoc]
      have hat : a ≫ t = f.app (op ⦋n⦌) := by
        dsimp only [a, t]
        unfold vertexComparison
        exact pullback.lift_fst _ _ _
      rw [hat]
      exact (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst
        (vertexMap W n) (vertexMap R n) (f.app (op ⦋n⦌)) g
        ((OrdinarySegalAllVertexResolution.vertexRestriction n).naturality f).symm
        b (b ≫ g) rfl).symm
    · rw [Category.assoc, sq.isoPullback_hom_snd]
      dsimp only [v, mapOver]
      rw [pullback.lift_snd]
      exact (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd
        (vertexMap W n) (vertexMap R n) (f.app (op ⦋n⦌)) g
        ((OrdinarySegalAllVertexResolution.vertexRestriction n).naturality f).symm
        b (b ≫ g) rfl).symm
  have : WeakEquivalence e.hom := inferInstance
  have : WeakEquivalence (v ≫ e.hom) := by rw [hcal]; exact hf b
  exact weakEquivalence_of_postcomp v e.hom

/-- Conditional all-vertex comparison for the actual corrected unit followed
by the specified rowwise weak replacement. -/
theorem replacement_vertexComparison_weak
    (W : Space) [IsFibrant W] (R : Space) [IsFibrant R]
    (i : P W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (hDerived : ∀ (n : ℕ)
      (b : (Δ[0] : SSet.{0}) ⟶
        diagramMappingSpace (discrete.obj (vertices n)) W),
      WeakEquivalence
        (tupleMap (OrdinarySegalVerticalPrecompletion.unit W) n b ≫
          inclusion (vertexMap (P W) n)
            (b ≫ diagramMappingPostcomp (discrete.obj (vertices n))
              (OrdinarySegalVerticalPrecompletion.unit W))))
    (n : ℕ) :
    WeakEquivalence
      (vertexComparison (OrdinarySegalVerticalPrecompletion.unit W ≫ i) n) := by
  apply vertexComparison_weak_of_tupleMaps _ n
  intro b
  exact replacement_tupleMap_weak W R i hi hDerived n b

#print axioms vertexBaseMap_weak_of_rowZero_weak
#print axioms replacementChosenMap_weak
#print axioms replacement_tupleMap_weak
#print axioms vertexComparison_weak_of_tupleMaps
#print axioms replacement_vertexComparison_weak

end

end DaggerModels.PartII.OrdinaryAllVertexReplacementComparison
