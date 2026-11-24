import OrdinaryZeroCoskeletonVertexTuple
import OrdinaryRelativeRowWeak
import OrdinaryGroupoidSimplexTransitionEndpointSquare

/-!
# Every ordered-vertex square of an ordinary Segal map

The zero-coskeleton relative target has, in every horizontal dimension,
the literal pullback of the target all-vertex map along the source vertex
map. The comparison retains the original `n`-simplex and its full ordered
vertex tuple. Weakness follows from the already proved relative row theorem.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexSquareComparison

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryZeroCoskeleton (coskeleton vertices targetOverZero relativeComparison)
open OrdinarySegalVertexTupleFibres (vertexMap)
open OrdinaryZeroCoskeletonVertexTuple
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The zero-coskeleton row and the complete ordered-vertex mapping space
are the same finite product, with its actual source object. -/
def coskeletonMappingIso (W : Space) (n : ℕ) :
    (coskeleton.obj (W.obj zero)).obj (op ⦋n⦌) ≅
      diagramMappingSpace (discrete.obj
        (OrdinarySegalVertexTupleFibres.vertices n)) W :=
  coskeletonPiIso (W.obj zero) n ≪≫ (mappingVertexPiIso W n).symm

theorem coskeletonMappingIso_vertices (W : Space) (n : ℕ) :
    (vertices W).app (op ⦋n⦌) ≫ (coskeletonMappingIso W n).hom =
      vertexMap W n := by
  dsimp only [coskeletonMappingIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, vertices_vertexMap_square W n, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem coskeletonMappingIso_natural {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    (coskeleton.map (f.app zero)).app (op ⦋n⦌) ≫
        (coskeletonMappingIso Z n).hom =
      (coskeletonMappingIso W n).hom ≫
        diagramMappingPostcomp
          (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f := by
  apply (cancel_mono (mappingVertexPiIso Z n).hom).1
  dsimp only [coskeletonMappingIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [mappingVertexPiIso_natural f n]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact coskeletonPiIso_natural (f.app zero) n

private theorem vertexMap_natural {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    f.app (op ⦋n⦌) ≫ vertexMap Z n =
      vertexMap W n ≫
        diagramMappingPostcomp
          (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f := by
  have hunit : f ≫ vertices Z =
      vertices W ≫ coskeleton.map (f.app zero) :=
    (evaluationAdjunctionLeft SSet.{0} zero).unit.naturality f
  have hn := NatTrans.congr_app hunit (op ⦋n⦌)
  calc
    f.app (op ⦋n⦌) ≫ vertexMap Z n =
        f.app (op ⦋n⦌) ≫
          (vertices Z).app (op ⦋n⦌) ≫
          (coskeletonMappingIso Z n).hom := by
            rw [coskeletonMappingIso_vertices]
    _ = (vertices W).app (op ⦋n⦌) ≫
          (coskeleton.map (f.app zero)).app (op ⦋n⦌) ≫
          (coskeletonMappingIso Z n).hom := by
            rw [← Category.assoc]
            exact congrArg (fun g ↦ g ≫ (coskeletonMappingIso Z n).hom) hn
    _ = (vertices W).app (op ⦋n⦌) ≫
          (coskeletonMappingIso W n).hom ≫
          diagramMappingPostcomp
            (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f := by
            simpa only [Category.assoc] using congrArg
              (fun m ↦ (vertices W).app (op ⦋n⦌) ≫ m)
              (coskeletonMappingIso_natural f n)
    _ = vertexMap W n ≫
          diagramMappingPostcomp
            (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f := by
            rw [← Category.assoc, coskeletonMappingIso_vertices]

/-- The literal comparison of all ordered vertices of the original map. -/
def vertexComparison {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    W.obj (op ⦋n⦌) ⟶
      pullback (vertexMap Z n)
        (diagramMappingPostcomp
          (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f) :=
  pullback.lift (f.app (op ⦋n⦌)) (vertexMap W n)
    (vertexMap_natural f n)

private theorem relativeVertexPullback {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    IsPullback
      ((pullback.fst (vertices Z) (coskeleton.map (f.app zero))).app (op ⦋n⦌))
      ((pullback.snd (vertices Z) (coskeleton.map (f.app zero))).app (op ⦋n⦌) ≫
        (coskeletonMappingIso W n).hom)
      (vertexMap Z n)
      (diagramMappingPostcomp
        (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f) := by
  let k := coskeleton.map (f.app zero)
  let e := (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋n⦌)
  have h := (IsPullback.of_hasPullback (vertices Z) k).map e
  have hb : IsPullback (e.map k) (coskeletonMappingIso W n).hom
      (coskeletonMappingIso Z n).hom
      (diagramMappingPostcomp
        (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f) :=
    IsPullback.of_vert_isIso ⟨coskeletonMappingIso_natural f n⟩
  have hv : e.map (vertices Z) ≫ (coskeletonMappingIso Z n).hom =
      vertexMap Z n := coskeletonMappingIso_vertices Z n
  rw [← hv]
  exact h.paste_vert hb

/-- Rowwise pullback identification retaining the exact original simplex
and the exact complete ordered tuple. -/
def relativeVertexIso {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    (targetOverZero f).obj (op ⦋n⦌) ≅
      pullback (vertexMap Z n)
        (diagramMappingPostcomp
          (discrete.obj (OrdinarySegalVertexTupleFibres.vertices n)) f) :=
  (relativeVertexPullback f n).isoPullback

/-- The relative comparison has the same two coordinates as the literal
all-vertex comparison. -/
theorem relativeComparison_vertexComparison {W Z : Space}
    (f : W ⟶ Z) (n : ℕ) :
    (relativeComparison f).app (op ⦋n⦌) ≫ (relativeVertexIso f n).hom =
      vertexComparison f n := by
  let k := coskeleton.map (f.app zero)
  let h := relativeVertexPullback f n
  have hrT : (relativeComparison f).app (op ⦋n⦌) ≫
      ((pullback.fst (vertices Z) k).app (op ⦋n⦌)) = f.app (op ⦋n⦌) := by
    change ((relativeComparison f ≫ pullback.fst (vertices Z) k).app (op ⦋n⦌)) = _
    exact congrArg (fun a : W ⟶ Z ↦ a.app (op ⦋n⦌)) (pullback.lift_fst _ _ _)
  have hrS : (relativeComparison f).app (op ⦋n⦌) ≫
      ((pullback.snd (vertices Z) k).app (op ⦋n⦌) ≫
        (coskeletonMappingIso W n).hom) = vertexMap W n := by
    rw [← Category.assoc]
    change ((relativeComparison f ≫ pullback.snd (vertices Z) k).app
      (op ⦋n⦌)) ≫ _ = _
    have hu : relativeComparison f ≫ pullback.snd (vertices Z) k = vertices W :=
      pullback.lift_snd _ _ _
    exact (congrArg (fun m : W ⟶ coskeleton.obj (W.obj zero) ↦
      m.app (op ⦋n⦌) ≫ (coskeletonMappingIso W n).hom) hu).trans
        (coskeletonMappingIso_vertices W n)
  change (relativeComparison f).app (op ⦋n⦌) ≫ h.isoPullback.hom = vertexComparison f n
  apply pullback.hom_ext
  · rw [Category.assoc, h.isoPullback_hom_fst, vertexComparison, pullback.lift_fst]
    exact hrT
  · rw [Category.assoc, h.isoPullback_hom_snd, vertexComparison, pullback.lift_snd]
    exact hrS

/-- Weakness on every original ordered mapping fiber gives weakness of
the actual all-vertex square in every finite dimension. -/
theorem vertexComparison_weak {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) (hW : OrdinaryCSSConditions.segalCondition W)
    (hZ : OrdinaryCSSConditions.segalCondition Z)
    (hf : ∀ x y : (W.obj zero).obj (op ⦋0⦌), WeakEquivalence (mappingMap f x y))
    (n : ℕ) : WeakEquivalence (vertexComparison f n) := by
  have hrel := OrdinaryRelativeRowWeak.relative_weak f hW hZ hf
  have hrows := (weakEquivalence_iff _).mp hrel
  rw [InjectiveKanDiagram.model_weakEquivalences] at hrows
  have hr : WeakEquivalence ((relativeComparison f).app (op ⦋n⦌)) :=
    (weakEquivalence_iff _).mpr (hrows (op ⦋n⦌))
  have : WeakEquivalence
      ((relativeComparison f).app (op ⦋n⦌) ≫ (relativeVertexIso f n).hom) :=
    inferInstance
  rw [relativeComparison_vertexComparison] at this
  exact this

/-- Every original groupoid-simplex transition is homotopy cartesian on
its full ordered vertex tuple in every horizontal dimension. -/
theorem transition_vertexComparison_weak {a b : SimplexCategory} (θ : a ⟶ b)
    (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ) :
    WeakEquivalence (vertexComparison
      (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W) n) := by
  let X := OrdinarySegalHorizontalCotensor.cotensor
    (GroupoidSimplex.parameter.obj b) W
  let Y := OrdinarySegalHorizontalCotensor.cotensor
    (GroupoidSimplex.parameter.obj a) W
  have : IsFibrant X :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have : IsFibrant Y :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  exact vertexComparison_weak _
    (OrdinarySegalCotensorSegal.cotensor_segalCondition _ W hSegal)
    (OrdinarySegalCotensorSegal.cotensor_segalCondition _ W hSegal)
    (OrdinaryGroupoidSimplexTransitionFullyFaithful.mappingMap_weak θ W hSegal) n

#print axioms vertexComparison
#print axioms relativeVertexIso
#print axioms vertexComparison_weak
#print axioms transition_vertexComparison_weak

end

end DaggerModels.PartII.OrdinaryAllVertexSquareComparison
