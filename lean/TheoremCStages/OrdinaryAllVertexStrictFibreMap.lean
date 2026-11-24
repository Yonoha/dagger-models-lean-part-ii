import OrdinarySegalAllVertexUnitFibres
import OrdinarySegalAllVertexResolution
import NativeSSetFibrationSquareFibreWeak

/-!
# Direct strict fiber maps of the original complete vertex square

A weak comparison into the actual square pullback gives weakness on the direct
strict fibers over any point object. The application uses every ordered vertex
of the original constant section, with the original tuple point and its image.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexStrictFibreMap

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open DaggerNativeSSetFibrationSquareFibreWeak (fibreMap)
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks (mapOver)

noncomputable section

/-- A weak square comparison between fibrations preserves its direct strict fibers. -/
theorem fibreMap_weak_of_comparison_weak {X Y B D K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)
    [Fibration p] [Fibration q]
    (hc : WeakEquivalence (pullback.lift f p h.symm)) :
    WeakEquivalence (fibreMap p q f g h b d hb) := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  let a : X ⟶ pullback q g := pullback.lift f p h.symm
  have ha : a ≫ k = p := by simp only [a, k, pullback.lift_snd]
  have hat : a ≫ t = f := by simp only [a, t, pullback.lift_fst]
  have : WeakEquivalence a := hc
  have : Fibration k := inferInstance
  let u := mapOver p k a ha b
  have : WeakEquivalence u :=
    DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_weakEquivalence p k a ha b
  have square : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := square.isoPullback
  have he : u ≫ e.hom = fibreMap p q f g h b d hb := by
    apply pullback.hom_ext
    · rw [Category.assoc, square.isoPullback_hom_fst, ← Category.assoc]
      rw [DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst,
        Category.assoc, hat, DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst]
    · rw [Category.assoc, square.isoPullback_hom_snd,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
      simp only [u, mapOver, pullback.lift_snd]
  rw [← he]
  infer_instance

/-- The actual direct full-tuple fiber action of any original target map. -/
def tupleMap {W Z : Space} (f : W ⟶ Z) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    pullback (vertexMap W n) b ⟶
      pullback (vertexMap Z n)
        (b ≫ diagramMappingPostcomp (discrete.obj (vertices n)) f) :=
  fibreMap (vertexMap W n) (vertexMap Z n) (f.app (op ⦋n⦌))
    (diagramMappingPostcomp (discrete.obj (vertices n)) f)
    ((OrdinarySegalAllVertexResolution.vertexRestriction n).naturality f).symm
    b (b ≫ diagramMappingPostcomp (discrete.obj (vertices n)) f) rfl

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The weak original all-vertex square gives a weak direct full-tuple fiber map. -/
theorem tupleMap_weak_of_vertexComparison {W Z : Space}
    [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W)
    (hc : WeakEquivalence (OrdinaryAllVertexSquareComparison.vertexComparison f n)) :
    WeakEquivalence (tupleMap f n b) := by
  have : Fibration (vertexMap W n) :=
    OrdinarySegalVertexTupleFibres.vertexMap_fibration W n
  have : Fibration (vertexMap Z n) :=
    OrdinarySegalVertexTupleFibres.vertexMap_fibration Z n
  unfold tupleMap
  apply fibreMap_weak_of_comparison_weak
  exact hc

/-- Every original constant-section tuple map is weak, with its actual tuple retained. -/
theorem constantSection_tupleMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (q : SimplexCategory) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence
      (tupleMap (OrdinarySegalHorizontalCotensorPoint.constantSection
        (GroupoidSimplex.parameter.obj q) W) n b) := by
  have : IsFibrant
      (OrdinarySegalHorizontalCotensor.cotensor (GroupoidSimplex.parameter.obj q) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  exact tupleMap_weak_of_vertexComparison _ n b
    (OrdinarySegalAllVertexUnitFibres.constantSection_vertexComparison_weak W hSegal q n)

#print axioms fibreMap_weak_of_comparison_weak
#print axioms tupleMap_weak_of_vertexComparison
#print axioms constantSection_tupleMap_weak

end

end DaggerModels.PartII.OrdinaryAllVertexStrictFibreMap
