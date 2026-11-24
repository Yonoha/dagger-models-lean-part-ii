import DaggerModelsPartII.JTRealizationGenerators
import DaggerModelsPartII.JTReversalInput
import DaggerModelsPartII.GroupoidSimplexReversal

/-!
# Fixed vertices of the JT realization reversal

The horizontal coend relation identifies the reversed vertex generator with
the original vertex generator. Groupoid inversion fixes vertices in the
vertical parameter.
-/

set_option autoImplicit false

open CategoryTheory Opposite MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTRealizationVertices

open OrdinaryJTRealization JTRealizationGenerators JTReversalInput
  GroupoidSimplex GroupoidSimplexReversal

noncomputable section

/-- The horizontal coefficient action of reversal on the literal JT input. -/
def horizontalReversalCoefficient
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (m k : SimplexCategory)
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (ordinaryInput.obj W).obj (op (m, k)) :=
  ((W.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m)).op).app
    (op k)) w

private theorem horizontal_reversal_vertex
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (m k : SimplexCategory)
    (a : ⦋0⦌ ⟶ m)
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (ordinaryInput.obj W).map
        (show (⦋0⦌, k) ⟶ (m, k) from (SimplexCategory.rev.map a, 𝟙 k)).op
        (horizontalReversalCoefficient W m k w) =
      (ordinaryInput.obj W).map
        (show (⦋0⦌, k) ⟶ (m, k) from (a, 𝟙 k)).op w := by
  have hrev : ReverseSimplex.inclusion.map (SimplexCategory.rev.map a) ≫
      ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m) =
      ReverseSimplex.inclusion.map a := by
    have h := ReverseSimplex.reversal_naturality (SimplexCategory.rev.map a)
    have hz : ReverseSimplex.reversal
        (ReverseSimplex.inclusion.obj (⦋0⦌ : SimplexCategory)) =
        𝟙 (ReverseSimplex.inclusion.obj (⦋0⦌ : SimplexCategory)) :=
      ReverseSimplex.reversal_zero
    simpa only [SimplexCategory.rev_obj, SimplexCategory.rev_map_rev_map,
      hz, Category.id_comp] using h
  have hnat : W.map (ReverseSimplex.reversal
        (ReverseSimplex.inclusion.obj m)).op ≫
      W.map (ReverseSimplex.inclusion.map (SimplexCategory.rev.map a)).op =
      W.map (ReverseSimplex.inclusion.map a).op := by
    rw [← W.map_comp, ← op_comp, hrev]
  have hpoint := congrArg (fun η : W.obj (op (ReverseSimplex.inclusion.obj m)) ⟶
      W.obj (op (ReverseSimplex.inclusion.obj (⦋0⦌ : SimplexCategory))) ↦
        η.app (op k) w) hnat
  change ((W.map (ReverseSimplex.inclusion.map
      (SimplexCategory.rev.map a)).op).app (op k))
        (((W.map (ReverseSimplex.reversal
          (ReverseSimplex.inclusion.obj m)).op).app (op k)) w) =
      ((W.map (ReverseSimplex.inclusion.map a).op).app (op k)) w at hpoint
  simpa [JTReversalInput.ordinaryInput, Functor.uncurry,
    horizontalReversalCoefficient] using hpoint

/-- At degree zero, groupoid-path reversal fixes every parameter vertex. -/
theorem parameter_reversal_vertex (k : SimplexCategory)
    (ξ : (parameter.obj k).obj (op ⦋0⦌)) :
    SSet.opObjEquiv ((daggerParameter.obj k).dagger.app (op ⦋0⦌) ξ) = ξ :=
  (daggerParameter.obj k).fixedVertices ξ

private theorem reversed_generator_vertex_plain
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (m k : SimplexCategory)
    (a : ⦋0⦌ ⟶ m)
    (ξ : (parameter.obj k).obj (op ⦋0⦌))
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (generator (ordinaryInput.obj W) (m, k)
      (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a), ξ) =
    (generator (ordinaryInput.obj W) (m, k) w).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm a, ξ) := by
  let f : (⦋0⦌, k) ⟶ (m, k) := (a, 𝟙 k)
  let fr : (⦋0⦌, k) ⟶ (m, k) := (SimplexCategory.rev.map a, 𝟙 k)
  have hleft := generator_relation (ordinaryInput.obj W) fr
    (horizontalReversalCoefficient W m k w)
  have hright := generator_relation (ordinaryInput.obj W) f w
  have hw := horizontal_reversal_vertex W m k a w
  let u : (tFunctor.obj (⦋0⦌, k)).obj (op ⦋0⦌) :=
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌), ξ)
  have hfr : (tFunctor.map fr).app (op ⦋0⦌) u =
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a), ξ) := by
    change ((SSet.stdSimplex.map (SimplexCategory.rev.map a) ⊗ₘ
      parameter.map (𝟙 k)).app (op ⦋0⦌)) u = _
    change ((SSet.stdSimplex.map (SimplexCategory.rev.map a)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)),
      (parameter.map (𝟙 k)).app (op ⦋0⦌) ξ) = _
    rw [parameter.map_id]
    change (SSet.stdSimplex.objEquiv.symm
      (𝟙 ⦋0⦌ ≫ SimplexCategory.rev.map a), ξ) = _
    simp
    exact congrArg SSet.stdSimplex.objEquiv.symm
      (Category.id_comp (SimplexCategory.rev.map a))
  have hf : (tFunctor.map f).app (op ⦋0⦌) u =
      (SSet.stdSimplex.objEquiv.symm a, ξ) := by
    change ((SSet.stdSimplex.map a ⊗ₘ parameter.map (𝟙 k)).app (op ⦋0⦌)) u = _
    change ((SSet.stdSimplex.map a).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)),
      (parameter.map (𝟙 k)).app (op ⦋0⦌) ξ) = _
    rw [parameter.map_id]
    change (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌ ≫ a), ξ) = _
    simp
    exact Category.id_comp a
  have hleftpoint := congrArg
    (fun h : tFunctor.obj (⦋0⦌, k) ⟶ realization.obj (ordinaryInput.obj W) ↦
      h.app (op ⦋0⦌) u) hleft
  have hrightpoint := congrArg
    (fun h : tFunctor.obj (⦋0⦌, k) ⟶ realization.obj (ordinaryInput.obj W) ↦
      h.app (op ⦋0⦌) u) hright
  have hleftvalue :
      (generator (ordinaryInput.obj W) (m, k)
        (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
          (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a), ξ) =
        (generator (ordinaryInput.obj W) (⦋0⦌, k)
          ((ordinaryInput.obj W).map fr.op
            (horizontalReversalCoefficient W m k w))).app (op ⦋0⦌) u := by
    change (generator (ordinaryInput.obj W) (m, k)
      (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
        ((tFunctor.map fr).app (op ⦋0⦌) u) = _ at hleftpoint
    rw [hfr] at hleftpoint
    exact hleftpoint
  have hrightvalue :
      (generator (ordinaryInput.obj W) (m, k) w).app (op ⦋0⦌)
          (SSet.stdSimplex.objEquiv.symm a, ξ) =
        (generator (ordinaryInput.obj W) (⦋0⦌, k)
          ((ordinaryInput.obj W).map f.op w)).app (op ⦋0⦌) u := by
    change (generator (ordinaryInput.obj W) (m, k) w).app (op ⦋0⦌)
      ((tFunctor.map f).app (op ⦋0⦌) u) = _ at hrightpoint
    rw [hf] at hrightpoint
    exact hrightpoint
  calc
    _ = (generator (ordinaryInput.obj W) (⦋0⦌, k)
          ((ordinaryInput.obj W).map fr.op
            (horizontalReversalCoefficient W m k w))).app (op ⦋0⦌) u := by
          exact hleftvalue
    _ = (generator (ordinaryInput.obj W) (⦋0⦌, k)
          ((ordinaryInput.obj W).map f.op w)).app (op ⦋0⦌) u := by
          rw [hw]
    _ = _ := by
          exact hrightvalue.symm

/-- The manuscript's fixed-vertex coend calculation for every generator. -/
theorem reversed_generator_vertex
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (m k : SimplexCategory)
    (a : ⦋0⦌ ⟶ m)
    (ξ : (parameter.obj k).obj (op ⦋0⦌))
    (w : (ordinaryInput.obj W).obj (op (m, k))) :
    (generator (ordinaryInput.obj W) (m, k)
      (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a),
        SSet.opObjEquiv ((daggerParameter.obj k).dagger.app (op ⦋0⦌) ξ)) =
    (generator (ordinaryInput.obj W) (m, k) w).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm a, ξ) := by
  have hξ := parameter_reversal_vertex k ξ
  calc
    _ = (generator (ordinaryInput.obj W) (m, k)
      (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a), ξ) := by
          exact congrArg (fun ζ => (generator (ordinaryInput.obj W) (m, k)
            (horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
              (SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map a), ζ)) hξ
    _ = _ := reversed_generator_vertex_plain W m k a ξ w

end

end DaggerModels.PartII.JTRealizationVertices
