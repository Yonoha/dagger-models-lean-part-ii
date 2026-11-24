import OrdinaryWalkingCoherentObject
import OrdinarySegalCotensorPointEvaluation

/-!
# Evaluating an actual cotensor object at its original parameter vertex

The row-zero right unitor and point-parameter left unitor express the
same map from the original parameter vertex. This calibrates the full
parameter map extracted from a literal cotensor object with the checked
evaluation natural transformation, in the actual target space.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalCotensorObjectEvaluation

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinaryWalkingCoherentObject (objectMap)

noncomputable section

private theorem level_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (discrete.obj L) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPrecomp (discrete.map f) W).app q t) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv L W q.unop) t := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f W) q) t
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem vertex_tensor (K : SSet.{0})
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    (SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{0})).inv ≫
        v ▷ (Δ[0] : SSet.{0}) =
      v ≫ (SSet.stdSimplex.rightUnitor K).inv := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · change v.app q
        ((SSet.stdSimplex.isTerminalObj₀.from (Δ[0] : SSet.{0})).app q x) =
      v.app q x
    have h : SSet.stdSimplex.isTerminalObj₀.from (Δ[0] : SSet.{0}) =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
    rfl
  · change x = (SSet.stdSimplex.isTerminalObj₀.from K).app q (v.app q x)
    have h : v ≫ SSet.stdSimplex.isTerminalObj₀.from K =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have hx := congrFun (NatTrans.congr_app h q) x
    exact hx.symm

private theorem evaluation_zero (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    (OrdinarySegalCotensorPointEvaluation.evaluation K W v).app (op ⦋0⦌) =
      (OrdinarySegalCotensorZeroIso.mappingIso K W).hom ≫
        diagramMappingPrecomp (discrete.map v) W ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom := by
  change diagramMappingPrecomp (discrete.map (v ▷ (Δ[0] : SSet.{0}))) W ≫
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.leftUnitor (Δ[0] : SSet.{0})).inv) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom =
    diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W ≫
      diagramMappingPrecomp (discrete.map v) W ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 0).hom
  simp only [← Category.assoc]
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp, ← discrete.map_comp, vertex_tensor]

/-- Evaluating the complete parameter map at a specified original
vertex gives the literal checked cotensor evaluation of the object. -/
theorem objectMap_evaluation (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K)
    (z : ((cotensor K W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (v ≫ objectMap K W z) =
      ((OrdinarySegalCotensorPointEvaluation.evaluation K W v).app
        (op ⦋0⦌)).app (op ⦋0⦌) z := by
  have h := congrFun
    (NatTrans.congr_app (evaluation_zero K W v) (op ⦋0⦌)) z
  change ((OrdinarySegalCotensorPointEvaluation.evaluation K W v).app
      (op ⦋0⦌)).app (op ⦋0⦌) z =
    SSet.yonedaEquiv
      ((OrdinaryDiscreteMapping.levelEquiv (Δ[0] : SSet.{0}) W ⦋0⦌)
        ((diagramMappingPrecomp (discrete.map v) W).app (op ⦋0⦌)
          ((OrdinarySegalCotensorZeroIso.mappingIso K W).hom.app (op ⦋0⦌) z))) at h
  rw [level_pre] at h
  exact h.symm

#print axioms objectMap_evaluation

end
end DaggerModels.PartII.OrdinarySegalCotensorObjectEvaluation
