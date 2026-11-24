import OrdinaryZeroCoskeletonMapping
import OrdinarySegalCoherentArrowImage
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import DaggerModelsPartII.JTParameterVertexKan

/-!
# Coherent walking arrows over the actual zero coskeleton

The original free-groupoid edge unit has exactly the same two vertices as
the standard one-simplex. Its restriction on mapping spaces into the
ordinary zero coskeleton is therefore an isomorphism. The resulting square
for a pullback over the source zero row is strictly Cartesian.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryCoherentZeroCoskeleton

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryZeroCoskeleton

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev zero : J := op ⦋0⦌
private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit : (Δ[1] : SSet.{0}) ⟶ E :=
  JTCylinderCEComparison.simplexUnit.app ⦋1⦌
private abbrev A := discrete.obj E
private abbrev B := discrete.obj (Δ[1] : SSet.{0})
private abbrev F := diagramMappingTarget A
private abbrev G := diagramMappingTarget B

/-- The original free-groupoid unit is bijective on its two literal vertices. -/
private theorem unit_vertices_bijective :
    Function.Bijective (unit.app zero) := by
  let c := (GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌).hom
  let e : (DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj (Fin 2)).obj zero ≃
      Fin 2 := nerveEquiv.trans CategoryTheory.codiscreteEquiv
  have hc : Function.Injective (c.app zero) :=
    (isIso_iff_bijective (c.app zero)).mp inferInstance |>.1
  have h (x : (Δ[1] : SSet.{0}).obj zero) :
      e (c.app zero (unit.app zero x)) = SSet.stdSimplex.obj₀Equiv x := by
    obtain ⟨j, rfl⟩ := (SSet.stdSimplex.obj₀Equiv (n := 1)).symm.surjective x
    fin_cases j <;> rfl
  constructor
  · intro x y hxy
    apply (SSet.stdSimplex.obj₀Equiv (n := 1)).injective
    rw [← h x, ← h y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := (SSet.stdSimplex.obj₀Equiv (n := 1)).surjective
      (e (c.app zero y))
    refine ⟨x, hc ?_⟩
    apply e.injective
    exact (h x).trans hx

/-- Horizontal discretization of the original edge unit is invertible at
the ordinary zero row, with no replacement of its parameter. -/
theorem unit_discrete_zero_isIso : IsIso ((discrete.map unit).app zero) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  apply (isIso_iff_bijective _).mpr
  change Function.Bijective (unit.app zero)
  exact unit_vertices_bijective

/-- The original edge restriction is invertible on mapping spaces into
the ordinary zero coskeleton, in every vertical simplicial degree. -/
theorem unit_precomp_coskeleton_isIso (K : SSet.{0}) :
    IsIso (diagramMappingPrecomp (discrete.map unit) (coskeleton.obj K)) := by
  letI := unit_discrete_zero_isIso
  exact OrdinaryZeroCoskeletonMapping.precomp_isIso _ K

/-- Restriction from the original walking parameter to its directed edge. -/
def restrict : F ⟶ G where
  app W := diagramMappingPrecomp (discrete.map unit) W
  naturality X Y f := by
    apply NatTrans.ext
    funext q z
    rfl

/-- The walking-extension square of the actual relative zero target is a
pullback of whole simplicial mapping spaces. -/
theorem walking_pullback {W Z : Space} (f : W ⟶ Z) :
    IsPullback
      (F.map (pullback.fst (vertices Z) (coskeleton.map (f.app zero))))
      (restrict.app (targetOverZero f))
      (restrict.app Z)
      (G.map (pullback.fst (vertices Z) (coskeleton.map (f.app zero)))) := by
  let k := coskeleton.map (f.app zero)
  let h := IsPullback.of_hasPullback (vertices Z) k
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramTensorMappingAdjunction A).rightAdjoint_preservesLimits
  letI : PreservesLimitsOfSize.{0, 0} G :=
    (diagramTensorMappingAdjunction B).rightAdjoint_preservesLimits
  letI : IsIso (restrict.app (coskeleton.obj (W.obj zero))) :=
    unit_precomp_coskeleton_isIso (W.obj zero)
  letI : IsIso (restrict.app (coskeleton.obj (Z.obj zero))) :=
    unit_precomp_coskeleton_isIso (Z.obj zero)
  have hB : IsPullback (F.map k) (restrict.app (coskeleton.obj (W.obj zero)))
      (restrict.app (coskeleton.obj (Z.obj zero))) (G.map k) :=
    IsPullback.of_vert_isIso ⟨(restrict.naturality k).symm⟩
  have ho := (h.map F).paste_vert hB
  rw [restrict.naturality, restrict.naturality] at ho
  exact ho.of_bot (restrict.naturality (pullback.fst (vertices Z) k)).symm (h.map G)

#print axioms unit_vertices_bijective
#print axioms unit_discrete_zero_isIso
#print axioms unit_precomp_coskeleton_isIso
#print axioms walking_pullback

end
end DaggerModels.PartII.OrdinaryCoherentZeroCoskeleton
