import OrdinaryAllVertexReplacementComparison
import OrdinarySegalVerticalPrecompletionComponents
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# Component coverage of the actual complete vertex tuple map

At vertical degree zero, the original unit is an isomorphism of entire
horizontal simplicial sets. Therefore every discrete horizontal test is
bijective on vertices. After any rowwise weak replacement, every full finite
tuple base is component-surjective, without a target Segal assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexComponentCover

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices)
open OrdinarySegalVerticalPrecompletion (unit precompletion)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- Every original horizontal discrete test sees a vertex bijection of the unit. -/
theorem unit_discrete_vertices_bijective (W : Space) (K : SSet.{0}) :
    Function.Bijective
      ((diagramMappingPostcomp (discrete.obj K) (unit W)).app zero) := by
  have : IsIso (NatTrans.flipApp (unit W) zero) :=
    OrdinarySegalVerticalPrecompletion.unit_verticalZero_isIso W
  have hh : IsIso
      ((DaggerNativeBisimplicialHorizontalMapping.horizontalMap K (unit W)).app zero) := by
    change IsIso ((coyoneda.obj (op K)).map (NatTrans.flipApp (unit W) zero))
    infer_instance
  have bH := (CategoryTheory.isIso_iff_bijective
    ((DaggerNativeBisimplicialHorizontalMapping.horizontalMap K (unit W)).app zero)).mp hh
  have bW := (CategoryTheory.isIso_iff_bijective
    ((OrdinaryDiscreteMapping.mappingIso K W).hom.app zero)).mp inferInstance
  have bP := (CategoryTheory.isIso_iff_bijective
    ((OrdinaryDiscreteMapping.mappingIso K (precompletion W)).hom.app zero)).mp inferInstance
  have h := NatTrans.congr_app
    (OrdinarySegalRestrictionTargetNaturality.mappingIso_post K (unit W)) zero
  constructor
  · intro x y hxy
    apply bW.injective
    apply bH.injective
    exact (congrFun h x).symm.trans
      ((congrArg ((OrdinaryDiscreteMapping.mappingIso K (precompletion W)).hom.app zero)
        hxy).trans (congrFun h y))
  · intro y
    obtain ⟨z, hz⟩ := bH.surjective
      (((OrdinaryDiscreteMapping.mappingIso K (precompletion W)).hom.app zero) y)
    obtain ⟨x, hx⟩ := bW.surjective z
    refine ⟨x, bP.injective ?_⟩
    calc
      _ = ((DaggerNativeBisimplicialHorizontalMapping.horizontalMap K (unit W)).app zero)
          (((OrdinaryDiscreteMapping.mappingIso K W).hom.app zero) x) := congrFun h x
      _ = _ := by rw [hx, hz]

/-- Every component of the actual full finite-tuple base has an original preimage. -/
theorem unit_tuple_components_surjective (W : Space) (n : ℕ) :
    Function.Surjective
      (SSet.mapπ₀ (diagramMappingPostcomp (discrete.obj (vertices n)) (unit W))) :=
  DaggerNativeKanRigHomWeakRecognition.mapπ₀_surjective_of_vertices _
    (unit_discrete_vertices_bijective W (vertices n)).surjective

/-- The actual unit followed by a rowwise weak replacement still covers every
component of every original complete finite vertex-tuple base. -/
theorem replacement_tuple_components_surjective (W R : Space)
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) (n : ℕ) :
    Function.Surjective (SSet.mapπ₀
      (diagramMappingPostcomp (discrete.obj (vertices n)) (unit W ≫ i))) := by
  have : WeakEquivalence (diagramMappingPostcomp (discrete.obj (vertices n)) i) :=
    OrdinaryAllVertexReplacementComparison.vertexBaseMap_weak_of_rowZero_weak i n (hi zero)
  have hR := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
    (diagramMappingPostcomp (discrete.obj (vertices n)) i)).surjective
  have hW := unit_tuple_components_surjective W n
  intro c
  obtain ⟨d, hd⟩ := hR c
  obtain ⟨e, he⟩ := hW d
  refine ⟨e, ?_⟩
  have hcomp : diagramMappingPostcomp (discrete.obj (vertices n)) (unit W ≫ i) =
      diagramMappingPostcomp (discrete.obj (vertices n)) (unit W) ≫
        diagramMappingPostcomp (discrete.obj (vertices n)) i :=
    (diagramMappingTarget (discrete.obj (vertices n))).map_comp (unit W) i
  rw [hcomp, SSet.mapπ₀_comp_apply, he, hd]

#print axioms unit_discrete_vertices_bijective
#print axioms unit_tuple_components_surjective
#print axioms replacement_tuple_components_surjective

end

end DaggerModels.PartII.OrdinaryAllVertexComponentCover
