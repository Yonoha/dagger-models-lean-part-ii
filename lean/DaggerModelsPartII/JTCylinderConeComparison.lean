import DaggerModelsPartII.JTCylinderFrame
import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import ActualRightConeProjectionNaturality
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# The reduced standard cylinder maps to the original right cone

The first interval level retains an old simplex vertex. The second
interval level maps to the appended terminal vertex. The two resulting
boundary maps descend through the literal reduced-cylinder pushout.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerModels.PartII
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerNativeRightConeCofaceGeometry

namespace DaggerModels.PartII.JTCylinderConeComparison

noncomputable section

/-- The pointwise product-poset map which keeps the old simplex at time
zero and sends every time-one vertex to the appended terminal vertex. -/
def productOrder (k : SimplexCategory) :
    Fin 2 × Fin (k.len + 1) →o Fin (k.len + 2) where
  toFun p := if p.1 = 0 then p.2.castSucc else Fin.last (k.len + 1)
  monotone' a b hab := by
    rcases a with ⟨ta, ia⟩
    rcases b with ⟨tb, ib⟩
    fin_cases ta <;> fin_cases tb
    · exact Fin.castSucc_le_castSucc_iff.mpr hab.2
    · exact Fin.le_last _
    · exact False.elim ((by decide : ¬ ((1 : Fin 2) ≤ 0)) hab.1)
    · exact le_refl _

/-- The uncollapsed product cylinder maps to the large standard simplex
of the actual right cone. -/
def intervalJoin (k : SimplexCategory) :
    JTXiEndpointCollapse.interval ⊗ SSet.stdSimplex.obj k ⟶
      (Δ[k.len + 1] : SSet.{0}) where
  app d z := SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk
      ((productOrder k).comp (OrderHom.prod
        (SSet.stdSimplex.objEquiv z.1).toOrderHom
        (SSet.stdSimplex.objEquiv z.2).toOrderHom)))
  naturality {d e} θ := by
    funext z
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    rfl

/-- The two formal cone endpoints classified by the literal ordered
boundary of the standard interval. -/
def coneBoundary (k : SimplexCategory) :
    JTXiEndpointCollapse.boundary ⟶ cone.{0} k.len :=
  SSet.boundary₁.desc
    (SSet.yonedaEquiv (alphaMap.{0} k.len))
    (SSet.yonedaEquiv (omegaMap.{0} k.len))

theorem coneBoundary_zero (k : SimplexCategory) :
    SSet.boundary₁.ι₀ ≫ coneBoundary k = alphaMap.{0} k.len := by
  simp only [coneBoundary, SSet.boundary₁.ι₀_desc,
    Equiv.symm_apply_apply]

theorem coneBoundary_one (k : SimplexCategory) :
    SSet.boundary₁.ι₁ ≫ coneBoundary k = omegaMap.{0} k.len := by
  simp only [coneBoundary, SSet.boundary₁.ι₁_desc,
    Equiv.symm_apply_apply]

theorem coneBoundary_naturality {k l : SimplexCategory} (α : k ⟶ l) :
    coneBoundary k ≫ coneFunctor.{0}.map α = coneBoundary l := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc, coneBoundary_zero, alphaMap_naturality,
      coneBoundary_zero]
  · rw [← Category.assoc, coneBoundary_one, omegaMap_naturality,
      coneBoundary_one]

/-- The actual cone functor with its two ordered formal endpoints under
the literal boundary, without replacing the original pushout. -/
def coneBoundaryNat :
    (Functor.const SimplexCategory).obj JTXiEndpointCollapse.boundary ⟶
      coneFunctor.{0} where
  app := coneBoundary
  naturality {k l} α := by
    simpa only [Functor.const_obj_map, Category.id_comp] using
      (coneBoundary_naturality α).symm

def coneUnder : SimplexCategory ⥤ Under JTXiEndpointCollapse.boundary :=
  Under.lift coneFunctor.{0} coneBoundaryNat

/-- The large-simplex leg of the cylinder-to-cone comparison. -/
def cylinderToCone (k : SimplexCategory) :
    JTXiEndpointCollapse.interval ⊗ SSet.stdSimplex.obj k ⟶
      coneFunctor.{0}.obj k :=
  intervalJoin k ≫ simplexIncl.{0} k.len

theorem intervalJoin_naturality {k l : SimplexCategory} (α : k ⟶ l) :
    intervalJoin k ≫ joinMap.{0} α =
      (𝟙 JTXiEndpointCollapse.interval ⊗ₘ SSet.stdSimplex.map α) ≫
        intervalJoin l := by
  apply NatTrans.ext
  funext d z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  let p := ((SSet.stdSimplex.objEquiv z.1).toOrderHom i,
    (SSet.stdSimplex.objEquiv z.2).toOrderHom i)
  change (joinHom α).toOrderHom (productOrder k p) =
    productOrder l (p.1, α.toOrderHom p.2)
  rcases p with ⟨t, v⟩
  fin_cases t
  · simpa [productOrder] using
      (DaggerNativeRightConeCofaceGeometry.joinHom_prefix
        (α := show ⦋k.len⦌ ⟶ ⦋l.len⦌ from α) v)
  · simpa [productOrder] using
      (DaggerNativeRightConeCofaceGeometry.joinHom_last
        (α := show ⦋k.len⦌ ⟶ ⦋l.len⦌ from α))

theorem cylinderToCone_naturality {k l : SimplexCategory} (α : k ⟶ l) :
    cylinderToCone k ≫ coneFunctor.{0}.map α =
      (𝟙 JTXiEndpointCollapse.interval ⊗ₘ SSet.stdSimplex.map α) ≫
        cylinderToCone l := by
  change (intervalJoin k ≫ simplexIncl.{0} k.len) ≫ coneMap.{0} α = _
  rw [Category.assoc, simplexIncl_naturality, ← Category.assoc,
    intervalJoin_naturality, Category.assoc]
  rfl

/-- The first boundary cylinder hits the collapsed old face. -/
theorem intervalJoin_zero (k : SimplexCategory) :
    (SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 0) ⊗ₘ
        𝟙 (SSet.stdSimplex.obj k)) ≫ intervalJoin k =
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{0})
        (SSet.stdSimplex.obj k) ≫ face.{0} k.len := by
  apply NatTrans.ext
  funext d z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change productOrder k
      (((JTXiEndpointCollapseBoundary.ordinaryEndpoint 0).toOrderHom
        ((SSet.stdSimplex.objEquiv z.1).toOrderHom i)),
        (SSet.stdSimplex.objEquiv z.2).toOrderHom i) =
      (SimplexCategory.δ (Fin.last (k.len + 1))).toOrderHom
        ((SSet.stdSimplex.objEquiv z.2).toOrderHom i)
  have ht : (JTXiEndpointCollapseBoundary.ordinaryEndpoint 0).toOrderHom
      ((SSet.stdSimplex.objEquiv z.1).toOrderHom i) = (0 : Fin 2) := rfl
  rw [ht]
  simp [productOrder, SimplexCategory.δ, Fin.succAbove_last]

/-- The second boundary cylinder hits the appended terminal vertex. -/
theorem intervalJoin_one (k : SimplexCategory) :
    (SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 1) ⊗ₘ
        𝟙 (SSet.stdSimplex.obj k)) ≫ intervalJoin k =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (SSet.stdSimplex.obj k) ≫ lastVertex.{0} k.len := by
  apply NatTrans.ext
  funext d z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change productOrder k
      (((JTXiEndpointCollapseBoundary.ordinaryEndpoint 1).toOrderHom
        ((SSet.stdSimplex.objEquiv z.1).toOrderHom i)),
        (SSet.stdSimplex.objEquiv z.2).toOrderHom i) =
      Fin.last (k.len + 1)
  have ht : (JTXiEndpointCollapseBoundary.ordinaryEndpoint 1).toOrderHom
      ((SSet.stdSimplex.objEquiv z.1).toOrderHom i) = (1 : Fin 2) := rfl
  rw [ht]
  simp [productOrder]

private theorem boundaryInclusion_zero :
    SSet.boundary₁.ι₀ ≫ JTCylinderFrame.j =
      SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 0) := by
  change SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι = _
  rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
  apply SSet.yonedaEquiv.injective
  rfl

private theorem boundaryInclusion_one :
    SSet.boundary₁.ι₁ ≫ JTCylinderFrame.j =
      SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 1) := by
  change SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι = _
  rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
  apply SSet.yonedaEquiv.injective
  rfl

private theorem cylinderBoundary_zero (k : SimplexCategory) :
    (SSet.boundary₁.ι₀ ▷ SSet.stdSimplex.obj k) ≫
        (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
          (SSet.stdSimplex.obj k) ≫ cylinderToCone k =
      (SSet.boundary₁.ι₀ ▷ SSet.stdSimplex.obj k) ≫
        (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary).app
          (SSet.stdSimplex.obj k) ≫ coneBoundary k := by
  let K := SSet.stdSimplex.obj k
  have hcollapse : CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) K ≫
      collapse.{0} k.len = CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hfst : (SSet.boundary₁.ι₀ ▷ K) ≫
      CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K ≫
        SSet.boundary₁.ι₀ := by
    simpa only [JTXiEndpointCollapse.boundary] using
      (CartesianMonoidalCategory.whiskerRight_fst SSet.boundary₁.ι₀ K)
  change (SSet.boundary₁.ι₀ ▷ K) ≫
      (JTCylinderFrame.j ⊗ₘ 𝟙 K) ≫
        (intervalJoin k ≫ simplexIncl.{0} k.len) =
    (SSet.boundary₁.ι₀ ▷ K) ≫
      CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K ≫
        coneBoundary k
  calc
    _ = (SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 0)
          ⊗ₘ 𝟙 K) ≫ intervalJoin k ≫ simplexIncl.{0} k.len := by
          rw [← Category.assoc, MonoidalCategory.tensorHom_id,
            ← MonoidalCategory.comp_whiskerRight, boundaryInclusion_zero]
          rfl
    _ = (CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) K ≫
          face.{0} k.len) ≫ simplexIncl.{0} k.len := by
          rw [← Category.assoc, intervalJoin_zero]
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K ≫
          alphaMap.{0} k.len := by
          rw [Category.assoc, face_eq_collapse, ← Category.assoc, hcollapse]
          rfl
    _ = (SSet.boundary₁.ι₀ ▷ K) ≫
          CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K ≫
            coneBoundary k := by
          simpa only [Category.assoc, coneBoundary_zero] using
            (congrArg (fun f ↦ f ≫ coneBoundary k) hfst).symm

private theorem cylinderBoundary_one (k : SimplexCategory) :
    (SSet.boundary₁.ι₁ ▷ SSet.stdSimplex.obj k) ≫
        (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
          (SSet.stdSimplex.obj k) ≫ cylinderToCone k =
      (SSet.boundary₁.ι₁ ▷ SSet.stdSimplex.obj k) ≫
        (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary).app
          (SSet.stdSimplex.obj k) ≫ coneBoundary k := by
  let K := SSet.stdSimplex.obj k
  have hfst : (SSet.boundary₁.ι₁ ▷ K) ≫
      CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K ≫
        SSet.boundary₁.ι₁ := by
    simpa only [JTXiEndpointCollapse.boundary] using
      (CartesianMonoidalCategory.whiskerRight_fst SSet.boundary₁.ι₁ K)
  change (SSet.boundary₁.ι₁ ▷ K) ≫
      (JTCylinderFrame.j ⊗ₘ 𝟙 K) ≫
        (intervalJoin k ≫ simplexIncl.{0} k.len) =
    (SSet.boundary₁.ι₁ ▷ K) ≫
      CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K ≫
        coneBoundary k
  calc
    _ = (SSet.stdSimplex.map (JTXiEndpointCollapseBoundary.ordinaryEndpoint 1)
          ⊗ₘ 𝟙 K) ≫ intervalJoin k ≫ simplexIncl.{0} k.len := by
          rw [← Category.assoc, MonoidalCategory.tensorHom_id,
            ← MonoidalCategory.comp_whiskerRight, boundaryInclusion_one]
          rfl
    _ = (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K ≫
          lastVertex.{0} k.len) ≫ simplexIncl.{0} k.len := by
          rw [← Category.assoc, intervalJoin_one]
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{0}) K ≫
          omegaMap.{0} k.len := by rw [Category.assoc]; rfl
    _ = (SSet.boundary₁.ι₁ ▷ K) ≫
          CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K ≫
            coneBoundary k := by
          simpa only [Category.assoc, coneBoundary_one] using
            (congrArg (fun f ↦ f ≫ coneBoundary k) hfst).symm

/-- The product-order map obeys the literal pushout relation at both
ordered boundary vertices. -/
theorem cylinderBoundaryCompatibility (k : SimplexCategory) :
    (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
        (SSet.stdSimplex.obj k) ≫ cylinderToCone k =
      (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary).app
        (SSet.stdSimplex.obj k) ≫ coneBoundary k := by
  apply SSet.boundary₁.hom_ext_rightTensor
  · exact cylinderBoundary_zero k
  · exact cylinderBoundary_one k

/-- Pointwise descent from the literal standard reduced cylinder to the
actual original right-cone pushout. -/
def comparisonComponent (k : SimplexCategory) :
    JTCylinderFrame.value.obj k ⟶ coneFunctor.{0}.obj k :=
  (JTCylinderFrame.isPushout k).desc (cylinderToCone k)
    (coneBoundary k) (cylinderBoundaryCompatibility k)

theorem cylinder_comparison (k : SimplexCategory) :
    JTCylinderFrame.cylinder k ≫ comparisonComponent k = cylinderToCone k :=
  (JTCylinderFrame.isPushout k).inl_desc _ _ _

theorem boundary_comparison (k : SimplexCategory) :
    JTCylinderFrame.boundary.app k ≫ comparisonComponent k = coneBoundary k :=
  (JTCylinderFrame.isPushout k).inr_desc _ _ _

theorem comparisonComponent_naturality {k l : SimplexCategory} (α : k ⟶ l) :
    JTCylinderFrame.value.map α ≫ comparisonComponent l =
      comparisonComponent k ≫ coneFunctor.{0}.map α := by
  apply (JTCylinderFrame.isPushout k).hom_ext
  · have hn := (ReducedCylinder.cylinder JTCylinderFrame.j).naturality
      (SSet.stdSimplex.map α)
    change (𝟙 JTXiEndpointCollapse.interval ⊗ₘ SSet.stdSimplex.map α) ≫
        JTCylinderFrame.cylinder l =
      JTCylinderFrame.cylinder k ≫ JTCylinderFrame.value.map α at hn
    change JTCylinderFrame.cylinder k ≫
        (JTCylinderFrame.value.map α ≫ comparisonComponent l) =
      JTCylinderFrame.cylinder k ≫
        (comparisonComponent k ≫ coneFunctor.{0}.map α)
    rw [← Category.assoc, ← hn, Category.assoc, cylinder_comparison,
      ← Category.assoc, cylinder_comparison]
    exact (cylinderToCone_naturality α).symm
  · have hn := JTCylinderFrame.boundary.naturality α
    have hn' : JTCylinderFrame.boundary.app k ≫
        JTCylinderFrame.value.map α = JTCylinderFrame.boundary.app l := by
      simpa only [Functor.const_obj_map, Category.id_comp] using hn.symm
    change JTCylinderFrame.boundary.app k ≫
        (JTCylinderFrame.value.map α ≫ comparisonComponent l) =
      JTCylinderFrame.boundary.app k ≫
        (comparisonComponent k ≫ coneFunctor.{0}.map α)
    rw [← Category.assoc, hn', boundary_comparison,
      ← Category.assoc, boundary_comparison]
    exact (coneBoundary_naturality α).symm

/-- The actual natural map from the reduced cylinder to the original
right cone, including every simplex operator. -/
def comparison : JTCylinderFrame.value ⟶ coneFunctor.{0} where
  app := comparisonComponent
  naturality {_ _} α := comparisonComponent_naturality α

/-- The same natural map under the original ordered boundary. -/
def comparisonUnder : JTCylinderFrame.under ⟶ coneUnder where
  app k := Under.homMk (comparison.app k) (boundary_comparison k)
  naturality {k l} α := by
    apply Under.UnderMorphism.ext
    exact comparison.naturality α

/-- The ordered zero endpoint is the collapsed old face of the original
right cone. -/
theorem comparison_endpoint_zero (k : SimplexCategory) :
    SSet.boundary₁.ι₀ ≫ JTCylinderFrame.boundary.app k ≫
        comparison.app k = alphaMap.{0} k.len := by
  change SSet.boundary₁.ι₀ ≫ JTCylinderFrame.boundary.app k ≫
    comparisonComponent k = _
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ SSet.boundary₁.ι₀ ≫ f)
      (boundary_comparison k)).trans (coneBoundary_zero k)

/-- The ordered one endpoint is the appended terminal cone vertex. -/
theorem comparison_endpoint_one (k : SimplexCategory) :
    SSet.boundary₁.ι₁ ≫ JTCylinderFrame.boundary.app k ≫
        comparison.app k = omegaMap.{0} k.len := by
  change SSet.boundary₁.ι₁ ≫ JTCylinderFrame.boundary.app k ≫
    comparisonComponent k = _
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ SSet.boundary₁.ι₁ ≫ f)
      (boundary_comparison k)).trans (coneBoundary_one k)

theorem intervalJoin_projection (k : SimplexCategory) :
    intervalJoin k ≫ DaggerActualRightConeFinalEdgeMaps.heightMap k.len =
      CartesianMonoidalCategory.fst JTXiEndpointCollapse.interval
        (SSet.stdSimplex.obj k) := by
  apply NatTrans.ext
  funext d z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  let p := ((SSet.stdSimplex.objEquiv z.1).toOrderHom i,
    (SSet.stdSimplex.objEquiv z.2).toOrderHom i)
  change (DaggerActualRightConeFinalEdgeMaps.heightHom k.len).toOrderHom
    (productOrder k p) = p.1
  rcases p with ⟨t, v⟩
  fin_cases t
  · exact DaggerActualRightConeProjectionNaturality.height_prefix k.len v
  · exact DaggerActualRightConeProjectionNaturality.height_last k.len

theorem coneBoundary_projection (k : SimplexCategory) :
    coneBoundary k ≫ DaggerActualRightConeFinalEdgeMaps.projection k.len =
      JTCylinderFrame.j := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc, coneBoundary_zero,
      DaggerActualRightConeFinalEdgeMaps.alpha_projection]
    simpa only [SSet.stdSimplex.δ_one] using boundaryInclusion_zero.symm
  · rw [← Category.assoc, coneBoundary_one,
      DaggerActualRightConeFinalEdgeMaps.omega_projection]
    simpa only [SSet.stdSimplex.δ_zero] using boundaryInclusion_one.symm

/-- The cylinder-to-cone comparison preserves the two exact projections
to the ordinary interval. -/
theorem comparison_augmentation (k : SimplexCategory) :
    comparison.app k ≫ DaggerActualRightConeFinalEdgeMaps.projection k.len =
      JTCylinderFrame.augmentation.app k := by
  apply (JTCylinderFrame.isPushout k).hom_ext
  · change JTCylinderFrame.cylinder k ≫ comparisonComponent k ≫
      DaggerActualRightConeFinalEdgeMaps.projection k.len =
      JTCylinderFrame.cylinder k ≫ JTCylinderFrame.augmentation.app k
    rw [← Category.assoc, cylinder_comparison, cylinderToCone,
      Category.assoc, DaggerActualRightConeFinalEdgeMaps.simplex_projection,
      intervalJoin_projection, JTCylinderFrame.cylinder_augmentation]
  · change JTCylinderFrame.boundary.app k ≫ comparisonComponent k ≫
      DaggerActualRightConeFinalEdgeMaps.projection k.len =
      JTCylinderFrame.boundary.app k ≫ JTCylinderFrame.augmentation.app k
    rw [← Category.assoc, boundary_comparison, coneBoundary_projection,
      JTCylinderFrame.boundary_augmentation]

end

end DaggerModels.PartII.JTCylinderConeComparison
