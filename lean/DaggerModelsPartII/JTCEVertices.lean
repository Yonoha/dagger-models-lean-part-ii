import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModels.Vertices
import TopCatModelCategory.SSet.FundamentalGroupoid

/-!
# The literal vertex seam of the collapsed endpoint interval

The boundary of the ordinary one-simplex is the constant simplicial set on
its two ordered vertices. In every parameter degree the canonical boundary
inclusion into `C_E` is an isomorphism on vertices. These facts identify the
vertex seam of the free dagger completion of `C_E` with the manuscript's
literal endpoint boundary.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTCEVertices

open JTXiEndpointCollapse

noncomputable section

private theorem boundaryInclusion_vertex_bijective :
    Function.Bijective (((SSet.boundary 1).ι).app (op ⦋0⦌)) := by
  constructor
  · intro a b h
    exact Subtype.ext h
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    change ¬Function.Surjective
      (fun i : Fin 1 ↦ (SSet.stdSimplex.objEquiv x) i)
    intro hs
    obtain ⟨a, ha⟩ := hs 0
    obtain ⟨b, hb⟩ := hs 1
    have hab : a = b := Subsingleton.elim a b
    have hb' : (SSet.stdSimplex.objEquiv x) a = 1 := by
      simpa only [hab] using hb
    exact (by decide : (0 : Fin 2) ≠ 1) (ha.symm.trans hb')

/-- The literal boundary inclusion contains both and only the vertices of
`Δ[1]`, with their original order. -/
theorem boundaryInclusion_vertex_isIso :
    IsIso (((SSet.boundary 1).ι).app (op ⦋0⦌)) :=
  (isIso_iff_bijective _).2 boundaryInclusion_vertex_bijective

private def boundaryToVertices : boundary ⟶ SSetVertices.obj boundary := by
  let v0 : boundary.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₀
  let v1 : boundary.obj (op ⦋0⦌) := SSet.yonedaEquiv SSet.boundary₁.ι₁
  exact SSet.boundary₁.desc v0 v1

private theorem boundaryToVertices_comp_inclusion :
    boundaryToVertices ≫ SSetVertices.inclusion boundary = 𝟙 boundary := by
  apply SSet.boundary₁.hom_ext
  · dsimp [boundaryToVertices]
    rw [← Category.assoc, SSet.boundary₁.ι₀_desc]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      SSetVertices.inclusion_app_zero]
    rfl
  · dsimp [boundaryToVertices]
    rw [← Category.assoc, SSet.boundary₁.ι₁_desc]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      SSetVertices.inclusion_app_zero]
    rfl

/-- The one-boundary is the constant simplicial set on its two vertices.
The hom is exactly the existing total-degeneracy inclusion. -/
def boundaryVerticesIso : SSetVertices.obj boundary ≅ boundary where
  hom := SSetVertices.inclusion boundary
  inv := boundaryToVertices
  hom_inv_id := by
    apply (cancel_mono (SSetVertices.inclusion boundary)).1
    simp only [Category.assoc, boundaryToVertices_comp_inclusion,
      Category.comp_id, Category.id_comp]
  inv_hom_id := boundaryToVertices_comp_inclusion

private theorem boundaryVerticesMap_isIso :
    IsIso (SSetVertices.map (SSet.boundary 1).ι) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  change IsIso (((SSet.boundary 1).ι).app (op ⦋0⦌))
  exact boundaryInclusion_vertex_isIso

/-- The two ordered vertices of the interval are precisely its literal
boundary. The map is calibrated to the actual boundary inclusion. -/
def boundaryAsVertices : boundary ≅ SSetVertices.obj interval :=
  letI : IsIso (SSetVertices.map (SSet.boundary 1).ι) :=
    boundaryVerticesMap_isIso
  boundaryVerticesIso.symm ≪≫ asIso (SSetVertices.map (SSet.boundary 1).ι)

theorem boundaryAsVertices_inclusion :
    boundaryAsVertices.hom ≫ SSetVertices.inclusion interval =
      (SSet.boundary 1).ι := by
  letI : IsIso (SSetVertices.map (SSet.boundary 1).ι) :=
    boundaryVerticesMap_isIso
  change boundaryVerticesIso.inv ≫
      SSetVertices.map (SSet.boundary 1).ι ≫
        SSetVertices.inclusion interval = (SSet.boundary 1).ι
  rw [SSetVertices.map_inclusion]
  change (boundaryVerticesIso.inv ≫ boundaryVerticesIso.hom) ≫
    (SSet.boundary 1).ι = _
  rw [boundaryVerticesIso.inv_hom_id, Category.id_comp]

private theorem cylinderInclusion_vertex_isIso (k : SimplexCategory) :
    IsIso ((cylinderInclusion.app k).app (op ⦋0⦌)) := by
  apply (isIso_iff_bijective _).2
  have h := boundaryInclusion_vertex_bijective
  constructor
  · intro a b hab
    change (((SSet.boundary 1).ι).app (op ⦋0⦌) a.1, a.2) =
      (((SSet.boundary 1).ι).app (op ⦋0⦌) b.1, b.2) at hab
    apply Prod.ext
    · have h₁ := congrArg Prod.fst hab
      exact h.1 h₁
    · have h₂ := congrArg Prod.snd hab
      exact h₂
  · intro p
    obtain ⟨a, ha⟩ := h.2 p.1
    refine ⟨(a, p.2), ?_⟩
    change (((SSet.boundary 1).ι).app (op ⦋0⦌) a, p.2) = p
    exact Prod.ext ha rfl

/-- The canonical map `∂Δ¹ → C_E^k` is an isomorphism on actual vertices,
for every parameter degree `k`. -/
theorem ceBoundary_vertex_isIso (k : SimplexCategory) :
    IsIso ((CE_boundary.app k).app (op ⦋0⦌)) := by
  have hCE : IsPushout (cylinderInclusion.app k) (cylinderProjection.app k)
      (CE_interval.app k) (CE_boundary.app k) :=
    (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
      ((evaluation SimplexCategory SSet.{0}).obj k)
  have h0 := hCE.map ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj (op ⦋0⦌))
  change IsPushout ((cylinderInclusion.app k).app (op ⦋0⦌))
    ((cylinderProjection.app k).app (op ⦋0⦌))
    ((CE_interval.app k).app (op ⦋0⦌))
    ((CE_boundary.app k).app (op ⦋0⦌)) at h0
  letI : IsIso ((cylinderInclusion.app k).app (op ⦋0⦌)) :=
    cylinderInclusion_vertex_isIso k
  exact h0.isIso_inr_of_isIso

private theorem ceBoundary_verticesMap_isIso (k : SimplexCategory) :
    IsIso (SSetVertices.map (CE_boundary.app k)) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  change IsIso ((CE_boundary.app k).app (op ⦋0⦌))
  exact ceBoundary_vertex_isIso k

/-- The entire vertex seam of `C_E^k` is its literal ordered boundary. -/
def ceVerticesIso (k : SimplexCategory) :
    SSetVertices.obj (CE.obj k) ≅ boundary :=
  letI : IsIso (SSetVertices.map (CE_boundary.app k)) :=
    ceBoundary_verticesMap_isIso k
  (asIso (SSetVertices.map (CE_boundary.app k))).symm ≪≫ boundaryVerticesIso

/-- The seam identification is calibrated to the chosen boundary inclusion. -/
theorem ceVerticesIso_inclusion (k : SimplexCategory) :
    (ceVerticesIso k).hom ≫ CE_boundary.app k =
      SSetVertices.inclusion (CE.obj k) := by
  letI : IsIso (SSetVertices.map (CE_boundary.app k)) :=
    ceBoundary_verticesMap_isIso k
  change (asIso (SSetVertices.map (CE_boundary.app k))).inv ≫
    SSetVertices.inclusion boundary ≫ CE_boundary.app k = _
  rw [← SSetVertices.map_inclusion]
  change ((asIso (SSetVertices.map (CE_boundary.app k))).inv ≫
    (asIso (SSetVertices.map (CE_boundary.app k))).hom) ≫
      SSetVertices.inclusion (CE.obj k) = _
  rw [Iso.inv_hom_id, Category.id_comp]

end

end DaggerModels.PartII.JTCEVertices
