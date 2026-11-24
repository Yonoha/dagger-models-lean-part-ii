import OrdinarySegalSpineTwoPullback
import DaggerModelsPartII.OuterFaceSpineGeometry

/-!
# The literal shared-vertex incidences of the degree-two spine

The three part isomorphisms in `OrdinarySegalSpineTwoPullback` are calibrated
against the inclusions into the original degree-two simplex. The common
vertex is the middle vertex, so its maps into the two edge parts become the
two distinct standard cofaces `δ₁` and `δ₀`. No choice of a replacement
Segal space or of an equivalence-arrow component is made here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalSpineTwoIncidence

open OrdinarySegalSpineTwoPullback SpineOuterFacePushout OuterFaceSpineGeometry

noncomputable section

theorem firstPart_face :
    firstPartIso.hom ≫ SSet.stdSimplex.δ (0 : Fin 3) =
      (firstSpinePart.{0} 0).ι := by
  letI : IsIso (firstSpinePartMap.{0} 0) := firstSpinePartMap_isIso 0
  apply (cancel_epi (firstSpinePartMap.{0} 0)).mp
  simp only [firstPartIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    smallSpineIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  change (DaggerNativeStandardSpineInner.spine.{0} 1).ι ≫
      SSet.stdSimplex.δ (0 : Fin 3) =
    firstSpinePartMap 0 ≫ (firstSpinePart 0).ι
  rfl

theorem lastPart_face :
    lastPartIso.hom ≫ DaggerOriginalCounitRightCone.face 1 =
      (lastSpinePart.{0} 0).ι := by
  letI : IsIso (lastSpinePartMap.{0} 0) := lastSpinePartMap_isIso 0
  apply (cancel_epi (lastSpinePartMap.{0} 0)).mp
  simp only [lastPartIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    smallSpineIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  change (DaggerNativeStandardSpineInner.spine.{0} 1).ι ≫
      DaggerOriginalCounitRightCone.face 1 =
    lastSpinePartMap 0 ≫ (lastSpinePart 0).ι
  have transport {X : SSet.{0}} {A B : X.Subcomplex} (h : A = B) :
      (eqToIso (congrArg SSet.Subcomplex.toSSet h)).hom ≫ B.ι = A.ι := by
    cases h
    simp
  rw [lastSpinePartMap, Category.assoc, transport (lastPartEq 0)]
  rfl

theorem middlePart_face :
    middlePartIso.hom ≫ middleCoface.{0} 0 =
      (middleSpinePart.{0} 0).ι := by
  letI : IsIso (middleSpinePartMap.{0} 0) := middleSpinePartMap_isIso 0
  apply (cancel_epi (middleSpinePartMap.{0} 0)).mp
  simp only [middlePartIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    smallSpineIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  rfl

private theorem middlePart_inv_face :
    middlePartIso.inv ≫ (middleSpinePart.{0} 0).ι = middleCoface.{0} 0 := by
  rw [← middlePart_face, Iso.inv_hom_id_assoc]

/-- The common vertex in the final edge is its initial vertex. -/
theorem first_incidence :
    middlePartIso.inv ≫
        SSet.Subcomplex.homOfLE
          (inf_le_left : middleSpinePart.{0} 0 ≤ firstSpinePart 0) ≫
      firstPartIso.hom = SSet.stdSimplex.δ (1 : Fin 2) := by
  have hmono : Mono (SSet.stdSimplex.δ (0 : Fin 3) :
      (Δ[1] : SSet.{0}) ⟶ Δ[2]) := by
    rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    infer_instance
  apply (cancel_mono (SSet.stdSimplex.δ (0 : Fin 3))).mp
  simp only [Category.assoc, firstPart_face, SSet.Subcomplex.homOfLE_ι,
    middlePart_inv_face]
  change middleCoface 0 =
    SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3)
  rfl

/-- The common vertex in the initial edge is its final vertex. -/
theorem last_incidence :
    middlePartIso.inv ≫
        SSet.Subcomplex.homOfLE
          (inf_le_right : middleSpinePart.{0} 0 ≤ lastSpinePart 0) ≫
      lastPartIso.hom = SSet.stdSimplex.δ (0 : Fin 2) := by
  have hmono : Mono (DaggerOriginalCounitRightCone.face.{0} 1) := by
    change Mono (SSet.stdSimplex.δ (Fin.last 2) :
      (Δ[1] : SSet.{0}) ⟶ Δ[2])
    rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    infer_instance
  apply (cancel_mono (DaggerOriginalCounitRightCone.face.{0} 1)).mp
  simp only [Category.assoc, lastPart_face, SSet.Subcomplex.homOfLE_ι,
    middlePart_inv_face]
  change middleCoface 0 =
    SSet.stdSimplex.δ (0 : Fin 2) ≫ DaggerOriginalCounitRightCone.face 1
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) =
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3))
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  congr 1
  ext i
  fin_cases i
  rfl

#print axioms first_incidence
#print axioms last_incidence

end

end DaggerModels.PartII.OrdinarySegalSpineTwoIncidence
