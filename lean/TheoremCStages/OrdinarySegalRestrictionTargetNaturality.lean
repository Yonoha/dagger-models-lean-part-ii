import OrdinarySegalRestrictionTranspose
import OrdinarySegalWalkingEvaluation

/-!
# The original mapping transpose is natural in its whole target diagram

The existing native horizontal target action and restriction-Hom target
naturality retain the actual flipped diagram map. Both the whole transpose
and its inverse commute with postcomposition, at every original parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalRestrictionTargetNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalRestrictionTranspose (transpose)

noncomputable section

/-- The discrete mapping isomorphism commutes with the original target map. -/
theorem mappingIso_post (A : SSet.{0}) {W V : Space} (f : W ⟶ V) :
    diagramMappingPostcomp (discrete.obj A) f ≫
        (OrdinaryDiscreteMapping.mappingIso A V).hom =
      (OrdinaryDiscreteMapping.mappingIso A W).hom ≫
        DaggerNativeBisimplicialHorizontalMapping.horizontalMap A f := by
  apply NatTrans.ext
  funext n η
  apply NatTrans.ext
  funext q x
  rfl

/-- Target postcomposition commutes with the entire original transpose. -/
theorem transpose_post (K A : SSet.{0}) {W V : Space} (f : W ⟶ V)
    (h : K ⟶ diagramMappingSpace (discrete.obj A) W) :
    transpose K A V (h ≫ diagramMappingPostcomp (discrete.obj A) f) =
      transpose K A W h ≫
        diagramRestrictionPost K
          ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f) := by
  change diagramRestrictionHomEquiv K A V.flip
      ((h ≫ diagramMappingPostcomp (discrete.obj A) f) ≫
        (OrdinaryDiscreteMapping.mappingIso A V).hom) =
    diagramRestrictionHomEquiv K A W.flip
      (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom) ≫ _
  rw [Category.assoc, mappingIso_post, ← Category.assoc]
  exact diagramRestrictionHomEquiv_post K
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)
    (h ≫ (OrdinaryDiscreteMapping.mappingIso A W).hom)

/-- The inverse transpose retains the same actual postcomposition map. -/
theorem transpose_symm_post (K A : SSet.{0}) {W V : Space} (f : W ⟶ V)
    (g : A ⟶ diagramRestriction K W.flip) :
    (transpose K A V).symm
        (g ≫ diagramRestrictionPost K
          ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)) =
      (transpose K A W).symm g ≫ diagramMappingPostcomp (discrete.obj A) f := by
  apply (transpose K A V).injective
  rw [Equiv.apply_symm_apply, transpose_post, Equiv.apply_symm_apply]

/-- The representable mapping isomorphism is natural in every whole target map. -/
theorem simplexMappingIso_post {W V : Space} (f : W ⟶ V) (n : ℕ) :
    diagramMappingPostcomp (discrete.obj (Δ[n] : SSet.{0})) f ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso V n).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W n).hom ≫ f.app (op ⦋n⦌) := by
  dsimp only [OrdinarySegalWalkingEvaluation.simplexMappingIso, Iso.trans_hom]
  rw [← Category.assoc, mappingIso_post, Category.assoc,
    DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso_natural,
    ← Category.assoc]

#print axioms mappingIso_post
#print axioms transpose_post
#print axioms transpose_symm_post
#print axioms simplexMappingIso_post

end
end DaggerModels.PartII.OrdinarySegalRestrictionTargetNaturality
