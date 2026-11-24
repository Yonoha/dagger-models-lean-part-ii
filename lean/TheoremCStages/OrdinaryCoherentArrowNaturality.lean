import OrdinarySegalCoherentArrowImage
import OrdinarySegalRestrictionTargetNaturality

/-!
# Naturality of the actual coherent-arrow component image

Every map of ordinary simplicial spaces sends the component-saturated image
of the walking-isomorphism edge evaluation into the corresponding image.
The resulting restricted map retains the original arrow-row map exactly.
No reflection of coherent arrows or weak-equivalence claim is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryCoherentArrowNaturality

open OrdinaryCSSLocalization (Space discrete walkingSpace)
open OrdinarySegalWalkingEvaluation (walkingMapping edgeEvaluation simplexMappingIso)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex coherentEvaluation)
open OrdinarySegalComponentImage (imageComponents)

noncomputable section

private abbrev unit := JTCylinderCEComparison.simplexUnit.app ⦋1⦌

/-- The original whole target map on walking-isomorphism mapping spaces. -/
def walkingMap {W Z : Space} (f : W ⟶ Z) : walkingMapping W ⟶ walkingMapping Z :=
  diagramMappingPostcomp walkingSpace f

/-- Edge evaluation is natural for every original whole target map. -/
theorem edgeEvaluation_post {W Z : Space} (f : W ⟶ Z) :
    walkingMap f ≫ edgeEvaluation Z =
      edgeEvaluation W ≫ f.app (op ⦋1⦌) := by
  have h : walkingMap f ≫ diagramMappingPrecomp (discrete.map unit) Z =
      diagramMappingPrecomp (discrete.map unit) W ≫
        diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f := by
    apply NatTrans.ext
    funext q η
    rfl
  calc
    walkingMap f ≫ edgeEvaluation Z =
        (walkingMap f ≫ diagramMappingPrecomp (discrete.map unit) Z) ≫
          (simplexMappingIso Z 1).hom := by
            rw [edgeEvaluation, Category.assoc]
    _ = (diagramMappingPrecomp (discrete.map unit) W ≫
          diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f) ≫
            (simplexMappingIso Z 1).hom := by rw [h]
    _ = (diagramMappingPrecomp (discrete.map unit) W ≫
          (simplexMappingIso W 1).hom) ≫ f.app (op ⦋1⦌) := by
            rw [Category.assoc,
              OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post f 1,
              ← Category.assoc]
    _ = edgeEvaluation W ≫ f.app (op ⦋1⦌) := rfl

private theorem image_post {W Z : Space} (f : W ⟶ Z) :
    ∀ c ∈ imageComponents (edgeEvaluation W),
      SSet.mapπ₀ (f.app (op ⦋1⦌)) c ∈ imageComponents (edgeEvaluation Z) := by
  rintro c ⟨d, rfl⟩
  refine ⟨SSet.mapπ₀ (walkingMap f) d, ?_⟩
  have h := congrFun (congrArg SSet.mapπ₀ (edgeEvaluation_post f)) d
  simpa only [SSet.mapπ₀_comp_apply] using h

/-- The original arrow-row map restricted to both literal coherent images. -/
def coherentArrowMap {W Z : Space} (f : W ⟶ Z) :
    (coherentArrowSubcomplex W).toSSet ⟶
      (coherentArrowSubcomplex Z).toSSet :=
  OrdinarySegalComponentSubcomplex.restrict (f.app (op ⦋1⦌))
    (imageComponents (edgeEvaluation W))
    (imageComponents (edgeEvaluation Z)) (image_post f)

/-- The restriction has exactly the original arrow-row map after inclusion. -/
theorem coherentArrowMap_inclusion {W Z : Space} (f : W ⟶ Z) :
    coherentArrowMap f ≫ (coherentArrowSubcomplex Z).ι =
      (coherentArrowSubcomplex W).ι ≫ f.app (op ⦋1⦌) :=
  OrdinarySegalComponentSubcomplex.restrict_inclusion _ _ _ _

/-- Coherent walking evaluation commutes with the restricted arrow-row map. -/
theorem coherentEvaluation_post {W Z : Space} (f : W ⟶ Z) :
    walkingMap f ≫ coherentEvaluation Z =
      coherentEvaluation W ≫ coherentArrowMap f := by
  apply (cancel_mono (coherentArrowSubcomplex Z).ι).mp
  calc
    (walkingMap f ≫ coherentEvaluation Z) ≫ (coherentArrowSubcomplex Z).ι =
        walkingMap f ≫ edgeEvaluation Z := by
          rw [Category.assoc,
            OrdinarySegalCoherentArrowImage.coherentEvaluation_inclusion]
    _ = edgeEvaluation W ≫ f.app (op ⦋1⦌) := edgeEvaluation_post f
    _ = (coherentEvaluation W ≫ coherentArrowMap f) ≫
          (coherentArrowSubcomplex Z).ι := by
            rw [Category.assoc, coherentArrowMap_inclusion, ← Category.assoc,
              OrdinarySegalCoherentArrowImage.coherentEvaluation_inclusion]

#print axioms edgeEvaluation_post
#print axioms coherentArrowMap_inclusion
#print axioms coherentEvaluation_post

end

end DaggerModels.PartII.OrdinaryCoherentArrowNaturality
