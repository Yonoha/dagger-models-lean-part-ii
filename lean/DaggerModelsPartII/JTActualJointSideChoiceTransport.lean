import DaggerModelsPartII.JTActualSourceJointSupportTransport
import DaggerModelsPartII.JTActualJointCutCoefficientTransport
import DaggerModelsPartII.JTActualJointSideFamilies
import DaggerModelsPartII.JTComposedPrismLabelOperators
import DaggerModelsPartII.LocalEquivalenceClasses

/-! Compatible choices of both relative edges under exact transport of the cut. -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointSideChoiceTransport

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTActualSourceJointSupport (usedInclusion usedInclusion_mono oldVertexRow)
open JTActualSourceJointSupportTransport (usedOperator usedOperator_inclusion oldVertexRow_map)
open JTJointEndpointRelativeLift (identityOnFace boundaryPair reverseBoundaryPair
  boundaryPair_endpoints reverseBoundaryPair_endpoints restrict_edge restrict_reverse_edge)
open JTProjectiveOrderedFiberComparison (row endpointArrow)
open JTActualJointCutCoefficientTransport (leftCoefficient_map rightCoefficient_map)
open JTActualJointSideFamilies (leftCoefficientsOf rightCoefficientsOf)
open JTParametrizedBeadGraph (jointCoefficient)
open ReversalDiscreteFreeColimits
open TwoBeadEndpointLabel (edgeLabelFromRow)
open DaggerOriginalProductGadget (cutLeftHom cutRightHom)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev E := single 1

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
private abbrev k := JTJointRelativeGraphFamily.coefficient (L := L)
private abbrev z := jointCoefficient (Q := Q) j

/-- Both normalized edges, each with its exact relative identity face and its full endpoints. -/
structure Choices (a : A) (v : Fin (((codes L).obj a).len + 1))
    (hv : orderMap (F.collapse.app a).map v = j.val) where
  ending : std.obj ((k (L := L)).obj a) ⟶ row W ⦋1⦌
  starting : std.obj ((k (L := L)).obj a) ⟶ row W ⦋1⦌
  ending_face : std.map (usedInclusion F a j v hv) ≫ ending = identityOnFace W (z j)
  starting_face : std.map (usedInclusion F a j v hv) ≫ starting = identityOnFace W (z j)
  ending_pair : ending ≫ endpointArrow W = boundaryPair W (oldVertexRow (L := L) a v) (z j)
  starting_pair : starting ≫ endpointArrow W =
    reverseBoundaryPair W (oldVertexRow (L := L) a v) (z j)

private theorem choices_ext {a : A} {v : Fin (((codes L).obj a).len + 1)}
    {hv : orderMap (F.collapse.app a).map v = j.val} {C D : Choices F j a v hv}
    (he : C.ending = D.ending) (hs : C.starting = D.starting) : C = D := by
  cases C
  cases D
  cases he
  cases hs
  rfl

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

variable {a : A} {v : Fin (((codes L).obj a).len + 1)}
variable {hv : orderMap (F.collapse.app a).map v = j.val}

/-- Every actual cut has both choices. -/
theorem nonempty_choices (hW : Localization.localObject SegalLocalizers.localizingFamily W) :
    Nonempty (Choices F j a v hv) := by
  let u := usedInclusion F a j v hv
  letI : Mono u := usedInclusion_mono F a j v hv
  have hf := JTActualSourceJointSupport.oldVertexRow_supported_joint F a j v hv
  obtain ⟨e, he, hp⟩ :=
    JTJointEndpointRelativeLift.exists_edge W u (oldVertexRow (L := L) a v) (z j) hW.1 hf
  obtain ⟨s, hs, hsp⟩ :=
    JTJointEndpointRelativeLift.exists_reverse_edge W u (oldVertexRow (L := L) a v) (z j) hW.1 hf
  exact ⟨⟨e, s, he, hs, hp, hsp⟩⟩

/-- Use a specified ending edge for the actual left coefficient. -/
def Choices.leftCoefficients (C : Choices F j a v hv) :=
  leftCoefficientsOf a j v C.ending (boundaryPair_endpoints W _ _ C.ending_pair).1
    (boundaryPair_endpoints W _ _ C.ending_pair).2

/-- Use a specified starting edge for the actual right coefficient. -/
def Choices.rightCoefficients (C : Choices F j a v hv) :=
  rightCoefficientsOf a j v C.starting (reverseBoundaryPair_endpoints W _ _ C.starting_pair).1
    (reverseBoundaryPair_endpoints W _ _ C.starting_pair).2

variable {b : A} (f : a ⟶ b) {w : Fin (((codes L).obj b).len + 1)}
variable {hw : orderMap (F.collapse.app b).map w = j.val}
variable (h : orderMap ((codes L).map f).map v = w)
variable (C : Choices F j b w hw)

private abbrev gf := (codes L).map f
private abbrev rf := (k (L := L)).map f

include h in
private theorem restrictEnding :
    std.map (usedInclusion F a j v hv) ≫ (std.map (rf f) ≫ C.ending) =
      identityOnFace W (z j) ∧
      (std.map (rf f) ≫ C.ending) ≫ endpointArrow W =
        boundaryPair W (oldVertexRow (L := L) a v) (z j) := by
  have hh := restrict_edge W (usedInclusion F b j w hw)
    (oldVertexRow (L := L) b w) (z j)
    (usedInclusion F a j v hv) (usedOperator F j f v w hv hw h) (rf f)
    (usedOperator_inclusion F j f v w hv hw h) C.ending_face C.ending_pair
  rw [oldVertexRow_map F j f v w hv hw h] at hh
  exact hh

include h in
private theorem restrictStarting :
    std.map (usedInclusion F a j v hv) ≫ (std.map (rf f) ≫ C.starting) =
      identityOnFace W (z j) ∧
      (std.map (rf f) ≫ C.starting) ≫ endpointArrow W =
        reverseBoundaryPair W (oldVertexRow (L := L) a v) (z j) := by
  have hh := restrict_reverse_edge W (usedInclusion F b j w hw)
    (oldVertexRow (L := L) b w) (z j)
    (usedInclusion F a j v hv) (usedOperator F j f v w hv hw h) (rf f)
    (usedOperator_inclusion F j f v w hv hw h) C.starting_face C.starting_pair
  rw [oldVertexRow_map F j f v w hv hw h] at hh
  exact hh

/-- Restrict a pair of choices by the exact original coefficient operator. -/
def restrictChoices : Choices F j a v hv where
  ending := std.map (rf f) ≫ C.ending
  starting := std.map (rf f) ≫ C.starting
  ending_face := (restrictEnding F j f (hv := hv) h C).1
  starting_face := (restrictStarting F j f (hv := hv) h C).1
  ending_pair := (restrictEnding F j f (hv := hv) h C).2
  starting_pair := (restrictStarting F j f (hv := hv) h C).2

section Laws

/-- Restriction along the identity cut operator fixes both complete edge choices. -/
theorem restrictChoices_id (D : Choices F j a v hv)
    (h₀ : orderMap ((codes L).map (𝟙 a)).map v = v) :
    restrictChoices F j (𝟙 a) (hv := hv) h₀ D = D := by
  apply choices_ext F j
  · change std.map ((k (L := L)).map (𝟙 a)) ≫ D.ending = D.ending
    rw [(k (L := L)).map_id a, std.map_id, Category.id_comp]
  · change std.map ((k (L := L)).map (𝟙 a)) ≫ D.starting = D.starting
    rw [(k (L := L)).map_id a, std.map_id, Category.id_comp]

variable {c : A} (g : b ⟶ c) {u : Fin (((codes L).obj c).len + 1)}
variable {hu : orderMap (F.collapse.app c).map u = j.val}
variable (hg : orderMap ((codes L).map g).map w = u)
variable (hfg : orderMap ((codes L).map (f ≫ g)).map v = u)

/-- The two full edge choices restrict contravariantly under composition. -/
theorem restrictChoices_comp (D : Choices F j c u hu) :
    restrictChoices F j f (hv := hv) h (restrictChoices F j g (hv := hw) hg D) =
      restrictChoices F j (f ≫ g) (hv := hv) hfg D := by
  apply choices_ext F j
  · change std.map ((k (L := L)).map f) ≫
      (std.map ((k (L := L)).map g) ≫ D.ending) =
        std.map ((k (L := L)).map (f ≫ g)) ≫ D.ending
    rw [(k (L := L)).map_comp f g, std.map_comp, Category.assoc]
  · change std.map ((k (L := L)).map f) ≫
      (std.map ((k (L := L)).map g) ≫ D.starting) =
        std.map ((k (L := L)).map (f ≫ g)) ≫ D.starting
    rw [(k (L := L)).map_comp f g, std.map_comp, Category.assoc]

end Laws

private theorem identityRestriction :
    diagramMappingPrecomp (discreteFree.{0}.map (𝟙 E.toSSet)) W = 𝟙 _ := by
  have he : discreteFree.{0}.map (𝟙 E.toSSet) = 𝟙 _ := discreteFree.{0}.map_id _
  rw [he, diagramMappingPrecomp_id]

/-- Compatible pairs give a literal morphism of the decorated left labels. -/
def leftLabelMap :=
  JTComposedPrismLabelOperators.indexMap
    (Choices.leftCoefficients F j (restrictChoices F j f (hv := hv) h C))
    (Choices.leftCoefficients F j C)
    (cutLeftHom (gf f) v w h) (𝟙 E) (rf f)
    (leftCoefficient_map (L := L) f v w h)
    (by
      change (std.map (rf f) ≫ C.ending) ≫ edgeLabelFromRow W =
        std.map (rf f) ≫ (C.ending ≫ edgeLabelFromRow W) ≫
          diagramMappingPrecomp (discreteFree.{0}.map (𝟙 E.toSSet)) W
      rw [identityRestriction, Category.comp_id, Category.assoc])

/-- The same compatible pairs give a literal morphism of the decorated right labels. -/
def rightLabelMap :=
  JTComposedPrismLabelOperators.indexMap
    (Choices.rightCoefficients F j (restrictChoices F j f (hv := hv) h C))
    (Choices.rightCoefficients F j C)
    (𝟙 E) (cutRightHom (gf f) v w h) (rf f)
    (by
      change (std.map (rf f) ≫ C.starting) ≫ edgeLabelFromRow W =
        std.map (rf f) ≫ (C.starting ≫ edgeLabelFromRow W) ≫
          diagramMappingPrecomp (discreteFree.{0}.map (𝟙 E.toSSet)) W
      rw [identityRestriction, Category.comp_id, Category.assoc])
    (rightCoefficient_map (L := L) f v w h)

end
end DaggerModels.PartII.JTActualJointSideChoiceTransport
