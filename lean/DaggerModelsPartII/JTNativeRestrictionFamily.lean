import DaggerModelsPartII.JTNativeRestrictionLabels
import DaggerModelsPartII.JTParametrizedTargetFamilyComparison

/-!
Pull a whole original parameter family back along ALL native restrictions,
including commuting squares over every original base arrow. The old family law
supplies full mixed parameter naturality, and the existing native pullback raw
lemma supplies the unchanged fixed-target raw equation. No natural lift or raw
condition is added. Normalized corrected-cut data are still separate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeRestrictionFamily

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family codes)
open JTNativeRestrictionLabels (Index labels degree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

/-- The complete old time varies along its original base operator. -/
abbrev pulledTime := JTNativeRestrictionIndex.projection (codes L) ⋙ time

/-- The original native collapse after the actual restriction. -/
def collapse : codes (labels L) ⟶ (Functor.const (Index L)).obj Q.code :=
  JTParametrizedTargetFamilyComparison.native (JTNativeRestrictionLabels.toOriginal L) ≫
    (F.precomp (JTNativeRestrictionIndex.projection (codes L))).collapse

/-- The full old parameter is restricted only in its native coordinate. -/
abbrev parameter (a : Index L) :=
  (a.hom.map ⊗ₘ 𝟙 (J.obj (time.obj a.right))) ≫ F.parameter a.right

private theorem coefficient_section :
    (𝟙 (JTParametrizedTargetFamilyComparison.degrees
      (JTNativeRestrictionIndex.projection (codes L) ⋙ L))) ≫
        JTParametrizedTargetFamilyComparison.coefficient
          (L := labels L) (M := JTNativeRestrictionIndex.projection (codes L) ⋙ L)
          (JTNativeRestrictionLabels.toOriginal L) =
      𝟙 (JTParametrizedTargetFamilyComparison.degrees
        (JTNativeRestrictionIndex.projection (codes L) ⋙ L)) := by
  apply NatTrans.ext
  funext a
  rfl

private def pulledFamily : Family Q (labels L) (pulledTime (L := L) (time := time)) :=
  JTParametrizedTargetFamilyComparison.pullback
    (L := labels L) (M := JTNativeRestrictionIndex.projection (codes L) ⋙ L)
    (JTNativeRestrictionLabels.toOriginal L)
    (F.precomp (JTNativeRestrictionIndex.projection (codes L))) (𝟙 _)
    (coefficient_section (L := L))

private theorem pulled_parameter (a : Index L) :
    (pulledFamily F).parameter a = parameter F a := by
  change (a.hom.map ⊗ₘ 𝟙 (J.obj (time.obj a.right))) ≫
      F.parameter a.right ≫ J.map (𝟙 _) = parameter F a
  rw [J.map_id, Category.comp_id]

/-- The original family law and the literal native square give mixed
parameter naturality, retaining the whole original time and coefficient degree. -/
theorem parameter_map {a b : Index L} (f : a ⟶ b) :
    (f.left.map ⊗ₘ J.map (time.map f.right)) ≫ parameter F b =
      parameter F a ≫ J.map ((degree L).map f.right) := by
  have h := (pulledFamily F).parameter_map f
  change (f.left.map ⊗ₘ J.map (time.map f.right)) ≫ (pulledFamily F).parameter b =
    (pulledFamily F).parameter a ≫ J.map ((degree L).map f.right) at h
  rw [pulled_parameter, pulled_parameter] at h
  exact h

/-- One strict full fixed-Q family over all native restrictions and all
original base operators, derived entirely from the given old family. -/
def family : Family Q (labels L) (pulledTime (L := L) (time := time)) :=
  pulledFamily F

/-- The actual restriction comparison obeys the full native and parameter
squares required by the existing evaluation-comparison constructor. -/
theorem compatible : JTParametrizedTargetFamilyComparison.Compatible
    (L := labels L) (M := JTNativeRestrictionIndex.projection (codes L) ⋙ L)
    (JTNativeRestrictionLabels.toOriginal L) (𝟙 (pulledTime (L := L) (time := time)))
    (family F) (F.precomp (JTNativeRestrictionIndex.projection (codes L))) :=
  JTParametrizedTargetFamilyComparison.pullback_compatible
    (L := labels L) (M := JTNativeRestrictionIndex.projection (codes L) ⋙ L)
    (JTNativeRestrictionLabels.toOriginal L)
    (F.precomp (JTNativeRestrictionIndex.projection (codes L))) (𝟙 _)
    (coefficient_section (L := L))

/-- The derived family retains the literal original native collapse. -/
theorem family_collapse (a : Index L) :
    (family F).collapse.app a = a.hom ≫ F.collapse.app a.right := rfl

/-- The derived family retains the full original native pullback parameter. -/
theorem family_parameter (a : Index L) :
    (family F).parameter a = parameter F a := pulled_parameter F a

end
end DaggerModels.PartII.JTNativeRestrictionFamily
