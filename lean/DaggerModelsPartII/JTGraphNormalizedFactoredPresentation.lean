import DaggerModelsPartII.JTGraphBeadBoundaryReflection
import DaggerModelsPartII.JTGraphFactoredComparison
import DaggerModelsPartII.JTGraphFlankedBoundaryReflection
import DaggerModelsPartII.JTNativeNormalizationEpi
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import OriginalFlagNormalizedBeadCharts

/-!
# The normalized cylinder traversal over a monic native target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTGraphNormalizedFactoredPresentation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphRestrictionRaw (predecessor)
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphBeadBoundaryReflection
open JTNecklaceEndpointCylinder (cylinder value endpointInclusion)
open JTGraphNondegenerateBead (boundary_iff_constant graph_nondegenerate_bead_not_boundary
  bead_length_pos)
open JTGraphFactoredPresentation (TargetComma Traversal)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode}

private abbrev label := (underDiagram W x y).obj U.left.base

variable (c : S ⟶ U.left.fiber.left)

private def source :=
  (BoundaryNecklaceComma.toNative (label (U := U))).obj
    (CostructuredArrow.mk (BoundaryNecklaceComma.necklaceUnder.map c ≫ U.left.fiber.hom))

/-- The code of the usual nondegenerate-bead normalization of the exact cylinder map. -/
def normalizedCode : NecklaceCode := (normOver (source c)).code

/-- Use the original normalization map, with all simplicial degrees retained. -/
def quotient : S ⟶ normalizedCode c := (originalNormalization (source c)).hom

instance quotient_epi : Epi (quotient c).map :=
  JTNativeNormalizationEpi.originalNormalization_epi (source c)

/-- The normalized traversal stays over the original reduced cylinder and its boundary. -/
def traversal : Traversal U (normalizedCode c) :=
  ((BoundaryNecklaceComma.fromNative (label (U := U))).obj (normOver (source c))).hom

theorem traversal_factor :
    (quotient c).map ≫ (traversal c).right = c.map ≫ U.left.fiber.hom.right :=
  originalNormalization_triangle (source c)

private abbrev nativeTarget := c ≫ U.hom.hom
private abbrev descend := ((underCocone W x y).app U.left.base).right

/-- A prescribed factor of the native target map defines the normalized
object in the unchanged target comma. -/
def objectOfFactor (r : normalizedCode c ⟶ Q.code) (hr : quotient c ≫ r = nativeTarget c) :
    TargetComma Q :=
  JTGraphFactoredPresentation.object U c (quotient c) (traversal c) r (traversal_factor c) hr

/-- The normalized cylinder traversal reflects boundary on each full source
bead, independently of the factor used to retain the native target map. -/
theorem reflectsBeadBoundary_of_factor (r : normalizedCode c ⟶ Q.code)
    (hr : quotient c ≫ r = nativeTarget c) :
    ReflectsBeadBoundary (quotient c) (augmentationCode (objectOfFactor c r hr).left) := by
  let V := objectOfFactor c r hr
  let T := normalizedCode c
  let L := code U.left
  let k := degree U.left
  let f : T ⟶ L := augmentationCode V.left
  let u : T.toSSet ⟶ (value L).obj k := (traversal c).right
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift V.left
  have hs : lift f.map E.parameter ≫ (cylinder L).app k = u := by
    have h := E.comm
    change lift (E.collapse ≫ f).map E.parameter ≫ (cylinder L).app k =
      E.collapse.map ≫ u at h
    rw [hE, Category.id_comp] at h
    exact h.trans (Category.id_comp u)
  have noBoundary (b : T.Bead) :
      ¬ ∃ a : JTXiEndpointCollapse.boundary.obj (op ⦋b.length⦌),
        (endpointInclusion L).app (op ⦋b.length⦌) a =
          SSet.yonedaEquiv (T.beadSimplex b ≫ f.map) := by
    have hND : SSet.yonedaEquiv (T.beadSimplex b ≫ u) ∈
        ((value L).obj k).nonDegenerate b.length := normOver_beads_nondegenerate (source c) b
    have hND' : SSet.yonedaEquiv (T.beadSimplex b ≫
        (lift f.map E.parameter ≫ (cylinder L).app k)) ∈
        ((value L).obj k).nonDegenerate b.length := hs.symm ▸ hND
    exact graph_nondegenerate_bead_not_boundary f k E.parameter b (bead_length_pos b) hND'
  obtain ⟨F, hF, hG⟩ := JTNativeNormalizationEpi.originalNormalization_exists_flanked (source c)
  apply JTGraphFlankedBoundaryReflection.reflects_of_flanked F
    (NecklaceCode.Flag.map (quotient c) F) (quotient c) f rfl hF hG
  · intro b hb
    exact noBoundary b ((boundary_iff_constant L b.length _).mpr (Or.inl hb))
  · intro b hb
    exact noBoundary b ((boundary_iff_constant L b.length _).mpr (Or.inr hb))

/-- All choices of graph parameter on the same collapse admit an actual
comparison to one graph on the normalized traversal. -/
theorem exists_common_of_factor (r : normalizedCode c ⟶ Q.code)
    (hr : quotient c ≫ r = nativeTarget c) :
    ∃ E : GraphLift (objectOfFactor c r hr).left (normalizedCode c), E.collapse = 𝟙 _ ∧
      ∀ D : GraphLift U.left S, D.collapse = c →
        Nonempty (predecessor (U := U) D ⟶ predecessor (U := objectOfFactor c r hr) E) :=
  JTGraphFactoredComparison.exists_common c (quotient c) (traversal c) r
    (traversal_factor c) hr
    (graph_eq_of_reflectsBeadBoundary (quotient c) _ (reflectsBeadBoundary_of_factor c r hr)
      (degree U.left))

private theorem rawSquare : CommSq (nativeTarget c).map (quotient c).map Q.map
    ((traversal c).right ≫ descend (U := U)) := by
  constructor
  have hu : U.hom.hom.map ≫ Q.map = U.left.fiber.hom.right ≫ descend (U := U) := U.hom.w
  change (c.map ≫ U.hom.hom.map) ≫ Q.map =
    (quotient c).map ≫ (traversal c).right ≫ descend (U := U)
  calc
    _ = c.map ≫ U.hom.hom.map ≫ Q.map := Category.assoc _ _ _
    _ = c.map ≫ U.left.fiber.hom.right ≫ descend (U := U) :=
      congrArg (fun h ↦ c.map ≫ h) hu
    _ = (c.map ≫ U.left.fiber.hom.right) ≫ descend (U := U) := (Category.assoc _ _ _).symm
    _ = ((quotient c).map ≫ (traversal c).right) ≫ descend (U := U) :=
      congrArg (fun h ↦ h ≫ descend (U := U)) (traversal_factor c).symm
    _ = _ := Category.assoc _ _ _

variable [Mono Q.map]

private instance rawSquare_hasLift : (rawSquare c).HasLift := by
  letI : StrongEpi (quotient c).map := strongEpi_of_epi _
  letI : HasLiftingProperty (quotient c).map Q.map := StrongEpi.llp Q.map
  infer_instance

/-- The map into the fixed target code descends along the actual normalization. -/
def targetFactor : normalizedCode c ⟶ Q.code where
  map := (rawSquare c).lift
  first := first_of_point _ (by
    rw [← pointAt_first_comp (quotient c), Category.assoc, (rawSquare c).fac_left,
      pointAt_first_comp])
  last := last_of_point _ (by
    rw [← pointAt_last_comp (quotient c), Category.assoc, (rawSquare c).fac_left,
      pointAt_last_comp])

theorem targetFactor_factor : quotient c ≫ targetFactor c = nativeTarget c :=
  NecklaceCode.Hom.ext (rawSquare c).fac_left

/-- The normalization yields an actual object over the same monic raw target. -/
def object : TargetComma Q :=
  JTGraphFactoredPresentation.object U c (quotient c) (traversal c) (targetFactor c)
    (traversal_factor c) (targetFactor_factor c)

/-- A boundary test on full source beads gives one common graph over the
canonical normalization, for every parameter on the original collapse. -/
theorem exists_common
    (hf : ReflectsBeadBoundary (quotient c) (augmentationCode (object c).left)) :
    ∃ E : GraphLift (object c).left (normalizedCode c), E.collapse = 𝟙 _ ∧
      ∀ D : GraphLift U.left S, D.collapse = c →
        Nonempty (predecessor (U := U) D ⟶ predecessor (U := object c) E) :=
  JTGraphFactoredComparison.exists_common c (quotient c) (traversal c) (targetFactor c)
    (traversal_factor c) (targetFactor_factor c)
    (graph_eq_of_reflectsBeadBoundary (quotient c) _ hf (degree U.left))

/-- A monic raw target gives one common normalized graph for each fixed collapse. -/
theorem exists_common_monic :
    ∃ E : GraphLift (object c).left (normalizedCode c), E.collapse = 𝟙 _ ∧
      ∀ D : GraphLift U.left S, D.collapse = c →
        Nonempty (predecessor (U := U) D ⟶ predecessor (U := object c) E) :=
  exists_common_of_factor c (targetFactor c) (targetFactor_factor c)

end

end DaggerModels.PartII.JTGraphNormalizedFactoredPresentation
