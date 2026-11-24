import DaggerModelsPartII.JTGraphFactoredPresentation
import DaggerModelsPartII.JTGraphInterpolatedComparison
import DaggerModelsPartII.JTGraphTransportRaw
import DaggerModelsPartII.JTTargetCommaPullback
import DaggerModelsPartII.JTNativeNormalizationEpi
import OriginalFlagNormalizedBeadCharts

/-! Normalize a traversal and its specified native target map simultaneously. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification

namespace DaggerModels.PartII.JTPairedTargetNormalization

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma Traversal)
open BoundaryNecklaceComma (necklaceUnder toNative fromNative)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q) {S : NecklaceCode} (c : S ⟶ U.left.fiber.left)

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev P := (E (Q := Q)).obj U.left.base

private def pair : necklaceUnder.obj S ⟶ P U :=
  necklaceUnder.map c ≫ JTTargetCommaPullback.lift W x y Q U

private def nativePair := (toNative (P U)).obj (CostructuredArrow.mk (pair U c))

/-- The normalized traverse retains the nondegenerate beads of the map to the
actual pullback of the decorated cylinder and the specified native target. -/
def normalized := normOver (nativePair U c)

theorem normalized_beads_nondegenerate (b : (normalized U c).code.Bead) :
    beadElement (normalized U c) b ∈ (P U).right.nonDegenerate b.length :=
  normOver_beads_nondegenerate (nativePair U c) b

/-- The original collapse onto the paired normalized code. -/
def quotient : S ⟶ (normalized U c).code :=
  (originalNormalization (nativePair U c)).hom

instance quotient_epi : Epi (quotient U c).map :=
  JTNativeNormalizationEpi.originalNormalization_epi (nativePair U c)

private abbrev pairedTraversal :=
  ((fromNative (P U)).obj (normalized U c)).hom

private theorem paired_factor :
    necklaceUnder.map (quotient U c) ≫ pairedTraversal U c = pair U c := by
  apply Under.UnderMorphism.ext
  exact originalNormalization_triangle (nativePair U c)

/-- Project the whole normalized traversal to the actual label cylinder. -/
def decorated : Traversal U (normalized U c).code :=
  pairedTraversal U c ≫ JTTargetCommaPullback.fst W x y Q U.left.base

/-- Project the same normalized traversal to the unchanged native target. -/
def native : (normalized U c).code ⟶ Q.code :=
  JTTargetCommaPullback.nativeArrow
    (pairedTraversal U c ≫ JTTargetCommaPullback.snd W x y Q U.left.base)

theorem decorated_factor :
    (quotient U c).map ≫ (decorated U c).right = c.map ≫ U.left.fiber.hom.right := by
  have h : necklaceUnder.map (quotient U c) ≫ decorated U c =
      necklaceUnder.map c ≫ U.left.fiber.hom := by
    rw [decorated, ← Category.assoc, paired_factor, pair, Category.assoc,
      JTTargetCommaPullback.lift_fst]
  exact congrArg (fun f ↦ f.right) h

theorem native_factor : quotient U c ≫ native U c = c ≫ U.hom.hom := by
  apply NecklaceCode.Hom.ext
  have h : necklaceUnder.map (quotient U c) ≫
      (pairedTraversal U c ≫ JTTargetCommaPullback.snd W x y Q U.left.base) =
      necklaceUnder.map c ≫ necklaceUnder.map U.hom.hom := by
    rw [← Category.assoc, paired_factor, pair, Category.assoc, JTTargetCommaPullback.lift_snd]
  exact congrArg (fun f ↦ f.right) h

/-- Both whole factorization equations produce a point of the original comma. -/
def object : TargetComma Q :=
  JTGraphFactoredPresentation.object U c (quotient U c) (decorated U c) (native U c)
    (decorated_factor U c) (native_factor U c)

/-- At the identity collapse the paired normalization is an actual arrow
from the original comma object over the same target. -/
def comparison : U ⟶ object U (𝟙 _) := by
  let V := object U (𝟙 _)
  let g := quotient U (𝟙 _)
  refine CostructuredArrow.homMk (f := U) (f' := V) ⟨𝟙 _, CostructuredArrow.homMk g ?_⟩ ?_
  · apply Under.UnderMorphism.ext
    change g.map ≫ (decorated U (𝟙 _)).right =
      (U.left.fiber.hom ≫ (DecoratedCylinderNecklacePresentation.underDiagram W x y).map
        (𝟙 U.left.base)).right
    rw [decorated_factor, (DecoratedCylinderNecklacePresentation.underDiagram W x y).map_id]
    change (𝟙 _) ≫ U.left.fiber.hom.right = U.left.fiber.hom.right ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · apply NecklacesOver.Hom.ext
    change g ≫ native U (𝟙 _) = U.hom.hom
    rw [native_factor, Category.id_comp]

open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict)
open JTGraphRestrictionRaw (predecessor commaRestriction)
open JTGraphTransportRaw (commaTransport)

/-- Transport to the normalized paired target before changing the graph
parameter. The independently chosen parameters need only have the same
native collapse after restriction. -/
theorem exists_common_graph_zigzags :
    ∃ E : GraphLift (object U (𝟙 _)).left (object U (𝟙 _)).left.fiber.left,
      E.collapse = 𝟙 _ ∧ ∀ {T : NecklaceCode} (D : GraphLift U.left T),
        Relation.EqvGen (fun P P' : TargetComma Q ↦ Nonempty (P ⟶ P'))
          (predecessor D) (predecessor E) := by
  let V := object U (𝟙 _)
  let a := comparison U
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift V.left
  refine ⟨E, hE, ?_⟩
  intro T D
  let P := D.transport a.left
  let c := P.collapse
  let E' := restrict E c
  have hE' : E'.collapse = c := by
    change c ≫ E.collapse = c
    rw [hE, Category.comp_id]
  let F : Fin 2 → GraphLift V.left T := Fin.cases P (fun _ ↦ E')
  have hF (i : Fin 2) : (F i).collapse = c := by
    fin_cases i
    · rfl
    · exact hE'
  let h := JTGraphInterpolatedComparison.comparison_zigzag (n := ⦋1⦌) c F hF 0 1
  exact .trans _ _ _ (.rel _ _ ⟨commaTransport D a⟩)
    (.trans _ _ _ h (.rel _ _ ⟨commaRestriction E c⟩))

end
end DaggerModels.PartII.JTPairedTargetNormalization

