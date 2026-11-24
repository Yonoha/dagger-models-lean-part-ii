import DaggerModelsPartII.JTThreePieceMiddleSupportDiagram
import DaggerModelsPartII.JTTwoEndpointChoiceCover
import DaggerModelsPartII.JTTwoEndpointChoicePrism
import DaggerModelsPartII.JTOrdinalInverseFaceDiagram
import DaggerModelsPartII.JTActualJointChoiceChainGraph

/-!
All higher relative edge choices at the naturally used middle support.
`JTTwoEndpointChoiceCover` supplies a weak cover of paired edges;
`JTTwoEndpointChoicePrism` supplies their mixed natural full prisms;
`TimePrismChainDiagram` synchronizes coefficient and choice degrees; and
`JTOrdinalInverseFaceDiagram` carries the full used face to that common chain.
The old surroundings family and fixed target joint remain explicit inputs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTThreePieceMiddleEdgeChoices

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I] (W : Source)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (K : I ⥤ SimplexCategory)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (time : I ⥤ SimplexCategory)
variable (oldTimed : Family Q (JTChosenSeamOldComparison.oldFamily W K f O).labels time)
variable (j : Joint Q.code)
variable (hj : ∀ a : I, orderMap (oldTimed.collapse.app a).map
  (JTThreePieceMiddleSupport.middleVertex P R a) = j.val)

private abbrev S := JTThreePieceMiddleSupportDiagram.support
  W K f O Q time oldTimed j hj
private abbrev u := JTThreePieceMiddleSupportDiagram.u
  W K f O Q time oldTimed j hj
private abbrev hs := JTThreePieceMiddleSupportDiagram.supported_row
  W K f O Q time oldTimed j hj

/-- Full paired choice spaces, retaining all higher simplices and operators. -/
abbrev spaces := JTTwoEndpointChoiceCover.spaces W
  (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
  f f (JTParametrizedBeadGraph.jointCoefficient j) (hs W K f O Q time oldTimed j hj)
  (hs W K f O Q time oldTimed j hj)

/-- The complete paired forward and reverse edge-choice cover. -/
abbrev Cover := JTTwoEndpointChoiceCover.Cover W
  (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
  f f (JTParametrizedBeadGraph.jointCoefficient j) (hs W K f O Q time oldTimed j hj)
  (hs W K f O Q time oldTimed j hj)

/-- Forget edge choices while retaining every original old-family arrow. -/
abbrev projection : Cover W K f O Q time oldTimed j hj ⥤ I :=
  JTTwoEndpointChoiceCover.projection W
    (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
    f f (JTParametrizedBeadGraph.jointCoefficient j) (hs W K f O Q time oldTimed j hj)
    (hs W K f O Q time oldTimed j hj)

/-- The higher edge-choice simplex degree. -/
abbrev choiceTime : Cover W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  JTTwoEndpointChoiceCover.choiceTime W
    (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
    f f (JTParametrizedBeadGraph.jointCoefficient j) (hs W K f O Q time oldTimed j hj)
    (hs W K f O Q time oldTimed j hj)

/-- The old coefficient degree on the complete choice cover. -/
abbrev coefficient : Cover W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  projection W K f O Q time oldTimed j hj ⋙ K

/-- The paired full choice cover is weak under injective fibrancy of `W`. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection W K f O Q time oldTimed j hj)) :=
  JTTwoEndpointChoiceCover.projection_weak W
    (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
    f f (JTParametrizedBeadGraph.jointCoefficient j) (hs W K f O Q time oldTimed j hj)
    (hs W K f O Q time oldTimed j hj) hW
    (JTThreePieceMiddleSupportDiagram.u_mono W K f O Q time oldTimed j hj)

/-- The full coefficient and higher-choice prism before common chains. -/
abbrev prisms := JTTwoEndpointChoicePrism.prisms W
  (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
  f f (JTParametrizedBeadGraph.jointCoefficient j)
  (hs W K f O Q time oldTimed j hj)
  (hs W K f O Q time oldTimed j hj)

/-- The forward edge runs from the supplied row to the joint. -/
abbrev forwardPrism := JTTwoEndpointChoicePrism.back W
  (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
  f f (JTParametrizedBeadGraph.jointCoefficient j)
  (hs W K f O Q time oldTimed j hj)
  (hs W K f O Q time oldTimed j hj)

/-- The reverse edge runs from the joint to the supplied row. -/
abbrev reversePrism := JTTwoEndpointChoicePrism.front W
  (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
  f f (JTParametrizedBeadGraph.jointCoefficient j)
  (hs W K f O Q time oldTimed j hj)
  (hs W K f O Q time oldTimed j hj)

/-- One full chain synchronizes the old coefficient and all higher edge choices. -/
abbrev Index := TimePrismChainDiagram.Index
  (coefficient W K f O Q time oldTimed j hj)
  (choiceTime W K f O Q time oldTimed j hj)

/-- Retain the complete paired edge-choice simplex. -/
abbrev chainBase : Index W K f O Q time oldTimed j hj ⥤
    Cover W K f O Q time oldTimed j hj :=
  TimePrismChainDiagram.base
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj)

/-- The common coefficient-choice ordinal. -/
abbrev ordinals : Index W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  TimePrismChainDiagram.ordinals
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj)

/-- The surjective projection to the unchanged old coefficient degree. -/
abbrev toOld : ordinals W K f O Q time oldTimed j hj ⟶
    chainBase W K f O Q time oldTimed j hj ⋙
      coefficient W K f O Q time oldTimed j hj :=
  TimePrismChainDiagram.coeffProjection
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj)

/-- The projection to the complete higher edge-choice degree. -/
abbrev toChoice : ordinals W K f O Q time oldTimed j hj ⟶
    chainBase W K f O Q time oldTimed j hj ⋙
      choiceTime W K f O Q time oldTimed j hj :=
  TimePrismChainDiagram.timeProjection
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj)

/-- The original old-family index, after both full covers. -/
abbrev toOriginal : Index W K f O Q time oldTimed j hj ⥤ I :=
  chainBase W K f O Q time oldTimed j hj ⋙
    projection W K f O Q time oldTimed j hj

/-- The composite all-choice common-chain cover is nerve weak. -/
theorem toOriginal_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toOriginal W K f O Q time oldTimed j hj)) := by
  haveI : WeakEquivalence (nerveMap (chainBase W K f O Q time oldTimed j hj)) :=
    TimePrismChainProjection.projection_weak _ _
  haveI : WeakEquivalence (nerveMap (projection W K f O Q time oldTimed j hj)) :=
    projection_weak W K f O Q time oldTimed j hj hW
  change WeakEquivalence
    (nerveMap (chainBase W K f O Q time oldTimed j hj) ≫
      nerveMap (projection W K f O Q time oldTimed j hj))
  infer_instance

/-- The literal common-chain chart into the full edge-choice prism. -/
abbrev chainChart : ordinals W K f O Q time oldTimed j hj ⋙ std ⟶
    chainBase W K f O Q time oldTimed j hj ⋙
      prisms W K f O Q time oldTimed j hj :=
  JTActualJointChoiceChainGraph.chart
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj)

/-- A natural forward edge on every full common-chain simplex. -/
def e : ordinals W K f O Q time oldTimed j hj ⋙ std ⟶
    (Functor.const (Index W K f O Q time oldTimed j hj)).obj (row W ⦋1⦌) :=
  chainChart W K f O Q time oldTimed j hj ≫
    Functor.whiskerLeft (chainBase W K f O Q time oldTimed j hj)
      (forwardPrism W K f O Q time oldTimed j hj)

/-- A natural reverse edge on the same full common-chain simplices. -/
def s : ordinals W K f O Q time oldTimed j hj ⋙ std ⟶
    (Functor.const (Index W K f O Q time oldTimed j hj)).obj (row W ⦋1⦌) :=
  chainChart W K f O Q time oldTimed j hj ≫
    Functor.whiskerLeft (chainBase W K f O Q time oldTimed j hj)
      (reversePrism W K f O Q time oldTimed j hj)

/-- The supplied seam row pulled back along the literal old-degree projection. -/
def seamRow : ordinals W K f O Q time oldTimed j hj ⋙ std ⟶
    (Functor.const (Index W K f O Q time oldTimed j hj)).obj (row W ⦋0⦌) :=
  Functor.whiskerRight (toOld W K f O Q time oldTimed j hj) std ≫
    Functor.whiskerLeft (toOriginal W K f O Q time oldTimed j hj) f

private def oldSupport : Index W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  toOriginal W K f O Q time oldTimed j hj ⋙ S W K f O Q time oldTimed j hj

private def oldDegree : Index W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  toOriginal W K f O Q time oldTimed j hj ⋙ K

private def oldIncl : oldSupport W K f O Q time oldTimed j hj ⟶
    oldDegree W K f O Q time oldTimed j hj :=
  Functor.whiskerLeft (toOriginal W K f O Q time oldTimed j hj)
    (u W K f O Q time oldTimed j hj)

private def alpha : ordinals W K f O Q time oldTimed j hj ⟶
    oldDegree W K f O Q time oldTimed j hj :=
  toOld W K f O Q time oldTimed j hj

private theorem oldIncl_mono (c : Index W K f O Q time oldTimed j hj) :
    Mono ((oldIncl W K f O Q time oldTimed j hj).app c) :=
  JTThreePieceMiddleSupportDiagram.u_mono W K f O Q time oldTimed j hj
    ((toOriginal W K f O Q time oldTimed j hj).obj c)

private theorem alpha_surjective (c : Index W K f O Q time oldTimed j hj) :
    Function.Surjective ((alpha W K f O Q time oldTimed j hj).app c).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective
    (coefficient W K f O Q time oldTimed j hj)
    (choiceTime W K f O Q time oldTimed j hj) c

/-- The full inverse image of the original used support on every common chain. -/
abbrev support : Index W K f O Q time oldTimed j hj ⥤ SimplexCategory :=
  JTOrdinalInverseFaceDiagram.supportDiagram
    (oldSupport W K f O Q time oldTimed j hj)
    (oldDegree W K f O Q time oldTimed j hj)
    (ordinals W K f O Q time oldTimed j hj)
    (oldIncl W K f O Q time oldTimed j hj)
    (alpha W K f O Q time oldTimed j hj)
    (oldIncl_mono W K f O Q time oldTimed j hj)
    (alpha_surjective W K f O Q time oldTimed j hj)

/-- The actual common-chain support inclusion. -/
abbrev incl : support W K f O Q time oldTimed j hj ⟶
    ordinals W K f O Q time oldTimed j hj :=
  JTOrdinalInverseFaceDiagram.inclNat
    (oldSupport W K f O Q time oldTimed j hj)
    (oldDegree W K f O Q time oldTimed j hj)
    (ordinals W K f O Q time oldTimed j hj)
    (oldIncl W K f O Q time oldTimed j hj)
    (alpha W K f O Q time oldTimed j hj)
    (oldIncl_mono W K f O Q time oldTimed j hj)
    (alpha_surjective W K f O Q time oldTimed j hj)

/-- The natural coordinate from the common-chain support to the old support. -/
abbrev toOldFace : support W K f O Q time oldTimed j hj ⟶
    oldSupport W K f O Q time oldTimed j hj :=
  JTOrdinalInverseFaceDiagram.toFaceNat
    (oldSupport W K f O Q time oldTimed j hj)
    (oldDegree W K f O Q time oldTimed j hj)
    (ordinals W K f O Q time oldTimed j hj)
    (oldIncl W K f O Q time oldTimed j hj)
    (alpha W K f O Q time oldTimed j hj)
    (oldIncl_mono W K f O Q time oldTimed j hj)
    (alpha_surjective W K f O Q time oldTimed j hj)

/-- The exact full inverse-image square retains the old coefficient projection. -/
theorem support_square :
    toOldFace W K f O Q time oldTimed j hj ≫
      oldIncl W K f O Q time oldTimed j hj =
    incl W K f O Q time oldTimed j hj ≫
      alpha W K f O Q time oldTimed j hj :=
  JTOrdinalInverseFaceDiagram.natural_square
    (oldSupport W K f O Q time oldTimed j hj)
    (oldDegree W K f O Q time oldTimed j hj)
    (ordinals W K f O Q time oldTimed j hj)
    (oldIncl W K f O Q time oldTimed j hj)
    (alpha W K f O Q time oldTimed j hj)
    (oldIncl_mono W K f O Q time oldTimed j hj)
    (alpha_surjective W K f O Q time oldTimed j hj)

/-- The common-chain support remains a literal subordinal. -/
theorem incl_mono (c : Index W K f O Q time oldTimed j hj) :
    Mono ((incl W K f O Q time oldTimed j hj).app c) :=
  JTOrdinalInverseFaceDiagram.incl_mono
    (oldSupport W K f O Q time oldTimed j hj)
    (oldDegree W K f O Q time oldTimed j hj)
    (ordinals W K f O Q time oldTimed j hj)
    (oldIncl W K f O Q time oldTimed j hj)
    (alpha W K f O Q time oldTimed j hj)
    (oldIncl_mono W K f O Q time oldTimed j hj)
    (alpha_surjective W K f O Q time oldTimed j hj) c

/-- The seam row is the joint row on the entire common-chain used support. -/
theorem seamRow_onSupport (c : Index W K f O Q time oldTimed j hj) :
    std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      (seamRow W K f O Q time oldTimed j hj).app c =
        SSet.stdSimplex.isTerminalObj₀.from _ ≫
          vertexPoint W (JTParametrizedBeadGraph.jointCoefficient j) := by
  have h := congrArg (fun η ↦ η.app c)
    (support_square W K f O Q time oldTimed j hj)
  change (toOldFace W K f O Q time oldTimed j hj).app c ≫
      (u W K f O Q time oldTimed j hj).app
        ((toOriginal W K f O Q time oldTimed j hj).obj c) =
    (incl W K f O Q time oldTimed j hj).app c ≫
      (toOld W K f O Q time oldTimed j hj).app c at h
  change std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      std.map ((toOld W K f O Q time oldTimed j hj).app c) ≫
        f.app ((toOriginal W K f O Q time oldTimed j hj).obj c) = _
  calc
    _ = std.map ((toOldFace W K f O Q time oldTimed j hj).app c) ≫
        std.map ((u W K f O Q time oldTimed j hj).app
          ((toOriginal W K f O Q time oldTimed j hj).obj c)) ≫
          f.app ((toOriginal W K f O Q time oldTimed j hj).obj c) := by
      rw [← Category.assoc, ← std.map_comp, ← h, std.map_comp, Category.assoc]
    _ = std.map ((toOldFace W K f O Q time oldTimed j hj).app c) ≫
        (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          vertexPoint W (JTParametrizedBeadGraph.jointCoefficient j)) := by
      rw [JTThreePieceMiddleSupportDiagram.supported_row
        W K f O Q time oldTimed j hj]
      rfl
    _ = _ := by
      have ht : std.map ((toOldFace W K f O Q time oldTimed j hj).app c) ≫
          SSet.stdSimplex.isTerminalObj₀.from _ =
          SSet.stdSimplex.isTerminalObj₀.from _ :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [← Category.assoc, ht]

/-- The chosen forward edge has endpoints `f` and the original joint. -/
theorem e_endpoints (c : Index W K f O Q time oldTimed j hj) :
    (e W K f O Q time oldTimed j hj).app c ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W
        ((seamRow W K f O Q time oldTimed j hj).app c)
        (JTParametrizedBeadGraph.jointCoefficient j) := by
  change (lift (std.map ((toOld W K f O Q time oldTimed j hj).app c))
      (std.map ((toChoice W K f O Q time oldTimed j hj).app c)) ≫
        (forwardPrism W K f O Q time oldTimed j hj).app
          ((chainBase W K f O Q time oldTimed j hj).obj c)) ≫ endpointArrow W = _
  rw [Category.assoc, JTTwoEndpointChoicePrism.back_endpoints]
  calc
    _ = std.map ((toOld W K f O Q time oldTimed j hj).app c) ≫
        JTJointEndpointRelativeLift.boundaryPair W
          (f.app ((toOriginal W K f O Q time oldTimed j hj).obj c))
          (JTParametrizedBeadGraph.jointCoefficient j) := by
      rw [← Category.assoc]
      exact congrArg (fun t ↦ t ≫ JTJointEndpointRelativeLift.boundaryPair W
        (f.app ((toOriginal W K f O Q time oldTimed j hj).obj c))
        (JTParametrizedBeadGraph.jointCoefficient j))
        (lift_fst _ _)
    _ = _ := JTJointEndpointRelativeLift.boundaryPair_natural W
      (JTParametrizedBeadGraph.jointCoefficient j)
      ((toOld W K f O Q time oldTimed j hj).app c) _

/-- The reverse edge has the same endpoints in the opposite order. -/
theorem s_endpoints (c : Index W K f O Q time oldTimed j hj) :
    (s W K f O Q time oldTimed j hj).app c ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W
        ((seamRow W K f O Q time oldTimed j hj).app c)
        (JTParametrizedBeadGraph.jointCoefficient j) := by
  change (lift (std.map ((toOld W K f O Q time oldTimed j hj).app c))
      (std.map ((toChoice W K f O Q time oldTimed j hj).app c)) ≫
        (reversePrism W K f O Q time oldTimed j hj).app
          ((chainBase W K f O Q time oldTimed j hj).obj c)) ≫ endpointArrow W = _
  rw [Category.assoc, JTTwoEndpointChoicePrism.front_endpoints]
  calc
    _ = std.map ((toOld W K f O Q time oldTimed j hj).app c) ≫
        JTJointEndpointRelativeLift.reverseBoundaryPair W
          (f.app ((toOriginal W K f O Q time oldTimed j hj).obj c))
          (JTParametrizedBeadGraph.jointCoefficient j) := by
      rw [← Category.assoc]
      exact congrArg (fun t ↦ t ≫ JTJointEndpointRelativeLift.reverseBoundaryPair W
        (f.app ((toOriginal W K f O Q time oldTimed j hj).obj c))
        (JTParametrizedBeadGraph.jointCoefficient j))
        (lift_fst _ _)
    _ = _ := JTJointEndpointRelativeLift.reverseBoundaryPair_natural W
      (JTParametrizedBeadGraph.jointCoefficient j)
      ((toOld W K f O Q time oldTimed j hj).app c) _

/-- The forward edge is the identity on the entire inverse-image used face. -/
theorem e_onSupport (c : Index W K f O Q time oldTimed j hj) :
    std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      (e W K f O Q time oldTimed j hj).app c =
        JTJointEndpointRelativeLift.identityOnFace W
          (JTParametrizedBeadGraph.jointCoefficient j) := by
  have h := congrArg (fun η ↦ η.app c)
    (support_square W K f O Q time oldTimed j hj)
  change (toOldFace W K f O Q time oldTimed j hj).app c ≫
      (u W K f O Q time oldTimed j hj).app
        ((toOriginal W K f O Q time oldTimed j hj).obj c) =
    (incl W K f O Q time oldTimed j hj).app c ≫
      (toOld W K f O Q time oldTimed j hj).app c at h
  change std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      lift (std.map ((toOld W K f O Q time oldTimed j hj).app c))
        (std.map ((toChoice W K f O Q time oldTimed j hj).app c)) ≫
          (forwardPrism W K f O Q time oldTimed j hj).app
            ((chainBase W K f O Q time oldTimed j hj).obj c) = _
  exact JTTwoEndpointChoicePrism.back_chain_face W
    (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
    f f (JTParametrizedBeadGraph.jointCoefficient j)
    (hs W K f O Q time oldTimed j hj)
    (hs W K f O Q time oldTimed j hj)
    ((chainBase W K f O Q time oldTimed j hj).obj c)
    ((toOld W K f O Q time oldTimed j hj).app c)
    ((toChoice W K f O Q time oldTimed j hj).app c)
    ((incl W K f O Q time oldTimed j hj).app c)
    ((toOldFace W K f O Q time oldTimed j hj).app c) h.symm

/-- The reverse edge is the identity on the same full inverse-image face. -/
theorem s_onSupport (c : Index W K f O Q time oldTimed j hj) :
    std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      (s W K f O Q time oldTimed j hj).app c =
        JTJointEndpointRelativeLift.identityOnFace W
          (JTParametrizedBeadGraph.jointCoefficient j) := by
  have h := congrArg (fun η ↦ η.app c)
    (support_square W K f O Q time oldTimed j hj)
  change (toOldFace W K f O Q time oldTimed j hj).app c ≫
      (u W K f O Q time oldTimed j hj).app
        ((toOriginal W K f O Q time oldTimed j hj).obj c) =
    (incl W K f O Q time oldTimed j hj).app c ≫
      (toOld W K f O Q time oldTimed j hj).app c at h
  change std.map ((incl W K f O Q time oldTimed j hj).app c) ≫
      lift (std.map ((toOld W K f O Q time oldTimed j hj).app c))
        (std.map ((toChoice W K f O Q time oldTimed j hj).app c)) ≫
          (reversePrism W K f O Q time oldTimed j hj).app
            ((chainBase W K f O Q time oldTimed j hj).obj c) = _
  exact JTTwoEndpointChoicePrism.front_chain_face W
    (S W K f O Q time oldTimed j hj) K (u W K f O Q time oldTimed j hj)
    f f (JTParametrizedBeadGraph.jointCoefficient j)
    (hs W K f O Q time oldTimed j hj)
    (hs W K f O Q time oldTimed j hj)
    ((chainBase W K f O Q time oldTimed j hj).obj c)
    ((toOld W K f O Q time oldTimed j hj).app c)
    ((toChoice W K f O Q time oldTimed j hj).app c)
    ((incl W K f O Q time oldTimed j hj).app c)
    ((toOldFace W K f O Q time oldTimed j hj).app c) h.symm

end
end DaggerModels.PartII.JTThreePieceMiddleEdgeChoices
