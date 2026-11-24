import DaggerModelsPartII.JTGraphParameterLiftSpace
import DaggerModelsPartII.JTGraphTransportNaturality
import DaggerModelsPartII.JTGraphWedgeIdentityLift

/-!
# Identity-collapse graph predecessors for arbitrary original necklaces
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphMultiBeadIdentityLift

open JTNecklaceEndpointCylinder JTInternalNecklaceGraphLift
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev C (T : NecklaceCode) (k : SimplexCategory) := (value T).obj k

variable {T : NecklaceCode} {k : SimplexCategory} {a b : (C T k).obj (op ⦋0⦌)}

private theorem prefix_parameter (P : NecklacesOver (C T k) a b) (n : ℕ)
    (hn : n ≤ beadCount P.code) :
    ∃ s : (orderedPrefix P n hn).source.code.toSSet ⟶ J.obj k,
      graph (orderedPrefix P n hn).source.map s = (orderedPrefix P n hn).source.map := by
  induction n with
  | zero =>
    let e : point.toSSet ≅ (Δ[0] : SSet.{0}) :=
      eqToIso (congrArg NecklaceCode.toSSet (code_zero_eq_point (single 0) rfl).symm) ≪≫
        singleIso 0
    exact exists_parameter_on_simplex e (orderedPrefix P 0 hn).source.map
  | succ n ih =>
    let i : Fin (beadCount P.code) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let c := jointBead P.code i
    let L := (orderedPrefix P n (Nat.le_of_succ_le hn)).source
    let R := sourceBeadOver P c
    obtain ⟨s, hs⟩ := ih (Nat.le_of_succ_le hn)
    obtain ⟨t, ht⟩ := exists_parameter_on_simplex (singleIso c.length) R.map
    exact JTGraphWedgeIdentityLift.exists_wedge_parameter L R s t hs ht

/-- The graph lifts the complete traversal on the original native necklace. -/
theorem exists_parameter (P : NecklacesOver (C T k) a b) :
    ∃ s : P.code.toSSet ⟶ J.obj k, graph P.map s = P.map := by
  obtain ⟨s, hs⟩ := prefix_parameter P (beadCount P.code) le_rfl
  change graph (assembledSource P).map s = (assembledSource P).map at hs
  let f := (sourceAssemblyIso P).inv
  refine ⟨f.hom.map ≫ s, ?_⟩
  have h := congrArg (fun u ↦ f.hom.map ≫ u) hs
  dsimp only at h
  rw [graph_comp, f.w] at h
  exact h

/-- With the native domain unchanged, the exact parameter space of every traversal
has a trivial fibration to a point. -/
theorem parameterSpace_toPoint_trivialFibration (P : NecklacesOver (C T k) a b) :
    trivialFibrations SSet.{0} (SSet.stdSimplex.isTerminalObj₀.from
      (JTGraphParameterLiftSpace.fiber T k
        (P.map ≫ NecklaceCylinderAugmentation.augmentation T k) P.map : SSet.{0})) := by
  obtain ⟨s, hs⟩ := exists_parameter P
  exact JTGraphParameterLiftSpace.toPoint_trivialFibration T k _ P.map s hs

open JTGraphLiftTransport
open JTProjectiveOrderedFiberComparison (row)
open JTCommaGraphPredecessor (augmentationCode)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

/-- The graph of an arbitrary decorated presentation needs only the identity collapse. -/
theorem exists_identity_lift (P : Pres (W := W) (x := x) (y := y)) :
    ∃ E : GraphLift P P.fiber.left, E.collapse = 𝟙 _ := by
  let U := (BoundaryNecklaceComma.toNative
    ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj P.base)).obj P.fiber
  obtain ⟨s, hs⟩ := exists_parameter U
  refine ⟨⟨𝟙 _, s, ?_⟩, rfl⟩
  change graph P.fiber.hom.right s = P.fiber.hom.right
  exact hs

/-- The actual graph predecessor over the same raw target has identity native collapse. -/
theorem exists_identity_predecessor
    {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    (U : CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q) :
    ∃ E : GraphLift U.left U.left.fiber.left, E.collapse = 𝟙 _ ∧
      Nonempty (JTGraphRestrictionRaw.predecessor (U := U) E ⟶ U) := by
  obtain ⟨E, hE⟩ := exists_identity_lift U.left
  exact ⟨E, hE, ⟨JTGraphTransportNaturality.toComma E⟩⟩

end

end DaggerModels.PartII.JTGraphMultiBeadIdentityLift
