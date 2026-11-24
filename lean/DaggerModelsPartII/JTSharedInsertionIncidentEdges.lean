import DaggerModelsPartII.JTSharedInsertionChainSupport
import DaggerModelsPartII.JTJointRelativeEdgePrism

/-!
The shared all-vertex tuple is evaluated before restricting incident support.
Its full edge maps agree with the checked actual chain edges. Both edges are
stationary on the entire inverse image of the genuine incident support union,
with the original coefficient and complete common choice clock retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionIncidentEdges

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTTargetJointMarks (Joint)
open JTJointEndpointLiftSpaceRestriction (precompSquare precompSquare_ι)
open JTFixedLiftSpaceTimeEquiv (timeMap timeMap_conditions)
open GrothendieckTotalElements (totalDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem chain_identity (W : Source) (z : Vertex W)
    {S U D K N : SSet.{0}} (i : S ⟶ D) (j : S ⟶ U) (u : U ⟶ K)
    (α : D ⟶ K) (β : D ⟶ N) (h : j ≫ u = i ≫ α)
    (E : K ⊗ N ⟶ row W ⦋1⦌)
    (hE : (u ▷ N) ≫ E = fst U N ≫ JTJointSubcomplexRelativeLift.identityOnU W z) :
    i ≫ lift α β ≫ E = JTJointSubcomplexRelativeLift.identityOnU W z := by
  have hc : i ≫ lift α β = lift j (i ≫ β) ≫ (u ▷ N) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerRight_fst, lift_fst_assoc]
      exact h.symm
    · simp only [Category.assoc, lift_snd, whiskerRight_snd]
  rw [← Category.assoc, hc, Category.assoc, hE, ← Category.assoc, lift_fst]
  change j ≫ (term U ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) =
    term S ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W
  rw [← Category.assoc]
  congr 1

private def reindex {C D : Type} [SmallCategory C] [SmallCategory D]
    (G : C ⥤ D) (X : D ⥤ SSet.{0}) :
    (totalDiagram (G ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(G.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(G.map f.val.1, f.val.2), f.property⟩
  map_id p := by apply CategoryOfElements.ext; exact Prod.ext (G.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_comp f.val.1 g.val.1) rfl

private theorem chain_endpoints (W : Source) (z : Vertex W)
    {d k n : SimplexCategory} (α : d ⟶ k) (β : d ⟶ n)
    (f : std.obj k ⟶ row W ⦋0⦌) (E : std.obj k ⊗ std.obj n ⟶ row W ⦋1⦌)
    (hE : E ≫ endpointArrow W = fst _ _ ≫ JTJointSubcomplexRelativeLift.boundaryPair W f z) :
    (lift (std.map α) (std.map β) ≫ E) ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W (std.map α ≫ f) z := by
  rw [Category.assoc, hE, ← Category.assoc, lift_fst]
  exact JTJointEndpointRelativeLift.boundaryPair_natural W z α f

private theorem chain_reverse_endpoints (W : Source) (z : Vertex W)
    {d k n : SimplexCategory} (α : d ⟶ k) (β : d ⟶ n)
    (f : std.obj k ⟶ row W ⦋0⦌) (E : std.obj k ⊗ std.obj n ⟶ row W ⦋1⦌)
    (hE : E ≫ endpointArrow W =
      fst _ _ ≫ JTJointSubcomplexRelativeLift.reverseBoundaryPair W f z) :
    (lift (std.map α) (std.map β) ≫ E) ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W (std.map α ≫ f) z := by
  rw [Category.assoc, hE, ← Category.assoc, lift_fst]
  exact JTJointEndpointRelativeLift.reverseBoundaryPair_natural W z α f

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTExactlyMarkedSourceDiagram.Index F j
private abbrev leftSquare (m : M F j) := JTJointSubcomplexRelativeLift.square W
  ((JTIncidentBeadSupportTransport.inclusion F j).app m)
  ((JTExactlyMarkedSourceDiagram.endpointRows F j).app m) (z j)
  (JTIncidentBeadSupportData.row_on_support F j m)
private abbrev rightSquare (m : M F j) := JTJointSubcomplexRelativeLift.reverseSquare W
  ((JTIncidentBeadSupportTransport.inclusion F j).app m)
  ((JTExactlyMarkedSourceDiagram.endpointRows F j).app m) (z j)
  (JTIncidentBeadSupportData.row_on_support F j m)
private abbrev oldLeftSquare (m : M F j) := JTJointEndpointRelativeLift.square W
  ((JTExactlyMarkedSourceDiagram.incl F j).app m)
  ((JTExactlyMarkedSourceDiagram.endpointRows F j).app m) (z j)
  (JTExactlyMarkedSourceDiagram.supported_endpoint F j m)
private abbrev oldRightSquare (m : M F j) := JTJointEndpointRelativeLift.reverseSquare W
  ((JTExactlyMarkedSourceDiagram.incl F j).app m)
  ((JTExactlyMarkedSourceDiagram.endpointRows F j).app m) (z j)
  (JTExactlyMarkedSourceDiagram.supported_endpoint F j m)

private abbrev leftSimplex (m : M F j) (n : SimplexCategory)
    (x : ((JTIncidentBeadChoiceDiagram.spaces F j).obj (op m)).obj (op n)) :=
  (fst ((JTIncidentBeadChoiceDiagram.endingSpaces F j).obj (op m))
    ((JTIncidentBeadChoiceDiagram.startingSpaces F j).obj (op m))).app (op n) x
private abbrev rightSimplex (m : M F j) (n : SimplexCategory)
    (x : ((JTIncidentBeadChoiceDiagram.spaces F j).obj (op m)).obj (op n)) :=
  (snd ((JTIncidentBeadChoiceDiagram.endingSpaces F j).obj (op m))
    ((JTIncidentBeadChoiceDiagram.startingSpaces F j).obj (op m))).app (op n) x

private theorem restriction_face (m : M F j) :
    (JTIncidentBeadSupportTransport.vertexToSupport F j).app m ≫
        (JTIncidentBeadSupportTransport.inclusion F j).app m =
      std.map ((JTExactlyMarkedSourceDiagram.incl F j).app m) ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact NatTrans.congr_app (JTIncidentBeadSupportTransport.vertexToSupport_fac F j) m

private theorem restriction_identity (m : M F j) :
    (JTIncidentBeadSupportTransport.vertexToSupport F j).app m ≫
        JTJointSubcomplexRelativeLift.identityOnU W (z j) =
      JTJointEndpointRelativeLift.identityOnFace W (z j)
        (l := (JTExactlyMarkedSourceDiagram.supports F j).obj m) := by
  change (JTIncidentBeadSupportTransport.vertexToSupport F j).app m ≫
      (term ((JTIncidentBeadSupportTransport.diagram F j).obj m) ≫ vertexPoint W (z j) ≫
        JTEndpointNormalizationLifts.identityFamily W) =
    (term (std.obj ((JTExactlyMarkedSourceDiagram.supports F j).obj m)) ≫
      vertexPoint W (z j)) ≫ JTEndpointNormalizationLifts.identityFamily W
  simp only [Category.assoc]
  rw [← Category.assoc ((JTIncidentBeadSupportTransport.vertexToSupport F j).app m)]
  congr 1

private theorem endingMap_restriction (m : M F j) (n : SimplexCategory)
    (x : ((JTIncidentBeadChoiceDiagram.spaces F j).obj (op m)).obj (op n)) :
    JTActualJointChoicePrism.endingMap F j m n
        (((JTIncidentBeadChoiceDiagram.restriction F j).app (op m)).app (op n) x) =
      timeMap (leftSquare F j m) n (leftSimplex F j m n x) := by
  let l := (JTIncidentBeadChoiceDiagram.restrictEnding F j).app (op m)
  let r := (JTIncidentBeadChoiceDiagram.restrictStarting F j).app (op m)
  have hp := congrFun (NatTrans.congr_app (tensorHom_fst l r) (op n)) x
  change (fst ((JTActualJointChoiceCover.endingSpaces F j).obj (op m))
      ((JTActualJointChoiceCover.startingSpaces F j).obj (op m))).app (op n)
        ((l ⊗ₘ r).app (op n) x) =
    l.app (op n) ((fst ((JTIncidentBeadChoiceDiagram.endingSpaces F j).obj (op m))
      ((JTIncidentBeadChoiceDiagram.startingSpaces F j).obj (op m))).app (op n) x) at hp
  change timeMap (oldLeftSquare F j m) n
    ((fst ((JTActualJointChoiceCover.endingSpaces F j).obj (op m))
      ((JTActualJointChoiceCover.startingSpaces F j).obj (op m))).app (op n)
        ((l ⊗ₘ r).app (op n) x)) = _
  rw [hp]
  have h := JTJointRelativeEdgePrism.timeMap_precompSquare
    (leftSquare F j m) (oldLeftSquare F j m)
    ((JTIncidentBeadSupportTransport.vertexToSupport F j).app m) (𝟙 _)
    (restriction_face F j m) (restriction_identity F j m) (Category.id_comp _)
    n (leftSimplex F j m n x)
  simpa only [id_whiskerRight, Category.id_comp] using h

private theorem startingMap_restriction (m : M F j) (n : SimplexCategory)
    (x : ((JTIncidentBeadChoiceDiagram.spaces F j).obj (op m)).obj (op n)) :
    JTActualJointChoicePrism.startingMap F j m n
        (((JTIncidentBeadChoiceDiagram.restriction F j).app (op m)).app (op n) x) =
      timeMap (rightSquare F j m) n (rightSimplex F j m n x) := by
  let l := (JTIncidentBeadChoiceDiagram.restrictEnding F j).app (op m)
  let r := (JTIncidentBeadChoiceDiagram.restrictStarting F j).app (op m)
  have hp := congrFun (NatTrans.congr_app (tensorHom_snd l r) (op n)) x
  change (snd ((JTActualJointChoiceCover.endingSpaces F j).obj (op m))
      ((JTActualJointChoiceCover.startingSpaces F j).obj (op m))).app (op n)
        ((l ⊗ₘ r).app (op n) x) =
    r.app (op n) ((snd ((JTIncidentBeadChoiceDiagram.endingSpaces F j).obj (op m))
      ((JTIncidentBeadChoiceDiagram.startingSpaces F j).obj (op m))).app (op n) x) at hp
  change timeMap (oldRightSquare F j m) n
    ((snd ((JTActualJointChoiceCover.endingSpaces F j).obj (op m))
      ((JTActualJointChoiceCover.startingSpaces F j).obj (op m))).app (op n)
        ((l ⊗ₘ r).app (op n) x)) = _
  rw [hp]
  have h := JTJointRelativeEdgePrism.timeMap_precompSquare
    (rightSquare F j m) (oldRightSquare F j m)
    ((JTIncidentBeadSupportTransport.vertexToSupport F j).app m) (𝟙 _)
    (restriction_face F j m) (restriction_identity F j m) (Category.id_comp _)
    n (rightSimplex F j m n x)
  simpa only [id_whiskerRight, Category.id_comp] using h



private def lookup {C : Type} [SmallCategory C] (H : C ⥤ M F j) :
    (totalDiagram ((H ⋙ JTExactlyMarkedSourceDiagram.base F j).op ⋙
      JTIncidentAllVertexChoices.spaces F j)).Elementsᵒᵖ ⥤ JTIncidentBeadChoiceDiagram.Cover F j :=
  (((Functor.uncurry.map (Functor.whiskerLeft H.op
    (JTIncidentAllVertexChoices.evaluation F j))).mapElements) ⋙
      reindex H.op (JTIncidentBeadChoiceDiagram.spaces F j)).op

/-- Evaluate the original full tuple in incident-supported choices BEFORE vertex restriction. -/
def incidentLookup (which : Fin 3) :
    JTSharedInsertionChoices.Cover F j ⥤ JTIncidentBeadChoiceDiagram.Cover F j :=
  ![lookup F j (JTSharedInsertionChoices.earlierMark F j),
    lookup F j (JTSharedInsertionChoices.middleMark F j),
    lookup F j (JTSharedInsertionChoices.laterMark F j)] which

/-- The common insertion chain, with its unchanged coefficient and choice clock. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The common ordinal on which all three edge pairs are defined. -/
abbrev ordinals := JTSharedInsertionChoices.ordinals F j

private def earlierChoice (p : Index F j) :
    ((JTIncidentBeadChoiceDiagram.spaces F j).obj
      (op ((JTSharedInsertionChainSupport.marks F j 0).obj p))).obj
        (op ((JTSharedInsertionChoices.clock F j).obj p.base)) :=
  ((incidentLookup F j 0).obj p.base).unop.2

private def middleChoice (p : Index F j) :
    ((JTIncidentBeadChoiceDiagram.spaces F j).obj
      (op ((JTSharedInsertionChainSupport.marks F j 1).obj p))).obj
        (op ((JTSharedInsertionChoices.clock F j).obj p.base)) :=
  ((incidentLookup F j 1).obj p.base).unop.2

private def laterChoice (p : Index F j) :
    ((JTIncidentBeadChoiceDiagram.spaces F j).obj
      (op ((JTSharedInsertionChainSupport.marks F j 2).obj p))).obj
        (op ((JTSharedInsertionChoices.clock F j).obj p.base)) :=
  ((incidentLookup F j 2).obj p.base).unop.2

private def incidentChoice (which : Fin 3) (p : Index F j) :
    ((JTIncidentBeadChoiceDiagram.spaces F j).obj
      (op ((JTSharedInsertionChainSupport.marks F j which).obj p))).obj
        (op ((JTSharedInsertionChoices.clock F j).obj p.base)) := by
  refine Fin.cases ?_ ?_ which
  · exact earlierChoice F j p
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact middleChoice F j p
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact laterChoice F j p
      · intro i
        exact Fin.elim0 i

private def chart (which : Fin 3) (p : Index F j) :=
  lift (std.map ((JTSharedInsertionChainSupport.toOriginal F j which).app p))
    (std.map ((JTSharedInsertionChoices.toTime F j).app p))

private def incidentEnding (which : Fin 3) (p : Index F j) :=
  timeMap (leftSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (leftSimplex F j _ _ (incidentChoice F j which p))
private def incidentStarting (which : Fin 3) (p : Index F j) :=
  timeMap (rightSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (rightSimplex F j _ _ (incidentChoice F j which p))

private def earlierEnding : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.earlierChain F j)
    (JTActualJointChoiceChainGraph.chainEnding F j)

private def middleEnding : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.middleChain F j)
    (JTActualJointChoiceChainGraph.chainEnding F j)

private def laterEnding : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.laterChain F j)
    (JTActualJointChoiceChainGraph.chainEnding F j)

private def earlierStarting : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.earlierChain F j)
    (JTActualJointChoiceChainGraph.chainStarting F j)

private def middleStarting : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.middleChain F j)
    (JTActualJointChoiceChainGraph.chainStarting F j)

private def laterStarting : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  Functor.whiskerLeft (JTSharedInsertionChoices.laterChain F j)
    (JTActualJointChoiceChainGraph.chainStarting F j)

/-- The checked chain-ending maps, retained as a genuine natural transformation. -/
def ending (which : Fin 3) : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  ![earlierEnding F j, middleEnding F j, laterEnding F j] which

/-- The checked chain-starting maps on exactly that same original ordinal. -/
def starting (which : Fin 3) : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  ![earlierStarting F j, middleStarting F j, laterStarting F j] which

private theorem earlierEnding_eq (p : Index F j) :
    (ending F j 0).app p = chart F j 0 p ≫ incidentEnding F j 0 p :=
  congrArg (fun q ↦ chart F j 0 p ≫ q)
    (endingMap_restriction F j _ _ (incidentChoice F j 0 p))

private theorem middleEnding_eq (p : Index F j) :
    (ending F j 1).app p = chart F j 1 p ≫ incidentEnding F j 1 p :=
  congrArg (fun q ↦ chart F j 1 p ≫ q)
    (endingMap_restriction F j _ _ (incidentChoice F j 1 p))

private theorem laterEnding_eq (p : Index F j) :
    (ending F j 2).app p = chart F j 2 p ≫ incidentEnding F j 2 p :=
  congrArg (fun q ↦ chart F j 2 p ≫ q)
    (endingMap_restriction F j _ _ (incidentChoice F j 2 p))

private theorem earlierStarting_eq (p : Index F j) :
    (starting F j 0).app p = chart F j 0 p ≫ incidentStarting F j 0 p :=
  congrArg (fun q ↦ chart F j 0 p ≫ q)
    (startingMap_restriction F j _ _ (incidentChoice F j 0 p))

private theorem middleStarting_eq (p : Index F j) :
    (starting F j 1).app p = chart F j 1 p ≫ incidentStarting F j 1 p :=
  congrArg (fun q ↦ chart F j 1 p ≫ q)
    (startingMap_restriction F j _ _ (incidentChoice F j 1 p))

private theorem laterStarting_eq (p : Index F j) :
    (starting F j 2).app p = chart F j 2 p ≫ incidentStarting F j 2 p :=
  congrArg (fun q ↦ chart F j 2 p ≫ q)
    (startingMap_restriction F j _ _ (incidentChoice F j 2 p))

/-- The entire checked edge is the incident-supported time map on the common chart. -/
theorem ending_eq_incident (which : Fin 3) (p : Index F j) :
    (ending F j which).app p = chart F j which p ≫ incidentEnding F j which p := by
  fin_cases which
  · exact earlierEnding_eq F j p
  · exact middleEnding_eq F j p
  · exact laterEnding_eq F j p

/-- The starting edge is the other component of that SAME incident-supported simplex. -/
theorem starting_eq_incident (which : Fin 3) (p : Index F j) :
    (starting F j which).app p = chart F j which p ≫ incidentStarting F j which p := by
  fin_cases which
  · exact earlierStarting_eq F j p
  · exact middleStarting_eq F j p
  · exact laterStarting_eq F j p

/-- Both original ordered endpoints of the entire checked ending edge. -/
theorem ending_endpoints (which : Fin 3) (p : Index F j) :
    (ending F j which).app p ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W
        ((JTSharedInsertionChainSupport.rows F j which).app p) (z j) := by
  have h := (timeMap_conditions
    (leftSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (leftSimplex F j _ _ (incidentChoice F j which p))).2
  rw [ending_eq_incident]
  exact chain_endpoints W (z j)
    ((JTSharedInsertionChainSupport.toOriginal F j which).app p)
    ((JTSharedInsertionChoices.toTime F j).app p) _ _ h

/-- The same two original endpoints, in reverse order, for the checked starting edge. -/
theorem starting_endpoints (which : Fin 3) (p : Index F j) :
    (starting F j which).app p ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W
        ((JTSharedInsertionChainSupport.rows F j which).app p) (z j) := by
  have h := (timeMap_conditions
    (rightSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (rightSimplex F j _ _ (incidentChoice F j which p))).2
  rw [starting_eq_incident]
  exact chain_reverse_endpoints W (z j)
    ((JTSharedInsertionChainSupport.toOriginal F j which).app p)
    ((JTSharedInsertionChoices.toTime F j).app p) _ _ h

/-- The checked ending edge is identity on the ENTIRE full incident-union inverse image. -/
theorem ending_on_support (which : Fin 3) (p : Index F j) :
    (JTSharedInsertionChainSupport.inclusion F j which).app p ≫ (ending F j which).app p =
      JTJointSubcomplexRelativeLift.identityOnU W (z j) := by
  have h := (timeMap_conditions
    (leftSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (leftSimplex F j _ _ (incidentChoice F j which p))).1
  rw [ending_eq_incident]
  exact chain_identity W (z j) _ _ _ _ _
    (NatTrans.congr_app (JTSharedInsertionChainSupport.natural_square F j which) p) _ h

/-- The checked starting edge retains identity on that SAME full inverse-image union. -/
theorem starting_on_support (which : Fin 3) (p : Index F j) :
    (JTSharedInsertionChainSupport.inclusion F j which).app p ≫ (starting F j which).app p =
      JTJointSubcomplexRelativeLift.identityOnU W (z j) := by
  have h := (timeMap_conditions
    (rightSquare F j ((JTSharedInsertionChainSupport.marks F j which).obj p))
    ((JTSharedInsertionChoices.clock F j).obj p.base)
    (rightSimplex F j _ _ (incidentChoice F j which p))).1
  rw [starting_eq_incident]
  exact chain_identity W (z j) _ _ _ _ _
    (NatTrans.congr_app (JTSharedInsertionChainSupport.natural_square F j which) p) _ h

end
end DaggerModels.PartII.JTSharedInsertionIncidentEdges
