import DaggerModelsPartII.JTJoinedGraphParameterTransport
import DaggerModelsPartII.JTGraphVariableTimeTraversal
import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport

/-! Transport the complete joined cylinder presentation along original comma arrows. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTJoinedGraphCylinderTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTIndependentTargetResolutions (Resolution)
open JTJoinedGraphParameterTransport (transportPair)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {W : Source} {x z y : Vertex W}
variable {P : Native W x z} {Q : Native W z y}
variable {U U' : TargetComma P} {V V' : TargetComma Q}

private abbrev A₁ := NecklaceCode.single 1

/-- The native map on both sides of the joined code preserves composition. -/
theorem sideMap_comp {L₀ L₁ L₂ R₀ R₁ R₂ : NecklaceCode}
    (f : L₀ ⟶ L₁) (g : R₀ ⟶ R₁) (f' : L₁ ⟶ L₂) (g' : R₁ ⟶ R₂) :
    JTBinaryPrismParameter.sideMap (f ≫ f') (g ≫ g') =
      Hom.comp.{0} (JTBinaryPrismParameter.sideMap f g) (JTBinaryPrismParameter.sideMap f' g') := by
  unfold JTBinaryPrismParameter.sideMap
  rw [← NecklaceCode.wedgeMap_comp, ← NecklaceCode.wedgeMap_comp]
  rfl

private def joinCode : NecklaceCode × NecklaceCode ⥤ NecklaceCode where
  obj p := JTOrderedLabelBinaryGlue.code p.1 p.2
  map f := JTBinaryPrismParameter.sideMap f.1 f.2
  map_id a := by
    change NecklaceCode.wedgeMap (Hom.id.{0} a.1)
      (NecklaceCode.wedgeMap (Hom.id.{0} A₁) (Hom.id.{0} a.2)) = Hom.id.{0} _
    rw [NecklaceCode.wedgeMap_id, NecklaceCode.wedgeMap_id]
  map_comp f g := sideMap_comp f.1 f.2 g.1 g.2

/-- Full synchronized join of two native graph resolutions. -/
def joined (U : TargetComma P) (V : TargetComma Q) :
    Resolution (NecklacesOver.wedge P Q) :=
  (Resolution.ofGraph U).join (Resolution.ofGraph V)

abbrev codeTime (U : TargetComma P) (V : TargetComma Q) :=
  (JTParametrizedTargetFamilies.codes (joined U V).family.labels).prod'
    (SynchronizedSimplicialParameters.time (joined U V).spaces)

private abbrev sideCode (U : TargetComma P) :=
  JTGraphVariableTimeIndex.joint U ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory

private abbrev factoredCode (U : TargetComma P) (V : TargetComma Q) :=
  ((SynchronizedSimplicialParameters.left
      (JTGraphVariableTimeIndex.timeDiagram U) (JTGraphVariableTimeIndex.timeDiagram V) ⋙
      sideCode U).prod'
    (SynchronizedSimplicialParameters.right
      (JTGraphVariableTimeIndex.timeDiagram U) (JTGraphVariableTimeIndex.timeDiagram V) ⋙
      sideCode V)) ⋙ joinCode

set_option maxHeartbeats 1000000 in
private theorem code_factor (U : TargetComma P) (V : TargetComma Q) :
    JTParametrizedTargetFamilies.codes (joined U V).family.labels = factoredCode U V := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · rfl
  · intro i j f
    dsimp only [JTParametrizedTargetFamilies.codes, joined,
      JTIndependentTargetResolutions.Resolution.join,
      JTFiniteParametrizedTargetFamilies.Synchronized.join,
      JTFiniteParametrizedTargetFamilies.Synchronized.precomp]
    simp only [Functor.comp_map, JTParametrizedTargetFamilyJoin.joinedLabels_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl


private theorem sideCode_eq {T T' : TargetComma P} (a : T ⟶ T') :
    JTGraphVariableTimeTransport.transport a ⋙ sideCode T' = sideCode T := by
  exact (Functor.assoc _ _ _).symm.trans
    (congrArg (· ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory)
      (JTGraphVariableTimeTransport.transport_joint a))

private theorem factoredCode_eq (a : U ⟶ U') (b : V ⟶ V') :
    transportPair a b ⋙ factoredCode U' V' = factoredCode U V := by
  unfold factoredCode
  rw [← Functor.assoc]
  change ((transportPair a b ⋙
      SynchronizedSimplicialParameters.left
        (JTGraphVariableTimeIndex.timeDiagram U') (JTGraphVariableTimeIndex.timeDiagram V') ⋙
        sideCode U').prod'
    (transportPair a b ⋙
      SynchronizedSimplicialParameters.right
        (JTGraphVariableTimeIndex.timeDiagram U') (JTGraphVariableTimeIndex.timeDiagram V') ⋙
        sideCode V')) ⋙ joinCode = _
  simp only [← Functor.assoc]
  rw [JTJoinedGraphParameterTransport.transportPair_left,
    JTJoinedGraphParameterTransport.transportPair_right]
  change ((SynchronizedSimplicialParameters.left
      (JTGraphVariableTimeIndex.timeDiagram U) (JTGraphVariableTimeIndex.timeDiagram V) ⋙
        JTGraphVariableTimeTransport.transport a ⋙ sideCode U').prod'
    (SynchronizedSimplicialParameters.right
      (JTGraphVariableTimeIndex.timeDiagram U) (JTGraphVariableTimeIndex.timeDiagram V) ⋙
        JTGraphVariableTimeTransport.transport b ⋙ sideCode V')) ⋙ joinCode = _
  simp only [Functor.assoc, sideCode_eq]

private abbrev joinedTime (U : TargetComma P) (V : TargetComma Q) :=
  SynchronizedSimplicialParameters.time (joined U V).spaces

private theorem joinedTime_eq (a : U ⟶ U') (b : V ⟶ V') :
    transportPair a b ⋙ joinedTime U' V' = joinedTime U V := by
  rfl


/-- Native joined code and common time are strictly invariant under both
original anchor arrows. Decorated label coefficients may change. -/
theorem codeTime_eq (a : U ⟶ U') (b : V ⟶ V') :
    transportPair a b ⋙ codeTime U' V' = codeTime U V := by
  have hCode : transportPair a b ⋙
      JTParametrizedTargetFamilies.codes (joined U' V').family.labels =
      JTParametrizedTargetFamilies.codes (joined U V).family.labels := by
    calc
      _ = transportPair a b ⋙ factoredCode U' V' :=
        congrArg (transportPair a b ⋙ ·) (code_factor U' V')
      _ = factoredCode U V := factoredCode_eq a b
      _ = _ := (code_factor U V).symm
  change transportPair a b ⋙
      (JTParametrizedTargetFamilies.codes (joined U' V').family.labels).prod'
        (joinedTime U' V') =
    (JTParametrizedTargetFamilies.codes (joined U V).family.labels).prod'
      (joinedTime U V)
  calc
    _ = (transportPair a b ⋙
        JTParametrizedTargetFamilies.codes (joined U' V').family.labels).prod'
      (transportPair a b ⋙ joinedTime U' V') := rfl
    _ = _ := by rw [hCode, joinedTime_eq a b]

/-- Both anchor arrows transport the full presentation, including every
internal necklace over every common-time parameter. -/
def transport (a : U ⟶ U') (b : V ⟶ V') :
    (joined U V).FullPresentation ⥤ (joined U' V').FullPresentation :=
  JTBoundaryNecklacePresentationTransport.preJoint (transportPair a b)
    (codeTime U' V') (codeTime U V)
    (NecklaceCylinderJointDiagram.cylinderUnder ⋙ BoundaryNecklaceComma.diagram)
    (codeTime_eq a b)

end
end DaggerModels.PartII.JTJoinedGraphCylinderTransport
