import DaggerModelsPartII.SynchronizedParameterMorphisms
import DaggerModelsPartII.JTGraphVariableTimeTransport
import DaggerModelsPartII.JTIndependentTargetResolutions

/-! Transport two original graph resolutions simultaneously to a common time. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJoinedGraphParameterTransport

open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex (Index NativeSlice timeDiagram)
open JTGraphVariableTimeTransport (transport)
open JTGraphLiftRestriction (restrict)
open JTGraphParameterTimeResolution (Lifts)
open JTProjectiveOrderedFiberComparison (row)
open JTIndependentTargetResolutions (Resolution)
open SynchronizedSimplicialParameters (mapIndex mapPair left right)

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

/-- The base map is the postcomposition of the actual native slice operator. -/
abbrev onBase (a : U ⟶ U') : (NativeSlice U)ᵒᵖ ⥤ (NativeSlice U')ᵒᵖ :=
  (Over.map a.left.fiber.left).op

private def mapLift (a : U ⟶ U') {B : NativeSlice U}
    (D : Lifts U B.hom) : Lifts U' (((onBase a).obj (op B)).unop).hom :=
  ⟨D.val.transport a.left, congrArg (· ≫ a.left.fiber.left) D.property⟩

/-- Original target transport is a natural map of actual graph-parameter simplicial sets. -/
def onSpaces (a : U ⟶ U') : timeDiagram U ⟶ onBase a ⋙ timeDiagram U' where
  app B :=
    { app n D i := mapLift a (D i)
      naturality := by intros; rfl }
  naturality {B B'} f := by
    apply NatTrans.ext
    funext n D i
    apply Subtype.ext
    exact JTGraphTransportRestriction.transport_restrict (D i).val f.unop.left a

/-- The generic time transport is the already verified original comma transport. -/
theorem onIndex (a : U ⟶ U') : mapIndex (onBase a) (onSpaces a) = transport a := rfl

/-- Transport along two independent original comma arrows while retaining their common time. -/
def transportPair (a : U ⟶ U') (b : V ⟶ V') :
    SynchronizedSimplicialParameters.Index (timeDiagram U) (timeDiagram V) ⥤
      SynchronizedSimplicialParameters.Index (timeDiagram U') (timeDiagram V') :=
  mapPair (onBase a) (onBase b) (onSpaces a) (onSpaces b)

theorem transportPair_left (a : U ⟶ U') (b : V ⟶ V') :
    transportPair a b ⋙ left (timeDiagram U') (timeDiagram V') =
      left (timeDiagram U) (timeDiagram V) ⋙ transport a :=
  (SynchronizedSimplicialParameters.mapPair_left (onBase a) (onBase b)
    (onSpaces a) (onSpaces b)).trans (congrArg (_ ⋙ ·) (onIndex a))

theorem transportPair_right (a : U ⟶ U') (b : V ⟶ V') :
    transportPair a b ⋙ right (timeDiagram U') (timeDiagram V') =
      right (timeDiagram U) (timeDiagram V) ⋙ transport b :=
  (SynchronizedSimplicialParameters.mapPair_right (onBase a) (onBase b)
    (onSpaces a) (onSpaces b)).trans (congrArg (_ ⋙ ·) (onIndex b))

theorem transportPair_id (U : TargetComma P) (V : TargetComma Q) :
    transportPair (𝟙 U) (𝟙 V) = 𝟭 _ := by
  apply SynchronizedSimplicialParameters.joint_functor_ext
  · rw [transportPair_left, JTGraphVariableTimeTransport.transport_id,
      Functor.comp_id, Functor.id_comp]
  · rw [transportPair_right, JTGraphVariableTimeTransport.transport_id,
      Functor.comp_id, Functor.id_comp]

theorem transportPair_comp {U'' : TargetComma P} {V'' : TargetComma Q}
    (a : U ⟶ U') (a' : U' ⟶ U'') (b : V ⟶ V') (b' : V' ⟶ V'') :
    transportPair (a ≫ a') (b ≫ b') = transportPair a b ⋙ transportPair a' b' := by
  apply SynchronizedSimplicialParameters.joint_functor_ext
  · rw [Functor.assoc, transportPair_left a' b',
      ← Functor.assoc (transportPair a b) _ (transport a'), transportPair_left a b,
      Functor.assoc, transportPair_left (a ≫ a') (b ≫ b'),
      JTGraphVariableTimeTransport.transport_comp]
  · rw [Functor.assoc, transportPair_right a' b',
      ← Functor.assoc (transportPair a b) _ (transport b'), transportPair_right a b,
      Functor.assoc, transportPair_right (a ≫ a') (b ≫ b'),
      JTGraphVariableTimeTransport.transport_comp]

/-- All pairs of original anchors act on their full synchronized indices. -/
def indexDiagram (P : Native W x z) (Q : Native W z y) : TargetComma P × TargetComma Q ⥤ Cat.{0, 0}
    where
  obj p := Cat.of (SynchronizedSimplicialParameters.Index (timeDiagram p.1) (timeDiagram p.2))
  map f := (transportPair f.1 f.2).toCatHom
  map_id p := Cat.Hom.ext (transportPair_id p.1 p.2)
  map_comp f g := Cat.Hom.ext (transportPair_comp f.1 g.1 f.2 g.2)

/-- Every pair of anchors has a weakly contractible common-time parameter index. -/
theorem indexDiagram_point_GW (p : TargetComma P × TargetComma Q) :
    GW (pointMap (nerve ((indexDiagram P Q).obj p))) := by
  let L := Resolution.ofGraph p.1
  let R := Resolution.ofGraph p.2
  exact SynchronizedSimplicialParameters.index_point_GW L.spaces R.spaces
    L.base_point R.base_point L.space_point R.space_point

/-- Synchronizing all pairs in any diagram of original arrows is a weak
equivalence over the original indexing category. -/
theorem indexDiagram_projection_weak {A : Type} [SmallCategory A]
    (F : A ⥤ TargetComma P × TargetComma Q) :
    WeakEquivalence (nerveMap (Grothendieck.forget (F ⋙ indexDiagram P Q))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun a ↦ indexDiagram_point_GW (F.obj a))

end

end DaggerModels.PartII.JTJoinedGraphParameterTransport
