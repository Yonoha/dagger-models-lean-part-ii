import DaggerModelsPartII.JTGraphVariableParametrizedFamily
import DaggerModelsPartII.JTFiniteParametrizedTargetFamilies
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Independent native graph resolutions and their common-time gluing. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointMap_tensor_GW)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTIndependentTargetResolutions

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex (NativeSlice timeDiagram toNative lifts_nonempty)
open JTGraphVariableParametrizedFamily (coherentFamily)
open JTGraphVariableTimeTraversal (labels)
open JTParametrizedTargetFamilyJoin (PreservesFirst PreservesLast)
open JTFiniteParametrizedTargetFamilies (Synchronized)
open JTParametrizedTargetFamilies (Presentation)
open SynchronizedSimplicialParameters (time pairSpace)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {W : Source} {x z y : Vertex W}

/-- A resolution retains its independent base and its entire simplicial
parameter at every base object. The coherent family uses the original operators. -/
structure Resolution (Q : Native W x y) where
  base : Cat.{0, 0}
  spaces : base ⥤ SSet.{0}
  base_point : GW (pointMap (nerve base))
  space_point : ∀ b, GW (pointMap (spaces.obj b))
  family : Synchronized (time spaces) Q

variable {P : Native W x z} {Q : Native W z y}

/-- Use all independent pairs of bases and of parameters at the same time. -/
def Resolution.join (U : Resolution P) (V : Resolution Q) :
    Resolution (NecklacesOver.wedge P Q) where
  base := Cat.of (U.base × V.base)
  spaces := pairSpace U.spaces V.spaces
  base_point := SynchronizedSimplicialParameters.bases_point_GW U.base_point V.base_point
  space_point p := pointMap_tensor_GW (U.space_point p.1) (V.space_point p.2)
  family := (U.family.precomp (SynchronizedSimplicialParameters.left U.spaces V.spaces)).join
    (V.family.precomp (SynchronizedSimplicialParameters.right U.spaces V.spaces))

variable {D D' : Native W x y}

/-- Retain all independent parameters when moving along the original target map. -/
def Resolution.postcomp (U : Resolution D) (g : D ⟶ D') : Resolution D' where
  base := U.base
  spaces := U.spaces
  base_point := U.base_point
  space_point := U.space_point
  family := U.family.postcomp g

private theorem graphFirst (U : TargetComma D) : PreservesFirst (labels U) := by
  intro a b f
  let k := JTGraphLiftTransport.degree U.left
  change ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
    ((JTGraphNativeLabelDiagram.diagram U).map ((toNative U).map f))).2.toOrderHom 0 = 0
  rw [JTGraphNativeLabelDiagram.diagram_map]
  change SimplexCategory.Hom.toOrderHom (𝟙 k) 0 = 0
  exact congrArg (fun g ↦ g 0) (SimplexCategory.id_toOrderHom k)

private theorem graphLast (U : TargetComma D) : PreservesLast (labels U) := by
  intro a b f
  let k := JTGraphLiftTransport.degree U.left
  change ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
    ((JTGraphNativeLabelDiagram.diagram U).map ((toNative U).map f))).2.toOrderHom
      (Fin.last k.len) = Fin.last k.len
  rw [JTGraphNativeLabelDiagram.diagram_map]
  change SimplexCategory.Hom.toOrderHom (𝟙 k) (Fin.last k.len) = Fin.last k.len
  exact congrArg (fun g ↦ g (Fin.last k.len)) (SimplexCategory.id_toOrderHom k)

private theorem graphTime_point_GW (U : TargetComma D) (p : (NativeSlice U)ᵒᵖ) :
    GW (pointMap ((timeDiagram U).obj p)) :=
  (JTHomotopyTargetTimeResolution.point_GW_iff _ _).mp
    (JTGraphParameterTimeResolution.resolution_point_GW U p.unop.hom
      (lifts_nonempty U p.unop).some)

/-- Retain the entire original slice, every time family and all its operators. -/
def Resolution.ofGraph (U : TargetComma D) : Resolution D where
  base := Cat.of ((NativeSlice U)ᵒᵖ)
  spaces := timeDiagram U
  base_point := (SynchronizedSimplicialParameters.point_op_iff _).mpr
    (DaggerNativeOverNerveWeakContractibility.point_GW U.left.fiber.left)
  space_point := graphTime_point_GW U
  family := ⟨labels U, coherentFamily U, graphFirst U, graphLast U⟩

/-- The category retaining all internal necklaces of the synchronized family. -/
abbrev Resolution.FullPresentation (U : Resolution D) :=
  Presentation (L := U.family.labels) (time := time U.spaces)

/-- Evaluation to the original comma over the given native target. -/
def Resolution.evaluate (U : Resolution D) : U.FullPresentation ⥤ TargetComma D :=
  JTParametrizedTargetFamilies.evaluate U.family.family

/-- The full presentation over all the independent parameters has weakly
contractible nerve. -/
theorem Resolution.presentation_point_GW (U : Resolution D) :
    GW (pointMap (nerve U.FullPresentation)) :=
  JTParametrizedTargetFamilies.presentation_point_GW
    (SynchronizedSimplicialParameters.index_point_GW_of U.spaces U.base_point U.space_point)

end

end DaggerModels.PartII.JTIndependentTargetResolutions
