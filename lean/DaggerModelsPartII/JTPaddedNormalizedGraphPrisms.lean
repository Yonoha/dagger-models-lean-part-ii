import DaggerModelsPartII.JTFixedEdgePaddedTime
import DaggerModelsPartII.JTNormalizedGraphTimeResolution
import DaggerModelsPartII.JTBinaryPrismTargetLift
import DaggerModelsPartII.JTTimePrismTargetComparison

/-! Actual padded normalization families for the prescribed original raw bead. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTPaddedNormalizedGraphPrisms

open NecklaceCode (singleIso)
open JTProjectiveOrderedFiberComparison (row endpointArrow)
open JTMixedGraphEndpointLifts (vertex)
open JTRowGraphFiber (Fiber)
open JTRowGraphNormalizationDiagram (coefficient leftEndpoint rightEndpoint raw_eq)
open JTNormalizedGraphTimeResolution (Extensions)
open JTNormalizedGraphTargetArrow (target)
open JTHigherInterleavedParameter (common mapTime mapTime_id mapTime_comp)
open JTHigherGraphExtensionLabels (label families left_vertical right_vertical)
open JTBinaryPrismTargetLift (mixedSideParameter mixedSide_raw)
open JTMixedGraphRawRefinement (nativeGraphParameter nativeRawGraph)
open JTHomotopyTargetTimeResolution (degree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ Raw W} {x y : Vertex W}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)
variable (G : Fiber q)

private abbrev f := coefficient G
private abbrev s := G.obj.parameter
private abbrev T := MixedGraphCylinderTraversal.code d
private abbrev c := MixedGraphCylinderTraversal.collapseOuter d

/-- Actual choices at all padded time simplices with the prescribed edge. -/
abbrev Padded (e : (Extensions hx hy G).obj (op ⦋1⦌)) :=
  JTFixedEdgePaddedTime.space (Extensions hx hy G) e

/-- The literal padded time degree of every original simplex. -/
abbrev time (X : SSet.{0}) := degree X ⋙ JTPaddedTimeOperators.functor

variable {X : SSet.{0}} {e : (Extensions hx hy G).obj (op ⦋1⦌)}
variable (π : X ⟶ Padded hx hy G e)

private abbrev E (a : X.Elementsᵒᵖ) := (π.app a.unop.fst a.unop.snd).val

private theorem E_map {a b : X.Elementsᵒᵖ} (j : a ⟶ b) :
    (Extensions hx hy G).map ((time X).map j).op (E hx hy G π b) = E hx hy G π a := by
  have h := congrFun (π.naturality j.unop.val) b.unop.snd
  exact congrArg Subtype.val (h.symm.trans (congrArg (π.app a.unop.fst) j.unop.property))

private def toChoices : X.Elementsᵒᵖ ⥤
    JTHigherGraphExtensionComma.Index (f G) (s G) (leftEndpoint hx G) (rightEndpoint hy G) where
  obj a := op ⟨op ((time X).obj a), E hx hy G π a⟩
  map j := (CategoryOfElements.homMk (F := Extensions hx hy G) _ _
    ((time X).map j).op (E_map hx hy G π j)).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change ((time X).map (𝟙 a)).op = 𝟙 _
    rw [(time X).map_id]
    rfl
  map_comp j k := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change ((time X).map (j ≫ k)).op = ((time X).map j ≫ (time X).map k).op
    rw [(time X).map_comp]

private def coeff : X.Elementsᵒᵖ ⥤ SimplexCategory where
  obj a := common G.obj.degree ((time X).obj a)
  map j := mapTime G.obj.degree ((time X).map j)
  map_id a := by rw [(time X).map_id, mapTime_id]
  map_comp f g := by rw [(time X).map_comp, mapTime_comp]

private theorem parameter_map {a b : X.Elementsᵒᵖ} (j : a ⟶ b) :
    (𝟙 (T (d := d)).toSSet ⊗ₘ J.map ((time X).map j)) ≫
        mixedSideParameter (s G) ((time X).obj b) =
      mixedSideParameter (s G) ((time X).obj a) ≫ J.map ((coeff (X := X) G).map j) := by
  let v := (time X).map j
  unfold mixedSideParameter
  change (𝟙 (T (d := d)).toSSet ⊗ₘ J.map v) ≫
      (nativeGraphParameter (s G) ⊗ₘ 𝟙 _) ≫ _ =
    ((nativeGraphParameter (s G) ⊗ₘ 𝟙 _) ≫ _) ≫ J.map (mapTime G.obj.degree v)
  rw [Category.assoc, JTHigherGroupoidParameterPrism.paired_mapTime]
  simp only [← Category.assoc, ← MonoidalCategory.id_tensorHom,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

private theorem hq :
    nativeRawGraph W d G.obj.degree (f G) (s G) = (target hx hy).map :=
  congrArg (fun a ↦ (singleIso d).hom ≫ a) (raw_eq G)

private abbrev labelAt (a : X.Elementsᵒᵖ) :=
  label (f G) (s G) (leftEndpoint hx G) (rightEndpoint hy G)
    (E hx hy G π a).1 (E hx hy G π a).2

private theorem labelAt_map {a b : X.Elementsᵒᵖ} (j : a ⟶ b) :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj (op (T (d := d)))).map
      (mapTime G.obj.degree ((time X).map j)).op (labelAt hx hy G π b) =
        labelAt hx hy G π a :=
  JTHigherGraphExtensionComma.z_map (f G) (s G) (leftEndpoint hx G) (rightEndpoint hy G)
    ((toChoices hx hy G π).map j)

/-- The original normalized bead, with its entire padded extensions, is a
compatible family over the given projection of time spaces. -/
def family : JTCompatibleTimePrisms.Family (time X) (target hx hy) T c where
  coefficient := coeff G
  first j := JTBinaryPrismLabelOperators.padded_first G.obj.degree ((degree X).map j)
  last j := JTBinaryPrismLabelOperators.padded_last G.obj.degree ((degree X).map j)
  label := labelAt hx hy G π
  label_map j := labelAt_map hx hy G π j
  parameter a := mixedSideParameter (s G) ((time X).obj a)
  parameter_map j := parameter_map G j
  raw a := mixedSide_raw (f G) (s G) (hq hx hy G) (target hx hy).first (target hx hy).last
    (families (f G) (s G) (leftEndpoint hx G) (rightEndpoint hy G)
      (E hx hy G π a).1 (E hx hy G π a).2 0)
    (left_vertical (f G) (s G) (leftEndpoint hx G) (E hx hy G π a).1)
    (right_vertical (f G) (s G) (rightEndpoint hy G) (E hx hy G π a).2)

/-- The original injective fibrancy gives an actual edge to fix in the padded choices. -/
theorem edge_nonempty
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    Nonempty ((Extensions hx hy G).obj (op ⦋1⦌)) := by
  have : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  let a := JTOrdinaryGraphNormalizationSpace.chosenZero W ⦋d⦌ G.obj.degree
    (f G) (s G) x y (leftEndpoint hx G) (rightEndpoint hy G) hW
  obtain ⟨b, _⟩ := JTHigherGraphExtensionComma.forgetChoices_surjective
    (f G) (s G) (leftEndpoint hx G) (rightEndpoint hy G) ⦋0⦌ a
  exact ⟨(Extensions hx hy G).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op b⟩

end

end DaggerModels.PartII.JTPaddedNormalizedGraphPrisms
