import DaggerModelsPartII.JTGraphInterpolatedChainOver
import DaggerModelsPartII.JTGraphInterpolatedOverSource
import DaggerModelsPartII.JTGraphInterpolatedOverTransport

/-! Comparison of the actual cylinder functors along a finite simplex operator. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedChainSpan

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedChainOver
open JTGraphInterpolatedOverOriginal (overOriginal)
open JTGraphInterpolatedOverSource (overSourceComparison)
open JTGraphInterpolatedOverTransport (overTransportComparison)
open JTGraphInterpolatedTargetOperators (transported_collapse)
open JTGraphInterpolatedSourceComparison (sourceMap)
open JTNecklaceEndpointCylinder (under)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {m n : SimplexCategory} (F : Fin (n.len + 1) ⥤ TargetComma Q)
variable (H : ∀ i, GraphLift (F.obj i).left (F.obj i).left.fiber.left)
variable (hH : ∀ i, (H i).collapse = 𝟙 _)
variable (θ : m ⟶ n)

private abbrev arrow {i j : Fin (n.len + 1)} (h : i ≤ j) := F.map (homOfLE h)
private abbrev last := Fin.last n.len
private abbrev startOf (θ : m ⟶ n) := θ.toOrderHom 0
private abbrev endOf (θ : m ⟶ n) := θ.toOrderHom (Fin.last m.len)
private abbrev prefixCode := (arrow F (Fin.zero_le (startOf θ))).left.fiber.left
private abbrev suffix := arrow F (Fin.le_last (endOf θ))
private abbrev selectedCollapse :=
  (arrow F (θ.toOrderHom.monotone (Fin.zero_le (Fin.last m.len)))).left.fiber.left

private abbrev selectedFamily (i : Fin (m.len + 1)) :=
  intervalLift F H (θ.toOrderHom.monotone (Fin.zero_le i))
    (θ.toOrderHom.monotone (Fin.le_last i))

include hH in
private theorem selectedFamily_collapse (i : Fin (m.len + 1)) :
    (selectedFamily F H θ i).collapse = selectedCollapse F θ :=
  intervalLift_collapse F H hH (θ.toOrderHom.monotone (Fin.zero_le i))
    (θ.toOrderHom.monotone (Fin.le_last i))

private abbrev transported (i : Fin (m.len + 1)) :=
  (selectedFamily F H θ i).transport (suffix F θ).left

private theorem collapse_eq :
    (arrow F (Fin.zero_le last)).left.fiber.left =
      prefixCode F θ ≫ (selectedCollapse F θ ≫ (suffix F θ).left.fiber.left) := by
  let L := CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)
  let p := homOfLE (Fin.zero_le (startOf θ))
  let q := homOfLE (θ.toOrderHom.monotone (Fin.zero_le (Fin.last m.len)))
  let r := homOfLE (Fin.le_last (endOf θ))
  change (F ⋙ L).map (p ≫ q ≫ r) = (F ⋙ L).map p ≫ ((F ⋙ L).map q ≫ (F ⋙ L).map r)
  simp only [Functor.map_comp]

private theorem overOriginal_congr {V : TargetComma Q} {S : NecklaceCode}
    {c c' : S ⟶ V.left.fiber.left} {D D' : Fin (m.len + 1) → GraphLift V.left S}
    (hD : ∀ i, (D i).collapse = c) (hD' : ∀ i, (D' i).collapse = c')
    (hc : c = c') (h : D = D') : overOriginal (n := m) c D hD = overOriginal c' D' hD' := by
  subst c'
  subst D'
  rfl

/-- The selected chain with its original source and original last object. -/
def selectedOver :=
  overOriginal (n := m) (selectedCollapse F θ) (selectedFamily F H θ)
    (selectedFamily_collapse F H hH θ)

/-- The selected chain transported along the suffix of the larger chain. -/
def transportedOver :=
  overOriginal (n := m) (selectedCollapse F θ ≫ (suffix F θ).left.fiber.left)
    (transported F H θ)
    (transported_collapse (selectedCollapse F θ) (selectedFamily F H θ)
      (selectedFamily_collapse F H hH θ) (suffix F θ))

/-- The cylinder of the selected chain compares to its transport over the larger last object. -/
def fromSmaller :
    selectedOver F H hH θ ⋙ Over.map (suffix F θ) ⟶ transportedOver F H hH θ :=
  overTransportComparison (n := m) (selectedCollapse F θ) (selectedFamily F H θ)
    (selectedFamily_collapse F H hH θ) (suffix F θ)

/-- Restricting time in the larger cylinder compares to the transported selected cylinder
after precomposition by the native source map of the prefix. -/
def fromLarger :
    CostructuredArrow.map (S := necklaceUnder) ((under (F.obj 0).left.fiber.left).map θ) ⋙
        chainOver F H hH ⟶
      CostructuredArrow.map (S := necklaceUnder) (sourceMap (prefixCode F θ) m) ⋙
        transportedOver F H hH θ := by
  let a := suffix F θ
  let c := selectedCollapse F θ ≫ a.left.fiber.left
  let D := transported F H θ
  have hD : ∀ i, (D i).collapse = c :=
    transported_collapse (selectedCollapse F θ) (selectedFamily F H θ)
      (selectedFamily_collapse F H hH θ) a
  let g := prefixCode F θ
  let β := overSourceComparison (n := m) c D hD g
  have hFam : subchainFamily F H θ = fun i ↦ restrict (D i) g :=
    funext fun i ↦ JTGraphTransportRestriction.transport_restrict (selectedFamily F H θ i) g a
  have h := overOriginal_congr (subchainFamily_collapse F H hH θ)
    (fun i ↦ congrArg (fun f ↦ g ≫ f) (hD i)) (collapse_eq F θ) hFam
  exact eqToHom ((chainOver_reindex F H hH θ).trans h) ≫ β

end

end DaggerModels.PartII.JTGraphInterpolatedChainSpan
