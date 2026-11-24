import DaggerModelsPartII.JTEndpointGraphOverlapChoices
import DaggerModelsPartII.JTFiniteCoefficientBridgeSideExtension

/-! Restrict the joined endpoint choices to the original parent charts. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTEndpointGraphOverlapRestriction

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTEndpointGraphCoefficientSlice (MixedGraphs coefficientDegree coefficients)
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphCoefficientChoices (leftSquare rightSquare leftBase rightBase homOfChoiceMaps)

noncomputable section

private abbrev std := SSet.stdSimplex.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev I := ParameterIndex P parents refineTo
private abbrev F := projection P parents refineTo hx hy

private def leftSide (U : I P parents refineTo)
    (E : Left P parents refineTo hx U) (e : Fin (m + 1)) :
    JTCommonCoefficientLiftChoices.Extension
      (leftSquare (parents e) hx ((toParent P parents refineTo e).obj U.1))
      (timeAt P parents refineTo U) :=
  JTFiniteCoefficientBridgeSideExtension.toSide (side U.1) (final U.1)
    (fun t ↦ coefficientDegree.map (refineTo t)) (side_final U.1)
    (timeAt P parents refineTo U) (leftBase P x) (leftAt P parents refineTo hx U)
    (fun t ↦ leftBase (parents t) x)
    (fun t ↦ JTEndpointRowGraphNormalization.leftBase_map (refineTo t).unop)
    (fun t ↦ leftSquare (parents t) hx ((toParent P parents refineTo t).obj U.1)) E e

private def rightSide (U : I P parents refineTo)
    (E : Right P parents refineTo hy U) (e : Fin (m + 1)) :
    JTCommonCoefficientLiftChoices.Extension
      (rightSquare (parents e) hy ((toParent P parents refineTo e).obj U.1))
      (timeAt P parents refineTo U) :=
  JTFiniteCoefficientBridgeSideExtension.toSide (side U.1) (final U.1)
    (fun t ↦ coefficientDegree.map (refineTo t)) (side_final U.1)
    (timeAt P parents refineTo U) (rightBase P y) (rightAt P parents refineTo hy U)
    (fun t ↦ rightBase (parents t) y)
    (fun t ↦ JTEndpointRowGraphNormalization.rightBase_map (refineTo t).unop)
    (fun t ↦ rightSquare (parents t) hy ((toParent P parents refineTo t).obj U.1)) E e

private theorem sideMap_natural {U V : I P parents refineTo} (f : U ⟶ V)
    (e : Fin (m + 1)) {X : SSet.{0}}
    {a : std.obj ((bridgeParameter P parents refineTo).obj U) ⟶ X}
    {b : std.obj ((bridgeParameter P parents refineTo).obj V) ⟶ X}
    (h : a = std.map ((bridgeParameter P parents refineTo).map f) ≫ b) :
    std.map ((sideToBridge P parents refineTo e).app U) ≫ a =
      std.map ((sideParameter P parents refineTo e).map f) ≫
        std.map ((sideToBridge P parents refineTo e).app V) ≫ b := by
  rw [h, ← Category.assoc, ← Category.assoc, ← std.map_comp, ← std.map_comp,
    (sideToBridge P parents refineTo e).naturality f]

private abbrev sideBase (e : Fin (m + 1)) :
    I P parents refineTo ⥤ Over (parents e) × SemiSimplexCategory :=
  (CategoryTheory.Prod.fst _ _ ⋙ toParent P parents refineTo e).prod'
    (CategoryTheory.Prod.snd _ _)

private def sideObj (e : Fin (m + 1)) (U : Index P parents refineTo hx hy) :
    JTEndpointGraphCoefficientChoices.Index (parents e) hx hy :=
  let A := (F P parents refineTo hx hy).obj U
  op ⟨((prodOpEquiv (C := Over (parents e)) (D := SemiSimplexCategory)).functor.obj
    (op ((sideBase P parents refineTo e).obj A))),
    leftSide P parents refineTo hx A U.unop.snd.1 e,
    rightSide P parents refineTo hy A U.unop.snd.2 e⟩

/-- Restrict all the compatible bridge lifts to the actual chart at one parent.
Both the mixed graph and the entire injective time operator are preserved. -/
def toSide (e : Fin (m + 1)) :
    Index P parents refineTo hx hy ⥤ JTEndpointGraphCoefficientChoices.Index (parents e) hx hy where
  obj := sideObj P parents refineTo hx hy e
  map {U V} f :=
    let r := (F P parents refineTo hx hy).map f
    homOfChoiceMaps (parents e) hx hy ((sideBase P parents refineTo e).map r)
      (sideMap_natural P parents refineTo r e (choice_maps P parents refineTo hx hy f).1)
      (sideMap_natural P parents refineTo r e (choice_maps P parents refineTo hx hy f).2)
  map_id U := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    let B := F P parents refineTo hx hy ⋙ sideBase P parents refineTo e
    let M := (prodOpEquiv (C := Over (parents e)) (D := SemiSimplexCategory)).functor
    change M.map (B.map (𝟙 U)).op = 𝟙 (M.obj (op (B.obj U)))
    rw [B.map_id, op_id, M.map_id]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    let B := F P parents refineTo hx hy ⋙ sideBase P parents refineTo e
    let M := (prodOpEquiv (C := Over (parents e)) (D := SemiSimplexCategory)).functor
    change M.map (B.map (f ≫ g)).op = M.map (B.map g).op ≫ M.map (B.map f).op
    rw [B.map_comp, op_comp, M.map_comp]

/-- Exact left map on restriction to a parent. -/
theorem toSide_left (e : Fin (m + 1)) (U : Index P parents refineTo hx hy) :
    (JTEndpointGraphCoefficientChoices.leftChoice (parents e) hx hy
      ((toSide P parents refineTo hx hy e).obj U)).map =
    std.map ((sideToBridge P parents refineTo e).app ((F P parents refineTo hx hy).obj U)) ≫
      U.unop.snd.1.map := rfl

/-- Exact right map on restriction to a parent. -/
theorem toSide_right (e : Fin (m + 1)) (U : Index P parents refineTo hx hy) :
    (JTEndpointGraphCoefficientChoices.rightChoice (parents e) hx hy
      ((toSide P parents refineTo hx hy e).obj U)).map =
    std.map ((sideToBridge P parents refineTo e).app ((F P parents refineTo hx hy).obj U)) ≫
      U.unop.snd.2.map := rfl

end
end DaggerModels.PartII.JTEndpointGraphOverlapRestriction
