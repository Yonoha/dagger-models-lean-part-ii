import DaggerModelsPartII.JTEndpointGraphCoefficientOverlap
import DaggerModelsPartII.JTEndpointGraphCoefficientChoices
import DaggerModelsPartII.JTFiniteCoefficientBridgeExtension

/-! Exact paired finite bridge choices over arbitrary mixed arrows on an overlap. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTEndpointGraphOverlapChoices

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTEndpointGraphCoefficientSlice (MixedGraphs)
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphCoefficientChoices (leftSquare rightSquare)
open JTFiniteCoefficientBridgeExtension (Extension restrict)
open JTEndpointRowGraphNormalization (leftVertex_map rightVertex_map)

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

abbrev leftAt (U : I P parents refineTo) :=
  leftSquare P hx ((toCommon P parents refineTo).obj U.1)

abbrev rightAt (U : I P parents refineTo) :=
  rightSquare P hy ((toCommon P parents refineTo).obj U.1)

abbrev Left (U : I P parents refineTo) :=
  Extension (side U.1) (final U.1) (leftAt P parents refineTo hx U)
    (timeAt P parents refineTo U)

abbrev Right (U : I P parents refineTo) :=
  Extension (side U.1) (final U.1) (rightAt P parents refineTo hy U)
    (timeAt P parents refineTo U)

private def restrictLeft {U V : I P parents refineTo} (f : U ⟶ V)
    (E : Left P parents refineTo hx V) : Left P parents refineTo hx U :=
  restrict (side U.1) (side V.1) (final U.1) (final V.1)
    (leftAt P parents refineTo hx U) (leftAt P parents refineTo hx V)
    ((degree P parents refineTo).map f.1) ((joinedTime P parents refineTo).map f)
    ((bridgeParameter P parents refineTo).map f) (prism_natural f) (bridgeParameter_base f)
    (leftVertex_map f.1.hom.unop) E

private def restrictRight {U V : I P parents refineTo} (f : U ⟶ V)
    (E : Right P parents refineTo hy V) : Right P parents refineTo hy U :=
  restrict (side U.1) (side V.1) (final U.1) (final V.1)
    (rightAt P parents refineTo hy U) (rightAt P parents refineTo hy V)
    ((degree P parents refineTo).map f.1) ((joinedTime P parents refineTo).map f)
    ((bridgeParameter P parents refineTo).map f) (prism_natural f) (bridgeParameter_base f)
    (rightVertex_map f.1.hom.unop) E

/-- Preserve both literal extension maps, including their prescribed stationary lines. -/
def choices : (I P parents refineTo)ᵒᵖ ⥤ Type where
  obj U := Left P parents refineTo hx U.unop × Right P parents refineTo hy U.unop
  map f E := ⟨restrictLeft P parents refineTo hx f.unop E.1,
    restrictRight P parents refineTo hy f.unop E.2⟩
  map_id U := by
    funext E
    apply Prod.ext <;> apply JTFiniteCoefficientBridgeExtension.Extension.ext
    · change std.map ((bridgeParameter P parents refineTo).map (𝟙 U.unop)) ≫ E.1.map = E.1.map
      rw [(bridgeParameter P parents refineTo).map_id, std.map_id, Category.id_comp]
    · change std.map ((bridgeParameter P parents refineTo).map (𝟙 U.unop)) ≫ E.2.map = E.2.map
      rw [(bridgeParameter P parents refineTo).map_id, std.map_id, Category.id_comp]
  map_comp f g := by
    funext E
    apply Prod.ext <;> apply JTFiniteCoefficientBridgeExtension.Extension.ext
    · change std.map ((bridgeParameter P parents refineTo).map (g.unop ≫ f.unop)) ≫ E.1.map =
        std.map ((bridgeParameter P parents refineTo).map g.unop) ≫
          std.map ((bridgeParameter P parents refineTo).map f.unop) ≫ E.1.map
      rw [(bridgeParameter P parents refineTo).map_comp, std.map_comp, Category.assoc]
    · change std.map ((bridgeParameter P parents refineTo).map (g.unop ≫ f.unop)) ≫ E.2.map =
        std.map ((bridgeParameter P parents refineTo).map g.unop) ≫
          std.map ((bridgeParameter P parents refineTo).map f.unop) ≫ E.2.map
      rw [(bridgeParameter P parents refineTo).map_comp, std.map_comp, Category.assoc]

/-- Every specified extension and its actual compatible operators. -/
abbrev Index := (choices P parents refineTo hx hy).Elementsᵒᵖ

abbrev projection : Index P parents refineTo hx hy ⥤ I P parents refineTo :=
  (CategoryOfElements.π (choices P parents refineTo hx hy)).leftOp

/-- Both extended endpoint maps reindex by the same full bridge operator. -/
theorem choice_maps {U V : Index P parents refineTo hx hy} (f : U ⟶ V) :
    U.unop.snd.1.map = std.map ((projection P parents refineTo hx hy ⋙
      bridgeParameter P parents refineTo).map f) ≫ V.unop.snd.1.map ∧
    U.unop.snd.2.map = std.map ((projection P parents refineTo hx hy ⋙
      bridgeParameter P parents refineTo).map f) ≫ V.unop.snd.2.map := by
  exact ⟨(congrArg (fun E ↦ E.1.map) f.unop.property).symm,
    (congrArg (fun E ↦ E.2.map) f.unop.property).symm⟩

end
end DaggerModels.PartII.JTEndpointGraphOverlapChoices
