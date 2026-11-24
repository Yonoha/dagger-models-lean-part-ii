import DaggerModelsPartII.JTSharedCoefficientGraphPair
import DaggerModelsPartII.JTGraphChoiceIndex
import DaggerModelsPartII.JTTimePrismTargetComparison
import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.FiniteLastVertexFactor

/-! Whole families of compatible graphs evaluate on all faces over the original raw wedge. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode DaggerNerveHomotopy
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open DaggerSSetGluing (GW weakEquivalence_iff_GW)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteGraphWedgeEvaluation

open JTOrderedLabelBinaryGlue (code orderedTriplePoint)
open JTSharedCoefficientGraphPair (inputs family_over_wedge)
open JTBinaryPrismRealization (realizeProduct collapse)
open JTGraphChoiceIndex (Index phase time vertex vertex_map phase_injective)
open JTHigherGraphTimeFamily (extendFamily extendFamily_mapCopies)
open JTHigherInterleavedParameter (common)
open JTCompatibleTimePrisms (Family)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {T U : NecklaceCode} {m n k l : SimplexCategory}
variable (r : m ⟶ k) (r' : m ⟶ l)
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)

/-- A whole graph equipped with the two specified side restrictions. -/
abbrev Graph := {p : (code T U).toSSet ⊗ J.obj n ⟶ J.obj m //
    (tripleRightT T (single 1) U ▷ J.obj n) ≫ p ≫ J.map r = s ∧
    (tripleRightV T (single 1) U ▷ J.obj n) ≫ p ≫ J.map r' = t}

private abbrev I := Index (Graph r r' s t)
private abbrev timeDiagram := time (Graph r r' s t) n

private abbrev phases (a : I r r' s t) := ((phase (Graph r r' s t)).obj a).len

private abbrev familyAt (a : I r r' s t) (i : Fin (phases r r' s t a + 1)) := (vertex a i).val

/-- Every ordered family has its simultaneous interpolation in the whole enlarged time. -/
def parameter (a : I r r' s t) :
    (code T U).toSSet ⊗ J.obj ((timeDiagram r r' s t).obj a) ⟶ J.obj m :=
  extendFamily (k := ⦋phases r r' s t a⦌) (familyAt r r' s t a)

/-- Interpolating and restricting along an arbitrary face give exactly the same graph. -/
theorem parameter_map {a b : I r r' s t} (f : a ⟶ b) :
    ((code T U).toSSet ◁ J.map ((timeDiagram r r' s t).map f)) ≫ parameter r r' s t b =
      parameter r r' s t a := by
  let j := (phase (Graph r r' s t)).map f
  let hj := phase_injective f
  change ((code T U).toSSet ◁ J.map (JTFiniteCoefficientBridgeTime.mapCopies j hj n)) ≫
    extendFamily (k := ⦋phases r r' s t b⦌) (familyAt r r' s t b) = _
  rw [extendFamily_mapCopies j hj]
  unfold parameter
  congr 1
  funext i
  exact congrArg Subtype.val (vertex_map f i).symm

variable {W : Source} {x z y : Vertex W}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)
variable (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
variable (hs : realizeProduct W k s (orderedLabel W x z T k u) =
  fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
variable (ht : realizeProduct W l t (orderedLabel W z y U l v) =
  fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map)

/-- These are the original time-prism family equations on all faces. -/
def comparison : Family (timeDiagram r r' s t) (NecklacesOver.wedge P Q) (code T U)
    (collapse c e) where
  coefficient := (Functor.const _).obj m
  first _ := rfl
  last _ := rfl
  label _ := orderedTriplePoint (inputs r r' u v)
  label_map _ := by
    change (L W x y (code T U)).map ((𝟙 m).op) (orderedTriplePoint (inputs r r' u v)) = _
    rw [op_id]
    exact congrFun ((L W x y (code T U)).map_id (op m)) _
  parameter := parameter r r' s t
  parameter_map f := by
    change (𝟙 (code T U).toSSet ⊗ₘ J.map ((timeDiagram r r' s t).map f)) ≫
      parameter r r' s t _ = parameter r r' s t _ ≫ J.map (𝟙 m)
    rw [id_tensorHom, J.map_id, Category.comp_id]
    exact parameter_map r r' s t f
  raw a := family_over_wedge (K := ⦋phases r r' s t a⦌) r r' u v c e
    (familyAt r r' s t a) s t
    (fun i ↦ (vertex a i).property.1) (fun i ↦ (vertex a i).property.2) hs ht

/-- The domain keeps every internal necklace and every original face map. -/
abbrev Presentation := BoundaryNecklaceComma.Presentation
  (timeDiagram r r' s t ⋙ JTNecklaceEndpointCylinder.under (code T U))

/-- A single functor evaluates the whole diagram in the actual fixed-target comma. -/
def evaluate := JTTimePrismTargetComparison.toComma (comparison r r' s t c e u v hs ht)

/-- A single compatible graph makes the full presentation, with all its
simultaneous interpolations and internal necklaces, weakly contractible. -/
theorem presentation_point_GW (p : Graph r r' s t) :
    GW (pointMap (nerve (Presentation r r' s t))) := by
  let F := BoundaryNecklaceComma.fiberDiagram
    (timeDiagram r r' s t ⋙ JTNecklaceEndpointCylinder.under (code T U))
  let f := nerveMap (Grothendieck.forget F)
  letI : Nonempty (Graph r r' s t) := ⟨p⟩
  haveI : WeakEquivalence f := GrothendieckContractibleFibers.projection_weak F
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at (code T U) ((timeDiagram r r' s t).obj a))
  letI : WeakEquivalence (pointMap (nerve (I r r' s t))) :=
    (weakEquivalence_iff_GW _).mpr (JTGraphChoiceIndex.index_point_GW (Graph r r' s t))
  have h : f ≫ pointMap (nerve (I r r' s t)) = pointMap (nerve (Presentation r r' s t)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← h]
  infer_instance

/-- The entire evaluation of all compatible graphs is nullhomotopic. -/
theorem evaluate_nullhomotopic (p : Graph r r' s t) :
    ∃ q : (Δ[0] : SSet.{0}) ⟶ nerve (CostructuredArrow
        (DecoratedCylinderNecklacePresentation.toTarget W x y) (NecklacesOver.wedge P Q)),
      Nonempty (SSet.Homotopy (R.map (nerveMap (evaluate r r' s t c e u v hs ht)))
        (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve (Presentation r r' s t)) ≫ q))) := by
  let F := evaluate r r' s t c e u v hs ht
  simpa only [Category.id_comp] using FiniteLastVertexFactor.nullhomotopic
    (𝟙 (nerve (Presentation r r' s t))) (nerveMap F) (presentation_point_GW r r' s t p)

end

end DaggerModels.PartII.JTFiniteGraphWedgeEvaluation
