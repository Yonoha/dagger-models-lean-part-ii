import DaggerModelsPartII.JTBinaryPrismLabelOperators
import DaggerModelsPartII.JTBinaryPrismParameter

/-! The exact binary gluing of families of time prisms.

The original raw equality is the one in `JTBinaryPrismRealization.raw_over_wedge`.
The coefficient and parameter restrictions are the previously checked maps of
whole ordered labels and of whole groupoid parameters.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCompatibleTimePrisms

open JTOrderedLabelBinaryGlue (code orderedTriplePoint)
open JTBinaryPrismRealization (blockInputs realizeProduct raw_over_wedge collapse)
open JTRealizedLabelEndpoints (orderedLabel)
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev labels (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {A : Type} [SmallCategory A] (time : A ⥤ SimplexCategory)
variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (T : NecklaceCode) (c : T ⟶ Q.code)

/-- Actual ordered labels and whole time parameters, over one original native
collapse, with their exact restrictions along every time operator. -/
structure Family where
  coefficient : A ⥤ SimplexCategory
  first : ∀ {a b : A} (f : a ⟶ b), (coefficient.map f).toOrderHom 0 = 0
  last : ∀ {a b : A} (f : a ⟶ b),
    (coefficient.map f).toOrderHom (Fin.last (coefficient.obj a).len) =
      Fin.last (coefficient.obj b).len
  label : ∀ a, (labels W x y T).obj (op (coefficient.obj a))
  label_map : ∀ {a b : A} (f : a ⟶ b),
    (labels W x y T).map (coefficient.map f).op (label b) = label a
  parameter : ∀ a, T.toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (coefficient.obj a)
  parameter_map : ∀ {a b : A} (f : a ⟶ b),
    (𝟙 T.toSSet ⊗ₘ J.map (time.map f)) ≫ parameter b =
      parameter a ≫ J.map (coefficient.map f)
  raw : ∀ a, realizeProduct W (coefficient.obj a) (parameter a)
    (orderedLabel W x y T (coefficient.obj a) (label a)) =
      fst T.toSSet (J.obj (time.obj a)) ≫ c.map ≫ Q.map

section Change

variable {time Q T c}

/-- Pull the full family back along its exact time index. -/
def Family.precomp {B : Type} [SmallCategory B] (v : B ⥤ A) (F : Family time Q T c) :
    Family (v ⋙ time) Q T c where
  coefficient := v ⋙ F.coefficient
  first f := F.first (v.map f)
  last f := F.last (v.map f)
  label b := F.label (v.obj b)
  label_map f := F.label_map (v.map f)
  parameter b := F.parameter (v.obj b)
  parameter_map f := F.parameter_map (v.map f)
  raw b := F.raw (v.obj b)

/-- Postcompose the unchanged native collapse with an actual over-target arrow. -/
def Family.postcomp {Q' : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    (F : Family time Q T c) (g : Q ⟶ Q') : Family time Q' T (c ≫ g.hom) where
  coefficient := F.coefficient
  first := F.first
  last := F.last
  label := F.label
  label_map := F.label_map
  parameter := F.parameter
  parameter_map := F.parameter_map
  raw a := by
    rw [F.raw]
    change fst T.toSSet (J.obj (time.obj a)) ≫ c.map ≫ Q.map =
      fst T.toSSet (J.obj (time.obj a)) ≫ (c.map ≫ g.hom.map) ≫ Q'.map
    rw [Category.assoc c.map, g.w]

end Change

variable {time Q T c} {z : Vertex W}
variable {P : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W x)}
variable {S : NecklaceCode} {d : S ⟶ P.code}
variable (F : Family time P S d) (G : Family time Q T c)

open JTParameterBlocks (common leftIn rightIn)
open JTParameterBlockOperators (leftIn_map rightIn_map)

private abbrev k (a : A) := F.coefficient.obj a
private abbrev l (a : A) := G.coefficient.obj a

private def joinedCoefficient : A ⥤ SimplexCategory where
  obj a := common (k F a) (l G a)
  map f := JTParameterBlockOperators.map (F.coefficient.map f) (G.coefficient.map f)
  map_id a := by
    rw [F.coefficient.map_id, G.coefficient.map_id]
    exact JTParameterBlockOperators.map_id _ _
  map_comp f g := by
    rw [F.coefficient.map_comp, G.coefficient.map_comp]
    exact (JTParameterBlockOperators.map_comp _ _ _ _).symm

private def joinedParameter (a : A) :
    (code S T).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj ((joinedCoefficient F G).obj a) :=
  JTBinaryPrismParameter.parameter S T (common (k F a) (l G a)) (J.obj (time.obj a))
    (F.parameter a ≫ J.map (leftIn (k F a) (l G a)))
    (G.parameter a ≫ J.map (rightIn (k F a) (l G a)))

private theorem joinedParameter_map {a b : A} (f : a ⟶ b) :
    (𝟙 (code S T).toSSet ⊗ₘ J.map (time.map f)) ≫ joinedParameter F G b =
      joinedParameter F G a ≫ J.map ((joinedCoefficient F G).map f) := by
  unfold joinedParameter
  rw [JTBinaryPrismParameter.parameter_mapTime, JTBinaryPrismParameter.parameter_postcomp]
  congr 1
  · simp only [← Category.assoc]
    rw [F.parameter_map f, Category.assoc, ← J.map_comp, Category.assoc, ← J.map_comp]
    exact congrArg (fun m ↦ F.parameter a ≫ J.map m)
      (leftIn_map (F.coefficient.map f) (G.coefficient.map f)).symm
  · simp only [← Category.assoc]
    rw [G.parameter_map f, Category.assoc, ← J.map_comp, Category.assoc, ← J.map_comp]
    exact congrArg (fun m ↦ G.parameter a ≫ J.map m)
      (rightIn_map (F.coefficient.map f) (G.coefficient.map f)).symm

/-- Glue two full families along their shared ordered endpoint.
The resulting data admit the same construction at the next joint. -/
def join : Family time (NecklacesOver.wedge P Q) (code S T) (collapse d c) where
  coefficient := joinedCoefficient F G
  first f := JTParameterBlockOperators.map_first _ _ (F.first f)
  last f := JTParameterBlockOperators.map_last _ _ (G.last f)
  label a := orderedTriplePoint (blockInputs (F.label a) (G.label a))
  label_map {a b} f := by
    exact (JTBinaryPrismLabelOperators.label_map (F.label b) (G.label b)
      (F.coefficient.map f) (G.coefficient.map f) (F.last f) (G.first f)).trans
        (congrArg₂ (fun u v ↦ orderedTriplePoint (blockInputs u v))
          (F.label_map f) (G.label_map f))
  parameter := joinedParameter F G
  parameter_map f := joinedParameter_map F G f
  raw a := raw_over_wedge (F.label a) (G.label a) (joinedParameter F G a) d c
    (F.parameter a) (G.parameter a)
    (JTBinaryPrismParameter.parameter_left _ _ _ _ _ _)
    (JTBinaryPrismParameter.parameter_right _ _ _ _ _ _) (F.raw a) (G.raw a)

end

end DaggerModels.PartII.JTCompatibleTimePrisms
