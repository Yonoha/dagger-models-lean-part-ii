import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTParametrizedTargetPullback

/-! Literal pullback of a decorated graph along subdivisions into the same original necklace. -/

set_option autoImplicit false
set_option maxHeartbeats 900000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativePulledCutComparison

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetLiftTransport (graph)
open DecoratedCylinderNecklacePresentation (underCocone)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : Vertex W}
private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
private abbrev Index := DecoratedNecklaceHomDiagram.Index W x y
private abbrev code (i : Index (W := W) (x := x) (y := y)) := (pr.obj i).1
private abbrev degree (i : Index (W := W) (x := x) (y := y)) := (pr.obj i).2

variable (i : Index (W := W) (x := x) (y := y))

private abbrev operator {S U : NecklaceCode} (f : S ⟶ U) :
    (S, degree i) ⟶ (U, degree i) :=
  (f, 𝟙 (degree i))

/-- Pull the actual ordered label back on a native subdivision, without changing the degree. -/
def label {S : NecklaceCode} (f : S ⟶ code i) : Index (W := W) (x := x) (y := y) :=
  op (P.elementsMk (op (S, degree i)) (P.map (operator i f).op i.unop.2))

/-- Its canonical arrow to the original decorated label carries the literal native inclusion. -/
def toOriginal {S : NecklaceCode} (f : S ⟶ code i) : label i f ⟶ i :=
  (CategoryOfElements.homMk i.unop (label i f).unop (operator i f).op rfl).op

/-- A triangle over the original native code gives the same triangle of restrictions. -/
def labelMap {S U : NecklaceCode} (f : S ⟶ code i) (e : U ⟶ code i)
    (g : S ⟶ U) (h : g ≫ e = f) : label i f ⟶ label i e := by
  refine (CategoryOfElements.homMk (label i e).unop (label i f).unop
    (operator i g).op ?_).op
  change P.map (operator i g).op (P.map (operator i e).op i.unop.2) =
    P.map (operator i f).op i.unop.2
  rw [← FunctorToTypes.map_comp_apply]
  have hop : (operator i e).op ≫ (operator i g).op = (operator i f).op := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (Prod.ext h (Category.id_comp _))
  rw [hop]

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (n : SimplexCategory) (c : code i ⟶ Q.code)
variable (p : (code i).toSSet ⊗ J.obj n ⟶ J.obj (degree i))
variable (hr : (graph (i := i) p).right ≫ ((underCocone W x y).app i).right =
  augmentation (code i) n ≫ c.map ≫ Q.map)

/-- Pull back the original full time graph with the coefficient degree unchanged. -/
abbrev parameter {S : NecklaceCode} (f : S ⟶ code i) :
    S.toSSet ⊗ J.obj n ⟶ J.obj (degree i) :=
  (f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p

include hr in
/-- The raw map of the pulled graph is the exact original raw map after the subdivision. -/
theorem raw {S : NecklaceCode} (f : S ⟶ code i) :
    (graph (i := label i f) (parameter i n p f)).right ≫
        ((underCocone W x y).app (label i f)).right =
      augmentation S n ≫ (f ≫ c).map ≫ Q.map := by
  have hs : (𝟙 (degree i)) ≫ (pr.map (toOriginal i f)).2 = 𝟙 (degree i) := by
    change 𝟙 (degree i) ≫ 𝟙 (degree i) = 𝟙 (degree i)
    exact Category.id_comp _
  have he :=
    JTParametrizedTargetPullback.pulled_raw (toOriginal i f) n (𝟙 (degree i)) hs p Q c hr
  have hp : JTParametrizedTargetPullback.parameter (toOriginal i f) n (𝟙 (degree i)) p =
      parameter i n p f := by
    change (f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p ≫ J.map (𝟙 (degree i)) = _
    rw [J.map_id, Category.comp_id]
  rw [hp] at he
  exact he

/-- Every original internal necklace of the restricted graph is evaluated over the same target. -/
def evaluation {S : NecklaceCode} (f : S ⟶ code i) :=
  JTCylinderOverTarget.functor W x y Q (label i f) S n
    (graph (i := label i f) (parameter i n p f)) (f ≫ c) (raw i n c p hr f)

/-- A commuting native triangle compares the complete evaluations in the original comma. -/
def compare {S U : NecklaceCode} (f : S ⟶ code i) (e : U ⟶ code i)
    (g : S ⟶ U) (h : g ≫ e = f) :=
  JTParametrizedTargetLiftTransport.compare Q (labelMap i f e g h) (𝟙 n)
    (parameter i n p f) (parameter i n p e) (f ≫ c) (e ≫ c)
    (by
      change g ≫ (e ≫ c) = f ≫ c
      rw [← Category.assoc, h])
    (by
      change (g.map ⊗ₘ J.map (𝟙 n)) ≫ ((e.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
        ((f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (degree i))
      rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
        tensorHom_comp_tensorHom, Category.id_comp]
      exact congrArg (fun v : S.toSSet ⟶ (code i).toSSet ↦
        (v ⊗ₘ 𝟙 (J.obj n)) ≫ p) (congrArg (fun q : S ⟶ code i ↦ q.map) h))
    (raw i n c p hr f) (raw i n c p hr e)

end
end DaggerModels.PartII.JTNativePulledCutComparison
