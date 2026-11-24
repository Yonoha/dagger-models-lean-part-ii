import DaggerModelsPartII.JTVariableMiddleWhiskeredDiagram
import DaggerModelsPartII.JTSupportedPathChainLabels

/-! Whisker the complete supported coefficient path with natural outer labels. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSupportedPathWhiskeredDiagram

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open OrderedNecklaceVertexPoints (zeroPoint)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {I : Type} [SmallCategory I] (W : Source)
variable (x z y : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (P R : I ⥤ NecklaceCode)

/-- The outer full coefficients and their four endpoint equations are data on
the original index. The inner endpoints are the same fixed vertex `z`. -/
structure Surroundings where
  left : ∀ a : I, std.obj ((K W z L).obj a) ⟶ labels W (P.obj a)
  right : ∀ a : I, std.obj ((K W z L).obj a) ⟶ labels W (R.obj a)
  left_nat : ∀ {a b : I} (g : a ⟶ b),
    left a = std.map ((K W z L).map g) ≫ left b ≫ pre W (P.map g).map
  right_nat : ∀ {a b : I} (g : a ⟶ b),
    right a = std.map ((K W z L).map g) ≫ right b ≫ pre W (R.map g).map
  global_first : ∀ a : I,
    left a ≫ firstRestriction W (P.obj a) =
      term (std.obj ((K W z L).obj a)) ≫ zeroPoint W x
  inner_left : ∀ a : I,
    left a ≫ lastRestriction W (P.obj a) =
      term (std.obj ((K W z L).obj a)) ≫ zeroPoint W z
  inner_right : ∀ a : I,
    right a ≫ firstRestriction W (R.obj a) =
      term (std.obj ((K W z L).obj a)) ≫ zeroPoint W z
  global_last : ∀ a : I,
    right a ≫ lastRestriction W (R.obj a) =
      term (std.obj ((K W z L).obj a)) ≫ zeroPoint W y

variable (A : Surroundings W x z y L P R)

private abbrev Index := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev base := JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev ord := JTSupportedPathChainLabels.ordinals W z L S u hs
private abbrev α := JTSupportedPathChainLabels.toOldCoefficient W z L S u hs
private abbrev M := base W z L S u hs ⋙ codes L
private abbrev PL := base W z L S u hs ⋙ P
private abbrev RR := base W z L S u hs ⋙ R

/-- The unchanged left coefficient pulled back along the surjective old-degree
chain coordinate. -/
def pulledLeft (p : Index W z L S u hs) :
    std.obj ((ord W z L S u hs).obj p) ⟶
      labels W ((PL W z L S u hs P).obj p) :=
  std.map ((α W z L S u hs).app p) ≫
    A.left ((base W z L S u hs).obj p)

/-- The unchanged right coefficient on the same full chain coordinate. -/
def pulledRight (p : Index W z L S u hs) :
    std.obj ((ord W z L S u hs).obj p) ⟶
      labels W ((RR W z L S u hs R).obj p) :=
  std.map ((α W z L S u hs).app p) ≫
    A.right ((base W z L S u hs).obj p)

private theorem term_map {k l : SimplexCategory} (f : k ⟶ l) :
    std.map f ≫ term (std.obj l) = term (std.obj k) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem pulledLeft_map {p q : Index W z L S u hs} (f : p ⟶ q) :
    pulledLeft W x z y L S u hs P R A p =
      std.map ((ord W z L S u hs).map f) ≫
        pulledLeft W x z y L S u hs P R A q ≫
          pre W ((PL W z L S u hs P).map f).map := by
  unfold pulledLeft
  rw [A.left_nat ((base W z L S u hs).map f)]
  simp only [← Category.assoc, ← std.map_comp]
  exact (congrArg (fun v ↦ std.map v ≫ A.left ((base W z L S u hs).obj q) ≫
    pre W (P.map ((base W z L S u hs).map f)).map)
    ((α W z L S u hs).naturality f)).symm

private theorem pulledRight_map {p q : Index W z L S u hs} (f : p ⟶ q) :
    pulledRight W x z y L S u hs P R A p =
      std.map ((ord W z L S u hs).map f) ≫
        pulledRight W x z y L S u hs P R A q ≫
          pre W ((RR W z L S u hs R).map f).map := by
  unfold pulledRight
  rw [A.right_nat ((base W z L S u hs).map f)]
  simp only [← Category.assoc, ← std.map_comp]
  exact (congrArg (fun v ↦ std.map v ≫ A.right ((base W z L S u hs).obj q) ≫
    pre W (R.map ((base W z L S u hs).map f)).map)
    ((α W z L S u hs).naturality f)).symm

private theorem pulledLeft_first (p : Index W z L S u hs) :
    pulledLeft W x z y L S u hs P R A p ≫
        firstRestriction W ((PL W z L S u hs P).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W x := by
  unfold pulledLeft
  change std.map ((α W z L S u hs).app p) ≫
    A.left ((base W z L S u hs).obj p) ≫
      firstRestriction W (P.obj ((base W z L S u hs).obj p)) = _
  rw [A.global_first ((base W z L S u hs).obj p), ← Category.assoc]
  exact congrArg (· ≫ zeroPoint W x) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem pulledLeft_last (p : Index W z L S u hs) :
    pulledLeft W x z y L S u hs P R A p ≫
        lastRestriction W ((PL W z L S u hs P).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W z := by
  unfold pulledLeft
  change std.map ((α W z L S u hs).app p) ≫
    A.left ((base W z L S u hs).obj p) ≫
      lastRestriction W (P.obj ((base W z L S u hs).obj p)) = _
  rw [A.inner_left ((base W z L S u hs).obj p), ← Category.assoc]
  exact congrArg (· ≫ zeroPoint W z) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem pulledRight_first (p : Index W z L S u hs) :
    pulledRight W x z y L S u hs P R A p ≫
        firstRestriction W ((RR W z L S u hs R).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W z := by
  unfold pulledRight
  change std.map ((α W z L S u hs).app p) ≫
    A.right ((base W z L S u hs).obj p) ≫
      firstRestriction W (R.obj ((base W z L S u hs).obj p)) = _
  rw [A.inner_right ((base W z L S u hs).obj p), ← Category.assoc]
  exact congrArg (· ≫ zeroPoint W z) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem pulledRight_last (p : Index W z L S u hs) :
    pulledRight W x z y L S u hs P R A p ≫
        lastRestriction W ((RR W z L S u hs R).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W y := by
  unfold pulledRight
  change std.map ((α W z L S u hs).app p) ≫
    A.right ((base W z L S u hs).obj p) ≫
      lastRestriction W (R.obj ((base W z L S u hs).obj p)) = _
  rw [A.global_last ((base W z L S u hs).obj p), ← Category.assoc]
  exact congrArg (· ≫ zeroPoint W y) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem middle_first (p : Index W z L S u hs) :
    JTSupportedPathChainLabels.coefficientMap W z L S u hs p ≫
        firstRestriction W ((M W z L S u hs).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W z := by
  rw [← JTSupportedPathChainLabels.orderedPoint_coefficient]
  exact JTOrderedLabelBinaryGlue.coefficient_first W z z
    ((M W z L S u hs).obj p) ((ord W z L S u hs).obj p)
    (JTSupportedPathChainLabels.orderedPoint W z L S u hs p)

private theorem middle_last (p : Index W z L S u hs) :
    JTSupportedPathChainLabels.coefficientMap W z L S u hs p ≫
        lastRestriction W ((M W z L S u hs).obj p) =
      term (std.obj ((ord W z L S u hs).obj p)) ≫ zeroPoint W z := by
  rw [← JTSupportedPathChainLabels.orderedPoint_coefficient]
  exact JTOrderedLabelBinaryGlue.coefficient_last W z z
    ((M W z L S u hs).obj p) ((ord W z L S u hs).obj p)
    (JTSupportedPathChainLabels.orderedPoint W z L S u hs p)

/-- The actual chain simplex gives the full three-piece coefficient data,
with the middle equal to the literal supported path coefficient. -/
def data (p : Index W z L S u hs) :
    JTThreePieceLabelOperators.Data W
      ((PL W z L S u hs P).obj p)
      ((M W z L S u hs).obj p)
      ((RR W z L S u hs R).obj p)
      ((ord W z L S u hs).obj p) x y where
  left := pulledLeft W x z y L S u hs P R A p
  middle := JTSupportedPathChainLabels.coefficientMap W z L S u hs p
  right := pulledRight W x z y L S u hs P R A p
  left_join := (pulledLeft_last W x z y L S u hs P R A p).trans
    (middle_first W z L S u hs p).symm
  right_join := (middle_last W z L S u hs p).trans
    (pulledRight_first W x z y L S u hs P R A p).symm
  first := pulledLeft_first W x z y L S u hs P R A p
  last := pulledRight_last W x z y L S u hs P R A p

theorem data_left (p : Index W z L S u hs) :
    (data W x z y L S u hs P R A p).left =
      std.map ((JTSupportedPathChainLabels.toOldCoefficient
        W z L S u hs).app p) ≫
        A.left ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj p) := rfl

theorem data_middle (p : Index W z L S u hs) :
    (data W x z y L S u hs P R A p).middle =
      JTSupportedPathChainLabels.coefficientMap W z L S u hs p := rfl

theorem data_right (p : Index W z L S u hs) :
    (data W x z y L S u hs P R A p).right =
      std.map ((JTSupportedPathChainLabels.toOldCoefficient
        W z L S u hs).app p) ≫
        A.right ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj p) := rfl

/-- The supported path is the literal changing middle coefficient of a
three-piece decorated diagram, with both original outer families whiskered. -/
def variableMiddleFamily : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y)
    (PL W z L S u hs P) (M W z L S u hs)
    (RR W z L S u hs R) (ord W z L S u hs) where
  data p := data W x z y L S u hs P R A p
  left_nat f := pulledLeft_map W x z y L S u hs P R A f
  middle_nat f := by
    exact JTSupportedPathChainLabels.coefficientMap_map W z L S u hs f
  right_nat f := pulledRight_map W x z y L S u hs P R A f

/-- The full globally whiskered decorated-label functor on every higher
supported-path chain simplex. -/
def labels : Index W z L S u hs ⥤ DecoratedNecklaceHomDiagram.Index W x y :=
  (variableMiddleFamily W x z y L S u hs P R A).labels

theorem labels_projection (p : Index W z L S u hs) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        ((labels W x z y L S u hs P R A).obj p) =
      (wedge ((PL W z L S u hs P).obj p)
        (wedge ((M W z L S u hs).obj p)
          ((RR W z L S u hs R).obj p)),
        (ord W z L S u hs).obj p) :=
  JTVariableMiddleWhiskeredDiagram.Family.labels_projection
    (variableMiddleFamily W x z y L S u hs P R A) p

theorem labels_projection_explicit (p : Index W z L S u hs) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        ((labels W x z y L S u hs P R A).obj p) =
      (wedge (P.obj ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj p))
        (wedge ((codes L).obj
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj p))
          (R.obj ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj p))),
        (JTSupportedPathChainLabels.ordinals W z L S u hs).obj p) :=
  labels_projection W x z y L S u hs P R A p

theorem labels_map_projection {p q : Index W z L S u hs} (f : p ⟶ q) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        ((labels W x z y L S u hs P R A).map f) =
      (wedgeMap ((PL W z L S u hs P).map f)
        (wedgeMap ((M W z L S u hs).map f)
          ((RR W z L S u hs R).map f)),
        (ord W z L S u hs).map f) :=
  JTVariableMiddleWhiskeredDiagram.Family.arrow_projection
    (variableMiddleFamily W x z y L S u hs P R A) f

theorem labels_map_projection_explicit {p q : Index W z L S u hs}
    (f : p ⟶ q) :
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        ((labels W x z y L S u hs P R A).map f) =
      (wedgeMap (P.map ((JTSupportedPathChainLabels.toOriginal W z L S u hs).map f))
        (wedgeMap ((codes L).map
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).map f))
          (R.map ((JTSupportedPathChainLabels.toOriginal W z L S u hs).map f))),
        (JTSupportedPathChainLabels.ordinals W z L S u hs).map f) :=
  labels_map_projection W x z y L S u hs P R A f

end
end DaggerModels.PartII.JTSupportedPathWhiskeredDiagram
