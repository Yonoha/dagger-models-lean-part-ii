import DaggerModelsPartII.JTSupportedCoefficientPathCover
import DaggerModelsPartII.TimePrismChainProjection
import DaggerModelsPartII.JTOrderedLabelWedge
import DaggerModelsPartII.JTSupportedPathPrismRaw

/-! Same-degree ordered labels on two successive full prism-chain covers. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathChainLabels

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open OrderedNecklaceLabelDiagram (necklaceLabels necklaceBoundaryRestriction
  orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)

private abbrev C := JTSupportedCoefficientPathCover.Cover W z L S u hs
private abbrev CK := JTSupportedCoefficientPathCover.coefficient W z L S u hs
private abbrev CN := JTSupportedCoefficientPathCover.choiceTime W z L S u hs

/-- First cover: chains through old coefficient degree and path choice time. -/
abbrev First := TimePrismChainDiagram.Index (CK W z L S u hs) (CN W z L S u hs)

private abbrev firstBase := TimePrismChainDiagram.base (CK W z L S u hs) (CN W z L S u hs)
private abbrev firstOrd := TimePrismChainDiagram.ordinals (CK W z L S u hs) (CN W z L S u hs)
private abbrev firstOld := TimePrismChainDiagram.coeffProjection (CK W z L S u hs) (CN W z L S u hs)
private abbrev firstChoice := TimePrismChainDiagram.timeProjection
  (CK W z L S u hs) (CN W z L S u hs)

/-- Second cover: chains through the first ordinal and the contraction interval. -/
abbrev Index := TimePrismChainDiagram.Index (firstOrd W z L S u hs)
  ((Functor.const (First W z L S u hs)).obj ⦋1⦌)

/-- The final chain ordinal used by the actual decorated label. -/
abbrev ordinals : Index W z L S u hs ⥤ SimplexCategory :=
  TimePrismChainDiagram.ordinals _ _

private abbrev secondBase : Index W z L S u hs ⥤ First W z L S u hs :=
  TimePrismChainDiagram.base _ _

private abbrev secondCoefficient : ordinals W z L S u hs ⟶
    secondBase W z L S u hs ⋙ firstOrd W z L S u hs :=
  TimePrismChainDiagram.coeffProjection _ _

/-- Projection to the original decorated diagram through both chain covers. -/
abbrev toOriginal : Index W z L S u hs ⥤ I :=
  secondBase W z L S u hs ⋙ firstBase W z L S u hs ⋙
    JTSupportedCoefficientPathCover.projection W z L S u hs

/-- The old coefficient coordinate in each second-level chain. -/
def toOldCoefficient : ordinals W z L S u hs ⟶
    toOriginal W z L S u hs ⋙ K W z L :=
  secondCoefficient W z L S u hs ≫
    Functor.whiskerLeft (secondBase W z L S u hs) (firstOld W z L S u hs)

/-- The original full path-choice simplex coordinate. -/
def toChoice : ordinals W z L S u hs ⟶
    secondBase W z L S u hs ⋙ firstBase W z L S u hs ⋙ CN W z L S u hs :=
  secondCoefficient W z L S u hs ≫
    Functor.whiskerLeft (secondBase W z L S u hs) (firstChoice W z L S u hs)

/-- The contraction interval coordinate, at every higher chain simplex. -/
abbrev toInterval : ordinals W z L S u hs ⟶
    (Functor.const (Index W z L S u hs)).obj ⦋1⦌ :=
  TimePrismChainDiagram.timeProjection _ _

/-- Every vertex of the old coefficient occurs in the final chain. -/
theorem toOldCoefficient_surjective (p : Index W z L S u hs) :
    Function.Surjective ((toOldCoefficient W z L S u hs).app p).toOrderHom := by
  have h₂ := TimePrismChainDiagram.coeffProjection_surjective
    (firstOrd W z L S u hs)
    ((Functor.const (First W z L S u hs)).obj ⦋1⦌) p
  have h₁ := TimePrismChainDiagram.coeffProjection_surjective
    (CK W z L S u hs) (CN W z L S u hs)
      ((secondBase W z L S u hs).obj p)
  exact h₁.comp h₂

/-- Both chain covers and the full path-choice cover are weak over I. -/
theorem toOriginal_weak
    (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((codes L).obj a).len) :
    WeakEquivalence (nerveMap (toOriginal W z L S u hs)) := by
  haveI : WeakEquivalence (nerveMap (secondBase W z L S u hs)) :=
    TimePrismChainProjection.projection_weak _ _
  haveI : WeakEquivalence (nerveMap (firstBase W z L S u hs)) :=
    TimePrismChainProjection.projection_weak _ _
  haveI : WeakEquivalence (nerveMap
      (JTSupportedCoefficientPathCover.projection W z L S u hs)) :=
    JTSupportedCoefficientPathCover.projection_weak W z L S u hs hu hW hp
  change WeakEquivalence (nerveMap (secondBase W z L S u hs) ≫
    nerveMap (firstBase W z L S u hs) ≫
      nerveMap (JTSupportedCoefficientPathCover.projection W z L S u hs))
  infer_instance

private abbrev pathBase (p : Index W z L S u hs) : C W z L S u hs :=
  (firstBase W z L S u hs).obj ((secondBase W z L S u hs).obj p)

private abbrev oldBase (p : Index W z L S u hs) : I :=
  (JTSupportedCoefficientPathCover.projection W z L S u hs).obj
    (pathBase W z L S u hs p)

/-- The interval and higher-choice coordinates on the final single chain. -/
def pathTime (p : Index W z L S u hs) :
    std.obj ((ordinals W z L S u hs).obj p) ⟶
      std.obj ⦋1⦌ ⊗
        std.obj ((CN W z L S u hs).obj (pathBase W z L S u hs p)) :=
  lift (std.map ((toInterval W z L S u hs).app p))
    (std.map ((toChoice W z L S u hs).app p))

/-- The literal full path prism pulled back to one final chain simplex. -/
def coefficientMap (p : Index W z L S u hs) :
    std.obj ((ordinals W z L S u hs).obj p) ⟶
      (necklaceLabels W).obj (op ((codes L).obj (oldBase W z L S u hs p))) :=
  lift (std.map ((toOldCoefficient W z L S u hs).app p))
      (pathTime W z L S u hs p) ≫
    JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
      (oldBase W z L S u hs p)
      ((CN W z L S u hs).obj (pathBase W z L S u hs p))
      (pathBase W z L S u hs p).unop.2

/-- The coefficient is the stated nested lift, with no degree replacement. -/
theorem coefficientMap_eq (p : Index W z L S u hs) :
    coefficientMap W z L S u hs p =
      lift (std.map ((toOldCoefficient W z L S u hs).app p))
        (lift (std.map ((toInterval W z L S u hs).app p))
          (std.map ((toChoice W z L S u hs).app p))) ≫
        JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
          (oldBase W z L S u hs p)
          ((CN W z L S u hs).obj (pathBase W z L S u hs p))
          (pathBase W z L S u hs p).unop.2 := rfl

/-- Its outer native endpoints remain the original prescribed point. -/
theorem coefficientMap_boundary (p : Index W z L S u hs) :
    coefficientMap W z L S u hs p ≫
        (necklaceBoundaryRestriction W).app
          (op ((codes L).obj (oldBase W z L S u hs p))) =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ boundaryPoint W z z := by
  unfold coefficientMap
  rw [Category.assoc, JTSupportedCoefficientPathCover.pathCoefficient_boundary]
  simp only [← Category.assoc, lift_fst]
  change std.map ((toOldCoefficient W z L S u hs).app p) ≫
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ boundaryPoint W z z) = _
  rw [← Category.assoc]
  congr 1

private theorem pathTime_map {p q : Index W z L S u hs} (f : p ⟶ q) :
    std.map ((ordinals W z L S u hs).map f) ≫ pathTime W z L S u hs q =
      pathTime W z L S u hs p ≫
        (𝟙 (std.obj ⦋1⦌) ⊗ₘ
          std.map ((CN W z L S u hs).map
            ((firstBase W z L S u hs).map
              ((secondBase W z L S u hs).map f)))) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg std.map ((toInterval W z L S u hs).naturality f)
  · exact congrArg std.map ((toChoice W z L S u hs).naturality f)

private theorem chainChart_map {p q : Index W z L S u hs} (f : p ⟶ q) :
    std.map ((ordinals W z L S u hs).map f) ≫
      lift (std.map ((toOldCoefficient W z L S u hs).app q))
        (pathTime W z L S u hs q) =
    lift (std.map ((toOldCoefficient W z L S u hs).app p))
        (pathTime W z L S u hs p) ≫
      (std.map ((K W z L).map ((toOriginal W z L S u hs).map f)) ⊗ₘ
        (𝟙 (std.obj ⦋1⦌) ⊗ₘ
          std.map ((CN W z L S u hs).map
            ((firstBase W z L S u hs).map
              ((secondBase W z L S u hs).map f))))) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg std.map ((toOldCoefficient W z L S u hs).naturality f)
  · exact pathTime_map W z L S u hs f

private theorem coverElement_mixed
    {p q : C W z L S u hs} (f : p ⟶ q) :
    p.unop.2 =
      ((JTSupportedCoefficientPathCover.spaces W z L S u hs).map
        ((JTSupportedCoefficientPathCover.projection W z L S u hs).map f).op).app
        (op ((CN W z L S u hs).obj p))
          (((JTSupportedCoefficientPathCover.spaces W z L S u hs).obj
            (op ((JTSupportedCoefficientPathCover.projection W z L S u hs).obj q))).map
              ((CN W z L S u hs).map f).op q.unop.2) := by
  have h := f.unop.property.symm
  have hn := congrFun (((JTSupportedCoefficientPathCover.spaces W z L S u hs).map
      ((JTSupportedCoefficientPathCover.projection W z L S u hs).map f).op).naturality
        ((CN W z L S u hs).map f).op) q.unop.2
  exact h.trans hn.symm

private theorem pathCoefficient_cover
    {p q : C W z L S u hs} (f : p ⟶ q) :
    JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
      ((JTSupportedCoefficientPathCover.projection W z L S u hs).obj p)
      ((CN W z L S u hs).obj p) p.unop.2 =
    (std.map ((K W z L).map
      ((JTSupportedCoefficientPathCover.projection W z L S u hs).map f)) ⊗ₘ
        (std.obj ⦋1⦌ ◁ std.map ((CN W z L S u hs).map f))) ≫
      JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
        ((JTSupportedCoefficientPathCover.projection W z L S u hs).obj q)
        ((CN W z L S u hs).obj q) q.unop.2 ≫
          (((codes L).op ⋙ necklaceLabels W).map
            ((JTSupportedCoefficientPathCover.projection W z L S u hs).map f).op) := by
  rw [coverElement_mixed W z L S u hs f]
  exact JTSupportedCoefficientPathCover.pathCoefficient_mixed W z L S u hs
    ((JTSupportedCoefficientPathCover.projection W z L S u hs).map f)
    ((CN W z L S u hs).map f) q.unop.2

/-- The pulled coefficient obeys both the old native arrow and the final
chain ordinal arrow. -/
theorem coefficientMap_map {p q : Index W z L S u hs} (f : p ⟶ q) :
    coefficientMap W z L S u hs p =
      std.map ((ordinals W z L S u hs).map f) ≫
        coefficientMap W z L S u hs q ≫
          (((codes L).op ⋙ necklaceLabels W).map
            ((toOriginal W z L S u hs).map f).op) := by
  let g : pathBase W z L S u hs p ⟶ pathBase W z L S u hs q :=
    (firstBase W z L S u hs).map ((secondBase W z L S u hs).map f)
  have hp := pathCoefficient_cover W z L S u hs g
  have hc := chainChart_map W z L S u hs f
  rw [MonoidalCategory.id_tensorHom] at hc
  change std.map ((ordinals W z L S u hs).map f) ≫
      lift (std.map ((toOldCoefficient W z L S u hs).app q))
        (pathTime W z L S u hs q) =
    lift (std.map ((toOldCoefficient W z L S u hs).app p))
        (pathTime W z L S u hs p) ≫
      (std.map ((K W z L).map
        ((JTSupportedCoefficientPathCover.projection W z L S u hs).map g)) ⊗ₘ
          (std.obj ⦋1⦌ ◁ std.map ((CN W z L S u hs).map g))) at hc
  unfold coefficientMap
  rw [hp]
  change _ = _
  rw [← Category.assoc, ← Category.assoc]
  rw [← hc]
  rfl

/-- The exact ordered simplex carried by one final path-chain coefficient. -/
def orderedPoint (p : Index W z L S u hs) :
    ((orderedNecklaceLabels W (boundaryPoint W z z)).obj
      (op ((codes L).obj (oldBase W z L S u hs p)))).obj
        (op ((ordinals W z L S u hs).obj p)) :=
  SSet.yonedaEquiv (pullback.lift (coefficientMap W z L S u hs p)
    (SSet.stdSimplex.isTerminalObj₀.from _)
    (coefficientMap_boundary W z L S u hs p))

theorem orderedPoint_coefficient (p : Index W z L S u hs) :
    JTOrderedLabelBinaryGlue.coefficient W z z
      ((codes L).obj (oldBase W z L S u hs p))
      ((ordinals W z L S u hs).obj p)
      (orderedPoint W z L S u hs p) = coefficientMap W z L S u hs p := by
  rw [JTOrderedLabelWedge.coefficient_projection]
  simp only [orderedPoint, Equiv.symm_apply_apply, pullback.lift_fst]

/-- The decorated object has exactly the original native code. -/
def label (p : Index W z L S u hs) :
    DecoratedNecklaceHomDiagram.Index W z z :=
  OrderedLabelElements.mk W (boundaryPoint W z z)
    ((codes L).obj (oldBase W z L S u hs p))
    ((ordinals W z L S u hs).obj p) (orderedPoint W z L S u hs p)

/-- The exact native and ordinal operators transport the selected label. -/
def labelMap {p q : Index W z L S u hs} (f : p ⟶ q) :
    label W z L S u hs p ⟶ label W z L S u hs q :=
  JTOrderedLabelWedge.indexHomOfCoefficient
    ((codes L).map ((toOriginal W z L S u hs).map f))
    ((ordinals W z L S u hs).map f)
    (orderedPoint W z L S u hs p) (orderedPoint W z L S u hs q) (by
      change JTOrderedLabelBinaryGlue.coefficient W z z
          ((codes L).obj (oldBase W z L S u hs p))
          ((ordinals W z L S u hs).obj p) (orderedPoint W z L S u hs p) =
        std.map ((ordinals W z L S u hs).map f) ≫
          JTOrderedLabelBinaryGlue.coefficient W z z
            ((codes L).obj (oldBase W z L S u hs q))
            ((ordinals W z L S u hs).obj q)
            (orderedPoint W z L S u hs q) ≫
              (((codes L).op ⋙ necklaceLabels W).map
                ((toOriginal W z L S u hs).map f).op)
      rw [orderedPoint_coefficient, orderedPoint_coefficient]
      exact coefficientMap_map W z L S u hs f)

private theorem labelMap_projection {p q : Index W z L S u hs}
    (f : p ⟶ q) :
    (OrderedLabelElements.projection W (boundaryPoint W z z)).map
      (labelMap W z L S u hs f) =
      (((codes L).map ((toOriginal W z L S u hs).map f)),
        (ordinals W z L S u hs).map f) := rfl

private theorem hom_ext {a b : DecoratedNecklaceHomDiagram.Index W z z}
    {f g : a ⟶ b}
    (h : (OrderedLabelElements.projection W (boundaryPoint W z z)).map f =
      (OrderedLabelElements.projection W (boundaryPoint W z z)).map g) :
    f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

/-- Genuine decorated labels for every object and arrow of both full chain
covers, retaining the original native code and ordered boundary point. -/
def labels : Index W z L S u hs ⥤
    DecoratedNecklaceHomDiagram.Index W z z where
  obj p := label W z L S u hs p
  map f := labelMap W z L S u hs f
  map_id p := by
    apply hom_ext W z
    rw [labelMap_projection,
      (OrderedLabelElements.projection W (boundaryPoint W z z)).map_id,
      (toOriginal W z L S u hs).map_id,
      (ordinals W z L S u hs).map_id, (codes L).map_id]
    rfl
  map_comp f g := by
    apply hom_ext W z
    rw [labelMap_projection,
      (OrderedLabelElements.projection W (boundaryPoint W z z)).map_comp,
      labelMap_projection, labelMap_projection,
      (toOriginal W z L S u hs).map_comp,
      (ordinals W z L S u hs).map_comp,
      (codes L).map_comp]
    rfl

/-- The label functor projects to the unchanged native diagram and final
chain ordinal, with literal componentwise operators. -/
theorem labels_projection (p : Index W z L S u hs) :
    (OrderedLabelElements.projection W (boundaryPoint W z z)).obj
      ((labels W z L S u hs).obj p) =
      (((codes L).obj ((toOriginal W z L S u hs).obj p)),
        (ordinals W z L S u hs).obj p) := rfl

/-- The actual decorated label has exactly the nested lifted path
coefficient, at the same native code and final chain degree. -/
theorem labels_coefficient (p : Index W z L S u hs) :
    JTOrderedLabelBinaryGlue.coefficient W z z
      ((codes L).obj ((toOriginal W z L S u hs).obj p))
      ((ordinals W z L S u hs).obj p)
      (OrderedLabelElements.label W (boundaryPoint W z z)
        ((labels W z L S u hs).obj p)) =
      coefficientMap W z L S u hs p :=
  orderedPoint_coefficient W z L S u hs p

/-- The decorated arrow uses the original native operator and final
chain ordinal operator without any replacement. -/
theorem labels_map_projection {p q : Index W z L S u hs} (f : p ⟶ q) :
    (OrderedLabelElements.projection W (boundaryPoint W z z)).map
      ((labels W z L S u hs).map f) =
      (((codes L).map ((toOriginal W z L S u hs).map f)),
        (ordinals W z L S u hs).map f) :=
  labelMap_projection W z L S u hs f

/-- Every final chain retains the joint raw equation on any graph whose
parameter factors through the original full support. -/
theorem coefficientMap_raw (p : Index W z L S u hs)
    [Mono (u.app (oldBase W z L S u hs p))]
    {X : SSet.{0}}
    (h : X ⟶ ((codes L).obj (oldBase W z L S u hs p)).toSSet)
    (θ : X ⟶ J.obj ((ordinals W z L S u hs).obj p))
    (q : X ⟶ J.obj (S.obj (oldBase W z L S u hs p)))
    (hθ : θ ≫ J.map ((toOldCoefficient W z L S u hs).app p) =
      q ≫ J.map (u.app (oldBase W z L S u hs p))) :
    lift h θ ≫ JTNecklaceLabelRealization.realizedLabel
      ((codes L).obj (oldBase W z L S u hs p)).toSSet W
      ((ordinals W z L S u hs).obj p)
        (SSet.yonedaEquiv (coefficientMap W z L S u hs p)) =
      h ≫ term _ ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  exact JTSupportedPathPrismRaw.chain_raw W z L S u hs
    (oldBase W z L S u hs p)
    ((CN W z L S u hs).obj (pathBase W z L S u hs p))
    (pathBase W z L S u hs p).unop.2
    ((toOldCoefficient W z L S u hs).app p)
    (pathTime W z L S u hs p)
    (toOldCoefficient_surjective W z L S u hs p)
    h θ q hθ

end
end DaggerModels.PartII.JTSupportedPathChainLabels
