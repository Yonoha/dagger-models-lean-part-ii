import DaggerModelsPartII.JTSupportedPathChainLabels
import DaggerModelsPartII.JTConstantOrderedLabelDiagram

/-! Endpoint sections of the second full path-chain cover. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.ReversalDiscreteFreeColimits (discreteFree)

namespace DaggerModels.PartII.JTSupportedPathChainEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)

private abbrev First := JTSupportedPathChainLabels.First W z L S u hs
private abbrev Index := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev firstOrd := TimePrismChainDiagram.ordinals
  (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
  (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)

/-- The complete chain at one fixed endpoint of the interval. -/
def constantIntervalChain (k : ℕ) (b : Fin 2) : TimePrismChain.Chain k 1 where
  vertices := {v | v.2 = b}
  chain := by
    intro a ha c hc _
    change a.2 = b at ha
    change c.2 = b at hc
    rcases le_total a.1 c.1 with h | h
    · exact Or.inl ⟨h, ha.le.trans hc.ge⟩
    · exact Or.inr ⟨h, hc.le.trans ha.ge⟩
  covers i := ⟨b, rfl⟩

/-- Reinsert the whole first chain at an interval endpoint. -/
def endpointSection (b : Fin 2) : First W z L S u hs ⥤ Index W z L S u hs where
  obj p := ⟨p, constantIntervalChain ((firstOrd W z L S u hs).obj p).len b⟩
  map f := ⟨f, by
    intro v hv
    change v.2 = b at hv
    change (TimePrismChainDiagram.imageVertex
      (firstOrd W z L S u hs)
      ((Functor.const (First W z L S u hs)).obj ⦋1⦌) f v).2 = b
    simpa [TimePrismChainDiagram.imageVertex] using hv⟩
  map_id p := TimePrismChainDiagram.hom_ext _ _ rfl
  map_comp f g := TimePrismChainDiagram.hom_ext _ _ rfl

/-- Forgetting the second chain exactly recovers the original first chain. -/
theorem endpointSection_base (b : Fin 2) :
    endpointSection W z L S u hs b ⋙
      TimePrismChainDiagram.base (firstOrd W z L S u hs)
        ((Functor.const (First W z L S u hs)).obj ⦋1⦌) =
      𝟭 (First W z L S u hs) := rfl

/-- Hence the full projection recovers the same original decorated index. -/
theorem endpointSection_original (b : Fin 2) :
    endpointSection W z L S u hs b ⋙
      JTSupportedPathChainLabels.toOriginal W z L S u hs =
    TimePrismChainDiagram.base
        (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
        (JTSupportedCoefficientPathCover.choiceTime W z L S u hs) ⋙
      JTSupportedCoefficientPathCover.projection W z L S u hs := rfl

/-- Each literal endpoint section is weak because its retraction to the
first chain cover is weak. No fibrancy assumption is needed here. -/
theorem endpointSection_weak (b : Fin 2) :
    WeakEquivalence (nerveMap (endpointSection W z L S u hs b)) := by
  haveI : WeakEquivalence (nerveMap
      (TimePrismChainDiagram.base (firstOrd W z L S u hs)
        ((Functor.const (First W z L S u hs)).obj ⦋1⦌))) :=
    TimePrismChainProjection.projection_weak _ _
  have h : nerveMap (endpointSection W z L S u hs b) ≫
      nerveMap (TimePrismChainDiagram.base (firstOrd W z L S u hs)
        ((Functor.const (First W z L S u hs)).obj ⦋1⦌)) = 𝟙 _ := by
    change nerveMap (endpointSection W z L S u hs b ⋙
      TimePrismChainDiagram.base (firstOrd W z L S u hs)
        ((Functor.const (First W z L S u hs)).obj ⦋1⦌)) = 𝟙 _
    rw [endpointSection_base]
    rfl
  exact weakEquivalence_of_postcomp_of_fac h

/-- The second chain has the prescribed constant interval coordinate. -/
theorem endpointSection_interval (b : Fin 2) (p : First W z L S u hs) :
    (JTSupportedPathChainLabels.toInterval W z L S u hs).app
        ((endpointSection W z L S u hs b).obj p) =
      SimplexCategory.const _ ⦋1⦌ b := by
  ext i : 3
  change ((TimePrismChainDiagram.enumerate
    (constantIntervalChain ((firstOrd W z L S u hs).obj p).len b) i).val).2 = b
  exact (TimePrismChainDiagram.enumerate
    (constantIntervalChain ((firstOrd W z L S u hs).obj p).len b) i).property

private theorem intervalVertex_zero :
    SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι =
      std.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
  apply SSet.yonedaEquiv.injective
  rfl

private theorem intervalVertex_one :
    SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι =
      std.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
  apply SSet.yonedaEquiv.injective
  rfl

private def intervalVertex (b : Fin 2) : std.obj ⦋0⦌ ⟶ std.obj ⦋1⦌ :=
  std.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ b)

private theorem endpointSection_intervalMap (b : Fin 2)
    (p : First W z L S u hs) :
    std.map ((JTSupportedPathChainLabels.toInterval W z L S u hs).app
      ((endpointSection W z L S u hs b).obj p)) =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ intervalVertex b := by
  rw [endpointSection_interval]
  have hc : SimplexCategory.const
      ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
        ((endpointSection W z L S u hs b).obj p)) ⦋1⦌ b =
      SimplexCategory.isTerminalZero.from _ ≫
        SimplexCategory.const ⦋0⦌ ⦋1⦌ b := by
    ext i : 3
    rfl
  rw [hc, std.map_comp]
  congr 1

private theorem endpointSection_pathTime (b : Fin 2)
    (p : First W z L S u hs) :
    JTSupportedPathChainLabels.pathTime W z L S u hs
      ((endpointSection W z L S u hs b).obj p) =
      lift (SSet.stdSimplex.isTerminalObj₀.from _)
        (std.map ((JTSupportedPathChainLabels.toChoice W z L S u hs).app
          ((endpointSection W z L S u hs b).obj p))) ≫
        (intervalVertex b ▷
          std.obj ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
            ((TimePrismChainDiagram.base
              (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
              (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p))) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact endpointSection_intervalMap W z L S u hs b p
  · rfl

private theorem endpointCoefficient (b : Fin 2)
    (p : First W z L S u hs)
    (c : std.obj ((K W z L).obj
      ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
        ((endpointSection W z L S u hs b).obj p))) ⟶
      (OrderedNecklaceLabelDiagram.necklaceLabels W).obj
        (op ((JTParametrizedTargetFamilies.codes L).obj
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
            ((endpointSection W z L S u hs b).obj p)))))
    (hEnd : ((std.obj ((K W z L).obj
        ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
          ((endpointSection W z L S u hs b).obj p)))) ◁
        (intervalVertex b ▷
          std.obj ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
            ((TimePrismChainDiagram.base
              (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
              (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p)))) ≫
      JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
        ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
          ((endpointSection W z L S u hs b).obj p))
        ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
          ((TimePrismChainDiagram.base
            (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
            (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p))
        ((TimePrismChainDiagram.base
          (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
          (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p).unop.2 =
      fst _ (std.obj ⦋0⦌ ⊗ std.obj
        ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
          ((TimePrismChainDiagram.base
            (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
            (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p))) ≫ c) :
    JTSupportedPathChainLabels.coefficientMap W z L S u hs
        ((endpointSection W z L S u hs b).obj p) =
      std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpointSection W z L S u hs b).obj p)) ≫ c := by
  let s := (endpointSection W z L S u hs b).obj p
  let a := (JTSupportedPathChainLabels.toOriginal W z L S u hs).obj s
  let n := (JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
    ((TimePrismChainDiagram.base
      (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
      (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p)
  let d := (JTSupportedPathChainLabels.ordinals W z L S u hs).obj s
  let α := (JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app s
  let t₀ : std.obj d ⟶ std.obj ⦋0⦌ ⊗ std.obj n :=
    lift (SSet.stdSimplex.isTerminalObj₀.from _)
      (std.map ((JTSupportedPathChainLabels.toChoice W z L S u hs).app s))
  have hchart : lift (std.map α)
      (JTSupportedPathChainLabels.pathTime W z L S u hs s) =
    lift (std.map α) t₀ ≫
      ((𝟙 (std.obj ((K W z L).obj a))) ⊗ₘ
        (intervalVertex b ▷ std.obj n)) := by
    apply CartesianMonoidalCategory.hom_ext
    · rfl
    · exact endpointSection_pathTime W z L S u hs b p
  change lift (std.map α)
      (JTSupportedPathChainLabels.pathTime W z L S u hs s) ≫ _ = _
  rw [hchart]
  have heq : (𝟙 (std.obj ((K W z L).obj a))) ⊗ₘ
      (intervalVertex b ▷ std.obj n) =
        (std.obj ((K W z L).obj a)) ◁ (intervalVertex b ▷ std.obj n) :=
    MonoidalCategory.id_tensorHom _ _
  rw [heq]
  simp only [Category.assoc]
  have hh : (std.obj ((K W z L).obj a) ◁
      (intervalVertex b ▷ std.obj n)) ≫
      JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
        a n ((TimePrismChainDiagram.base
          (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
          (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p).unop.2 =
      fst (std.obj ((K W z L).obj a)) (std.obj ⦋0⦌ ⊗ std.obj n) ≫ c := hEnd
  change lift (std.map α) t₀ ≫
      ((std.obj ((K W z L).obj a) ◁ (intervalVertex b ▷ std.obj n)) ≫
        JTSupportedCoefficientPathCover.pathCoefficient W z L S u hs
          a n ((TimePrismChainDiagram.base
            (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
            (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p).unop.2) =
    std.map α ≫ c
  rw [hh]
  rw [← Category.assoc, lift_fst]

/-- The zero endpoint recovers the old coefficient at the original old
degree, pulled back only along the final chain ordinal. -/
theorem coefficientMap_zero (p : First W z L S u hs) :
    JTSupportedPathChainLabels.coefficientMap W z L S u hs
        ((endpointSection W z L S u hs 0).obj p) =
      std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpointSection W z L S u hs 0).obj p)) ≫
        JTSupportedOrderedCoefficientChoices.old W z L
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
            ((endpointSection W z L S u hs 0).obj p)) := by
  apply endpointCoefficient W z L S u hs 0 p
  unfold intervalVertex
  rw [← intervalVertex_zero]
  exact JTSupportedCoefficientPathCover.pathCoefficient_zero_old W z L S u hs
    ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
      ((endpointSection W z L S u hs 0).obj p))
    ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
      ((TimePrismChainDiagram.base
        (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
        (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p))
    ((TimePrismChainDiagram.base
      (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
      (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p).unop.2

/-- The one endpoint is the literal full-degree constant coefficient. -/
theorem coefficientMap_one (p : First W z L S u hs) :
    JTSupportedPathChainLabels.coefficientMap W z L S u hs
        ((endpointSection W z L S u hs 1).obj p) =
      std.map ((JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpointSection W z L S u hs 1).obj p)) ≫
        JTSupportedOrderedCoefficientChoices.constant W z L
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
            ((endpointSection W z L S u hs 1).obj p)) := by
  apply endpointCoefficient W z L S u hs 1 p
  unfold intervalVertex
  rw [← intervalVertex_one]
  exact JTSupportedCoefficientPathCover.pathCoefficient_one_constant W z L S u hs
    ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
      ((endpointSection W z L S u hs 1).obj p))
    ((JTSupportedCoefficientPathCover.choiceTime W z L S u hs).obj
      ((TimePrismChainDiagram.base
        (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
        (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p))
    ((TimePrismChainDiagram.base
      (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
      (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)).obj p).unop.2

private abbrev original : First W z L S u hs ⥤ I :=
  TimePrismChainDiagram.base
    (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
    (JTSupportedCoefficientPathCover.choiceTime W z L S u hs) ⋙
      JTSupportedCoefficientPathCover.projection W z L S u hs

private abbrev firstOld := TimePrismChainDiagram.coeffProjection
  (JTSupportedCoefficientPathCover.coefficient W z L S u hs)
  (JTSupportedCoefficientPathCover.choiceTime W z L S u hs)

/-- The ordinal comparison from a fixed-endpoint second chain to the
unchanged original coefficient degree. -/
def endpointDegree (b : Fin 2) :
    endpointSection W z L S u hs b ⋙
      JTSupportedPathChainLabels.ordinals W z L S u hs ⟶
        original W z L S u hs ⋙ K W z L :=
  Functor.whiskerLeft (endpointSection W z L S u hs b)
    (JTSupportedPathChainLabels.toOldCoefficient W z L S u hs)

private theorem endpointDegree_app (b : Fin 2) (p : First W z L S u hs) :
    (endpointDegree W z L S u hs b).app p =
      (JTSupportedPathChainLabels.toOldCoefficient W z L S u hs).app
        ((endpointSection W z L S u hs b).obj p) := rfl

/-- The old decorated label and the entire endpoint chain use exactly the
same native necklace. -/
def zeroToOldApp (p : First W z L S u hs) :
    (endpointSection W z L S u hs 0 ⋙
      JTSupportedPathChainLabels.labels W z L S u hs).obj p ⟶
      (original W z L S u hs ⋙ L).obj p := by
  apply JTOrderedLabelWedge.indexHomOfCoefficient (𝟙 _)
    ((endpointDegree W z L S u hs 0).app p)
  conv_lhs =>
    change JTOrderedLabelBinaryGlue.coefficient W z z
      ((JTParametrizedTargetFamilies.codes L).obj
        ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
          ((endpointSection W z L S u hs 0).obj p)))
      ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
        ((endpointSection W z L S u hs 0).obj p))
      (JTSupportedPathChainLabels.orderedPoint W z L S u hs
        ((endpointSection W z L S u hs 0).obj p))
  have hsource :
      JTOrderedLabelBinaryGlue.coefficient W z z
        ((JTParametrizedTargetFamilies.codes L).obj
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
            ((endpointSection W z L S u hs 0).obj p)))
        ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
          ((endpointSection W z L S u hs 0).obj p))
        (JTSupportedPathChainLabels.orderedPoint W z L S u hs
          ((endpointSection W z L S u hs 0).obj p)) =
        JTSupportedPathChainLabels.coefficientMap W z L S u hs
          ((endpointSection W z L S u hs 0).obj p) :=
    JTSupportedPathChainLabels.orderedPoint_coefficient W z L S u hs _
  rw [hsource]
  have htarget :
      JTOrderedLabelBinaryGlue.coefficient W z z
        ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p))
        ((K W z L).obj ((original W z L S u hs).obj p))
        (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W z z)
          ((original W z L S u hs ⋙ L).obj p)) =
        JTSupportedOrderedCoefficientChoices.old W z L
          ((original W z L S u hs).obj p) := rfl
  change JTSupportedPathChainLabels.coefficientMap W z L S u hs
      ((endpointSection W z L S u hs 0).obj p) =
    std.map ((endpointDegree W z L S u hs 0).app p) ≫
      JTOrderedLabelBinaryGlue.coefficient W z z
        ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p))
        ((K W z L).obj ((original W z L S u hs).obj p))
        (OrderedLabelElements.label W
          (OrderedNecklaceVertexPoints.boundaryPoint W z z)
          ((original W z L S u hs ⋙ L).obj p)) ≫
        diagramMappingPrecomp (discreteFree.map (𝟙 _)) W
  rw [htarget, discreteFree.map_id, diagramMappingPrecomp_id]
  simpa only [Category.comp_id, Category.assoc] using coefficientMap_zero W z L S u hs p

private theorem hom_ext {a c : DecoratedNecklaceHomDiagram.Index W z z}
    {f g : a ⟶ c}
    (h : (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W z z)).map f =
      (OrderedLabelElements.projection W
        (OrderedNecklaceVertexPoints.boundaryPoint W z z)).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

/-- At time zero the endpoint labels map naturally to the unchanged old labels. -/
def zeroToOld :
    endpointSection W z L S u hs 0 ⋙
      JTSupportedPathChainLabels.labels W z L S u hs ⟶
    original W z L S u hs ⋙ L where
  app p := zeroToOldApp W z L S u hs p
  naturality {p q} f := by
    apply hom_ext W z
    simp only [Functor.comp_map,
      (OrderedLabelElements.projection W
        (OrderedNecklaceVertexPoints.boundaryPoint W z z)).map_comp]
    simp only [JTSupportedPathChainLabels.labels_map_projection,
      zeroToOldApp, JTOrderedLabelWedge.indexHomOfCoefficient_projection]
    apply Prod.ext
    · rfl
    · simpa [K, original] using (endpointDegree W z L S u hs 0).naturality f

private abbrev constantLabels : First W z L S u hs ⥤
    DecoratedNecklaceHomDiagram.Index W z z :=
  JTConstantOrderedLabelDiagram.diagram W z
    (original W z L S u hs ⋙ JTParametrizedTargetFamilies.codes L)
    (original W z L S u hs ⋙ K W z L)

/-- At time one the label maps to the literal constant label in the
unchanged native necklace and original coefficient degree. -/
def oneToConstantApp (p : First W z L S u hs) :
    (endpointSection W z L S u hs 1 ⋙
      JTSupportedPathChainLabels.labels W z L S u hs).obj p ⟶
    (constantLabels W z L S u hs).obj p := by
  apply JTOrderedLabelWedge.indexHomOfCoefficient (𝟙 _)
    ((endpointDegree W z L S u hs 1).app p)
  conv_lhs =>
    change JTOrderedLabelBinaryGlue.coefficient W z z
      ((JTParametrizedTargetFamilies.codes L).obj
        ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
          ((endpointSection W z L S u hs 1).obj p)))
      ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
        ((endpointSection W z L S u hs 1).obj p))
      (JTSupportedPathChainLabels.orderedPoint W z L S u hs
        ((endpointSection W z L S u hs 1).obj p))
  have hsource :
      JTOrderedLabelBinaryGlue.coefficient W z z
        ((JTParametrizedTargetFamilies.codes L).obj
          ((JTSupportedPathChainLabels.toOriginal W z L S u hs).obj
            ((endpointSection W z L S u hs 1).obj p)))
        ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
          ((endpointSection W z L S u hs 1).obj p))
        (JTSupportedPathChainLabels.orderedPoint W z L S u hs
          ((endpointSection W z L S u hs 1).obj p)) =
        JTSupportedPathChainLabels.coefficientMap W z L S u hs
          ((endpointSection W z L S u hs 1).obj p) :=
    JTSupportedPathChainLabels.orderedPoint_coefficient W z L S u hs _
  rw [hsource]
  change JTSupportedPathChainLabels.coefficientMap W z L S u hs
      ((endpointSection W z L S u hs 1).obj p) =
    std.map ((endpointDegree W z L S u hs 1).app p) ≫
      JTOrderedLabelBinaryGlue.coefficient W z z
        ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p))
        ((K W z L).obj ((original W z L S u hs).obj p))
        (JTConstantOrderedLabel.constantLabel W z
          ((JTParametrizedTargetFamilies.codes L).obj
            ((original W z L S u hs).obj p))
          ((K W z L).obj ((original W z L S u hs).obj p))) ≫
        diagramMappingPrecomp (discreteFree.map (𝟙 _)) W
  rw [JTConstantOrderedLabel.coefficient_constantLabel,
    discreteFree.map_id, diagramMappingPrecomp_id]
  simpa only [Category.comp_id, Category.assoc] using coefficientMap_one W z L S u hs p

/-- The complete time-one endpoint label is naturally constant. -/
def oneToConstant :
    endpointSection W z L S u hs 1 ⋙
      JTSupportedPathChainLabels.labels W z L S u hs ⟶
    constantLabels W z L S u hs where
  app p := oneToConstantApp W z L S u hs p
  naturality {p q} f := by
    apply hom_ext W z
    simp only [Functor.comp_map,
      (OrderedLabelElements.projection W
        (OrderedNecklaceVertexPoints.boundaryPoint W z z)).map_comp,
      JTSupportedPathChainLabels.labels_map_projection,
      oneToConstantApp, JTOrderedLabelWedge.indexHomOfCoefficient_projection,
      JTConstantOrderedLabelDiagram.projection_map]
    apply Prod.ext
    · rfl
    · simpa [K, original] using
        (endpointDegree W z L S u hs 1).naturality f

/-- Collapse the naturally constant time-one endpoint to the actual
constant decorated point. -/
def oneToPoint :
    endpointSection W z L S u hs 1 ⋙
      JTSupportedPathChainLabels.labels W z L S u hs ⟶
    JTConstantOrderedLabelDiagram.pointDiagram W z :=
  oneToConstant W z L S u hs ≫
    JTConstantOrderedLabelDiagram.toPoint W z
      (original W z L S u hs ⋙ JTParametrizedTargetFamilies.codes L)
      (original W z L S u hs ⋙ K W z L)

end
end DaggerModels.PartII.JTSupportedPathChainEndpoints
