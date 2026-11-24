import DaggerModelsPartII.JTSupportedOrderedCoefficientChoices
import DaggerModelsPartII.JTPathChoiceDiagram
import DaggerModelsPartII.JTVariableFixedLiftEvaluation

/-! Full higher paths from a supported ordered coefficient to its literal constant. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedCoefficientPathCover

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open OrderedNecklaceLabelDiagram (necklaceLabels necklaceBoundaryRestriction)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hu : ∀ a : I, Mono (u.app a))
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)

/-- The complete simplicial path diagram between the two exact natural lifts. -/
abbrev spaces : Iᵒᵖ ⥤ SSet.{0} :=
  JTPathChoiceDiagram.paths
    (JTSupportedOrderedCoefficientChoices.spaces W z L S u)
    (JTSupportedOrderedCoefficientChoices.oldSection W z L S u hs)
    (JTSupportedOrderedCoefficientChoices.constantSection W z L S u)

/-- Every higher path simplex over the original decorated diagram. -/
abbrev Cover := JTPathChoiceDiagram.Cover
  (JTSupportedOrderedCoefficientChoices.spaces W z L S u)
  (JTSupportedOrderedCoefficientChoices.oldSection W z L S u hs)
  (JTSupportedOrderedCoefficientChoices.constantSection W z L S u)

/-- The path cover remembers the actual original index. -/
abbrev projection : Cover W z L S u hs ⥤ I :=
  JTPathChoiceDiagram.projection
    (JTSupportedOrderedCoefficientChoices.spaces W z L S u)
    (JTSupportedOrderedCoefficientChoices.oldSection W z L S u hs)
    (JTSupportedOrderedCoefficientChoices.constantSection W z L S u)

/-- The full path simplex degree, independent of the old coefficient degree. -/
abbrev choiceTime : Cover W z L S u hs ⥤ SimplexCategory :=
  SynchronizedSimplicialParameters.time (spaces W z L S u hs)

/-- The original coefficient degree on every path-cover object. -/
abbrev coefficient : Cover W z L S u hs ⥤ SimplexCategory :=
  projection W z L S u hs ⋙ K W z L

private abbrev D := JTSupportedOrderedCoefficientChoices.diagram W z L S u
private abbrev F := JTSupportedOrderedCoefficientChoices.spaces W z L S u
private abbrev c₀ := JTSupportedOrderedCoefficientChoices.oldSection W z L S u hs
private abbrev c₁ := JTSupportedOrderedCoefficientChoices.constantSection W z L S u

private theorem liftMap_section (a : I) (n : SimplexCategory)
    (c : JTVariableFixedLiftSections.LiftFamily (D W z L S u)) :
    JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
        (fst (std.obj ⦋0⦌) (std.obj n) ≫
          (JTVariableFixedLiftSections.sectionOfLifts (D W z L S u) c).app (op a)) =
      fst (std.obj ((K W z L).obj a)) (std.obj ⦋0⦌ ⊗ std.obj n) ≫
        c.lift a := by
  have hv : (JTVariableFixedLiftSections.sectionOfLifts (D W z L S u) c).app (op a) ≫
      (JTVariableFixedLiftChoiceDiagram.fiber (D W z L S u) a).ι =
      SSet.const (SSet.ihom₀Equiv.symm (c.lift a)) := by
    calc
      _ = SSet.yonedaEquiv.symm
          (((JTVariableFixedLiftChoiceDiagram.fiber (D W z L S u) a).ι).app
            (op ⦋0⦌) (JTVariableFixedLiftSections.vertex (D W z L S u) c a)) := by
            rw [JTVariableFixedLiftSections.sectionOfLifts,
              SSet.yonedaEquiv_symm_comp]
      _ = SSet.yonedaEquiv.symm (SSet.ihom₀Equiv.symm (c.lift a)) := rfl
      _ = SSet.const (SSet.ihom₀Equiv.symm (c.lift a)) := by
            simpa only [Equiv.apply_symm_apply] using
              (SSet.const_yonedaEquiv _ (SSet.yonedaEquiv.symm
                (SSet.ihom₀Equiv.symm (c.lift a)))).symm
  unfold JTVariableFixedLiftEvaluation.liftMap
  rw [Category.assoc, hv, SSet.comp_const,
    SSet.const_ihom₀Equiv_symm_apply, uncurry_curry]
  rfl

/-- Each full path simplex is evaluated at the SAME original coefficient degree. -/
def pathCoefficient (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    std.obj ((K W z L).obj a) ⊗
        (std.obj ⦋1⦌ ⊗ std.obj n) ⟶
      (necklaceLabels W).obj (op ((codes L).obj a)) :=
  JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
    (JTPathChoiceDiagram.pathMap (F W z L S u)
      (c₀ W z L S u hs) (c₁ W z L S u) a n v)

/-- The entire original support stays literal constant throughout the path. -/
theorem pathCoefficient_support (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    (std.map (u.app a) ▷ (std.obj ⦋1⦌ ⊗ std.obj n)) ≫
      pathCoefficient W z L S u hs a n v =
      fst (std.obj (S.obj a)) (std.obj ⦋1⦌ ⊗ std.obj n) ≫
        JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a :=
  JTVariableFixedLiftEvaluation.liftMap_support (D W z L S u) a _

/-- Both outer native endpoints are fixed in every higher path simplex. -/
theorem pathCoefficient_boundary (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    pathCoefficient W z L S u hs a n v ≫
        (necklaceBoundaryRestriction W).app (op ((codes L).obj a)) =
      fst (std.obj ((K W z L).obj a)) (std.obj ⦋1⦌ ⊗ std.obj n) ≫
        (D W z L S u).base a :=
  JTVariableFixedLiftEvaluation.liftMap_boundary (D W z L S u) a _

/-- Original arrows and higher time operators act on the entire same-degree
coefficient prism. -/
theorem pathCoefficient_mixed {a b : I} (f : a ⟶ b)
    {m n : SimplexCategory} (α : m ⟶ n)
    (v : ((spaces W z L S u hs).obj (op b)).obj (op n)) :
    pathCoefficient W z L S u hs a m
      (((spaces W z L S u hs).map f.op).app (op m)
        (((spaces W z L S u hs).obj (op b)).map α.op v)) =
      (std.map ((K W z L).map f) ⊗ₘ
        (std.obj ⦋1⦌ ◁ std.map α)) ≫
          pathCoefficient W z L S u hs b n v ≫
            (((codes L).op ⋙ necklaceLabels W).map f.op) := by
  unfold pathCoefficient
  rw [JTPathChoiceDiagram.pathMap_mixed]
  exact JTVariableFixedLiftEvaluation.liftMap_natural
    (D W z L S u) f (std.obj ⦋1⦌ ◁ std.map α)
    (JTPathChoiceDiagram.pathMap (F W z L S u)
      (c₀ W z L S u hs) (c₁ W z L S u) b n v)

/-- At the first interval endpoint, the full prism evaluates the original
natural coefficient section in every higher time degree. -/
theorem pathCoefficient_zero (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    (std.obj ((K W z L).obj a) ◁
      ((SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) ▷ std.obj n)) ≫
        pathCoefficient W z L S u hs a n v =
      JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
        (fst (std.obj ⦋0⦌) (std.obj n) ≫ (c₀ W z L S u hs).app (op a)) := by
  calc
    _ = JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
        (((SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) ▷ std.obj n) ≫
          JTPathChoiceDiagram.pathMap (F W z L S u)
            (c₀ W z L S u hs) (c₁ W z L S u) a n v) :=
      (JTVariableFixedLiftEvaluation.liftMap_time (D W z L S u) a _ _).symm
    _ = _ := by rw [JTPathChoiceDiagram.pathMap_zero]

/-- At the last interval endpoint, the full prism evaluates the literal
constant natural coefficient section in every higher time degree. -/
theorem pathCoefficient_one (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    (std.obj ((K W z L).obj a) ◁
      ((SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) ▷ std.obj n)) ≫
        pathCoefficient W z L S u hs a n v =
      JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
        (fst (std.obj ⦋0⦌) (std.obj n) ≫ (c₁ W z L S u).app (op a)) := by
  calc
    _ = JTVariableFixedLiftEvaluation.liftMap (D W z L S u) a
        (((SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) ▷ std.obj n) ≫
          JTPathChoiceDiagram.pathMap (F W z L S u)
            (c₀ W z L S u hs) (c₁ W z L S u) a n v) :=
      (JTVariableFixedLiftEvaluation.liftMap_time (D W z L S u) a _ _).symm
    _ = _ := by rw [JTPathChoiceDiagram.pathMap_one]

/-- The first full endpoint is exactly the original coefficient at its
original degree, constant only in the added path-time parameters. -/
theorem pathCoefficient_zero_old (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    (std.obj ((K W z L).obj a) ◁
      ((SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) ▷ std.obj n)) ≫
        pathCoefficient W z L S u hs a n v =
      fst (std.obj ((K W z L).obj a)) (std.obj ⦋0⦌ ⊗ std.obj n) ≫
        JTSupportedOrderedCoefficientChoices.old W z L a := by
  rw [pathCoefficient_zero]
  exact liftMap_section W z L S u a n
    (JTSupportedOrderedCoefficientChoices.oldFamily W z L S u hs)

/-- The last full endpoint is the literal global constant coefficient in
that same complete original degree. -/
theorem pathCoefficient_one_constant (a : I) (n : SimplexCategory)
    (v : ((spaces W z L S u hs).obj (op a)).obj (op n)) :
    (std.obj ((K W z L).obj a) ◁
      ((SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) ▷ std.obj n)) ≫
        pathCoefficient W z L S u hs a n v =
      fst (std.obj ((K W z L).obj a)) (std.obj ⦋0⦌ ⊗ std.obj n) ≫
        JTSupportedOrderedCoefficientChoices.constant W z L a := by
  rw [pathCoefficient_one]
  exact liftMap_section W z L S u a n
    (JTSupportedOrderedCoefficientChoices.constantFamily W z L S u)

/-- The higher path choice cover is weak over the original decorated diagram. -/
theorem projection_weak
    (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((codes L).obj a).len) :
    WeakEquivalence (nerveMap (projection W z L S u hs)) := by
  apply JTPathChoiceDiagram.projection_weak
  · exact JTSupportedOrderedCoefficientChoices.spaces_kan W z L S u hu hW hp
  · exact JTSupportedOrderedCoefficientChoices.spaces_toPoint_weak
      W z L S u hu hW hp

end
end DaggerModels.PartII.JTSupportedCoefficientPathCover
