import DaggerModelsPartII.JTVertexAssignmentCover
import DaggerModelsPartII.JTBinaryPrismRealization

/-! Lift graph coefficients to a coherent cover of ordered chains. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTPrismChainGraphCover

open JTCodiscreteParameterPairing (coord coord_map)
open JTJointRelativeParameters (parameter_ext)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceLabelRealization (realizedLabel realizedLabel_natural_k)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)

section Assignment

variable {I : Type} [SmallCategory I]
variable (X : I ⥤ SSet.{0}) {k m : I ⥤ SimplexCategory}
variable (p : X ⟶ k ⋙ J) (α : m ⟶ k)

private def allowed (i : I) (v : (X.obj i).obj zero) : Set (Fin ((m.obj i).len + 1)) :=
  {a | (α.app i).toOrderHom a = coord (k.obj i) zero ((p.app i).app zero v) 0}

private theorem stable {i j : I} (f : i ⟶ j) (v : (X.obj i).obj zero) :
    Set.MapsTo (m.map f).toOrderHom (allowed X p α i v)
      (allowed X p α j ((X.map f).app zero v)) := by
  intro a ha
  change (α.app j).toOrderHom ((m.map f).toOrderHom a) =
    coord (k.obj j) zero ((p.app j).app zero ((X.map f).app zero v)) 0
  have he := SimplexCategory.congr_toOrderHom_apply (α.naturality f) a
  have hp := congrFun (NatTrans.congr_app (p.naturality f) zero) v
  change (p.app j).app zero ((X.map f).app zero v) =
    (J.map (k.map f)).app zero ((p.app i).app zero v) at hp
  change (α.app i).toOrderHom a = _ at ha
  change (α.app j).toOrderHom ((m.map f).toOrderHom a) =
    (k.map f).toOrderHom ((α.app i).toOrderHom a) at he
  rw [hp, coord_map, he, ha]

/-- Along a surjective coefficient projection, all chain lifts are kept. -/
abbrev cover := JTVertexAssignmentCover.cover X m (allowed X p α) (stable X p α)

/-- The projection to the original graph domain. -/
abbrev projection : cover X p α ⟶ X :=
  JTVertexAssignmentCover.projection X m (allowed X p α) (stable X p α)

/-- The lifted groupoid parameter is natural under the original operators. -/
abbrev parameter : cover X p α ⟶ m ⋙ J :=
  JTVertexAssignmentCover.trace X m (allowed X p α) (stable X p α)

/-- The groupoid parameter projects to the exact original parameter. -/
theorem parameter_projection :
    parameter X p α ≫ Functor.whiskerRight α J = projection X p α ≫ p := by
  apply NatTrans.ext
  funext i
  apply parameter_ext
  intro v
  change coord (k.obj i) zero
      ((J.map (α.app i)).app zero (((parameter X p α).app i).app zero v)) 0 =
    coord (k.obj i) zero ((p.app i).app zero (((projection X p α).app i).app zero v)) 0
  rw [coord_map]
  exact JTVertexAssignmentCover.trace_allowed X m (allowed X p α) (stable X p α) i v

/-- Every surjective chain projection induces an objectwise trivial fibration of graph domains. -/
theorem projection_trivialFibration
    (hα : ∀ i, Function.Surjective (α.app i).toOrderHom) (i : I) :
    trivialFibrations SSet.{0} ((projection X p α).app i) := by
  apply JTVertexAssignmentCover.projection_trivialFibration
  intro j v
  exact hα j (coord (k.obj j) zero ((p.app j).app zero v) 0)

end Assignment

section Raw

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev F := discreteFree.{0}
variable {W : Source} {x y : Vertex W} {T : NecklaceCode}

private abbrev labelSpace := (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

private theorem ordered_restrict {s t : SimplexCategory} (g : s ⟶ t)
    (a : (labelSpace (W := W) (x := x) (y := y) (T := T)).obj (op t)) :
    orderedLabel W x y T s ((labelSpace (W := W) (x := x) (y := y) (T := T)).map g.op a) =
      (diagramTensor (F.obj T.toSSet)).map (SSet.stdSimplex.map g) ≫
        orderedLabel W x y T t a :=
  congrFun ((pullback.fst ((OrderedNecklaceLabelDiagram.necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)).naturality g.op) a

private theorem realize_restrict {X : SSet.{0}} {s t : SimplexCategory}
    (g : s ⟶ t) (r : X ⟶ T.toSSet) (p : X ⟶ J.obj s)
    (a : (labelSpace (W := W) (x := x) (y := y) (T := T)).obj (op t)) :
    lift r (p ≫ J.map g) ≫ realizedLabel T.toSSet W t (orderedLabel W x y T t a) =
      lift r p ≫ realizedLabel T.toSSet W s
        (orderedLabel W x y T s ((labelSpace (W := W) (x := x) (y := y) (T := T)).map g.op a)) := by
  have h : lift r (p ≫ J.map g) = lift r p ≫ (𝟙 T.toSSet ⊗ₘ J.map g) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · simp only [lift_snd, Category.assoc, tensorHom_snd, lift_snd_assoc]
  rw [h, Category.assoc, realizedLabel_natural_k, ← ordered_restrict]

/-- A common ordered chain with identical restricted labels preserves the raw map
for every lifted groupoid parameter, including arbitrary maps on the horizontal coordinate. -/
theorem realize_on_common_chain {X : SSet.{0}} {m k l : SimplexCategory}
    (f : m ⟶ k) (g : m ⟶ l) (r : X ⟶ T.toSSet) (p : X ⟶ J.obj m)
    (a : (labelSpace (W := W) (x := x) (y := y) (T := T)).obj (op k))
    (b : (labelSpace (W := W) (x := x) (y := y) (T := T)).obj (op l))
    (h : (labelSpace (W := W) (x := x) (y := y) (T := T)).map f.op a =
      (labelSpace (W := W) (x := x) (y := y) (T := T)).map g.op b) :
    lift r (p ≫ J.map g) ≫ realizedLabel T.toSSet W l (orderedLabel W x y T l b) =
      lift r (p ≫ J.map f) ≫ realizedLabel T.toSSet W k (orderedLabel W x y T k a) := by
  rw [realize_restrict g r p b, realize_restrict f r p a, h]

end Raw

end
end DaggerModels.PartII.JTPrismChainGraphCover
