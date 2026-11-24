import DaggerModelsPartII.JTMarkedParametrizedTargetFamilyJoin
import DaggerModelsPartII.JTOrderedLabelJointInsertion

/-! The existing marked join as the identity-middle joint insertion. -/

set_option autoImplicit false
set_option Elab.async false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMarkedJoinJointInsertion

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints ReversalDiscreteFreeColimits
open JTOrderedLabelBinaryGlue (coefficient)
open JTMarkedBinaryLabels (inputs)
open JTMarkedParametrizedTargetFamilyJoin (Mark degree joinedLabels)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Index (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev proj (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (free.map f) W

private theorem coefficient_reindex (W : Source) (x y : Vertex W)
    (T : NecklaceCode) {k l : SimplexCategory} (r : k ⟶ l)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    coefficient W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map r.op a) =
      std.map r ≫ coefficient W x y T l a := by
  rw [JTOrderedLabelWedge.coefficient_projection,
    JTOrderedLabelWedge.coefficient_projection, SSet.yonedaEquiv_symm_map,
    Category.assoc]

variable {A : Type} [SmallCategory A]
variable {W : Source} {x z y : Vertex W}
variable (L : A ⥤ Index W x z) (R : A ⥤ Index W z y)
variable (i : Mark L) (j : Mark R)

private abbrev leftCode := JTParametrizedTargetFamilies.codes L
private abbrev rightCode := JTParametrizedTargetFamilies.codes R
private abbrev commonDegree :=
  (((L ⋙ proj W x z).prod' (R ⋙ proj W z y)) ⋙ JTParametrizedTargetFamilyJoin.joinOperators) ⋙
    CategoryTheory.Prod.snd NecklaceCode SimplexCategory

private def actualInputs (a : A) :=
  inputs (OrderedLabelElements.label W (boundaryPoint W x z) (L.obj a))
    (OrderedLabelElements.label W (boundaryPoint W z y) (R.obj a))
    (i.vertex a) (j.vertex a)

/-- The two exact marked restrictions of the original decorated diagrams. -/
def sides : JTOrderedLabelJointInsertion.Sides (W := W) (x := x) (z := z) (y := y)
    (leftCode L) (rightCode R)
    (commonDegree L R) where
  labels a := actualInputs L R i j a
  left_map {a b} f := by
    let α := ((proj W x z).map (L.map f)).2
    let β := ((proj W z y).map (R.map f)).2
    let δ := JTParameterBlockOperators.map α β
    let m := JTMarkedParameterBlocks.leftMarked ((degree L).obj a) ((degree R).obj a)
      (i.vertex a)
    let n := JTMarkedParameterBlocks.leftMarked ((degree L).obj b) ((degree R).obj b)
      (i.vertex b)
    have hm : m ≫ α = δ ≫ n := by
      have hi : α.toOrderHom (i.vertex a) = i.vertex b := i.naturality f
      simpa only [m, n, δ, hi] using
        JTMarkedParameterBlocks.leftMarked_map α β (i.vertex a)
    have h := JTOrderedLabelWedge.coefficient_of_indexHom
      (OrderedLabelElements.label W (boundaryPoint W x z) (L.obj a))
      (OrderedLabelElements.label W (boundaryPoint W x z) (L.obj b))
      ((proj W x z).map (L.map f)).1 α (L.map f) rfl
    change coefficient W x z ((leftCode L).obj a) ((degree L).obj a) _ =
      std.map α ≫ coefficient W x z ((leftCode L).obj b) ((degree L).obj b) _ ≫
        pre W (((proj W x z).map (L.map f)).1).map at h
    change coefficient W x z ((leftCode L).obj a) ((commonDegree L R).obj a)
        (((orderedNecklaceLabels W (boundaryPoint W x z)).obj
          (op ((leftCode L).obj a))).map m.op
          (OrderedLabelElements.label W (boundaryPoint W x z) (L.obj a))) =
      std.map δ ≫ coefficient W x z ((leftCode L).obj b) ((commonDegree L R).obj b)
        (((orderedNecklaceLabels W (boundaryPoint W x z)).obj
          (op ((leftCode L).obj b))).map n.op
          (OrderedLabelElements.label W (boundaryPoint W x z) (L.obj b))) ≫
        pre W (((proj W x z).map (L.map f)).1).map
    rw [coefficient_reindex, coefficient_reindex, h]
    rw [← Category.assoc (std.map m) (std.map α), ← Functor.map_comp, hm,
      Functor.map_comp, Category.assoc]
    simp only [Category.assoc]

  right_map {a b} f := by
    let α := ((proj W x z).map (L.map f)).2
    let β := ((proj W z y).map (R.map f)).2
    let δ := JTParameterBlockOperators.map α β
    let m := JTMarkedParameterBlocks.rightMarked ((degree L).obj a) ((degree R).obj a)
      (j.vertex a)
    let n := JTMarkedParameterBlocks.rightMarked ((degree L).obj b) ((degree R).obj b)
      (j.vertex b)
    have hm : m ≫ β = δ ≫ n := by
      have hj : β.toOrderHom (j.vertex a) = j.vertex b := j.naturality f
      simpa only [m, n, δ, hj] using
        JTMarkedParameterBlocks.rightMarked_map α β (j.vertex a)
    have h := JTOrderedLabelWedge.coefficient_of_indexHom
      (OrderedLabelElements.label W (boundaryPoint W z y) (R.obj a))
      (OrderedLabelElements.label W (boundaryPoint W z y) (R.obj b))
      ((proj W z y).map (R.map f)).1 β (R.map f) rfl
    change coefficient W z y ((rightCode R).obj a) ((degree R).obj a) _ =
      std.map β ≫ coefficient W z y ((rightCode R).obj b) ((degree R).obj b) _ ≫
        pre W (((proj W z y).map (R.map f)).1).map at h
    change coefficient W z y ((rightCode R).obj a) ((commonDegree L R).obj a)
        (((orderedNecklaceLabels W (boundaryPoint W z y)).obj
          (op ((rightCode R).obj a))).map m.op
          (OrderedLabelElements.label W (boundaryPoint W z y) (R.obj a))) =
      std.map δ ≫ coefficient W z y ((rightCode R).obj b) ((commonDegree L R).obj b)
        (((orderedNecklaceLabels W (boundaryPoint W z y)).obj
          (op ((rightCode R).obj b))).map n.op
          (OrderedLabelElements.label W (boundaryPoint W z y) (R.obj b))) ≫
        pre W (((proj W z y).map (R.map f)).1).map
    rw [coefficient_reindex, coefficient_reindex, h]
    rw [← Category.assoc (std.map m) (std.map β), ← Functor.map_comp, hm,
      Functor.map_comp, Category.assoc]
    simp only [Category.assoc]

private abbrev identityMiddle := (Functor.const A).obj (single 1)

/-- The identity-middle insertion and the existing marked join have the same
decorated label at every object. -/
theorem labels_obj (a : A) :
    (JTOrderedLabelJointInsertion.labels (sides L R i j) (identityMiddle (A := A))).obj a =
      (joinedLabels L R i j).obj a := by
  change JTOrderedLabelJointInsertion.index (single 1) (actualInputs L R i j a) =
    JTSharedCoefficientEvaluation.index (actualInputs L R i j a)
  exact JTOrderedLabelJointInsertion.index_identity (actualInputs L R i j a)

private instance : (proj W x y).Faithful := by
  change ((CategoryOfElements.π
    (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y))).leftOp).Faithful
  infer_instance

private theorem functor_eq_of_faithful_projection {B C : Type} [SmallCategory B]
    [SmallCategory C] (p : B ⥤ C) [p.Faithful] {F G : A ⥤ B}
    (hObj : ∀ a, F.obj a = G.obj a) (hProj : F ⋙ p = G ⋙ p) : F = G := by
  refine CategoryTheory.Functor.ext hObj ?_
  intro a b f
  apply p.map_injective
  rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hProj f

private abbrev insertedLabels : A ⥤ Index W x y :=
  JTOrderedLabelJointInsertion.labels (sides L R i j) (identityMiddle (A := A))

private theorem projected_obj (a : A) :
    (proj W x y).obj ((insertedLabels L R i j).obj a) =
      (proj W x y).obj ((joinedLabels L R i j).obj a) :=
  congrArg (proj W x y).obj (labels_obj L R i j a)

set_option maxHeartbeats 120000 in
private theorem projected_map {a b : A} (f : a ⟶ b) :
    (proj W x y).map ((insertedLabels L R i j).map f) ≍
      (proj W x y).map ((joinedLabels L R i j).map f) := by
  have hF := JTOrderedLabelJointInsertion.labels_map_projection
    (sides L R i j) (identityMiddle (A := A)) f
  have hG := JTMarkedParametrizedTargetFamilyJoin.joinedLabels_map L R i j f
  exact (heq_of_eq hF).trans (heq_of_eq hG.symm)

set_option maxHeartbeats 120000 in
private theorem projected_eq :
    insertedLabels L R i j ⋙ proj W x y = joinedLabels L R i j ⋙ proj W x y := by
  exact CategoryTheory.Functor.hext (projected_obj L R i j)
    (fun _ _ f ↦ projected_map L R i j f)

/-- The identity-middle insertion is the original marked joined-label functor,
including every original native and coefficient arrow. -/
theorem labels_eq :
    JTOrderedLabelJointInsertion.labels (sides L R i j) (identityMiddle (A := A)) =
      joinedLabels L R i j :=
  functor_eq_of_faithful_projection (proj W x y) (labels_obj L R i j)
    (projected_eq L R i j)

end
end DaggerModels.PartII.JTMarkedJoinJointInsertion
