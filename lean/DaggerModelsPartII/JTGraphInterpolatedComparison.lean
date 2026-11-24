import DaggerModelsPartII.JTGraphInterpolatedRaw
import DaggerModelsPartII.JTInterpolatedCylinderReindex
import DaggerModelsPartII.JTCylinderOverTargetReindex
import DaggerModelsPartII.JTHomotopyTargetComma

/-!
# Finite graph families in the same original target comma
-/

set_option autoImplicit false
set_option maxHeartbeats 180000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedComparison

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphFactoredPresentation (TargetComma)
open JTGraphRestrictionRaw (predecessor)
open JTCommaGraphPredecessor (augmentationCode)
open JTNecklaceEndpointCylinder (under cylinder)
open BoundaryNecklaceComma (necklaceUnder sourceCode)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open JTInterpolatedReducedCylinder (slice slice_augmentation slice_map_interpolate)
open JTGraphInterpolatedRaw (index toDecorated toDecoratedBy whole_raw)
open JTGraphParameterInterpolation (interpolate)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The entire category of original necklaces over the time cylinder. -/
abbrev Fiber (S : NecklaceCode) (n : SimplexCategory) :=
  CostructuredArrow necklaceUnder ((under S).obj n)

/-- The original native necklace, held at the given time vertex. -/
def sliceObject (S : NecklaceCode) (n : SimplexCategory) (i : Fin (n.len + 1)) : Fiber S n :=
  CostructuredArrow.mk (slice S n i)

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)

private abbrev parameters (D : Fin (n.len + 1) → GraphLift U.left S) :
    Fin (n.len + 1) → (S.toSSet ⟶ J.obj (degree U.left)) :=
  fun i ↦ (D i).parameter

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ augmentationCode U.left).map ((D i).parameter) ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

/-- Any time family with the exact raw equation gives the comparison functor. -/
def comparisonFunctorBy (p : S.toSSet ⊗ J.obj n ⟶ J.obj (degree U.left))
    (hr : (toDecoratedBy U c p).right ≫ ((underCocone W x y).app (index U c)).right =
      NecklaceCylinderAugmentation.augmentation S n ≫ (c ≫ U.hom.hom).map ≫ Q.map) :
    Fiber S n ⥤ TargetComma Q :=
  JTCylinderOverTarget.functor W x y Q (index U c) S n
    (toDecoratedBy U c p) (c ≫ U.hom.hom) hr

/-- The finite family gives an actual functor into the unchanged target comma. -/
def comparisonFunctor : Fiber S n ⥤ TargetComma Q :=
  comparisonFunctorBy c (interpolate (parameters D))
    (whole_raw U c (parameters D) (parameter_comm c D hD))

private abbrev explicitSlice (i : Fin (n.len + 1)) : TargetComma Q :=
  JTCylinderOverTarget.targetObject W x y Q (index U c) S n
    (toDecorated U c (parameters D)) (c ≫ U.hom.hom)
    (whole_raw U c (parameters D) (parameter_comm c D hD)) (sliceObject S n i)

private def graphAt (i : Fin (n.len + 1)) : GraphLift U.left S :=
  ⟨c, (D i).parameter, parameter_comm c D hD i⟩

private theorem graphAt_eq (i : Fin (n.len + 1)) : graphAt c D hD i = D i := by
  apply GraphLift.ext
  · exact (hD i).symm
  · rfl

private theorem explicitSlice_eq (i : Fin (n.len + 1)) :
    explicitSlice c D hD i = predecessor (U := U) (graphAt c D hD i) := by
  let P := explicitSlice c D hD i
  let G := predecessor (U := U) (graphAt c D hD i)
  have hs : P.left.fiber.hom.right = G.left.fiber.hom.right := by
    calc
      _ = (slice S n i).right ≫ (toDecorated U c (parameters D)).right :=
        JTCylinderOverTarget.targetObject_map W x y Q (index U c) S n
          (toDecorated U c (parameters D)) (c ≫ U.hom.hom)
          (whole_raw U c (parameters D) (parameter_comm c D hD)) (sliceObject S n i)
      _ = _ := slice_map_interpolate S (parameters D) i
  have hu : P.left.fiber.hom = G.left.fiber.hom := Under.UnderMorphism.ext hs
  have hl : P.left = G.left := congrArg
    (fun f : necklaceUnder.obj S ⟶ (underDiagram W x y).obj (index U c) ↦
      (⟨index U c, CostructuredArrow.mk f⟩ : Pres (W := W) (x := x) (y := y))) hu
  apply CostructuredArrow.obj_ext P G hl
  apply NecklacesOver.Hom.ext
  change NecklaceCode.Hom.comp ((toTarget W x y).map (eqToHom hl)).hom G.hom.hom =
    P.hom.hom
  rw [DecoratedCylinderNecklacePresentation.toTarget_map_hom]
  have hc : (eqToHom hl).fiber.left = 𝟙 S := by
    let F := sourceCode (underDiagram W x y)
    change F.map (eqToHom hl) = _
    rw [eqToHom_map]
    rfl
  rw [hc]
  have hid : (𝟙 S : S ⟶ S) ≫ (G.hom.hom : S ⟶ Q.code) = G.hom.hom :=
    Category.id_comp _
  exact hid.trans (NecklaceCode.Hom.ext (by
    symm
    calc
      P.hom.hom.map = (slice S n i).right ≫
          NecklaceCylinderAugmentation.augmentation S n ≫ (c ≫ U.hom.hom).map :=
        JTCylinderOverTarget.targetObject_native_map W x y Q (index U c) S n
          (toDecorated U c (parameters D)) (c ≫ U.hom.hom)
          (whole_raw U c (parameters D) (parameter_comm c D hD)) (sliceObject S n i)
      _ = (c ≫ U.hom.hom).map := by
        rw [← Category.assoc, slice_augmentation]
        exact Category.id_comp _
      _ = G.hom.hom.map := rfl))

/-- Every time vertex represents its exact prescribed graph over the original target. -/
def comparison_slice_iso (i : Fin (n.len + 1)) :
    (comparisonFunctor c D hD).obj (sliceObject S n i) ≅ predecessor (U := U) (D i) :=
  (JTCylinderOverTarget.functor_obj_iso W x y Q (index U c) S n
    (toDecorated U c (parameters D)) (c ≫ U.hom.hom)
    (whole_raw U c (parameters D) (parameter_comm c D hD)) (sliceObject S n i)).trans
      (eqToIso ((explicitSlice_eq c D hD i).trans
        (congrArg (fun E ↦ predecessor (U := U) E) (graphAt_eq c D hD i))))

include hD in
/-- Every finite family of independently prescribed parameters compares by
actual zigzags over the fixed native target. -/
theorem comparison_zigzag (i j : Fin (n.len + 1)) :
    Relation.EqvGen (fun A B : TargetComma Q ↦ Nonempty (A ⟶ B))
      (predecessor (U := U) (D i)) (predecessor (U := U) (D j)) := by
  let F := comparisonFunctor c D hD
  let R := fun A B : TargetComma Q ↦ Nonempty (A ⟶ B)
  have hmap : ∀ {A B : Fiber S n},
      Relation.EqvGen (fun P Q : Fiber S n ↦ Nonempty (P ⟶ Q)) A B →
        Relation.EqvGen R (F.obj A) (F.obj B) := by
    intro A B e
    induction e with
    | rel A B f => exact Relation.EqvGen.rel _ _ ⟨F.map f.some⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have hi : Relation.EqvGen R (predecessor (U := U) (D i)) (F.obj (sliceObject S n i)) :=
    Relation.EqvGen.rel _ _ ⟨(comparison_slice_iso c D hD i).inv⟩
  have hj : Relation.EqvGen R (F.obj (sliceObject S n j)) (predecessor (U := U) (D j)) :=
    Relation.EqvGen.rel _ _ ⟨(comparison_slice_iso c D hD j).hom⟩
  have hm := hmap (JTHomotopyTargetComma.source_zigzag_at S n
    (sliceObject S n i) (sliceObject S n j))
  exact Relation.EqvGen.trans _ _ _ hi (Relation.EqvGen.trans _ _ _ hm hj)

/-- Reindexing the family is restriction along the original time operator. -/
theorem decorated_reindex {m : SimplexCategory} (j : m ⟶ n) :
    (under S).map j ≫ toDecorated U c (parameters D) =
      toDecorated U c (parameters (fun i ↦ D (j.toOrderHom i))) :=
  Under.UnderMorphism.ext (JTInterpolatedCylinderReindex.interpolated_reindex S j (parameters D))

/-- The comparison commutes strictly with reindexing on the original time. -/
theorem comparisonFunctor_reindex {m : SimplexCategory} (j : m ⟶ n) :
    CostructuredArrow.map ((under S).map j) ⋙ comparisonFunctor c D hD =
      comparisonFunctor c (fun i ↦ D (j.toOrderHom i)) (fun i ↦ hD (j.toOrderHom i)) :=
  JTCylinderOverTargetReindex.functor_reindex W x y Q (index U c) S m n j
    (toDecorated U c (parameters (fun i ↦ D (j.toOrderHom i))))
    (toDecorated U c (parameters D)) (c ≫ U.hom.hom)
    (whole_raw U c _ (fun i ↦ parameter_comm c D hD (j.toOrderHom i)))
    (whole_raw U c _ (parameter_comm c D hD))
    (decorated_reindex c D j)

/-- The prescribed native time slices also commute with the original operators. -/
theorem sliceObject_reindex (S : NecklaceCode) {m n : SimplexCategory} (j : m ⟶ n)
    (i : Fin (m.len + 1)) :
    (CostructuredArrow.map ((under S).map j)).obj (sliceObject S m i) =
      sliceObject S n (j.toOrderHom i) :=
  congrArg (fun f : necklaceUnder.obj S ⟶ (under S).obj n ↦ CostructuredArrow.mk f)
    (JTInterpolatedReducedCylinder.slice_reindex S j i)

end

end DaggerModels.PartII.JTGraphInterpolatedComparison
