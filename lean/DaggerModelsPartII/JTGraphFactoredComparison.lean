import DaggerModelsPartII.JTGraphFactoredPresentation
import DaggerModelsPartII.JTGraphBoundaryReflection
import DaggerModelsPartII.JTGraphPresentationOperator

/-!
# A common graph over a factored native traversal and target map
-/

set_option autoImplicit false
set_option maxHeartbeats 160000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphFactoredComparison

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open JTNecklaceEndpointCylinder
open JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphToPresentationArrow (pulledLabel)
open JTGraphRestrictionRaw (predecessor)
open JTGraphFactoredPresentation
open JTGraphBoundaryReflection

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S T : NecklaceCode}

private theorem native_postcompose (g : S ⟶ T) (k : SimplexCategory)
    (s : S.toSSet ⟶ J.obj k) :
    (lift (𝟙 S.toSSet) s ≫ (cylinder S).app k) ≫
        (nativeMap g k ≫ (value T).map (𝟙 k)) =
      lift g.map s ≫ (cylinder T).app k := by
  rw [(value T).map_id, Category.comp_id, Category.assoc, nativeMap_cylinder,
    ← Category.assoc]
  congr 1

/-- Equality after mapping into the original label cylinder implies equality
in the cylinder of the proposed quotient, for the specified native map. -/
def ReflectsGraphEquality {L : NecklaceCode} (g : S ⟶ T) (a : T ⟶ L)
    (k : SimplexCategory) : Prop :=
  ∀ s t : S.toSSet ⟶ J.obj k,
    lift (g ≫ a).map s ≫ (cylinder L).app k = lift (g ≫ a).map t ≫ (cylinder L).app k →
      lift g.map s ≫ (cylinder T).app k = lift g.map t ≫ (cylinder T).app k

/-- Boundary reflection suffices for graph equality reflection. -/
theorem reflectsGraphEquality_of_boundary {L : NecklaceCode} (g : S ⟶ T) (a : T ⟶ L)
    (k : SimplexCategory) (ha : ReflectsBoundary a) : ReflectsGraphEquality g a k :=
  graph_eq_of_reflectsBoundary g a ha k

private theorem project_graph_equality {L : NecklaceCode} (g : S ⟶ T) (a : T ⟶ L)
    (k : SimplexCategory) (s : S.toSSet ⟶ J.obj k) (t : T.toSSet ⟶ J.obj k)
    (u : T.toSSet ⟶ (value L).obj k) (ha : ReflectsGraphEquality g a k)
    (hs : lift (g ≫ a).map s ≫ (cylinder L).app k = g.map ≫ u)
    (ht : lift a.map t ≫ (cylinder L).app k = u) :
    lift g.map s ≫ (cylinder T).app k =
      lift g.map (g.map ≫ t) ≫ (cylinder T).app k := by
  apply ha s (g.map ≫ t)
  calc
    _ = g.map ≫ u := hs
    _ = g.map ≫ (lift a.map t ≫ (cylinder L).app k) := congrArg (fun b ↦ g.map ≫ b) ht.symm
    _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]; rfl

variable (c : S ⟶ U.left.fiber.left) (g : S ⟶ T) [Epi g.map]
  (v : Traversal U T) (r : T ⟶ Q.code)
  (hv : g.map ≫ v.right = c.map ≫ U.left.fiber.hom.right)
  (hr : g ≫ r = c ≫ U.hom.hom)

private abbrev V := object U c g v r hv hr
private abbrev k := degree U.left
private abbrev f := augmentationCode (V c g v r hv hr).left

variable (D : GraphLift U.left S) (E : GraphLift (V c g v r hv hr).left T)
  (hD : D.collapse = c) (hE : E.collapse = 𝟙 _)

include hD hE

private theorem horizontal :
    D.collapse ≫ augmentationCode U.left = g ≫ (E.collapse ≫ f c g v r hv hr) := by
  have h := horizontal_factor c g v r hv hr
  calc
    _ = c ≫ augmentationCode U.left :=
      congrArg (fun a ↦ a ≫ augmentationCode U.left) hD
    _ = g ≫ f c g v r hv hr := h
    _ = _ := congrArg (fun a ↦ g ≫ a) (by rw [hE, Category.id_comp])

private theorem label_factor :
    let L := orderedNecklaceLabels W (boundaryPoint W x y)
    (L.obj (op S)).map (𝟙 (k (U := U))).op
        ((L.map g.op).app (op (k (U := U)))
          (pulledLabel (V c g v r hv hr).left T (E.collapse ≫ f c g v r hv hr))) =
      pulledLabel U.left S (D.collapse ≫ augmentationCode U.left) := by
  dsimp only
  rw [horizontal c g v r hv hr D E hD hE]
  simp only [op_id, CategoryTheory.Functor.map_id, types_id_apply, pulledLabel, op_comp,
    CategoryTheory.Functor.map_comp]
  rfl

private theorem projected_traversal
    (hf : ReflectsGraphEquality g (f c g v r hv hr) (k (U := U))) :
    lift g.map D.parameter ≫ (cylinder T).app (k (U := U)) =
      lift g.map (g.map ≫ E.parameter) ≫ (cylinder T).app (k (U := U)) := by
  let a := f c g v r hv hr
  have hd : D.collapse ≫ augmentationCode U.left = g ≫ a := by
    calc
      _ = c ≫ augmentationCode U.left :=
        congrArg (fun b ↦ b ≫ augmentationCode U.left) hD
      _ = _ := horizontal_factor c g v r hv hr
  have he : lift a.map E.parameter ≫ (cylinder (code U.left)).app (k (U := U)) =
      v.right := by
    have h := E.comm
    change lift (E.collapse ≫ a).map E.parameter ≫
      (cylinder (code U.left)).app (k (U := U)) = E.collapse.map ≫ v.right at h
    rw [hE, Category.id_comp] at h
    change lift a.map E.parameter ≫ (cylinder (code U.left)).app (k (U := U)) =
      𝟙 T.toSSet ≫ v.right at h
    exact h.trans (Category.id_comp _)
  apply project_graph_equality g a (k (U := U)) D.parameter E.parameter v.right hf _ he
  calc
    _ = lift (D.collapse ≫ augmentationCode U.left).map D.parameter ≫
        (cylinder (code U.left)).app (k (U := U)) :=
      congrArg (fun b : S ⟶ code U.left ↦
        lift b.map D.parameter ≫ (cylinder (code U.left)).app (k (U := U))) hd.symm
    _ = D.collapse.map ≫ U.left.fiber.hom.right := D.comm
    _ = c.map ≫ U.left.fiber.hom.right :=
      congrArg (fun b : S ⟶ U.left.fiber.left ↦ b.map ≫ U.left.fiber.hom.right) hD
    _ = g.map ≫ v.right := hv.symm

private def presentationArrow (hf : ReflectsGraphEquality g (f c g v r hv hr) (k (U := U))) :
    (predecessor (U := U) D).left ⟶ (predecessor (U := V c g v r hv hr) E).left :=
  JTGraphPresentationOperator.presentationArrowOfTraversal g (𝟙 (k (U := U)))
    (pulledLabel U.left S (D.collapse ≫ augmentationCode U.left))
    (pulledLabel (V c g v r hv hr).left T (E.collapse ≫ f c g v r hv hr))
    D.parameter E.parameter (label_factor c g v r hv hr D E hD hE) (by
      calc
        g.map ≫ (lift (𝟙 T.toSSet) E.parameter ≫ (cylinder T).app (k (U := U))) =
            lift g.map (g.map ≫ E.parameter) ≫ (cylinder T).app (k (U := U)) := by
          rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id]
        _ = lift g.map D.parameter ≫ (cylinder T).app (k (U := U)) :=
          (projected_traversal c g v r hv hr D E hD hE hf).symm
        _ = _ := (native_postcompose g (k (U := U)) D.parameter).symm)

/-- The exact factorizations give an actual arrow with the prescribed native quotient. -/
def compare (hf : ReflectsGraphEquality g (f c g v r hv hr) (k (U := U))) :
    predecessor (U := U) D ⟶ predecessor (U := V c g v r hv hr) E := by
  refine CostructuredArrow.homMk (presentationArrow c g v r hv hr D E hD hE hf) ?_
  apply NecklacesOver.Hom.ext
  change g ≫ (E.collapse ≫ r) = D.collapse ≫ U.hom.hom
  calc
    _ = g ≫ r := congrArg (fun b ↦ g ≫ b) (by rw [hE, Category.id_comp])
    _ = c ≫ U.hom.hom := hr
    _ = _ := congrArg (fun b ↦ b ≫ U.hom.hom) hD.symm

theorem compare_code (hf : ReflectsGraphEquality g (f c g v r hv hr) (k (U := U))) :
    (compare c g v r hv hr D E hD hE hf).left.fiber.left = g := rfl

omit D E hD hE in
/-- One target graph works for every choice of parameters on the original collapse. -/
theorem exists_common (hf : ReflectsGraphEquality g (f c g v r hv hr) (k (U := U))) :
    ∃ E : GraphLift (V c g v r hv hr).left T, E.collapse = 𝟙 _ ∧
      ∀ D : GraphLift U.left S, D.collapse = c →
        Nonempty (predecessor (U := U) D ⟶ predecessor (U := V c g v r hv hr) E) := by
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift (V c g v r hv hr).left
  refine ⟨E, hE, ?_⟩
  intro D hD
  exact ⟨compare c g v r hv hr D E hD hE hf⟩

end

end DaggerModels.PartII.JTGraphFactoredComparison
