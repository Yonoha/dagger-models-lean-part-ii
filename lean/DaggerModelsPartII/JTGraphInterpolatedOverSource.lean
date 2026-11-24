import DaggerModelsPartII.JTGraphInterpolatedOverOriginal
import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.JTBoundaryNecklaceConeTriangle

/-!
# Source restriction over the original comma object
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedOverSource

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedComparison (Fiber comparisonFunctor)
open JTGraphInterpolatedOverOriginal
open JTGraphInterpolatedCollapseOriginal
open JTGraphInterpolatedSourceComparison
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTCommaGraphPredecessor (augmentationCode)
open JTNecklaceEndpointCylinder (cylinder nativeMap)
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)
open BoundaryNecklaceComma (necklaceUnder)
open JTTargetCommaPullback (diagram toPullback equivalence)
open JTBoundaryNecklaceConeTriangle (mapCone_triangle overHom)
open JTBoundaryNecklaceConeReindex (mapCone)

noncomputable section

private theorem mapCone_triangle_id {J J' C C' : Type*}
    [Category* J] [Category* J'] [Category* C] [Category* C']
    (M : J ⥤ J') {F : J ⥤ C} {F' : J' ⥤ C} {X : C}
    (τ : F ⟶ (Functor.const J).obj X) (τ' : F' ⟶ (Functor.const J').obj X)
    (α : F ⟶ M ⋙ F') (h : α ≫ Functor.whiskerLeft M τ' = τ)
    (K : C ⥤ C') {Y : C'} (k : K.obj X ⟶ Y) :
    Functor.whiskerRight α K ≫ Functor.whiskerLeft M (mapCone τ' K k) = mapCone τ K k := by
  have hk : K.map (𝟙 X) ≫ k = k ≫ 𝟙 Y := by
    rw [K.map_id, Category.id_comp, Category.comp_id]
  calc
    _ = mapCone τ K k ≫ (Functor.const J).map (𝟙 Y) :=
      mapCone_triangle M τ τ' α (𝟙 X) (h.trans (by rw [(Functor.const J).map_id,
        Category.comp_id])) K k k (𝟙 Y) hk
    _ = _ := by rw [(Functor.const J).map_id, Category.comp_id]

private def overHom_whisker {J J' C : Type*} [Category* J] [Category* J'] [Category* C]
    (M : J ⥤ J') {F : J ⥤ C} {F' : J' ⥤ C} {X : C}
    (τ : F ⟶ (Functor.const J).obj X) (τ' : F' ⟶ (Functor.const J').obj X)
    (α : F ⟶ M ⋙ F') (h : α ≫ Functor.whiskerLeft M τ' = τ) :
    Over.lift F τ ⟶ M ⋙ Over.lift F' τ' :=
  overHom τ (Functor.whiskerLeft M τ') α h

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {R S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (g : R ⟶ S)

private abbrev restricted := fun i ↦ restrict (D i) g

include hD in
private theorem restricted_collapse (i : Fin (n.len + 1)) :
    (restricted D g i).collapse = g ≫ c :=
  congrArg (fun d ↦ g ≫ d) (hD i)

private theorem timeCollapse_source :
    sourceMap g n ≫ timeCollapse (n := n) c = timeCollapse (n := n) (g ≫ c) := by
  apply Under.UnderMorphism.ext
  change nativeMap g n ≫ augmentation S n ≫ c.map = augmentation R n ≫ (g ≫ c).map
  rw [← Category.assoc, augmentation_native_natural, Category.assoc]
  rfl

private theorem indexCollapse_source :
    indexArrow c D hD g ≫ indexCollapse c D hD =
      indexCollapse (g ≫ c) (restricted D g) (restricted_collapse c D hD g) := by
  have h : (projection (W := W) (x := x) (y := y)).map
        (indexArrow c D hD g ≫ indexCollapse c D hD) =
      (projection (W := W) (x := x) (y := y)).map
        (indexCollapse (g ≫ c) (restricted D g) (restricted_collapse c D hD g)) := by
    calc
      _ = (g, 𝟙 (degree U.left)) ≫ (c ≫ augmentationCode U.left, 𝟙 (degree U.left)) := by
        rw [Functor.map_comp, indexArrow_operator, indexCollapse_operator]
      _ = ((g ≫ c) ≫ augmentationCode U.left, 𝟙 (degree U.left)) :=
        Prod.ext (Category.assoc g c (augmentationCode U.left)).symm (Category.id_comp _)
      _ = _ := (indexCollapse_operator (g ≫ c) (restricted D g)
        (restricted_collapse c D hD g)).symm
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun f ↦ f.op) h

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ augmentationCode U.left).map (D i).parameter ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

private abbrev decorated := toDecorated U c (fun i ↦ (D i).parameter)

private abbrev raw := whole_raw U c (fun i ↦ (D i).parameter) (parameter_comm c D hD)

private abbrev sourceFiberMap : Fiber R n ⥤ Fiber S n :=
  CostructuredArrow.map (S := necklaceUnder) (sourceMap g n)

private abbrev presentationComparison :=
  JTCylinderOverTargetBaseChange.comparePresentation W x y Q
    (index U (g ≫ c)) (index U c) R S n n
    (decorated (g ≫ c) (restricted D g)) (decorated c D) ((g ≫ c) ≫ U.hom.hom) (c ≫ U.hom.hom)
    (raw (g ≫ c) (restricted D g) (restricted_collapse c D hD g)) (raw c D hD)
    (sourceMap g n) (indexArrow c D hD g) (decorated_source c D hD g) (native_source (n := n) c g)

private abbrev restrictedCone :=
  presentationCone (n := n) (g ≫ c) (restricted D g) (restricted_collapse c D hD g)

private abbrev originalCone := presentationCone (n := n) c D hD

set_option maxHeartbeats 65000 in
private theorem presentationComparison_base (P : Fiber R n) :
    ((presentationComparison c D hD g).app P).base = indexArrow c D hD g :=
  JTCylinderOverTargetBaseChange.comparisonOfSquare_base _ _ _ _ _ _ _

set_option maxHeartbeats 65000 in
private theorem presentationComparison_code (P : Fiber R n) :
    (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
      ((presentationComparison c D hD g).app P) = 𝟙 P.left :=
  JTCylinderOverTargetBaseChange.comparisonOfSquare_code _ _ _ _ _ _ _

set_option maxHeartbeats 65000 in
private theorem source_triangle_base (P : Fiber R n) :
    (((presentationComparison c D hD g).app P) ≫
      (originalCone c D hD).app ((sourceFiberMap (n := n) g).obj P)).base =
    ((restrictedCone c D hD g).app P).base := by
  change ((presentationComparison c D hD g).app P).base ≫ indexCollapse c D hD =
    indexCollapse (g ≫ c) (restricted D g) (restricted_collapse c D hD g)
  rw [presentationComparison_base]
  exact indexCollapse_source c D hD g

set_option maxHeartbeats 65000 in
private theorem source_triangle_code (P : Fiber R n) :
    (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
      (((presentationComparison c D hD g).app P) ≫
        (originalCone c D hD).app ((sourceFiberMap (n := n) g).obj P)) =
    (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
      ((restrictedCone c D hD g).app P) := by
  rw [Functor.map_comp, presentationComparison_code]
  refine (Category.id_comp _).trans ?_
  apply NecklaceCode.Hom.ext
  change ((P.hom ≫ sourceMap g n) ≫ timeCollapse (n := n) c).right =
    (P.hom ≫ timeCollapse (n := n) (g ≫ c)).right
  rw [Category.assoc, timeCollapse_source]

set_option maxHeartbeats 65000 in
private theorem presentation_source_triangle :
    presentationComparison c D hD g ≫ Functor.whiskerLeft (sourceFiberMap (n := n) g)
        (originalCone c D hD) = restrictedCone c D hD g := by
  ext : 1
  funext P
  exact JTTargetCommaPullback.operator_ext (source_triangle_base c D hD g P)
    (source_triangle_code c D hD g P)

set_option maxHeartbeats 180000 in
/-- The whole source comparison commutes with the cone to the original object. -/
theorem comparisonToOriginal_source :
    sourceComparison c D hD g ≫ Functor.whiskerLeft (sourceFiberMap (n := n) g)
        (comparisonToOriginal (n := n) c D hD) =
      comparisonToOriginal (n := n) (g ≫ c) (restricted D g) (restricted_collapse c D hD g) := by
  unfold sourceComparison JTCylinderOverTargetBaseChange.compare comparisonToOriginal
  exact mapCone_triangle_id (sourceFiberMap (n := n) g)
    (presentationCone (n := n) (g ≫ c) (restricted D g) (restricted_collapse c D hD g))
    (presentationCone (n := n) c D hD) (presentationComparison c D hD g)
    (presentation_source_triangle c D hD g) (equivalence W x y Q).inverse
    ((equivalence W x y Q).unitIso.app U).inv

set_option maxHeartbeats 180000 in
/-- Source restriction gives a natural transformation of the actual slice functors. -/
def overSourceComparison :
    overOriginal (n := n) (g ≫ c) (restricted D g) (restricted_collapse c D hD g) ⟶
      CostructuredArrow.map (S := necklaceUnder) (sourceMap g n) ⋙ overOriginal (n := n) c D hD :=
  overHom_whisker (CostructuredArrow.map (S := necklaceUnder) (sourceMap g n))
    (comparisonToOriginal (n := n) (g ≫ c) (restricted D g) (restricted_collapse c D hD g))
    (comparisonToOriginal (n := n) c D hD) (sourceComparison c D hD g)
    (comparisonToOriginal_source c D hD g)

end

end DaggerModels.PartII.JTGraphInterpolatedOverSource
