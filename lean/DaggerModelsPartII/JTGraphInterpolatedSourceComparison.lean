import DaggerModelsPartII.JTGraphInterpolatedComparison
import DaggerModelsPartII.JTInterpolatedCylinderSource
import DaggerModelsPartII.JTCylinderOverTargetBaseChange

/-!
# Native source comparisons of the original time-cylinder functors
-/

set_option autoImplicit false
set_option maxHeartbeats 160000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedSourceComparison

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftRestriction (restrict)
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphInterpolatedComparison (Fiber sliceObject comparisonFunctor)
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTInterpolatedReducedCylinder (slice cylinderMap)
open JTGraphParameterInterpolation (interpolate)
open JTParameterContraction (parameterVertex)
open JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)
open BoundaryNecklaceComma (necklaceUnder)
open DecoratedCylinderNecklacePresentation (underDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {R S T : NecklaceCode}

/-- The original native operator at fixed time, as a map under the ordered endpoints. -/
def sourceMap (g : R ⟶ S) (n : SimplexCategory) : (under R).obj n ⟶ (under S).obj n :=
  Under.homMk (nativeMap g n) (nativeMap_boundary g n)

theorem sourceMap_id (n : SimplexCategory) :
    sourceMap (𝟙 S) n = 𝟙 ((under S).obj n) :=
  Under.UnderMorphism.ext (nativeMap_id S n)

theorem sourceMap_comp (g : R ⟶ S) (f : S ⟶ T) (n : SimplexCategory) :
    sourceMap (g ≫ f) n = sourceMap g n ≫ sourceMap f n :=
  Under.UnderMorphism.ext (nativeMap_comp g f n)

theorem sourceMap_time (g : R ⟶ S) {m n : SimplexCategory} (j : m ⟶ n) :
    sourceMap g m ≫ (under S).map j = (under R).map j ≫ sourceMap g n :=
  Under.UnderMorphism.ext (nativeMap_parameter_natural g j).symm

/-- The native map carries a prescribed time slice to the same slice. -/
theorem slice_source (g : R ⟶ S) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    slice R n i ≫ sourceMap g n = necklaceUnder.map g ≫ slice S n i := by
  apply Under.UnderMorphism.ext
  let t (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex n i
  change (lift (𝟙 R.toSSet) (t R.toSSet) ≫ (cylinder R).app n) ≫ nativeMap g n =
    g.map ≫ lift (𝟙 S.toSSet) (t S.toSSet) ≫ (cylinder S).app n
  rw [Category.assoc, nativeMap_cylinder, ← Category.assoc, ← Category.assoc g.map]
  congr 1

/-- At a time vertex the source comparison is the original native map. -/
def sliceSourceArrow (g : R ⟶ S) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (CostructuredArrow.map (sourceMap g n)).obj (sliceObject R n i) ⟶ sliceObject S n i :=
  CostructuredArrow.homMk g (slice_source g n i).symm

theorem sliceSourceArrow_code (g : R ⟶ S) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (sliceSourceArrow g n i).left = g := rfl

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (g : R ⟶ S)

include hD in
private theorem comm (i : Fin (n.len + 1)) :
    lift (c ≫ augmentationCode U.left).map ((D i).parameter) ≫
      (cylinder (code U.left)).app (degree U.left) =
        c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

private def reference : GraphLift U.left S := ⟨c, (D 0).parameter, comm c D hD 0⟩

/-- The original decorated source operator on the pulled-back labels. -/
def indexArrow : index U (g ≫ c) ⟶ index U c :=
  (JTGraphRestrictionRaw.restrictionArrow (reference c D hD) g).base

theorem indexArrow_operator :
    (projection (W := W) (x := x) (y := y)).map (indexArrow c D hD g) =
      (g, 𝟙 (degree U.left)) := rfl

private abbrev D' := fun i ↦ restrict (D i) g

include hD in
private theorem hD' (i : Fin (n.len + 1)) : ((D' D g) i).collapse = g ≫ c :=
  congrArg (fun d ↦ g ≫ d) (hD i)

private abbrev p := fun i ↦ (D i).parameter
private abbrev p' := fun i ↦ ((D' D g) i).parameter

/-- The entire decorated cylinder commutes with the original source restriction. -/
theorem decorated_source :
    toDecorated U (g ≫ c) (p' D g) ≫ (underDiagram W x y).map (indexArrow c D hD g) =
      sourceMap g n ≫ toDecorated U c (p D) := by
  apply Under.UnderMorphism.ext
  change cylinderMap R (interpolate (p' D g)) ≫
      (nativeMap g (degree U.left) ≫ (value S).map (𝟙 (degree U.left))) =
    nativeMap g n ≫ cylinderMap S (interpolate (p D))
  rw [(value S).map_id, Category.comp_id]
  exact JTInterpolatedCylinderSource.interpolated_source g (p D)

/-- The whole native leg into the fixed target commutes with restriction. -/
theorem native_source :
    JTCylinderOverTarget.native W x y Q R n ((g ≫ c) ≫ U.hom.hom) =
      sourceMap g n ≫ JTCylinderOverTarget.native W x y Q S n (c ≫ U.hom.hom) := by
  apply Under.UnderMorphism.ext
  change augmentation R n ≫ ((g ≫ c) ≫ U.hom.hom).map =
    nativeMap g n ≫ augmentation S n ≫ (c ≫ U.hom.hom).map
  rw [← Category.assoc (nativeMap g n), augmentation_native_natural]
  simp only [Category.assoc]
  rfl


/-- Source restriction gives a comparison of the actual functors into the fixed target. -/
def sourceComparison :
    comparisonFunctor (g ≫ c) (D' D g) (hD' c D hD g) ⟶
      CostructuredArrow.map (sourceMap g n) ⋙ comparisonFunctor c D hD :=
  JTCylinderOverTargetBaseChange.compare W x y Q
    (index U (g ≫ c)) (index U c) R S n n (toDecorated U (g ≫ c) (p' D g))
    (toDecorated U c (p D)) ((g ≫ c) ≫ U.hom.hom) (c ≫ U.hom.hom)
    (whole_raw U (g ≫ c) (p' D g) (comm (g ≫ c) (D' D g) (hD' c D hD g)))
    (whole_raw U c (p D) (comm c D hD)) (sourceMap g n) (indexArrow c D hD g)
    (decorated_source c D hD g) (native_source (n := n) c g)

/-- At a time vertex, the comparison has the prescribed native source slice as target. -/
def sliceComparison (i : Fin (n.len + 1)) :
    (comparisonFunctor (g ≫ c) (D' D g) (hD' c D hD g)).obj (sliceObject R n i) ⟶
      (comparisonFunctor c D hD).obj (sliceObject S n i) :=
  (sourceComparison c D hD g).app (sliceObject R n i) ≫
    (comparisonFunctor c D hD).map (sliceSourceArrow g n i)

end

end DaggerModels.PartII.JTGraphInterpolatedSourceComparison
