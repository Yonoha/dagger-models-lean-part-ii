import DaggerModelsPartII.JTGraphInterpolatedComparison
import DaggerModelsPartII.JTGraphTransportRaw
import DaggerModelsPartII.JTInterpolatedCylinderOutput
import DaggerModelsPartII.JTCylinderOverTargetBaseChange
import DaggerModelsPartII.JTCylinderOverTargetBaseChangeTime

/-!
# Transport of interpolated graph comparisons along an original target arrow
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (Fiber comparisonFunctor)
open JTGraphInterpolatedRaw (index toDecorated)
open JTNecklaceEndpointCylinder (under)
open JTInterpolatedReducedCylinder (cylinderMap)
open JTGraphParameterInterpolation (interpolate)
open JTGraphFactoredPresentation (TargetComma)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (a : U ⟶ V)

private def initialGraph : GraphLift U.left S := by
  let i : Fin (n.len + 1) := ⟨0, Nat.zero_lt_succ _⟩
  exact ⟨c, (D i).parameter, by
    have h := (D i).comm
    rw [hD i] at h
    exact h⟩

def indexArrow : index U c ⟶ index V (c ≫ a.left.fiber.left) := by
  exact (JTGraphTransportRaw.transportArrow (initialGraph c D hD) a.left).base

theorem indexArrow_projection :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      (indexArrow c D hD a) = (𝟙 S, degreeOperator a.left) := by
  exact JTGraphTransportRaw.transportArrow_base (initialGraph c D hD) a.left

private theorem decorated_natural :
    toDecorated U c (fun i ↦ (D i).parameter) ≫
        (underDiagram W x y).map (indexArrow c D hD a) =
      (𝟙 ((under S).obj n)) ≫
        toDecorated V (c ≫ a.left.fiber.left)
          (fun i ↦ ((D i).transport a.left).parameter) := by
  rw [Category.id_comp]
  apply Under.UnderMorphism.ext
  have hp := (JTInterpolatedCylinderOutput.interpolated_output S
    (degreeOperator a.left) (fun i ↦ (D i).parameter)).2
  have hi := indexArrow_projection c D hD a
  change cylinderMap S (interpolate (fun i ↦ (D i).parameter)) ≫
      ((NecklaceCylinderJointDiagram.cylinderUnder).map
        ((OrderedLabelElements.projection W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
            (indexArrow c D hD a))).right =
      cylinderMap S
          (interpolate (fun i ↦ ((D i).transport a.left).parameter))
  rw [hi]
  change cylinderMap S (interpolate (fun i ↦ (D i).parameter)) ≫
      (JTNecklaceEndpointCylinder.nativeMap (𝟙 S) (degree U.left) ≫
        (JTNecklaceEndpointCylinder.value S).map (degreeOperator a.left)) =
      cylinderMap S
          (interpolate (fun i ↦ (D i).parameter ≫ J.map (degreeOperator a.left)))
  rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp]
  exact hp

private theorem native_natural :
    JTCylinderOverTarget.native W x y Q S n (c ≫ U.hom.hom) =
      (𝟙 ((under S).obj n)) ≫
        JTCylinderOverTarget.native W x y Q S n
          ((c ≫ a.left.fiber.left) ≫ V.hom.hom) := by
  have hw := congrArg (fun f : (DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      U.left ⟶ Q ↦ f.hom) (CostructuredArrow.w a)
  change a.left.fiber.left ≫ V.hom.hom = U.hom.hom at hw
  have hd : c ≫ U.hom.hom = (c ≫ a.left.fiber.left) ≫ V.hom.hom := by
    rw [Category.assoc, hw]
  rw [← hd, Category.id_comp]

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ JTCommaGraphPredecessor.augmentationCode U.left).map ((D i).parameter) ≫
        (JTNecklaceEndpointCylinder.cylinder (JTGraphLiftTransport.code U.left)).app
          (degree U.left) =
      c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

include hD in
private theorem transported_collapse (i : Fin (n.len + 1)) :
    ((D i).transport a.left).collapse = c ≫ a.left.fiber.left := by
  change (D i).collapse ≫ a.left.fiber.left = _
  rw [hD i]

/-- The literal lift comparison square for target transport. -/
abbrev transportSquare :=
  JTCylinderOverTargetBaseChange.lift_compare W x y Q
    (index U c) (index V (c ≫ a.left.fiber.left)) S S n n
    (toDecorated U c (fun i ↦ (D i).parameter))
    (toDecorated V (c ≫ a.left.fiber.left)
      (fun i ↦ ((D i).transport a.left).parameter))
    (c ≫ U.hom.hom) ((c ≫ a.left.fiber.left) ≫ V.hom.hom)
    (JTGraphInterpolatedRaw.whole_raw U c _ (parameter_comm c D hD))
    (JTGraphInterpolatedRaw.whole_raw V (c ≫ a.left.fiber.left) _
      (parameter_comm (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left) (transported_collapse c D hD a)))
    (𝟙 ((under S).obj n)) (indexArrow c D hD a)
    (decorated_natural c D hD a) (native_natural c a)

/-- The target transport before mapping through the fixed-target equivalence. -/
abbrev transportPresentation :=
  JTCylinderOverTargetBaseChange.comparePresentation W x y Q
    (index U c) (index V (c ≫ a.left.fiber.left)) S S n n
    (toDecorated U c (fun i ↦ (D i).parameter))
    (toDecorated V (c ≫ a.left.fiber.left)
      (fun i ↦ ((D i).transport a.left).parameter))
    (c ≫ U.hom.hom) ((c ≫ a.left.fiber.left) ≫ V.hom.hom)
    (JTGraphInterpolatedRaw.whole_raw U c _ (parameter_comm c D hD))
    (JTGraphInterpolatedRaw.whole_raw V (c ≫ a.left.fiber.left) _
      (parameter_comm (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left) (transported_collapse c D hD a)))
    (𝟙 ((under S).obj n)) (indexArrow c D hD a)
    (decorated_natural c D hD a) (native_natural c a)

/-- Postcomposition by the identity time operator fixes the transported functor. -/
theorem transportTargetEq :
    CostructuredArrow.map (S := BoundaryNecklaceComma.necklaceUnder) (𝟙 ((under S).obj n)) ⋙
      comparisonFunctor (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left) (transported_collapse c D hD a) =
      comparisonFunctor (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left) (transported_collapse c D hD a) := by
  rw [JTCylinderOverTargetBaseChangeTime.map_id, Functor.id_comp]

/-- The actual interpolated comparison is natural under an arrow of the fixed target comma. -/
def transportComparison :
    comparisonFunctor c D hD ⟶
      comparisonFunctor (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left)
        (transported_collapse c D hD a) :=
  Functor.whiskerRight (transportPresentation c D hD a)
    (JTTargetCommaPullback.equivalence W x y Q).inverse ≫
      eqToHom (transportTargetEq c D hD a)

/-- The original target comparison is the mapped pullback transformation. -/
theorem transportComparison_eq_presentation :
    transportComparison c D hD a =
      Functor.whiskerRight (transportPresentation c D hD a)
        (JTTargetCommaPullback.equivalence W x y Q).inverse ≫
          eqToHom (transportTargetEq c D hD a) := rfl

/-- The transport operator on decorated labels is independent of time restriction. -/
theorem indexArrow_reindex {m : SimplexCategory} (j : m ⟶ n) :
    indexArrow c D hD a =
      indexArrow c (fun i ↦ D (j.toOrderHom i))
        (fun i ↦ hD (j.toOrderHom i)) a := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun f ↦ f.op) ((indexArrow_projection c D hD a).trans
    (indexArrow_projection c (fun i ↦ D (j.toOrderHom i))
      (fun i ↦ hD (j.toOrderHom i)) a).symm)

/-- Conjugacy remains true after composing both comparisons with equality casts. -/
private theorem postcast_conjugacy
    {C₀ C D : Type*} [Category* C₀] [Category* C] [Category* D]
    (M : C₀ ⥤ C) {Aₙ Bₙ Cₙ : C ⥤ D} {Aₘ Bₘ Cₘ : C₀ ⥤ D}
    (α : Aₙ ⟶ Bₙ) (β : Aₘ ⟶ Bₘ)
    (hs : M ⋙ Aₙ = Aₘ) (ht : M ⋙ Bₙ = Bₘ)
    (hn : Bₙ = Cₙ) (hm : Bₘ = Cₘ) (hc : M ⋙ Cₙ = Cₘ)
    (h : Functor.whiskerLeft M α ≫ eqToHom ht = eqToHom hs ≫ β) :
    Functor.whiskerLeft M (α ≫ eqToHom hn) ≫ eqToHom hc =
      eqToHom hs ≫ (β ≫ eqToHom hm) := by
  subst Cₙ Cₘ Bₘ Aₘ
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using h

set_option maxHeartbeats 800000 in
/-- Transport of the actual graph comparison commutes with time reindexing. -/
theorem transportComparison_reindex {m : SimplexCategory} (j : m ⟶ n) :
    Functor.whiskerLeft (CostructuredArrow.map ((under S).map j))
        (transportComparison c D hD a) ≫
      eqToHom (JTGraphInterpolatedComparison.comparisonFunctor_reindex
        (c ≫ a.left.fiber.left)
        (fun i ↦ (D i).transport a.left) (transported_collapse c D hD a) j) =
    eqToHom (JTGraphInterpolatedComparison.comparisonFunctor_reindex c D hD j) ≫
      transportComparison c (fun i ↦ D (j.toOrderHom i))
        (fun i ↦ hD (j.toOrderHom i)) a := by
  let Dm : Fin (m.len + 1) → GraphLift U.left S :=
    fun i ↦ D (j.toOrderHom i)
  let En : Fin (n.len + 1) → GraphLift V.left S :=
    fun i ↦ (D i).transport a.left
  let Em : Fin (m.len + 1) → GraphLift V.left S :=
    fun i ↦ (Dm i).transport a.left
  have hDm :
      toDecorated U c (fun i ↦ (Dm i).parameter) ≫
          (underDiagram W x y).map (indexArrow c D hD a) =
        (𝟙 ((under S).obj m)) ≫
          toDecorated V (c ≫ a.left.fiber.left)
            (fun i ↦ (Em i).parameter) := by
    rw [indexArrow_reindex c D hD a j]
    exact decorated_natural c Dm (fun i ↦ hD (j.toOrderHom i)) a
  have hRaw := JTCylinderOverTargetBaseChangeTime.compare_reindex
    W x y Q (index U c) (index V (c ≫ a.left.fiber.left)) S S j
    (toDecorated U c (fun i ↦ (Dm i).parameter))
    (toDecorated U c (fun i ↦ (D i).parameter))
    (toDecorated V (c ≫ a.left.fiber.left) (fun i ↦ (Em i).parameter))
    (toDecorated V (c ≫ a.left.fiber.left) (fun i ↦ (En i).parameter))
    (c ≫ U.hom.hom) ((c ≫ a.left.fiber.left) ≫ V.hom.hom)
    (JTGraphInterpolatedRaw.whole_raw U c _
      (parameter_comm c Dm (fun i ↦ hD (j.toOrderHom i))))
    (JTGraphInterpolatedRaw.whole_raw U c _ (parameter_comm c D hD))
    (JTGraphInterpolatedRaw.whole_raw V (c ≫ a.left.fiber.left) _
      (parameter_comm (c ≫ a.left.fiber.left) Em
        (transported_collapse c Dm (fun i ↦ hD (j.toOrderHom i)) a)))
    (JTGraphInterpolatedRaw.whole_raw V (c ≫ a.left.fiber.left) _
      (parameter_comm (c ≫ a.left.fiber.left) En (transported_collapse c D hD a)))
    (𝟙 ((under S).obj m)) (𝟙 ((under S).obj n)) (indexArrow c D hD a)
    (JTGraphInterpolatedComparison.decorated_reindex c D j)
    (JTGraphInterpolatedComparison.decorated_reindex
      (c ≫ a.left.fiber.left) En j)
    (by simp) hDm (decorated_natural c D hD a)
    (native_natural c a) (native_natural c a)
  unfold transportComparison
  exact postcast_conjugacy
    (CostructuredArrow.map ((under S).map j))
    _ _
    (JTGraphInterpolatedComparison.comparisonFunctor_reindex c D hD j)
    (JTCylinderOverTargetBaseChangeTime.reindex_target
      ((under S).map j) ((under S).map j)
      (𝟙 ((under S).obj m)) (𝟙 ((under S).obj n)) _ _ (by simp)
      (JTGraphInterpolatedComparison.comparisonFunctor_reindex
        (c ≫ a.left.fiber.left) En (transported_collapse c D hD a) j))
    (by
      have hi := congrArg Cat.Hom.toFunctor
        (BoundaryNecklaceComma.diagram.map_id ((under S).obj n))
      change CostructuredArrow.map (𝟙 ((under S).obj n)) = 𝟭 (Fiber S n) at hi
      rw [hi, Functor.id_comp])
    (by
      have hi := congrArg Cat.Hom.toFunctor
        (BoundaryNecklaceComma.diagram.map_id ((under S).obj m))
      change CostructuredArrow.map (𝟙 ((under S).obj m)) = 𝟭 (Fiber S m) at hi
      rw [hi, Functor.id_comp])
    (JTGraphInterpolatedComparison.comparisonFunctor_reindex
      (c ≫ a.left.fiber.left) En (transported_collapse c D hD a) j)
    hRaw

end

end DaggerModels.PartII.JTGraphInterpolatedTransport
