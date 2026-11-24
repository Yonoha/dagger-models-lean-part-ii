import DaggerModelsPartII.JTGraphInterpolatedSourceComparison

/-!
# Exact operators of the interpolated source comparison at a time slice
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedSourceSlice

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedComparison (sliceObject)
open JTGraphInterpolatedSourceComparison
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTNecklaceEndpointCylinder (cylinder)
open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)
open JTTargetCommaPullback (diagram equivalence)

noncomputable section

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
variable (g : R ⟶ S) (i : Fin (n.len + 1))

private abbrev restricted := fun j ↦ restrict (D j) g

include hD in
private theorem restricted_collapse (j : Fin (n.len + 1)) :
    (restricted D g j).collapse = g ≫ c :=
  congrArg (fun d ↦ g ≫ d) (hD j)

include hD in
private theorem parameter_comm (j : Fin (n.len + 1)) :
    lift (c ≫ JTCommaGraphPredecessor.augmentationCode U.left).map ((D j).parameter) ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D j).comm
  rw [hD j] at h
  exact h

private abbrev leg (c : S ⟶ U.left.fiber.left)
    (D : Fin (n.len + 1) → GraphLift U.left S) :=
  toDecorated U c (fun j ↦ (D j).parameter)

private abbrev witness (c : S ⟶ U.left.fiber.left)
    (D : Fin (n.len + 1) → GraphLift U.left S) (hD : ∀ i, (D i).collapse = c) :=
  whole_raw U c _ (parameter_comm c D hD)

private abbrev presentation (c : S ⟶ U.left.fiber.left)
    (D : Fin (n.len + 1) → GraphLift U.left S) (hD : ∀ i, (D i).collapse = c) :=
  JTCylinderOverTarget.atBase W x y Q (index U c) S n (leg c D) (c ≫ U.hom.hom)
      (witness c D hD) ⋙
    Grothendieck.ι (fiberDiagram (diagram W x y Q)) (index U c)

private abbrev comparison (c : S ⟶ U.left.fiber.left)
    (D : Fin (n.len + 1) → GraphLift U.left S) (hD : ∀ i, (D i).collapse = c) (g : R ⟶ S) :=
  JTCylinderOverTargetBaseChange.comparePresentation W x y Q
    (index U (g ≫ c)) (index U c) R S n n (leg (g ≫ c) (restricted D g)) (leg c D)
    ((g ≫ c) ≫ U.hom.hom) (c ≫ U.hom.hom)
    (witness (g ≫ c) (restricted D g) (restricted_collapse c D hD g))
    (witness c D hD) (sourceMap g n) (indexArrow c D hD g)
    (decorated_source c D hD g) (native_source (n := n) c g)

/-- The time-slice comparison arrow in the fixed-target pullback presentation. -/
def presentationSliceArrow :
    (presentation (g ≫ c) (restricted D g) (restricted_collapse c D hD g)).obj
        (sliceObject R n i) ⟶
      (presentation c D hD).obj (sliceObject S n i) :=
  (comparison c D hD g).app (sliceObject R n i) ≫
    (presentation c D hD).map (sliceSourceArrow g n i)

/-- The time-slice arrow has the original decorated source operator. -/
theorem presentationSliceArrow_base :
    (presentationSliceArrow c D hD g i).base = indexArrow c D hD g := by
  have hBase : ((comparison c D hD g).app (sliceObject R n i)).base =
      indexArrow c D hD g :=
    JTCylinderOverTargetBaseChange.comparisonOfSquare_base _ _ _ _ _ _ _
  rw [presentationSliceArrow, Grothendieck.comp_base, hBase]
  exact Category.comp_id _

private theorem eqToHom_left {T : Under JTXiEndpointCollapse.boundary}
    {P P' : CostructuredArrow necklaceUnder T} (h : P = P') :
    (eqToHom h).left = eqToHom (congrArg (fun A ↦ A.left) h) := by
  cases h
  rfl

private theorem slice_ι_code {I : Type} [SmallCategory I] (E : I ⥤ Under JTXiEndpointCollapse.boundary)
    (i : I) {A B : CostructuredArrow necklaceUnder (E.obj i)} (f : A ⟶ B) :
    (sourceCode E).map ((Grothendieck.ι (fiberDiagram E) i).map f) = f.left := by
  change ((Grothendieck.ι (fiberDiagram E) i).map f).fiber.left = f.left
  rw [Grothendieck.ι_map]
  dsimp only
  rw [CostructuredArrow.comp_left, eqToHom_left]
  exact Category.id_comp _

/-- The time-slice arrow has the original native necklace map. -/
theorem presentationSliceArrow_code :
    (sourceCode (diagram W x y Q)).map (presentationSliceArrow c D hD g i) = g := by
  have hCode :
      (sourceCode (diagram W x y Q)).map ((comparison c D hD g).app (sliceObject R n i)) =
        𝟙 R :=
    JTCylinderOverTargetBaseChange.comparisonOfSquare_code _ _ _ _ _ _ _
  rw [presentationSliceArrow, Functor.map_comp, hCode]
  change 𝟙 R ≫ (sourceCode (diagram W x y Q)).map
    ((Grothendieck.ι (fiberDiagram (diagram W x y Q)) (index U c)).map
      ((JTCylinderOverTarget.atBase W x y Q (index U c) S n (leg c D)
        (c ≫ U.hom.hom) (witness c D hD)).map (sliceSourceArrow g n i))) = g
  rw [slice_ι_code]
  exact Category.id_comp _

/-- The actual comma arrow is the inverse image of this presentation arrow. -/
theorem sliceComparison_eq_map :
    sliceComparison c D hD g i =
      (equivalence W x y Q).inverse.map (presentationSliceArrow c D hD g i) := by
  unfold sliceComparison sourceComparison JTCylinderOverTargetBaseChange.compare
  rw [presentationSliceArrow, Functor.map_comp]
  rfl

end

end DaggerModels.PartII.JTGraphInterpolatedSourceSlice
