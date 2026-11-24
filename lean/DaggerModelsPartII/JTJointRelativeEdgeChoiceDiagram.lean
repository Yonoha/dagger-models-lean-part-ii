import DaggerModelsPartII.JTJointEndpointLiftSpaceRestriction
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Full simplicial spaces of paired relative endpoint-edge choices. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointRelativeEdgeChoiceDiagram

open JTProjectiveOrderedFiberComparison JTJointEndpointRelativeLift
open JTJointEndpointLiftSpaceRestriction
open DaggerOriginalProductGadget (pointMap pointIsTerminal pointMap_tensor_GW)
open GrothendieckTotalElements (totalDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source)
  (s k : I ⥤ SimplexCategory) (u : s ⟶ k)
  (f : k ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
  (z : (row W ⦋0⦌).obj (op ⦋0⦌))
  (hf : ∀ i : I, std.map (u.app i) ≫ f.app i =
    term (Δ (s.obj i)) ≫ vertexPoint W z)

private def leftSquare (i : I) := square W (u.app i) (f.app i) z (hf i)
private def rightSquare (i : I) := reverseSquare W (u.app i) (f.app i) z (hf i)

private abbrev short {i j : I} (α : i ⟶ j) := std.map (s.map α)
private abbrev long {i j : I} (α : i ⟶ j) := std.map (k.map α)

private theorem short_long {i j : I} (α : i ⟶ j) :
    short s α ≫ std.map (u.app j) =
      std.map (u.app i) ≫ long k α := by
  simpa only [short, long, std.map_comp] using
    congrArg std.map (u.naturality α)

private theorem f_natural {i j : I} (α : i ⟶ j) :
    long k α ≫ f.app j = f.app i := by
  have h := f.naturality α
  change long k α ≫ f.app j = f.app i ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem left_base {i j : I} (α : i ⟶ j) :
    long k α ≫ boundaryPair W (f.app j) z =
      boundaryPair W (f.app i) z := by
  rw [boundaryPair_natural, f_natural W k f α]

private theorem right_base {i j : I} (α : i ⟶ j) :
    long k α ≫ reverseBoundaryPair W (f.app j) z =
      reverseBoundaryPair W (f.app i) z := by
  rw [reverseBoundaryPair_natural, f_natural W k f α]

private def leftRestrict {i j : I} (α : i ⟶ j) :
    (SSet.ihomToPullbackFiber (leftSquare W s k u f z hf j) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (leftSquare W s k u f z hf i) :=
  precompSquare (leftSquare W s k u f z hf j)
    (leftSquare W s k u f z hf i) (short s α) (long k α)
    (short_long s k u α) (identityOnFace_natural W z (s.map α))
    (left_base W k f z α)

private def rightRestrict {i j : I} (α : i ⟶ j) :
    (SSet.ihomToPullbackFiber (rightSquare W s k u f z hf j) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (rightSquare W s k u f z hf i) :=
  precompSquare (rightSquare W s k u f z hf j)
    (rightSquare W s k u f z hf i) (short s α) (long k α)
    (short_long s k u α) (identityOnFace_natural W z (s.map α))
    (right_base W k f z α)

private theorem long_id (i : I) : long k (𝟙 i) = 𝟙 _ := by
  simp only [long, k.map_id, std.map_id]

private theorem long_comp {i j h : I} (α : i ⟶ j) (β : j ⟶ h) :
    long k α ≫ long k β = long k (α ≫ β) := by
  simp only [long, k.map_comp, std.map_comp]

private theorem leftRestrict_ι {i j : I} (α : i ⟶ j) :
    leftRestrict W s k u f z hf α ≫
      (SSet.ihomToPullbackFiber (leftSquare W s k u f z hf i)).ι =
    (SSet.ihomToPullbackFiber (leftSquare W s k u f z hf j)).ι ≫
      (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌) :=
  precompSquare_ι _ _ _ _ _ _ _

private theorem rightRestrict_ι {i j : I} (α : i ⟶ j) :
    rightRestrict W s k u f z hf α ≫
      (SSet.ihomToPullbackFiber (rightSquare W s k u f z hf i)).ι =
    (SSet.ihomToPullbackFiber (rightSquare W s k u f z hf j)).ι ≫
      (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌) :=
  precompSquare_ι _ _ _ _ _ _ _

private theorem leftRestrict_id (i : I) :
    leftRestrict W s k u f z hf (𝟙 i) = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (leftSquare W s k u f z hf i)).ι).mp
  rw [leftRestrict, precompSquare_ι, long_id,
    MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem rightRestrict_id (i : I) :
    rightRestrict W s k u f z hf (𝟙 i) = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (rightSquare W s k u f z hf i)).ι).mp
  rw [rightRestrict, precompSquare_ι, long_id,
    MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem leftRestrict_comp {i j h : I} (α : i ⟶ j) (β : j ⟶ h) :
    leftRestrict W s k u f z hf (α ≫ β) =
      leftRestrict W s k u f z hf β ≫
        leftRestrict W s k u f z hf α := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (leftSquare W s k u f z hf i)).ι).mp
  calc
    leftRestrict W s k u f z hf (α ≫ β) ≫ _ =
        (SSet.ihomToPullbackFiber (leftSquare W s k u f z hf h)).ι ≫
          (MonoidalClosed.pre (long k (α ≫ β))).app (row W ⦋1⦌) := by
            exact precompSquare_ι _ _ _ _ _ _ _
    _ = (SSet.ihomToPullbackFiber (leftSquare W s k u f z hf h)).ι ≫
        ((MonoidalClosed.pre (long k β)).app (row W ⦋1⦌) ≫
          (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌)) := by
            rw [← long_comp, MonoidalClosed.pre_map, NatTrans.comp_app]
    _ = (leftRestrict W s k u f z hf β ≫
        leftRestrict W s k u f z hf α) ≫ _ := by
          rw [← Category.assoc]
          rw [← leftRestrict_ι W s k u f z hf β]
          simp only [Category.assoc, leftRestrict_ι]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌))
            (leftRestrict_ι W s k u f z hf β).symm

private theorem rightRestrict_comp {i j h : I} (α : i ⟶ j) (β : j ⟶ h) :
    rightRestrict W s k u f z hf (α ≫ β) =
      rightRestrict W s k u f z hf β ≫
        rightRestrict W s k u f z hf α := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (rightSquare W s k u f z hf i)).ι).mp
  calc
    rightRestrict W s k u f z hf (α ≫ β) ≫ _ =
        (SSet.ihomToPullbackFiber (rightSquare W s k u f z hf h)).ι ≫
          (MonoidalClosed.pre (long k (α ≫ β))).app (row W ⦋1⦌) := by
            exact precompSquare_ι _ _ _ _ _ _ _
    _ = (SSet.ihomToPullbackFiber (rightSquare W s k u f z hf h)).ι ≫
        ((MonoidalClosed.pre (long k β)).app (row W ⦋1⦌) ≫
          (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌)) := by
            rw [← long_comp, MonoidalClosed.pre_map, NatTrans.comp_app]
    _ = (rightRestrict W s k u f z hf β ≫
        rightRestrict W s k u f z hf α) ≫ _ := by
          rw [← Category.assoc]
          rw [← rightRestrict_ι W s k u f z hf β]
          simp only [Category.assoc, rightRestrict_ι]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (MonoidalClosed.pre (long k α)).app (row W ⦋1⦌))
            (rightRestrict_ι W s k u f z hf β).symm

/-- Full exact variable-left relative edge choices, including all coherent
higher simplices. -/
def leftChoices : Iᵒᵖ ⥤ SSet.{0} where
  obj i := liftSpace W (u.app i.unop) (f.app i.unop) z (hf i.unop)
  map α := leftRestrict W s k u f z hf α.unop
  map_id i := leftRestrict_id W s k u f z hf i.unop
  map_comp α β := leftRestrict_comp W s k u f z hf β.unop α.unop

/-- Full exact variable-right relative edge choices. -/
def rightChoices : Iᵒᵖ ⥤ SSet.{0} where
  obj i := reverseLiftSpace W (u.app i.unop) (f.app i.unop) z (hf i.unop)
  map α := rightRestrict W s k u f z hf α.unop
  map_id i := rightRestrict_id W s k u f z hf i.unop
  map_comp α β := rightRestrict_comp W s k u f z hf β.unop α.unop

/-- The two oriented relative edge spaces share every simplicial time degree. -/
def pairChoices : Iᵒᵖ ⥤ SSet.{0} :=
  Functor.diag Iᵒᵖ ⋙
    (leftChoices W s k u f z hf).prod (rightChoices W s k u f z hf) ⋙
    MonoidalCategory.tensor SSet.{0}

/-- A left relative choice restricts by literal precomposition on vertices. -/
theorem leftChoices_zero {i j : I} (α : i ⟶ j)
    (v : ((leftChoices W s k u f z hf).obj (op j)).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv
        (((leftChoices W s k u f z hf).map α.op).app (op ⦋0⦌) v).val =
      std.map (k.map α) ≫ SSet.ihom₀Equiv v.val := by
  change SSet.ihom₀Equiv
      (((leftRestrict W s k u f z hf α).app (op ⦋0⦌) v).val) =
      long k α ≫ SSet.ihom₀Equiv v.val
  exact precompSquare_zero
    (leftSquare W s k u f z hf j) (leftSquare W s k u f z hf i)
    (short s α) (long k α) (short_long s k u α)
    (identityOnFace_natural W z (s.map α)) (left_base W k f z α) v

/-- A right relative choice has the same strict vertex restriction. -/
theorem rightChoices_zero {i j : I} (α : i ⟶ j)
    (v : ((rightChoices W s k u f z hf).obj (op j)).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv
        (((rightChoices W s k u f z hf).map α.op).app (op ⦋0⦌) v).val =
      std.map (k.map α) ≫ SSet.ihom₀Equiv v.val := by
  change SSet.ihom₀Equiv
      (((rightRestrict W s k u f z hf α).app (op ⦋0⦌) v).val) =
      long k α ≫ SSet.ihom₀Equiv v.val
  exact precompSquare_zero
    (rightSquare W s k u f z hf j) (rightSquare W s k u f z hf i)
    (short s α) (long k α) (short_long s k u α)
    (identityOnFace_natural W z (s.map α)) (right_base W k f z α) v

private theorem point_GW_of_terminal_weak (X : SSet.{0})
    [WeakEquivalence (term X)] : GW (pointMap X) := by
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  haveI : WeakEquivalence (pointMap X) := by
    rw [← pointIsTerminal.hom_ext (term X ≫ e.hom) (pointMap X)]
    infer_instance
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- Each pair of complete relative edge spaces is weakly contractible. -/
theorem pairChoices_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hu : ∀ i : I, Mono (u.app i)) (i : Iᵒᵖ) :
    GW (pointMap ((pairChoices W s k u f z hf).obj i)) := by
  letI : Mono (u.app i.unop) := hu i.unop
  have hL : GW (pointMap ((leftChoices W s k u f z hf).obj i)) := by
    haveI : WeakEquivalence (term ((leftChoices W s k u f z hf).obj i)) :=
      liftSpace_toPoint_weak W (u.app i.unop) (f.app i.unop) z (hf i.unop) hW
    exact point_GW_of_terminal_weak _
  have hR : GW (pointMap ((rightChoices W s k u f z hf).obj i)) := by
    haveI : WeakEquivalence (term ((rightChoices W s k u f z hf).obj i)) :=
      reverseLiftSpace_toPoint_weak W (u.app i.unop) (f.app i.unop) z (hf i.unop) hW
    exact point_GW_of_terminal_weak _
  exact pointMap_tensor_GW hL hR

/-- The category of all paired simplices projects weakly to the exact-cut
index, retaining every time operator in the total category. -/
theorem pairChoices_projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hu : ∀ i : I, Mono (u.app i)) :
    WeakEquivalence (nerveMap
      (CategoryOfElements.π (totalDiagram (pairChoices W s k u f z hf)) ⋙
        CategoryTheory.Prod.fst Iᵒᵖ SimplexCategoryᵒᵖ)) :=
  SynchronizedSimplicialParameters.projection_weak
    (pairChoices W s k u f z hf)
    (pairChoices_point_GW W s k u f z hf hW hu)

end

end DaggerModels.PartII.JTJointRelativeEdgeChoiceDiagram
