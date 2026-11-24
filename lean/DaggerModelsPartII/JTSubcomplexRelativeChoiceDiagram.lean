import DaggerModelsPartII.JTJointSubcomplexRelativeLift
import DaggerModelsPartII.JTJointEndpointLiftSpaceRestriction
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Natural full relative-edge choice spaces over arbitrary simplicial supports. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSubcomplexRelativeChoiceDiagram

open JTProjectiveOrderedFiberComparison
open JTJointEndpointLiftSpaceRestriction (precompSquare precompSquare_ι precompSquare_zero)
open DaggerOriginalProductGadget (pointMap pointIsTerminal pointMap_tensor_GW)
open GrothendieckTotalElements (totalDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {B : Type} [SmallCategory B] (W : Source)
  (U : B ⥤ SSet.{0}) (K : B ⥤ SimplexCategory)
  (incl : U ⟶ K ⋙ std)
  (f : K ⋙ std ⟶ (Functor.const B).obj (row W ⦋0⦌))
  (z : (row W ⦋0⦌).obj (op ⦋0⦌))
  (hf : ∀ b : B, incl.app b ≫ f.app b = term (U.obj b) ≫ vertexPoint W z)

private def leftSquare (b : B) :=
  JTJointSubcomplexRelativeLift.square W (incl.app b) (f.app b) z (hf b)
private def rightSquare (b : B) :=
  JTJointSubcomplexRelativeLift.reverseSquare W (incl.app b) (f.app b) z (hf b)

private abbrev short {b c : B} (α : b ⟶ c) := U.map α
private abbrev long {b c : B} (α : b ⟶ c) := std.map (K.map α)

private theorem short_long {b c : B} (α : b ⟶ c) :
    short U α ≫ incl.app c = incl.app b ≫ long K α :=
  incl.naturality α

private theorem f_natural {b c : B} (α : b ⟶ c) :
    long K α ≫ f.app c = f.app b := by
  have h := f.naturality α
  change long K α ≫ f.app c = f.app b ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem identity_natural {b c : B} (α : b ⟶ c) :
    short U α ≫ JTJointSubcomplexRelativeLift.identityOnU W z (U := U.obj c) =
      JTJointSubcomplexRelativeLift.identityOnU W z (U := U.obj b) := by
  change U.map α ≫ (term (U.obj c) ≫ vertexPoint W z ≫
      JTEndpointNormalizationLifts.identityFamily W) =
    term (U.obj b) ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W
  have ht : U.map α ≫ term (U.obj c) = term (U.obj b) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ vertexPoint W z ≫ JTEndpointNormalizationLifts.identityFamily W) ht

private theorem left_base {b c : B} (α : b ⟶ c) :
    long K α ≫ JTJointSubcomplexRelativeLift.boundaryPair W (f.app c) z =
      JTJointSubcomplexRelativeLift.boundaryPair W (f.app b) z := by
  change long K α ≫ JTJointEndpointRelativeLift.boundaryPair W (f.app c) z =
    JTJointEndpointRelativeLift.boundaryPair W (f.app b) z
  rw [JTJointEndpointRelativeLift.boundaryPair_natural, f_natural W K f α]

private theorem right_base {b c : B} (α : b ⟶ c) :
    long K α ≫ JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app c) z =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app b) z := by
  change long K α ≫ JTJointEndpointRelativeLift.reverseBoundaryPair W (f.app c) z =
    JTJointEndpointRelativeLift.reverseBoundaryPair W (f.app b) z
  rw [JTJointEndpointRelativeLift.reverseBoundaryPair_natural, f_natural W K f α]

private def leftRestrict {b c : B} (α : b ⟶ c) :
    (SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf c) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf b) :=
  precompSquare (leftSquare W U K incl f z hf c)
    (leftSquare W U K incl f z hf b) (short U α) (long K α)
    (short_long U K incl α) (identity_natural W U z α)
    (left_base W K f z α)

private def rightRestrict {b c : B} (α : b ⟶ c) :
    (SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf c) : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf b) :=
  precompSquare (rightSquare W U K incl f z hf c)
    (rightSquare W U K incl f z hf b) (short U α) (long K α)
    (short_long U K incl α) (identity_natural W U z α)
    (right_base W K f z α)

private theorem long_id (b : B) : long K (𝟙 b) = 𝟙 _ := by
  simp only [long, K.map_id, std.map_id]

private theorem long_comp {b c d : B} (α : b ⟶ c) (β : c ⟶ d) :
    long K α ≫ long K β = long K (α ≫ β) := by
  simp only [long, K.map_comp, std.map_comp]

private theorem leftRestrict_ι {b c : B} (α : b ⟶ c) :
    leftRestrict W U K incl f z hf α ≫
      (SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf b)).ι =
    (SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf c)).ι ≫
      (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌) :=
  precompSquare_ι _ _ _ _ _ _ _

private theorem rightRestrict_ι {b c : B} (α : b ⟶ c) :
    rightRestrict W U K incl f z hf α ≫
      (SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf b)).ι =
    (SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf c)).ι ≫
      (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌) :=
  precompSquare_ι _ _ _ _ _ _ _

private theorem leftRestrict_id (b : B) :
    leftRestrict W U K incl f z hf (𝟙 b) = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (leftSquare W U K incl f z hf b)).ι).mp
  rw [leftRestrict, precompSquare_ι, long_id,
    MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem rightRestrict_id (b : B) :
    rightRestrict W U K incl f z hf (𝟙 b) = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (rightSquare W U K incl f z hf b)).ι).mp
  rw [rightRestrict, precompSquare_ι, long_id,
    MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem leftRestrict_comp {b c d : B} (α : b ⟶ c) (β : c ⟶ d) :
    leftRestrict W U K incl f z hf (α ≫ β) =
      leftRestrict W U K incl f z hf β ≫
        leftRestrict W U K incl f z hf α := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (leftSquare W U K incl f z hf b)).ι).mp
  calc
    leftRestrict W U K incl f z hf (α ≫ β) ≫ _ =
        (SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf d)).ι ≫
          (MonoidalClosed.pre (long K (α ≫ β))).app (row W ⦋1⦌) := by
            exact precompSquare_ι _ _ _ _ _ _ _
    _ = (SSet.ihomToPullbackFiber (leftSquare W U K incl f z hf d)).ι ≫
        ((MonoidalClosed.pre (long K β)).app (row W ⦋1⦌) ≫
          (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌)) := by
            rw [← long_comp, MonoidalClosed.pre_map, NatTrans.comp_app]
    _ = (leftRestrict W U K incl f z hf β ≫
        leftRestrict W U K incl f z hf α) ≫ _ := by
          rw [← Category.assoc]
          rw [← leftRestrict_ι W U K incl f z hf β]
          simp only [Category.assoc, leftRestrict_ι]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌))
            (leftRestrict_ι W U K incl f z hf β).symm

private theorem rightRestrict_comp {b c d : B} (α : b ⟶ c) (β : c ⟶ d) :
    rightRestrict W U K incl f z hf (α ≫ β) =
      rightRestrict W U K incl f z hf β ≫
        rightRestrict W U K incl f z hf α := by
  apply (cancel_mono (SSet.ihomToPullbackFiber
    (rightSquare W U K incl f z hf b)).ι).mp
  calc
    rightRestrict W U K incl f z hf (α ≫ β) ≫ _ =
        (SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf d)).ι ≫
          (MonoidalClosed.pre (long K (α ≫ β))).app (row W ⦋1⦌) := by
            exact precompSquare_ι _ _ _ _ _ _ _
    _ = (SSet.ihomToPullbackFiber (rightSquare W U K incl f z hf d)).ι ≫
        ((MonoidalClosed.pre (long K β)).app (row W ⦋1⦌) ≫
          (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌)) := by
            rw [← long_comp, MonoidalClosed.pre_map, NatTrans.comp_app]
    _ = (rightRestrict W U K incl f z hf β ≫
        rightRestrict W U K incl f z hf α) ≫ _ := by
          rw [← Category.assoc]
          rw [← rightRestrict_ι W U K incl f z hf β]
          simp only [Category.assoc, rightRestrict_ι]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (MonoidalClosed.pre (long K α)).app (row W ⦋1⦌))
            (rightRestrict_ι W U K incl f z hf β).symm

/-- The complete variable-left relative edge choices on arbitrary supports. -/
def leftChoices : Bᵒᵖ ⥤ SSet.{0} where
  obj b := JTJointSubcomplexRelativeLift.liftSpace W
    (incl.app b.unop) (f.app b.unop) z (hf b.unop)
  map α := leftRestrict W U K incl f z hf α.unop
  map_id b := leftRestrict_id W U K incl f z hf b.unop
  map_comp α β := leftRestrict_comp W U K incl f z hf β.unop α.unop

/-- The complete variable-right relative edge choices on the same supports. -/
def rightChoices : Bᵒᵖ ⥤ SSet.{0} where
  obj b := JTJointSubcomplexRelativeLift.reverseLiftSpace W
    (incl.app b.unop) (f.app b.unop) z (hf b.unop)
  map α := rightRestrict W U K incl f z hf α.unop
  map_id b := rightRestrict_id W U K incl f z hf b.unop
  map_comp α β := rightRestrict_comp W U K incl f z hf β.unop α.unop

/-- Both orientations retain the same full simplicial degree. -/
def pairChoices : Bᵒᵖ ⥤ SSet.{0} :=
  Functor.diag Bᵒᵖ ⋙
    (leftChoices W U K incl f z hf).prod (rightChoices W U K incl f z hf) ⋙
    MonoidalCategory.tensor SSet.{0}

/-- Left choices restrict by literal precomposition on zero simplices. -/
theorem leftChoices_zero {b c : B} (α : b ⟶ c)
    (v : ((leftChoices W U K incl f z hf).obj (op c)).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv
        (((leftChoices W U K incl f z hf).map α.op).app (op ⦋0⦌) v).val =
      long K α ≫ SSet.ihom₀Equiv v.val := by
  change SSet.ihom₀Equiv
      (((leftRestrict W U K incl f z hf α).app (op ⦋0⦌) v).val) = _
  exact precompSquare_zero
    (leftSquare W U K incl f z hf c) (leftSquare W U K incl f z hf b)
    (short U α) (long K α) (short_long U K incl α)
    (identity_natural W U z α) (left_base W K f z α) v

/-- Right choices have the same strict zero-simplex restriction. -/
theorem rightChoices_zero {b c : B} (α : b ⟶ c)
    (v : ((rightChoices W U K incl f z hf).obj (op c)).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv
        (((rightChoices W U K incl f z hf).map α.op).app (op ⦋0⦌) v).val =
      long K α ≫ SSet.ihom₀Equiv v.val := by
  change SSet.ihom₀Equiv
      (((rightRestrict W U K incl f z hf α).app (op ⦋0⦌) v).val) = _
  exact precompSquare_zero
    (rightSquare W U K incl f z hf c) (rightSquare W U K incl f z hf b)
    (short U α) (long K α) (short_long U K incl α)
    (identity_natural W U z α) (right_base W K f z α) v

/-- Every left relative-choice space is Kan for a mono support inclusion. -/
theorem leftChoices_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b)) (b : Bᵒᵖ) :
    ((leftChoices W U K incl f z hf).obj b).KanComplex := by
  letI : Mono (incl.app b.unop) := hm b.unop
  exact JTJointSubcomplexRelativeLift.liftSpace_kan W
    (incl.app b.unop) (f.app b.unop) z (hf b.unop) hW

/-- Every right relative-choice space is Kan under the same hypothesis. -/
theorem rightChoices_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b)) (b : Bᵒᵖ) :
    ((rightChoices W U K incl f z hf).obj b).KanComplex := by
  letI : Mono (incl.app b.unop) := hm b.unop
  exact JTJointSubcomplexRelativeLift.reverseLiftSpace_kan W
    (incl.app b.unop) (f.app b.unop) z (hf b.unop) hW

private theorem point_GW_of_terminal_weak (X : SSet.{0})
    [WeakEquivalence (term X)] : GW (pointMap X) := by
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  haveI : WeakEquivalence (pointMap X) := by
    rw [← pointIsTerminal.hom_ext (term X ≫ e.hom) (pointMap X)]
    infer_instance
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- The variable-left choice space is weakly contractible over a weak subcomplex. -/
theorem leftChoices_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b))
    (hw : ∀ b : B, WeakEquivalence (incl.app b)) (b : Bᵒᵖ) :
    GW (pointMap ((leftChoices W U K incl f z hf).obj b)) := by
  letI : Mono (incl.app b.unop) := hm b.unop
  letI : WeakEquivalence (incl.app b.unop) := hw b.unop
  haveI : WeakEquivalence (term ((leftChoices W U K incl f z hf).obj b)) :=
    JTJointSubcomplexRelativeLift.liftSpace_toPoint_weak W
      (incl.app b.unop) (f.app b.unop) z (hf b.unop) hW
  exact point_GW_of_terminal_weak _

/-- The variable-right choice space has the same weakly contractible fiber. -/
theorem rightChoices_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b))
    (hw : ∀ b : B, WeakEquivalence (incl.app b)) (b : Bᵒᵖ) :
    GW (pointMap ((rightChoices W U K incl f z hf).obj b)) := by
  letI : Mono (incl.app b.unop) := hm b.unop
  letI : WeakEquivalence (incl.app b.unop) := hw b.unop
  haveI : WeakEquivalence (term ((rightChoices W U K incl f z hf).obj b)) :=
    JTJointSubcomplexRelativeLift.reverseLiftSpace_toPoint_weak W
      (incl.app b.unop) (f.app b.unop) z (hf b.unop) hW
  exact point_GW_of_terminal_weak _

/-- Each pair of complete relative choices is weakly contractible. -/
theorem pairChoices_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b))
    (hw : ∀ b : B, WeakEquivalence (incl.app b)) (b : Bᵒᵖ) :
    GW (pointMap ((pairChoices W U K incl f z hf).obj b)) := by
  exact pointMap_tensor_GW
    (leftChoices_point_GW W U K incl f z hf hW hm hw b)
    (rightChoices_point_GW W U K incl f z hf hW hm hw b)

/-- The simultaneous-choice total category remains a weak cover of the base. -/
theorem pairChoices_projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hm : ∀ b : B, Mono (incl.app b))
    (hw : ∀ b : B, WeakEquivalence (incl.app b)) :
    WeakEquivalence (nerveMap
      (CategoryOfElements.π (totalDiagram (pairChoices W U K incl f z hf)) ⋙
        CategoryTheory.Prod.fst Bᵒᵖ SimplexCategoryᵒᵖ)) :=
  SynchronizedSimplicialParameters.projection_weak
    (pairChoices W U K incl f z hf)
    (pairChoices_point_GW W U K incl f z hf hW hm hw)

end
end DaggerModels.PartII.JTSubcomplexRelativeChoiceDiagram
