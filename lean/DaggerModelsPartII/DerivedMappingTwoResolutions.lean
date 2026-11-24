import DaggerModelsPartII.CosimplicialQuillenComparison
import NativeBisimplicialDiagonalWeak

/-! Comparing source and target resolutions using the diagonal of the two-variable Hom. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- A simplicial resolution of a target is a cosimplicial resolution in the opposite category. -/
abbrev TargetResolution (Z : C) := CosimplicialResolution (C := Cᵒᵖ) (op Z)

namespace TargetResolution

local instance targetResolutionReedyModel :
    ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖᵒᵖ

/-- Any map admits a Reedy fibration comparison of target resolutions. The resolution
of the codomain may be chosen first. -/
theorem exists_comparison_fibration {X Y : C} (T : TargetResolution Y) (f : X ⟶ Y) :
    ∃ (S : TargetResolution X) (g : T.Comparison S f.op), Fibration g.mapOp := by
  let a := (Functor.const SimplexCategoryᵒᵖ).map f.op.op ≫ T.augmentationOp
  let d := factorizationData (trivialCofibrations _) (fibrations _) a
  letI := T.fibrantOp
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  let S : TargetResolution X := ⟨d.Z, d.i, d.hi, isFibrant_of_fibration d.p⟩
  exact ⟨S, ⟨d.p, d.fac⟩, inferInstanceAs (Fibration d.p)⟩

/-- Every structure map of a target resolution is a weak equivalence. -/
theorem structureMap_weak {Z : C} (T : TargetResolution Z)
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    weakEquivalences C (T.oppositeDiagram.map f).unop.unop := by
  have hm := T.augmentation_weak m
  have hn := T.augmentation_weak n
  rw [weakEquivalences_op] at hm hn
  have w := congrArg (fun k ↦ Quiver.Hom.unop (Quiver.Hom.unop k))
    (T.augmentationOp.naturality f)
  change 𝟙 Z ≫ (T.augmentationOp.app n).unop.unop =
    (T.augmentationOp.app m).unop.unop ≫ (T.oppositeDiagram.map f).unop.unop at w
  rw [Category.id_comp] at w
  exact (weakEquivalences C).of_precomp _ _ hm (w ▸ hn)

variable {A Z : C} (R : CosimplicialResolution A) (S : TargetResolution Z)

omit [HasColimitsOfSize.{0, 0} C] in
private theorem unop_fibrant (X : Cᵒᵖᵒᵖ) [IsFibrant X] : IsFibrant X.unop.unop := by
  let t := terminal.from X
  have h := mem_fibrations t
  rw [fibrations_op, cofibrations_op] at h
  exact (isFibrant_iff_of_isTerminal t.unop.unop
    (terminalUnopOfInitial (initialUnopOfTerminal terminalIsTerminal))).mpr
    ((fibration_iff _).mpr h)

private def doubleMapping : BiSSet.{v} :=
  S.oppositeDiagram ⋙ unopUnop C ⋙ R.mappingSSet

private def reverseMapping : BiSSet.{v} :=
  R.oppositeDiagram ⋙ S.mappingSSet

private def leftAugmentation :
    (Functor.const SimplexCategoryᵒᵖ).obj (R.mappingSSet.obj Z) ⟶ doubleMapping R S :=
  (Functor.constComp SimplexCategoryᵒᵖ (op (op Z)) (unopUnop C ⋙ R.mappingSSet)).inv ≫
    Functor.whiskerRight S.augmentationOp (unopUnop C ⋙ R.mappingSSet)

private def rightAugmentation :
    (Functor.const SimplexCategoryᵒᵖ).obj (S.mappingSSet.obj (op A)) ⟶ reverseMapping R S :=
  (Functor.constComp SimplexCategoryᵒᵖ (op A) S.mappingSSet).inv ≫
    Functor.whiskerRight R.augmentationOp S.mappingSSet

private def diagonalConstIso (K : SSet.{v}) :
    diagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj K) ≅ K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j f
    change (K.map f ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ K.map f
    simp)

private def swapIso : (doubleMapping R S).flip ≅ reverseMapping R S :=
  NatIso.ofComponents (fun n ↦ NatIso.ofComponents (fun m ↦ Equiv.toIso
    { toFun := fun x ↦ Quiver.Hom.op x
      invFun := fun x ↦ Quiver.Hom.unop x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by
    intro i j f
    rfl)) (by
    intro i j f
    apply NatTrans.ext
    funext n
    rfl)

/-- The map from the source resolution into the diagonal comparison complex. -/
def fromSourceResolution :
    R.mappingSSet.obj Z ⟶ diagonalFunctor.obj (doubleMapping R S) :=
  (diagonalConstIso _).inv ≫ diagonalFunctor.map (leftAugmentation R S)

/-- The map from the target resolution into the same diagonal comparison complex. -/
def fromTargetResolution :
    S.mappingSSet.obj (op A) ⟶ diagonalFunctor.obj (doubleMapping R S) :=
  (diagonalConstIso _).inv ≫ diagonalFunctor.map (rightAugmentation R S) ≫
    diagonalFunctor.map (swapIso R S).inv ≫ (diagonalFlipIso (doubleMapping R S)).hom

/-- The comparison from a source resolution is a weak equivalence for a fibrant target. -/
theorem fromSourceResolution_weak [IsFibrant Z] :
    weakEquivalences SSet.{v} (fromSourceResolution R S) := by
  apply ((weakEquivalences SSet.{v}).cancel_left_of_respectsIso (diagonalConstIso _).inv _).mpr
  apply (weakEquivalence_iff _).mp
  apply DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
  intro n
  apply (weakEquivalence_iff _).mpr
  change weakEquivalences SSet.{v}
    (𝟙 _ ≫ R.mappingSSet.map (S.augmentationOp.app n).unop.unop)
  rw [Category.id_comp]
  letI := S.fibrantOp
  letI : IsFibrant (S.oppositeDiagram.obj n) := reedyFibrant_obj _ n
  letI := unop_fibrant (S.oppositeDiagram.obj n)
  have h := S.augmentation_weak n
  rw [weakEquivalences_op] at h
  letI : IsFibrant
      (((Functor.const SimplexCategoryᵒᵖ).obj (op (op Z))).obj n).unop.unop := ‹IsFibrant Z›
  exact R.mappingSSet_map_weak _ h

/-- The comparison from a target resolution is a weak equivalence for a cofibrant source. -/
theorem fromTargetResolution_weak [IsCofibrant A] :
    weakEquivalences SSet.{v} (fromTargetResolution R S) := by
  have h : weakEquivalences SSet.{v} (diagonalFunctor.map (rightAugmentation R S)) := by
    apply (weakEquivalence_iff _).mp
    apply DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
    intro n
    apply (weakEquivalence_iff _).mpr
    change weakEquivalences SSet.{v} (𝟙 _ ≫ S.mappingSSet.map (R.augmentationOp.app n))
    rw [Category.id_comp]
    letI := R.fibrantOp
    letI : IsFibrant (((Functor.const SimplexCategoryᵒᵖ).obj (op A)).obj n) := isFibrant_op_of_isCofibrant A
    letI : IsFibrant (R.oppositeDiagram.obj n) := reedyFibrant_obj _ n
    apply S.mappingSSet_map_weak
    rw [weakEquivalences_op]
    exact R.augmentation_weak n
  unfold fromTargetResolution
  rwa [(weakEquivalences SSet.{v}).cancel_left_of_respectsIso,
    ← Category.assoc, (weakEquivalences SSet.{v}).cancel_right_of_respectsIso,
    (weakEquivalences SSet.{v}).cancel_right_of_respectsIso]

variable {Z' : C} (T : TargetResolution Z') (p : Z ⟶ Z')
  (g : T.Comparison S p.op)

private def doubleComparison : doubleMapping R S ⟶ doubleMapping R T :=
  Functor.whiskerRight g.mapOp (unopUnop C ⋙ R.mappingSSet)

private theorem fromSourceResolution_natural :
    R.mappingSSet.map p ≫ fromSourceResolution R T =
      fromSourceResolution R S ≫ diagonalFunctor.map (doubleComparison R S T p g) := by
  ext n x : 2
  change op Z ⟶ R.oppositeDiagram.obj n at x
  apply Quiver.Hom.unop_inj
  have h := congrArg (fun f ↦ Quiver.Hom.unop (Quiver.Hom.unop f)) (congr_app g.comm n)
  change (S.augmentationOp.app n).unop.unop ≫ (g.mapOp.app n).unop.unop =
    p ≫ (T.augmentationOp.app n).unop.unop at h
  change (x.unop ≫ p) ≫ (T.augmentationOp.app n).unop.unop =
    (x.unop ≫ (S.augmentationOp.app n).unop.unop) ≫ (g.mapOp.app n).unop.unop
  rw [Category.assoc, Category.assoc, h]

private theorem fromTargetResolution_natural :
    g.precomp (op A) ≫ fromTargetResolution R T =
      fromTargetResolution R S ≫ diagonalFunctor.map (doubleComparison R S T p g) := by
  ext n x : 2
  change op (op A) ⟶ S.oppositeDiagram.obj n at x
  apply Quiver.Hom.unop_inj
  change (R.augmentationOp.app n).unop ≫ (x.unop.unop ≫ (g.mapOp.app n).unop.unop) =
    ((R.augmentationOp.app n).unop ≫ x.unop.unop) ≫ (g.mapOp.app n).unop.unop
  exact (Category.assoc _ _ _).symm

/-- Testing a map with a source resolution or a comparison of target resolutions is equivalent. -/
theorem mappingSSet_map_weak_iff [IsCofibrant A] [IsFibrant Z] [IsFibrant Z'] :
    weakEquivalences SSet.{v} (R.mappingSSet.map p) ↔
      weakEquivalences SSet.{v} (g.precomp (op A)) := by
  let W := weakEquivalences SSet.{v}
  have hs := fromSourceResolution_natural R S T p g
  have ht := fromTargetResolution_natural R S T p g
  have h₀ : W (fromSourceResolution R S) := fromSourceResolution_weak R S
  have h₁ : W (fromSourceResolution R T) := fromSourceResolution_weak R T
  have h₂ : W (fromTargetResolution R S) := fromTargetResolution_weak R S
  have h₃ : W (fromTargetResolution R T) := fromTargetResolution_weak R T
  constructor
  · intro hp
    have hdiag := W.of_precomp _ _ h₀ (hs ▸ W.comp_mem _ _ hp h₁)
    exact W.of_postcomp _ _ h₃ (ht.symm ▸ W.comp_mem _ _ h₂ hdiag)
  · intro hp
    have hdiag := W.of_precomp _ _ h₂ (ht ▸ W.comp_mem _ _ hp h₃)
    exact W.of_postcomp _ _ h₁ (hs.symm ▸ W.comp_mem _ _ h₀ hdiag)

end TargetResolution

end

end DaggerModels.PartII
