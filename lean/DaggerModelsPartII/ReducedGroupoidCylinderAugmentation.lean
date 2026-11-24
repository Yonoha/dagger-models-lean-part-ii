import DaggerModelsPartII.ReducedCylinder
import DaggerModelsPartII.JTCEJoyalAugmentation

/-!
# The actual general reduced groupoid-cylinder augmentation

The existing reduced cylinder augments naturally to its original target.
For a monomorphic boundary its augmentation is weak in the ORIGINAL ordinary
Joyal class. A split-epimorphic boundary instead gives an actual isomorphism.
Pointwise parameter sections are used only in proofs, never claimed natural.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.ReducedGroupoidCylinderAugmentation

open GroupoidSimplex DaggerNativeJoyalMappingTest

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Forget only the groupoid parameter in the SAME reduced-cylinder pushout. -/
def augmentation {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    (ReducedCylinder.value j).obj (J.obj k) ⟶ B :=
  (ReducedCylinder.value_isPushout j).desc
    (CartesianMonoidalCategory.fst B (J.obj k)) j
    (CartesianMonoidalCategory.tensorHom_fst j (𝟙 (J.obj k)))

theorem augmentation_cylinder {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    (ReducedCylinder.cylinder j).app (J.obj k) ≫ augmentation j k =
      CartesianMonoidalCategory.fst B (J.obj k) :=
  (ReducedCylinder.value_isPushout j).inl_desc _ _ _

theorem augmentation_boundary {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    (ReducedCylinder.boundary j).app (J.obj k) ≫ augmentation j k = j :=
  (ReducedCylinder.value_isPushout j).inr_desc _ _ _

/-- The actual augmentation is natural for every original parameter operator. -/
theorem augmentation_natural {A B : SSet.{0}} (j : A ⟶ B)
    {k l : SimplexCategory} (g : k ⟶ l) :
    (ReducedCylinder.value j).map (J.map g) ≫ augmentation j l = augmentation j k := by
  apply (ReducedCylinder.value_isPushout j (K := J.obj k)).hom_ext
  · rw [← Category.assoc, ← (ReducedCylinder.cylinder j).naturality (J.map g),
      Category.assoc, augmentation_cylinder, augmentation_cylinder]
    exact CartesianMonoidalCategory.tensorHom_fst (𝟙 B) (J.map g)
  · rw [← Category.assoc, ← (ReducedCylinder.boundary j).naturality (J.map g)]
    change (𝟙 A ≫ (ReducedCylinder.boundary j).app (J.obj l)) ≫ _ = _
    rw [Category.id_comp, augmentation_boundary, augmentation_boundary]

private def s (k : SimplexCategory) : (Δ[0] : SSet.{0}) ⟶ J.obj k :=
  JTParameterContraction.parameterVertex k 0

private theorem iso_weak {X Y : SSet.{0}} (f : X ⟶ Y) [IsIso f] :
    weakCategoricalEquivalences f := by
  let e : Arrow.mk (𝟙 X) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl X) (asIso f) (by simp)
  exact weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm)
    (weakCategoricalEquivalences.id_mem X)

private theorem s_weak (k : SimplexCategory) : weakCategoricalEquivalences (s k) := by
  have haug : weakCategoricalEquivalences (terminal.from (J.obj k)) :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial
      (terminal.from (J.obj k)) (GroupoidSimplex.augmentation_trivialFibration k)).2
  have hcomp : weakCategoricalEquivalences (s k ≫ terminal.from (J.obj k)) := by
    have he : s k ≫ terminal.from (J.obj k) = terminal.from (Δ[0] : SSet.{0}) :=
      terminalIsTerminal.hom_ext _ _
    rw [he]
    have : IsIso (terminal.from (Δ[0] : SSet.{0})) := by
      let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
        (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))
      have he' : terminal.from (Δ[0] : SSet.{0}) = e.hom :=
        terminalIsTerminal.hom_ext _ _
      rw [he']
      infer_instance
    exact iso_weak _
  exact weakCategoricalEquivalences.of_postcomp _ _ haug hcomp

private def input (X : SSet.{0}) (k : SimplexCategory) : X ⟶ X ⊗ J.obj k :=
  CartesianMonoidalCategory.lift (𝟙 X)
    (SSet.stdSimplex.isTerminalObj₀.from X ≫ s k)

private theorem input_fst (X : SSet.{0}) (k : SimplexCategory) :
    input X k ≫ CartesianMonoidalCategory.fst X (J.obj k) = 𝟙 X :=
  CartesianMonoidalCategory.lift_fst _ _

private theorem input_natural {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    j ≫ input B k = input A k ≫ (j ⊗ₘ 𝟙 (J.obj k)) := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · exact congrArg ((s k).app q) (Subsingleton.elim _ _)

private theorem boundary_section {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) :
    j ≫ input B k ≫ (ReducedCylinder.cylinder j).app (J.obj k) =
      (ReducedCylinder.boundary j).app (J.obj k) := by
  rw [← Category.assoc, input_natural, Category.assoc]
  have h := (ReducedCylinder.value_isPushout j (K := J.obj k)).w
  change (j ⊗ₘ 𝟙 (J.obj k)) ≫ (ReducedCylinder.cylinder j).app (J.obj k) =
    CartesianMonoidalCategory.fst A (J.obj k) ≫
      (ReducedCylinder.boundary j).app (J.obj k) at h
  rw [h, ← Category.assoc, input_fst, Category.id_comp]

/-- A POINTWISE section at one actual parameter vertex; no naturality in k is claimed. -/
def vertexSection {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    B ⟶ (ReducedCylinder.value j).obj (J.obj k) :=
  CartesianMonoidalCategory.lift (𝟙 B)
      (SSet.stdSimplex.isTerminalObj₀.from B ≫ JTParameterContraction.parameterVertex k 0) ≫
    (ReducedCylinder.cylinder j).app (J.obj k)

theorem vertexSection_augmentation {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) : vertexSection j k ≫ augmentation j k = 𝟙 B := by
  rw [vertexSection, Category.assoc, augmentation_cylinder]
  exact CartesianMonoidalCategory.lift_fst _ _

theorem boundary_vertexSection {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    j ≫ vertexSection j k = (ReducedCylinder.boundary j).app (J.obj k) :=
  boundary_section j k

private def t {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    SSet.PushoutTensor j (s k) := Functor.PushoutObjObj.ofHasPushout _ _ _

private theorem t_weak {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    weakCategoricalEquivalences (t j k).ι := by
  have : Mono (s k) := SSet.stdSimplex.isTerminalObj₀.mono_from (s k)
  have hflip : weakCategoricalEquivalences (t j k).flip.ι :=
    DaggerNativeOriginalWeakPushoutTensor.pushout_tensor_weak (s k) (s_weak k) j
      (t j k).flip
  exact weakCategoricalEquivalences.of_retract
    (Retract.ofIso (t j k).flipArrowIso.symm) hflip

private theorem t_mono {A B : SSet.{0}} (j : A ⟶ B) [Mono j]
    (k : SimplexCategory) : Mono (t j k).ι := by
  have : Mono (s k) := SSet.stdSimplex.isTerminalObj₀.mono_from (s k)
  exact DaggerNativeSimplicialPushoutTensorMono.mono_ι j (s k) (t j k)

private def c {A B : SSet.{0}} (j : A ⟶ B) : A ⟶ B ⊗ (Δ[0] : SSet.{0}) :=
  CartesianMonoidalCategory.lift j (SSet.stdSimplex.isTerminalObj₀.from A)

private def r (B : SSet.{0}) (k : SimplexCategory) :
    B ⊗ (Δ[0] : SSet.{0}) ⟶ B ⊗ J.obj k := B ◁ s k

private theorem p_condition {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    (A ◁ s k) ≫ (CartesianMonoidalCategory.fst A (J.obj k) ≫ c j) =
      (j ▷ (Δ[0] : SSet.{0})) ≫ 𝟙 (B ⊗ (Δ[0] : SSet.{0})) := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

private def p {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    (t j k).pt ⟶ B ⊗ (Δ[0] : SSet.{0}) :=
  (t j k).isPushout.flip.desc (CartesianMonoidalCategory.fst A (J.obj k) ≫ c j)
    (𝟙 _) (p_condition j k)

private theorem c_r {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    c j ≫ r B k = j ≫ input B k := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · exact congrArg ((s k).app q) (Subsingleton.elim _ _)

private theorem secondPushout {A B : SSet.{0}} (j : A ⟶ B) (k : SimplexCategory) :
    IsPushout (t j k).ι (p j k) ((ReducedCylinder.cylinder j).app (J.obj k))
      (r B k ≫ (ReducedCylinder.cylinder j).app (J.obj k)) := by
  apply PushoutSectionTensor.isPushout (ReducedCylinder.value_isPushout j)
    (t j k).isPushout.flip (t j k).ι (p j k) (r B k) (c j)
  · exact (t j k).inr_ι
  · exact (t j k).inl_ι
  · exact (t j k).isPushout.flip.inl_desc _ _ _
  · exact (t j k).isPushout.flip.inr_desc _ _ _
  · rw [← Category.assoc, c_r, Category.assoc]
    exact boundary_section j k

private theorem fst_isIso (B : SSet.{0}) :
    IsIso (CartesianMonoidalCategory.fst B (Δ[0] : SSet.{0})) :=
  (BinaryFan.isLimit_iff_isIso_fst SSet.stdSimplex.isTerminalObj₀
    (BinaryFan.mk (CartesianMonoidalCategory.fst B (Δ[0] : SSet.{0}))
      (CartesianMonoidalCategory.snd B (Δ[0] : SSet.{0})))).1
    ⟨CartesianMonoidalCategory.tensorProductIsBinaryProduct B (Δ[0] : SSet.{0})⟩

/-- For a monomorphic boundary, this SAME augmentation is original Joyal weak. -/
theorem augmentation_weak {A B : SSet.{0}} (j : A ⟶ B) [Mono j]
    (k : SimplexCategory) : weakCategoricalEquivalences (augmentation j k) := by
  have : Mono (t j k).ι := t_mono j k
  have hsection : weakCategoricalEquivalences
      (r B k ≫ (ReducedCylinder.cylinder j).app (J.obj k)) :=
    DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout (secondPushout j k) (t_weak j k)
  have hcomp : weakCategoricalEquivalences
      ((r B k ≫ (ReducedCylinder.cylinder j).app (J.obj k)) ≫ augmentation j k) := by
    rw [Category.assoc, augmentation_cylinder]
    change weakCategoricalEquivalences
      ((𝟙 B ⊗ₘ s k) ≫ CartesianMonoidalCategory.fst B (J.obj k))
    rw [CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
    have : IsIso (CartesianMonoidalCategory.fst B (Δ[0] : SSet.{0})) := fst_isIso B
    exact iso_weak _
  exact weakCategoricalEquivalences.of_precomp _ _ hsection hcomp

/-- A split-epimorphic boundary collapses the ENTIRE parameter exactly.
This covers a zero-length necklace without a false boundary-mono premise. -/
theorem augmentation_isIso_of_split_epi {A B : SSet.{0}} (j : A ⟶ B)
    (k : SimplexCategory) (u : B ⟶ A) (hu : u ≫ j = 𝟙 B) :
    IsIso (augmentation j k) := by
  let v := input B k ≫ (ReducedCylinder.cylinder j).app (J.obj k)
  have hv : v ≫ augmentation j k = 𝟙 B := by
    dsimp only [v]
    rw [Category.assoc, augmentation_cylinder, input_fst]
  have hep : IsSplitEpi (j ⊗ₘ 𝟙 (J.obj k)) := IsSplitEpi.mk'
    { section_ := u ⊗ₘ 𝟙 (J.obj k)
      id := by
        rw [tensorHom_comp_tensorHom, hu, Category.id_comp, id_tensorHom_id] }
  have hvi : augmentation j k ≫ v = 𝟙 _ := by
    apply (ReducedCylinder.value_isPushout j (K := J.obj k)).hom_ext
    · rw [← Category.assoc, augmentation_cylinder, Category.comp_id]
      apply (cancel_epi (j ⊗ₘ 𝟙 (J.obj k))).1
      rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
      have hb : j ≫ v = (ReducedCylinder.boundary j).app (J.obj k) :=
        boundary_section j k
      rw [hb]
      exact (ReducedCylinder.value_isPushout j (K := J.obj k)).w.symm
    · rw [← Category.assoc, augmentation_boundary, Category.comp_id]
      exact boundary_section j k
  exact ⟨v, hvi, hv⟩

end

end DaggerModels.PartII.ReducedGroupoidCylinderAugmentation
