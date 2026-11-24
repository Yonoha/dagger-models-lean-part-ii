import DaggerModelsPartII.JTRightAdjointOrderedFibersCore
import DaggerModelsPartII.JTOrderedFrameMate

/-!
# Native rows of the actual dagger JT right adjoint

The right adjoint is the restricted Yoneda functor on the literal dagger
frames, curried through the fixed source equivalence. This records its row
values and both frame-operator actions. The chosen adjunction equivalence
is calibrated against those literal values before passing to ordered fibers.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTRightAdjointNativeRow

open DaggerJTAdjunction JTRightAdjointOrderedFibersCore

noncomputable section

/-- Fix the reversal index in the actual two-index dagger frame. -/
def verticalFrame (m : ReverseSimplex) : SimplexCategory ⥤ DaggerSSet.{0} :=
  (Functor.curry.obj frame).obj m

@[simp] theorem verticalFrame_obj (m : ReverseSimplex) (k : SimplexCategory) :
    (verticalFrame m).obj k = frame.obj (m, k) := rfl

/-- The native right-adjoint row is the universe-lifted Hom from the
literal frame, including its vertical simplicial operators. -/
def nativeRowIso (m : ReverseSimplex) :
    daggerNerve ⋙
        (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) ≅
      Presheaf.restrictedULiftYoneda.{0} (verticalFrame m) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun _ ↦ Iso.refl _)
      (by intro k l β; ext z; rfl))
    (by intro X Y g; ext k z; rfl)

@[simp] theorem daggerNerve_row_obj (X : DaggerSSet.{0})
    (m : ReverseSimplex) (k : SimplexCategory) :
    ((daggerNerve.obj X).obj (op m)).obj (op k) =
      ULift (frame.obj (m, k) ⟶ X) := rfl

theorem daggerNerve_vertical_map (X : DaggerSSet.{0})
    (m : ReverseSimplex) {k l : SimplexCategory} (β : k ⟶ l)
    (f : ((daggerNerve.obj X).obj (op m)).obj (op l)) :
    ((daggerNerve.obj X).obj (op m)).map β.op f =
      ULift.up (frame.map (show (m, k) ⟶ (m, l) from (𝟙 m, β)) ≫ f.down) := by
  rfl

theorem daggerNerve_horizontal_map (X : DaggerSSet.{0})
    {m n : ReverseSimplex} (α : m ⟶ n) (k : SimplexCategory)
    (f : ((daggerNerve.obj X).obj (op n)).obj (op k)) :
    ((daggerNerve.obj X).map α.op).app (op k) f =
      ULift.up (frame.map (show (m, k) ⟶ (n, k) from (α, 𝟙 k)) ≫ f.down) := by
  rfl

theorem daggerNerve_target_map {X Y : DaggerSSet.{0}} (g : X ⟶ Y)
    (m : ReverseSimplex) (k : SimplexCategory)
    (f : ((daggerNerve.obj X).obj (op m)).obj (op k)) :
    ((daggerNerve.map g).app (op m)).app (op k) f =
      ULift.up (f.down ≫ g) := by
  rfl

private theorem source_homEquiv_cancel
    (P Y : DaggerIndexᵒᵖ ⥤ Type)
    (u : sourceEquivalence.functor.obj (sourceEquivalence.inverse.obj P) ⟶ Y) :
    sourceEquivalence.symm.toAdjunction.homEquiv P (sourceEquivalence.inverse.obj Y)
        (sourceEquivalence.toAdjunction.homEquiv
          (sourceEquivalence.inverse.obj P) Y u) =
      sourceEquivalence.counitInv.app P ≫ u ≫ sourceEquivalence.counitInv.app Y := by
  change sourceEquivalence.counitInv.app P ≫
      sourceEquivalence.functor.map
        (sourceEquivalence.unit.app (sourceEquivalence.inverse.obj P) ≫
          sourceEquivalence.inverse.map u) = _
  rw [sourceEquivalence.functor.map_comp,
    ← sourceEquivalence.counitInv_app_functor,
    sourceEquivalence.counitInv_naturality]

/-- The chosen composite adjunction sends a represented frame map to its
native Yoneda value. This is the calibration needed for the original mate. -/
theorem daggerGeneratorEquiv_eq_native (X : DaggerSSet.{0})
    (m : ReverseSimplex) (k : SimplexCategory)
    (f : frame.obj (m, k) ⟶ X) :
    daggerGeneratorEquiv X m k f = ULift.up f := by
  letI : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
  letI : PreservesColimits presheafRealization :=
    presheafRealization_preservesColimits
  letI : presheafRealization.IsLeftKanExtension (𝟙 frame) :=
    Presheaf.isLeftKanExtension_of_preservesColimits
      presheafRealization (Iso.refl _)
  let p : DaggerIndex := (m, k)
  let P := uliftYoneda.{0}.obj p
  let W := JTCoendMateFormula.representedInput p
  let Y := presheafNerve.obj X
  let g := realizationIso.hom.app W ≫ f
  have ht : presheafRealization.map (sourceEquivalence.counitIso.inv.app P) ≫
      realizationIso.hom.app W = 𝟙 (frame.obj p) := by
    change DaggerJTRealization.daggerRealization.map
        (sourceEquivalence.inverse.map (sourceEquivalence.counitIso.inv.app P)) ≫
      DaggerJTRealization.daggerRealization.map
        (sourceEquivalence.unitIso.inv.app W) = _
    change DaggerJTRealization.daggerRealization.map
        (sourceEquivalence.inverse.map (sourceEquivalence.counitInv.app P)) ≫
      DaggerJTRealization.daggerRealization.map
        (sourceEquivalence.unitInv.app (sourceEquivalence.inverse.obj P)) = _
    rw [← DaggerJTRealization.daggerRealization.map_comp]
    exact (congrArg DaggerJTRealization.daggerRealization.map
      (sourceEquivalence.inverse_counitInv_comp P)).trans
        (DaggerJTRealization.daggerRealization.map_id W)
  have hu : sourceEquivalence.counitInv.app P ≫
      presheafAdjunction.homEquiv (sourceEquivalence.functor.obj W) X g =
      presheafAdjunction.homEquiv P X f := by
    trans presheafAdjunction.homEquiv P X
      (presheafRealization.map (sourceEquivalence.counitInv.app P) ≫ g)
    · exact (presheafAdjunction.homEquiv_naturality_left
        (sourceEquivalence.counitInv.app P) g).symm
    apply congrArg (presheafAdjunction.homEquiv P X)
    change presheafRealization.map (sourceEquivalence.counitInv.app P) ≫
      (realizationIso.hom.app W ≫ f) = f
    rw [← Category.assoc, ht]
    exact Category.id_comp f
  unfold daggerGeneratorEquiv JTCoendMateFormula.representedEvaluation
  unfold adjunction
  simp only [Adjunction.ofNatIsoLeft, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.comp_homEquiv, Equiv.trans_apply]
  dsimp only [Adjunction.equivHomsetLeftOfNatIso, Iso.symm_inv]
  change uliftYonedaEquiv
    (sourceEquivalence.symm.toAdjunction.homEquiv P (sourceEquivalence.inverse.obj Y)
      (sourceEquivalence.toAdjunction.homEquiv W Y
        (presheafAdjunction.homEquiv (sourceEquivalence.functor.obj W) X g))) = _
  refine (congrArg uliftYonedaEquiv
    (source_homEquiv_cancel P Y
      (presheafAdjunction.homEquiv (sourceEquivalence.functor.obj W) X g))).trans ?_
  rw [← Category.assoc, hu]
  rw [uliftYonedaEquiv_comp]
  have hc (z : Y.obj (op p)) :
      (sourceEquivalence.counitInv.app Y).app (op p) z = z := by
    change Y.map (𝟙 (op p)) z = z
    rw [Y.map_id]
    rfl
  rw [hc]
  change ((presheafAdjunction.homEquiv P X f).app (op p)
    (ULift.up (𝟙 p))) = ULift.up f
  change (((Presheaf.uliftYonedaAdjunction presheafRealization (𝟙 frame)).homEquiv
    P X f).app (op p) (ULift.up (𝟙 p))) = ULift.up f
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  have hy : uliftYonedaEquiv.symm (ULift.up (𝟙 p)) = 𝟙 P := by
    apply uliftYonedaEquiv.injective
    exact (uliftYonedaEquiv (F := P)).apply_symm_apply (ULift.up (𝟙 p))
  rw [hy, presheafRealization.map_id]
  change ULift.up (𝟙 (frame.obj p) ≫ f) = ULift.up f
  exact congrArg (fun h : frame.obj p ⟶ X ↦ ULift.up h) (Category.id_comp f)

theorem daggerGeneratorEquiv_vertical (X : DaggerSSet.{0})
    (m : ReverseSimplex) {k l : SimplexCategory} (β : k ⟶ l)
    (f : frame.obj (m, l) ⟶ X) :
    daggerGeneratorEquiv X m k
        (frame.map (show (m, k) ⟶ (m, l) from (𝟙 m, β)) ≫ f) =
      ((daggerNerve.obj X).obj (op m)).map β.op
        (daggerGeneratorEquiv X m l f) := by
  rw [daggerGeneratorEquiv_eq_native, daggerGeneratorEquiv_eq_native,
    daggerNerve_vertical_map]

theorem daggerGeneratorEquiv_horizontal (X : DaggerSSet.{0})
    {m n : ReverseSimplex} (α : m ⟶ n) (k : SimplexCategory)
    (f : frame.obj (n, k) ⟶ X) :
    daggerGeneratorEquiv X m k
        (frame.map (show (m, k) ⟶ (n, k) from (α, 𝟙 k)) ≫ f) =
      ((daggerNerve.obj X).map α.op).app (op k)
        (daggerGeneratorEquiv X n k f) := by
  rw [daggerGeneratorEquiv_eq_native, daggerGeneratorEquiv_eq_native,
    daggerNerve_horizontal_map]

/-- The two ordered outer vertices are the literal horizontal operators
of the same chosen right-adjoint identification. -/
theorem daggerGeneratorEquiv_vertex (X : DaggerSSet.{0})
    (i : Fin 2) (k : SimplexCategory)
    (f : frame.obj (JTOrderedFrameMate.oneIndex, k) ⟶ X) :
    daggerGeneratorEquiv X JTZeroObjects.zeroIndex k
        (frame.map
          (show (JTZeroObjects.zeroIndex, k) ⟶
            (JTOrderedFrameMate.oneIndex, k) from
              (JTOrderedFrameMate.vertex i, 𝟙 k)) ≫ f) =
      ((daggerNerve.obj X).map (JTOrderedFrameMate.vertex i).op).app (op k)
        (daggerGeneratorEquiv X JTOrderedFrameMate.oneIndex k f) :=
  daggerGeneratorEquiv_horizontal X (JTOrderedFrameMate.vertex i) k f

end

end DaggerModels.PartII.JTRightAdjointNativeRow
