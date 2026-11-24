import ActualOriginalNecklaceInclusionWeak
import NativeRealEdgewiseStandardSimplexWeak

/-! Kan weak contractibility of the actual native necklace, with its original bead subcomplexes. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerNativeStandardSpineInner DaggerNativeStandardSpineGeometry
open DaggerNativeInnerHornFactorization DaggerActualOriginalNecklaceSpineGeometry
open DaggerNativeFiniteSubcomplexWeakGluing (intersection_union)
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNativeTargetKanWeak

noncomputable section

private theorem trivialCongr {X : SSet.{0}} {A A' B B' : X.Subcomplex}
    (ea : A = A') (eb : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    trivialCofibrations SSet.{0} (SSet.Subcomplex.homOfLE h) ↔
      trivialCofibrations SSet.{0} (SSet.Subcomplex.homOfLE h') := by
  subst A'
  subst B'
  rfl

private theorem finiteAttachments {X : SSet.{0}} {I : Type} (A : X.Subcomplex)
    (F : I → X.Subcomplex) (s : Finset I) (overlap : ∀ i j, i ≠ j → F i ⊓ F j ≤ A)
    (attach : ∀ i, trivialCofibrations SSet.{0}
      (SSet.Subcomplex.homOfLE (inf_le_left : F i ⊓ A ≤ F i))) :
    trivialCofibrations SSet.{0} (SSet.Subcomplex.homOfLE
      (le_sup_left : A ≤ A ⊔ s.sup F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply (trivialCongr rfl (by simp) _ (le_refl A)).mpr
    exact mem_trivialCofibrations (𝟙 (A : SSet.{0}))
  | @insert i s hi ih =>
    let B := A ⊔ s.sup F
    have he : F i ⊓ B = F i ⊓ A := intersection_union A F s i hi overlap
    have hj := (trivialCongr he rfl (inf_le_left : F i ⊓ B ≤ F i) _).mpr (attach i)
    have sq : SSet.Subcomplex.BicartSq (F i ⊓ B) (F i) B (F i ⊔ B) := ⟨rfl, rfl⟩
    have hw : trivialCofibrations SSet.{0}
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ F i ⊔ B)) :=
      MorphismProperty.of_isPushout sq.isPushout.flip hj
    have hc := (trivialCofibrations SSet.{0}).comp_mem _ _ ih hw
    have heq : A ⊔ (insert i s).sup F = F i ⊔ B := by
      rw [Finset.sup_insert]
      dsimp [B]
      ac_rfl
    apply (trivialCongr rfl heq _ (le_trans le_sup_left le_sup_right)).mpr
    exact hc

/-- Attach the original individual beads over their actual spines by Kan trivial cofibrations. -/
theorem spine_to_complex_trivial (T : NecklaceCode) : trivialCofibrations SSet.{0}
    (SSet.Subcomplex.homOfLE (spine_le_complex.{0} T)) := by
  classical
  letI : Fintype T.Bead := Fintype.ofFinite T.Bead
  have h := finiteAttachments (spine.{0} T.len) (NecklaceCode.Bead.face (T := T))
    Finset.univ (bead_overlap_le_spine T) (fun b ↦
      innerAnodyne_le_native_trivial _
        (DaggerActualOriginalNecklaceSpineAttachment.intersection_innerAnodyne b))
  exact (trivialCongr rfl (DaggerActualOriginalNecklaceInclusionWeak.finite_bead_union_eq T)
    _ _).mp h

/-- The exact original inclusion of the native target into its standard simplex is Kan weak. -/
theorem inclusion_weak (T : NecklaceCode) : WeakEquivalence (NecklaceCode.inclusion.{0} T) := by
  let j := SSet.Subcomplex.homOfLE (spine_le_complex.{0} T)
  letI : WeakEquivalence j :=
    ((mem_trivialCofibrations_iff j).mp (spine_to_complex_trivial T)).2
  letI : WeakEquivalence ((spine.{0} T.len).ι) :=
    ((mem_trivialCofibrations_iff _).mp (innerAnodyne_le_native_trivial _
      (inclusion_innerAnodyne.{0} T.len))).2
  haveI : WeakEquivalence (NecklaceCode.complex.{0} T).ι :=
    weakEquivalence_of_precomp_of_fac (SSet.Subcomplex.homOfLE_ι (spine_le_complex.{0} T))
  change WeakEquivalence (T.complexIso.hom ≫ (NecklaceCode.complex.{0} T).ι)
  infer_instance

/-- All actual target simplices of a necklace can be used in a weakly contractible resolution. -/
theorem point_GW (T : NecklaceCode) : GW (pointMap (NecklaceCode.toSSet.{0} T)) := by
  letI := inclusion_weak T
  let e := SSet.stdSimplex.isoNerve.{0} T.len
  haveI : WeakEquivalence (pointMap (nerve (ULift (Fin (T.len + 1))))) :=
    (weakEquivalence_iff_GW _).mpr (DaggerNativeOrderTopNerveWeakContractibility.point_GW _)
  haveI : WeakEquivalence (pointMap (Δ[T.len] : SSet.{0})) := by
    rw [← pointIsTerminal.hom_ext (e.hom ≫ pointMap _) (pointMap _)]
    infer_instance
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (T.inclusion ≫ pointMap _) (pointMap _)]
  infer_instance

end
end DaggerModels.PartII.JTNativeTargetKanWeak
