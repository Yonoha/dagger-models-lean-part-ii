import DaggerModelsPartII.ClassifyingReduction
import DaggerModelsPartII.InjectiveLocalEquivalences
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import ActualOriginalNecklaceInclusionWeak
import ChosenNecklaceWedgePushout
import ChosenNecklaceSingleBead

/-!
# Locality of the literal two-bead necklace inclusion

The proof first handles every native necklace by attaching its bead faces to
the full standard spine. Each attachment is a pushout of the corresponding
Segal spine inclusion after the actual discrete-free dagger functor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerNativeStandardSpineInner
open DaggerNativeFiniteSubcomplexWeakGluing
open DaggerActualOriginalNecklaceSpineGeometry
open DaggerActualOriginalNecklaceSpineAttachment
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TwoBeadSegalLocality

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private local instance : ModelCategory Source := injectiveSegalModel

private def mapArrowIso {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B A' B' : C} {i : A ⟶ B} {j : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk j) :
    Arrow.mk (G.map i) ≅ Arrow.mk (G.map j) := by
  refine Arrow.isoMk (G.mapIso (Arrow.leftFunc.mapIso e))
    (G.mapIso (Arrow.rightFunc.mapIso e)) ?_
  simpa only [Functor.map_comp] using congrArg G.map e.hom.w

private theorem mappedCofibration {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    cofibrations Source (F.map i) := by
  change injectiveSegalModel.categoryWithCofibrations.cofibrations (F.map i)
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).1]
  letI : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  change cofibrations Source (F.map i)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact map_mono i

private theorem beadAttachLocalWeak {T : NecklaceCode} (b : T.Bead) :
    weakEquivalences Source (F.map (SSet.Subcomplex.homOfLE
      (inf_le_left : b.face ⊓ spine T.len ≤ b.face))) := by
  have hi : IsIso (intersectionMap.{0} b) := intersectionMap_isIso b
  let e : Arrow.mk (spine.{0} b.length).ι ≅ Arrow.mk
      (SSet.Subcomplex.homOfLE
        (inf_le_left : b.face ⊓ spine T.len ≤ b.face)) :=
    Arrow.isoMk (asIso (intersectionMap b)) b.faceIso (by
      apply (cancel_mono b.face.ι).mp
      change intersectionMap b ≫
        SSet.Subcomplex.homOfLE
          (inf_le_left : b.face ⊓ spine T.len ≤ b.face) ≫ b.face.ι =
        ((spine b.length).ι ≫ b.faceIso.hom) ≫ b.face.ι
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
      rfl)
  exact ((weakEquivalences Source).arrow_mk_iso_iff (mapArrowIso F e)).mp
    (ClassifyingReduction.segalMap_localWeak b.length)

private theorem beadAttachTrivial {T : NecklaceCode} (b : T.Bead) :
    trivialCofibrations Source (F.map (SSet.Subcomplex.homOfLE
      (inf_le_left : b.face ⊓ spine T.len ≤ b.face))) := by
  letI : Mono (SSet.Subcomplex.homOfLE
      (inf_le_left : b.face ⊓ spine T.len ≤ b.face)) := inferInstance
  exact ⟨mappedCofibration _, beadAttachLocalWeak b⟩

private theorem localInclusionCongr {X : SSet.{0}}
    {A A' B B' : X.Subcomplex} (ea : A = A') (eb : B = B')
    (h : A ≤ B) (h' : A' ≤ B') :
    trivialCofibrations Source (F.map (SSet.Subcomplex.homOfLE h)) ↔
      trivialCofibrations Source (F.map (SSet.Subcomplex.homOfLE h')) := by
  subst A'
  subst B'
  rfl

private theorem finiteBeadUnionTrivial {X : SSet.{0}} {I : Type}
    (A : X.Subcomplex) (B : I → X.Subcomplex) (s : Finset I)
    (overlap : ∀ i j, i ≠ j → B i ⊓ B j ≤ A)
    (attach : ∀ i, trivialCofibrations Source
      (F.map (SSet.Subcomplex.homOfLE
        (inf_le_left : B i ⊓ A ≤ B i)))) :
    trivialCofibrations Source
      (F.map (SSet.Subcomplex.homOfLE
        (le_sup_left : A ≤ A ⊔ s.sup B))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply (localInclusionCongr rfl (by simp) _ (le_refl A)).mpr
    have hid : F.map (SSet.Subcomplex.homOfLE (le_refl A)) =
        𝟙 (F.obj (A : SSet.{0})) := by
      rw [SSet.Subcomplex.homOfLE_refl, F.map_id]
    rw [hid]
    exact (trivialCofibrations Source).id_mem _
  | @insert i s hi ih =>
    let C := A ⊔ s.sup B
    have he : B i ⊓ C = B i ⊓ A := intersection_union A B s i hi overlap
    have hat : trivialCofibrations Source
        (F.map (SSet.Subcomplex.homOfLE
          (inf_le_left : B i ⊓ C ≤ B i))) :=
      (localInclusionCongr he rfl _ _).mpr (attach i)
    have sq : SSet.Subcomplex.BicartSq (B i ⊓ C) (B i) C (B i ⊔ C) :=
      ⟨rfl, rfl⟩
    have hj : trivialCofibrations Source
        (F.map (SSet.Subcomplex.homOfLE
          (le_sup_right : C ≤ B i ⊔ C))) :=
      (trivialCofibrations Source).of_isPushout
        (map_isPushout sq.isPushout.flip) hat
    have hc : trivialCofibrations Source
        (F.map (SSet.Subcomplex.homOfLE
          (le_trans le_sup_left le_sup_right : A ≤ B i ⊔ C))) := by
      have hcof := (cofibrations Source).comp_mem _ _ ih.1 hj.1
      have hweak := (weakEquivalences Source).comp_mem _ _ ih.2 hj.2
      have hfac :
          F.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ C)) ≫
              F.map (SSet.Subcomplex.homOfLE
                (le_sup_right : C ≤ B i ⊔ C)) =
            F.map (SSet.Subcomplex.homOfLE
              (le_trans le_sup_left le_sup_right : A ≤ B i ⊔ C)) := by
        rw [← F.map_comp]
        rfl
      rw [hfac] at hcof hweak
      exact ⟨hcof, hweak⟩
    have heq : A ⊔ (insert i s).sup B = B i ⊔ C := by
      rw [Finset.sup_insert]
      dsimp [C]
      ac_rfl
    apply (localInclusionCongr rfl heq _
      (le_trans le_sup_left le_sup_right)).mpr
    exact hc

private theorem spineToComplexTrivial (T : NecklaceCode) :
    trivialCofibrations Source
      (F.map (SSet.Subcomplex.homOfLE (spine_le_complex.{0} T))) := by
  classical
  letI : Fintype T.Bead := Fintype.ofFinite T.Bead
  have h := finiteBeadUnionTrivial (spine.{0} T.len)
    (NecklaceCode.Bead.face (T := T)) Finset.univ
    (bead_overlap_le_spine T) (fun b ↦ beadAttachTrivial b)
  exact (localInclusionCongr rfl
    (DaggerActualOriginalNecklaceInclusionWeak.finite_bead_union_eq T) _ _).mp h

/-- Every original necklace inclusion is a local trivial cofibration after
the literal discrete-free dagger functor, with no positive-bead assumption. -/
theorem localNecklaceInclusion (T : NecklaceCode) :
    trivialCofibrations Source (F.map (T.inclusion : T.toSSet ⟶ Δ[T.len])) := by
  let P := weakEquivalences Source
  letI : P.HasTwoOutOfThreeProperty := injectiveSegalModel.cm2
  have hs := spineToComplexTrivial T
  have hspine : P (F.map (spine.{0} T.len).ι) :=
    ClassifyingReduction.segalMap_localWeak T.len
  have hcomplex : P (F.map T.complex.ι) := by
    apply P.of_precomp (W' := P) _ _ hs.2
    simpa only [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι] using hspine
  have hneck : P (F.map T.inclusion) := by
    rw [NecklaceCode.inclusion, Functor.map_comp]
    exact P.comp_mem _ _ (P.of_isIso _) hcomplex
  letI : Mono T.inclusion := inferInstance
  exact ⟨mappedCofibration T.inclusion, hneck⟩

/-- Into an actual localized injectively fibrant target, restriction from a
simplex to an entire native necklace is a Kan trivial fibration. -/
theorem necklace_mapping_trivialFibration (T : NecklaceCode) (W : Source)
    (hW : @IsFibrant Source _ injectiveSegalModel.categoryWithFibrations _ W) :
    trivialFibrations SSet.{0}
      (diagramMappingPrecomp (F.map (T.inclusion : T.toSSet ⟶ Δ[T.len])) W) := by
  letI : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hlocal : Localization.localObject localizingFamily W := by
    have h := (InjectiveKanDiagram.localized_isFibrant_iff ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono W).mp hW
    change Localization.localObject localizingFamily W at h
    exact h
  have ht := localNecklaceInclusion T
  have hc : cofibrations Source (F.map T.inclusion) := by
    have htcof := ht.1
    change injectiveSegalModel.categoryWithCofibrations.cofibrations _ at htcof
    rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).1] at htcof
    exact htcof
  have hw : Localization.localEquivalences localizingFamily
      (F.map T.inclusion) := by
    have htweak := ht.2
    change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences _ at htweak
    rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).2] at htweak
    exact htweak
  exact InjectiveKanDiagram.localTrivialCofibration_mapping_trivialFibration
    ReverseSimplexᵒᵖ localizingFamily (F.map T.inclusion) ⟨hc, hw⟩ W hlocal

/-- The literal two-bead pushout code, including either zero-length case. -/
def twoBeadCode (m n : ℕ) : NecklaceCode :=
  wedge (single m) (single n)

/-- The ordinary two-bead simplicial set `Δ[m] ⨿_{Δ[0]} Δ[n]`. -/
def twoBead (m n : ℕ) : SSet.{0} :=
  (twoBeadCode m n).toSSet

/-- The actual two-bead inclusion into the composite simplex. -/
def twoBeadInclusion (m n : ℕ) : twoBead m n ⟶ (Δ[m + n] : SSet.{0}) :=
  (twoBeadCode m n).inclusion

/-- Every two-bead inclusion is a trivial cofibration in the exact injective
Segal localization after actual discrete-free dagger completion. -/
theorem twoBead_localTrivial (m n : ℕ) :
    trivialCofibrations Source (F.map (twoBeadInclusion m n)) :=
  localNecklaceInclusion (twoBeadCode m n)

/-- Into an actual localized injectively fibrant target, restricting coherent
simplex labels to two bead labels is a Kan trivial fibration. -/
theorem twoBead_mapping_trivialFibration (m n : ℕ) (W : Source)
    (hW : @IsFibrant Source _ injectiveSegalModel.categoryWithFibrations _ W) :
    trivialFibrations SSet.{0}
      (diagramMappingPrecomp (F.map (twoBeadInclusion m n)) W) := by
  exact necklace_mapping_trivialFibration (twoBeadCode m n) W hW

end

end DaggerModels.PartII.TwoBeadSegalLocality
