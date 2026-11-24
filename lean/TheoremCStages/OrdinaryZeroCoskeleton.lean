import OrdinaryCSSConditions
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Relative zero-row extension for ordinary simplicial spaces

This is the ordinary-index compatibility of the checked JTZeroCoskeleton
lifting proof. The evaluation right adjoint and injective model are the
existing ones; the only index facts used are the unique degeneracy from
zero and a chosen vertex into zero in the opposite simplex category.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryZeroCoskeleton

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev S := OrdinaryCSSLocalization.Space
private abbrev zero : J := op ⦋0⦌

private def fromZero (n : J) : zero ⟶ n :=
  (SimplexCategory.const n.unop ⦋0⦌ 0).op

private theorem fromZero_unique {n : J} (f g : zero ⟶ n) : f = g := by
  apply Quiver.Hom.unop_inj
  exact (SimplexCategory.eq_const_to_zero f.unop).trans
    (SimplexCategory.eq_const_to_zero g.unop).symm

private def toZero (n : J) : n ⟶ zero :=
  (SimplexCategory.const ⦋0⦌ n.unop 0).op

/-- The actual totally degenerate extension of the zero row. -/
def degenerate (X : S) : (Functor.const J).obj (X.obj zero) ⟶ X where
  app n := X.map (fromZero n)
  naturality {n m} f := by
    change 𝟙 (X.obj zero) ≫ X.map (fromZero m) = X.map (fromZero n) ≫ X.map f
    rw [Category.id_comp, ← X.map_comp, fromZero_unique (fromZero n ≫ f) (fromZero m)]

theorem degenerate_zero (X : S) : (degenerate X).app zero = 𝟙 _ := by
  change X.map (fromZero zero) = 𝟙 (X.obj zero)
  rw [fromZero_unique (fromZero zero) (𝟙 zero), X.map_id]

private theorem degenerate_retraction (X : S) (n : J) :
    (degenerate X).app n ≫ X.map (toZero n) = 𝟙 _ := by
  change X.map (fromZero n) ≫ X.map (toZero n) = 𝟙 (X.obj zero)
  rw [← X.map_comp, fromZero_unique (fromZero n ≫ toZero n) (𝟙 zero), X.map_id]

private theorem degenerate_natural {X Y : S} (i : X ⟶ Y) :
    (degenerate X) ≫ i = (Functor.const J).map (i.app zero) ≫ degenerate Y := by
  apply NatTrans.ext
  funext n
  change X.map (fromZero n) ≫ i.app n = i.app zero ≫ Y.map (fromZero n)
  exact i.naturality (fromZero n)

variable {X Y : S} (i : X ⟶ Y)

/-- Attach the specified new zero-row values before extending to the whole diagram. -/
def withNewZero : S := pushout (degenerate X) ((Functor.const J).map (i.app zero))

/-- The exact map from the union of the old diagram and the new zero row into the target. -/
def relativeInclusion : withNewZero i ⟶ Y :=
  pushout.desc i (degenerate Y) (degenerate_natural i)

private theorem relativeInclusion_inl :
    pushout.inl (degenerate X) ((Functor.const J).map (i.app zero)) ≫ relativeInclusion i = i :=
  pushout.inl_desc _ _ _

private theorem relativeInclusion_inr :
    pushout.inr (degenerate X) ((Functor.const J).map (i.app zero)) ≫
      relativeInclusion i = degenerate Y :=
  pushout.inr_desc _ _ _

/-- At every two indices the degenerate-vertex square is an actual pullback for a mono. -/
private theorem relativeSquare [Mono i] (n : J) (q : SimplexCategoryᵒᵖ) :
    IsPullback (((degenerate X).app n).app q) ((i.app zero).app q)
      ((i.app n).app q) (((degenerate Y).app n).app q) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  have hW := congrArg (fun a : (Functor.const J).obj (X.obj zero) ⟶ Y ↦
    (a.app n).app q) (degenerate_natural i)
  refine ⟨hW, ?_, ?_⟩
  · intro a b hab
    have h := congrArg ((X.map (toZero n)).app q) hab.1
    exact ((congrFun (NatTrans.congr_app (degenerate_retraction X n) q) a).symm.trans h).trans
      (congrFun (NatTrans.congr_app (degenerate_retraction X n) q) b)
  · intro a b hab
    let z := (X.map (toZero n)).app q a
    have hz : (i.app zero).app q z = b := by
      have hn := congrFun (NatTrans.congr_app (i.naturality (toZero n)) q) a
      have h := congrArg ((Y.map (toZero n)).app q) hab
      have hr := congrFun (NatTrans.congr_app (degenerate_retraction Y n) q) b
      exact hn.trans (h.trans hr)
    have hi := (mono_iff_injective ((i.app n).app q)).mp inferInstance
    refine ⟨z, hi ?_, hz⟩
    have hc := congrFun hW z
    change (i.app n).app q (((degenerate X).app n).app q z) =
      ((degenerate Y).app n).app q ((i.app zero).app q z) at hc
    rw [hc, hz]
    exact hab.symm

/-- The relative extension of a monomorphism at zero is still monic. -/
theorem relativeInclusion_mono [Mono i] : Mono (relativeInclusion i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [NatTrans.mono_iff_mono_app]
  intro q
  let E := (evaluation J SSet.{0}).obj n ⋙ SSet.evaluation.obj q
  have hpush := (IsPushout.of_hasPushout (degenerate X)
    ((Functor.const J).map (i.app zero))).map E
  have hl := congrArg (fun a : X ⟶ Y ↦ (a.app n).app q) (relativeInclusion_inl i)
  have hr := congrArg (fun a : (Functor.const J).obj (Y.obj zero) ⟶ Y ↦
    (a.app n).app q) (relativeInclusion_inr i)
  have hmono : Mono ((i.app n).app q) := inferInstance
  change Mono (E.map (relativeInclusion i))
  exact Types.mono_of_isPushout_of_isPullback hpush (relativeSquare i n q) hl hr
    (fun a b _ _ h ↦ by
      have h' := congrArg ((Y.map (toZero n)).app q) h
      exact ((congrFun (NatTrans.congr_app (degenerate_retraction Y n) q) a).symm.trans h').trans
        (congrFun (NatTrans.congr_app (degenerate_retraction Y n) q) b))

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

/-- For an original injective trivial cofibration, the relative extension
at zero is also an original injective trivial cofibration. -/
theorem relativeInclusion_trivial [Cofibration i] [WeakEquivalence i] :
    trivialCofibrations S (relativeInclusion i) := by
  have hi := (cofibration_iff i).mp inferInstance
  rw [InjectiveKanDiagram.model_cofibrations] at hi
  haveI : Mono i := hi
  haveI : Cofibration (relativeInclusion i) := by
    apply (cofibration_iff _).mpr
    rw [InjectiveKanDiagram.model_cofibrations]
    exact relativeInclusion_mono i
  have hc : trivialCofibrations S ((Functor.const J).map (i.app zero)) := by
    refine ⟨?_, ?_⟩
    · rw [InjectiveKanDiagram.model_cofibrations]
      apply (NatTrans.mono_iff_mono_app _).mpr
      intro n
      change Mono (i.app zero)
      exact (NatTrans.mono_iff_mono_app i).mp inferInstance zero
    · have hw := (weakEquivalence_iff i).mp inferInstance
      rw [InjectiveKanDiagram.model_weakEquivalences] at hw ⊢
      exact fun _ ↦ hw zero
  haveI : (trivialCofibrations S).IsStableUnderCobaseChange := by
    rw [← llp_eq_of_wfs (trivialCofibrations S) (fibrations S)]
    infer_instance
  have hj : trivialCofibrations S
      (pushout.inl (degenerate X) ((Functor.const J).map (i.app zero))) :=
    (trivialCofibrations S).of_isPushout
      (IsPushout.of_hasPushout (degenerate X) ((Functor.const J).map (i.app zero))) hc
  haveI : WeakEquivalence (pushout.inl (degenerate X) ((Functor.const J).map (i.app zero))) :=
    (weakEquivalence_iff _).mpr hj.2
  haveI : WeakEquivalence (relativeInclusion i) :=
    weakEquivalence_of_precomp_of_fac (relativeInclusion_inl i)
  exact (mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩


/-- The existing Mathlib right adjoint to evaluation at the actual zero row. -/
abbrev coskeleton : SSet.{0} ⥤ S := evaluationRightAdjoint SSet.{0} zero

private abbrev zeroAdj := evaluationAdjunctionLeft SSet.{0} zero

/-- The exact map to the diagram of all ordered vertex values. -/
def vertices (W : S) : W ⟶ coskeleton.obj (W.obj zero) := zeroAdj.unit.app W

private theorem vertices_transpose {A Z : S} (a : A ⟶ Z) :
    (zeroAdj.homEquiv A (Z.obj zero)).symm (a ≫ vertices Z) = a.app zero := by
  have h := zeroAdj.homEquiv_naturality_left_symm a (vertices Z)
  change (zeroAdj.homEquiv A (Z.obj zero)).symm (a ≫ vertices Z) =
    a.app zero ≫ (zeroAdj.homEquiv Z (Z.obj zero)).symm (zeroAdj.unit.app Z) at h
  have hi : (zeroAdj.homEquiv Z (Z.obj zero)).symm (zeroAdj.unit.app Z) =
      𝟙 (Z.obj zero) :=
    (congrArg (zeroAdj.homEquiv Z (Z.obj zero)).symm
      (zeroAdj.homEquiv_id Z).symm).trans
      ((zeroAdj.homEquiv Z (Z.obj zero)).symm_apply_apply (𝟙 (Z.obj zero)))
  rw [hi] at h
  exact h.trans (Category.comp_id _)

/-- An injectively fibrant ordinary diagram has a fibration to its actual
zero coskeleton. Lifts are chosen after attaching the prescribed zero row. -/
theorem vertices_fibration (Z : S) [IsFibrant Z] : Fibration (vertices Z) := by
  apply (fibration_iff _).mpr
  rw [← rlp_eq_of_wfs (trivialCofibrations S) (fibrations S)]
  intro A B i hi
  constructor
  intro a b sq
  let b₀ := (zeroAdj.homEquiv B (Z.obj zero)).symm b
  have h₀ : i.app zero ≫ b₀ = a.app zero := by
    have h := congrArg (zeroAdj.homEquiv A (Z.obj zero)).symm sq.w
    rw [vertices_transpose, zeroAdj.homEquiv_naturality_left_symm] at h
    exact h.symm
  let c := (Functor.const J).map b₀ ≫ degenerate Z
  have hc : degenerate A ≫ a = (Functor.const J).map (i.app zero) ≫ c := by
    rw [degenerate_natural, show (Functor.const J).map (i.app zero) ≫ c =
      ((Functor.const J).map (i.app zero) ≫ (Functor.const J).map b₀) ≫ degenerate Z
      from (Category.assoc _ _ _).symm, ← Functor.map_comp, h₀]
  let g : withNewZero i ⟶ Z := pushout.desc a c hc
  have hi' := (mem_trivialCofibrations_iff i).mp hi
  letI : Cofibration i := hi'.1
  letI : WeakEquivalence i := hi'.2
  have hrel := (mem_trivialCofibrations_iff _).mp (relativeInclusion_trivial i)
  letI : Cofibration (relativeInclusion i) := hrel.1
  letI : WeakEquivalence (relativeInclusion i) := hrel.2
  let sq' : CommSq g (relativeInclusion i) (terminal.from Z) (terminal.from B) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let l := sq'.lift
  have hl : relativeInclusion i ≫ l = g := sq'.fac_left
  have hl₀ : degenerate B ≫ l = c := by
    rw [← relativeInclusion_inr i, Category.assoc, hl]
    exact pushout.inr_desc _ _ _
  refine ⟨l, ?_, ?_⟩
  · rw [← relativeInclusion_inl i, Category.assoc, hl]
    exact pushout.inl_desc _ _ _
  · apply (zeroAdj.homEquiv B (Z.obj zero)).symm.injective
    rw [vertices_transpose]
    have h : (degenerate B).app zero ≫ l.app zero =
        b₀ ≫ (degenerate Z).app zero := NatTrans.congr_app hl₀ zero
    rw [degenerate_zero, Category.id_comp, degenerate_zero] at h
    change l.app zero = b₀ ≫ 𝟙 (Z.obj zero) at h
    exact h.trans (Category.comp_id _)


theorem coskeleton_preservesFibrations : coskeleton.PreservesFibrations := by
  apply zeroAdj.preservesTrivialCofibrations_iff_preservesFibrations.mp
  constructor
  intro A B i hi
  have hC := hi.1
  have hW := hi.2
  rw [InjectiveKanDiagram.model_cofibrations] at hC
  rw [InjectiveKanDiagram.model_weakEquivalences] at hW
  refine ⟨?_, hW zero⟩
  haveI : Mono i := hC
  exact (HomotopicalAlgebra.cofibration_iff (i.app zero)).mp
    ((SSet.modelCategoryQuillen.cofibration_iff (i.app zero)).mpr
      ((NatTrans.mono_iff_mono_app i).mp inferInstance zero))

theorem coskeleton_fibrant (K : SSet.{0}) [IsFibrant K] :
    IsFibrant (coskeleton.obj K) := by
  letI := coskeleton_preservesFibrations
  letI : PreservesLimitsOfSize.{0, 0} coskeleton := zeroAdj.rightAdjoint_preservesLimits
  exact (isFibrant_iff_of_isTerminal (coskeleton.map (terminal.from K))
    (terminalIsTerminal.isTerminalObj coskeleton)).mpr inferInstance

/-- Pull back the literal target diagram to the same original zero row
as the source, retaining all the original ordered vertex maps. -/
def targetOverZero {W Z : S} (f : W ⟶ Z) :=
  pullback (vertices Z) (coskeleton.map (f.app zero))

/-- The actual relative comparison over the original source zero row. -/
def relativeComparison {W Z : S} (f : W ⟶ Z) : W ⟶ targetOverZero f :=
  pullback.lift f (vertices W) (zeroAdj.unit.naturality f)

theorem targetOverZero_fibrant {W Z : S} (f : W ⟶ Z) [IsFibrant Z]
    [IsFibrant (W.obj zero)] : IsFibrant (targetOverZero f) := by
  haveI := coskeleton_fibrant (W.obj zero)
  haveI := vertices_fibration Z
  exact isFibrant_of_fibration (pullback.snd (vertices Z) (coskeleton.map (f.app zero)))

#print axioms relativeInclusion_mono
#print axioms relativeInclusion_trivial
#print axioms vertices_fibration
#print axioms coskeleton_fibrant
#print axioms targetOverZero_fibrant

end

end DaggerModels.PartII.OrdinaryZeroCoskeleton
