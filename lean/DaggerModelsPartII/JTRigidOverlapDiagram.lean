import DaggerModelsPartII.JTGraphParameterSourceRestriction
import DaggerModelsPartII.JTVertexAssignmentCover
import DaggerModelsPartII.JTFiniteOrdinalConstraints

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels MorphismProperty
open DaggerChosenRigidificationNecklace
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidOverlapDiagram

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev J := GroupoidSimplex.parameter

noncomputable section

variable {I : Type} [SmallCategory I]

/-- Data of the whole overlap diagram, its two sides, and their reference parameters. -/
structure Data (I : Type) [SmallCategory I] where
  overlap : I ⥤ SSet.{0}
  left : I ⥤ SSet.{0}
  right : I ⥤ SSet.{0}
  degree : I ⥤ SimplexCategory
  leftInclusion : overlap ⟶ left
  rightInclusion : overlap ⟶ right
  leftReference : left ⟶ degree ⋙ J
  rightReference : right ⟶ degree ⋙ J
  leftCode : I → NecklaceCode
  rightCode : I → NecklaceCode
  leftNative : ∀ p, left.obj p ⟶ (leftCode p).toSSet
  rightNative : ∀ p, right.obj p ⟶ (rightCode p).toSSet

variable (D : Data I)

abbrev moved {p q : I} (a : p ⟶ q) (u : (D.overlap.obj p).obj zero) :=
  (D.overlap.map a).app zero u

abbrev leftImage (p : I) (u : (D.overlap.obj p).obj zero) :=
  (D.leftInclusion.app p).app zero u

abbrev rightImage (p : I) (u : (D.overlap.obj p).obj zero) :=
  (D.rightInclusion.app p).app zero u

abbrev leftValue (p : I) (u : (D.overlap.obj p).obj zero) :
    Fin ((D.degree.obj p).len + 1) :=
  JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
    ((D.leftReference.app p).app zero (leftImage D p u)) 0

abbrev rightValue (p : I) (u : (D.overlap.obj p).obj zero) :
    Fin ((D.degree.obj p).len + 1) :=
  JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
    ((D.rightReference.app p).app zero (rightImage D p u)) 0

abbrev coefficientMap {p q : I} (a : p ⟶ q) :=
  (D.degree.map a).toOrderHom

/-- Some outgoing operator sends the vertex to a left rigid vertex. -/
def LeftForced (p : I) (u : (D.overlap.obj p).obj zero) : Prop :=
  ∃ (q : I) (a : p ⟶ q),
    JTGraphParameterSourceRestriction.RigidVertex (D.leftCode q) (D.leftNative q)
      (leftImage D q (moved D a u))

/-- Some, possibly different, outgoing operator sends it to a right rigid vertex. -/
def RightForced (p : I) (u : (D.overlap.obj p).obj zero) : Prop :=
  ∃ (q : I) (a : p ⟶ q),
    JTGraphParameterSourceRestriction.RigidVertex (D.rightCode q) (D.rightNative q)
      (rightImage D q (moved D a u))

/-- Freeze each side's reference coefficient after every outgoing operator
whenever its target vertex is rigid on that side. -/
def stableAllowed (p : I) (u : (D.overlap.obj p).obj zero) :
    Set (Fin ((D.degree.obj p).len + 1)) :=
  {v | (∀ (q : I) (a : p ⟶ q),
      JTGraphParameterSourceRestriction.RigidVertex (D.leftCode q) (D.leftNative q)
        (leftImage D q (moved D a u)) →
      coefficientMap D a v = leftValue D q (moved D a u)) ∧
    (∀ (q : I) (a : p ⟶ q),
      JTGraphParameterSourceRestriction.RigidVertex (D.rightCode q) (D.rightNative q)
        (rightImage D q (moved D a u)) →
      coefficientMap D a v = rightValue D q (moved D a u))}

/-- The identity operator recovers the original left assignment at a rigid vertex. -/
theorem allowed_left_at_rigid (p : I) (u : (D.overlap.obj p).obj zero)
    (c : Fin ((D.degree.obj p).len + 1)) (hc : c ∈ stableAllowed D p u)
    (hr : JTGraphParameterSourceRestriction.RigidVertex (D.leftCode p)
      (D.leftNative p) ((D.leftInclusion.app p).app zero u)) :
    c = leftValue D p u := by
  have h := hc.1 p (𝟙 p)
  have hm : moved D (𝟙 p) u = u := by
    change (D.overlap.map (𝟙 p)).app zero u = u
    rw [D.overlap.map_id]
    rfl
  have hk : coefficientMap D (𝟙 p) c = c := by
    change (D.degree.map (𝟙 p)).toOrderHom c = c
    rw [D.degree.map_id, SimplexCategory.id_toOrderHom]
    rfl
  rw [hm, hk] at h
  exact h hr

/-- The identity operator recovers the original right assignment at a rigid vertex. -/
theorem allowed_right_at_rigid (p : I) (u : (D.overlap.obj p).obj zero)
    (c : Fin ((D.degree.obj p).len + 1)) (hc : c ∈ stableAllowed D p u)
    (hr : JTGraphParameterSourceRestriction.RigidVertex (D.rightCode p)
      (D.rightNative p) ((D.rightInclusion.app p).app zero u)) :
    c = rightValue D p u := by
  have h := hc.2 p (𝟙 p)
  have hm : moved D (𝟙 p) u = u := by
    change (D.overlap.map (𝟙 p)).app zero u = u
    rw [D.overlap.map_id]
    rfl
  have hk : coefficientMap D (𝟙 p) c = c := by
    change (D.degree.map (𝟙 p)).toOrderHom c = c
    rw [D.degree.map_id, SimplexCategory.id_toOrderHom]
    rfl
  rw [hm, hk] at h
  exact h hr

private theorem moved_comp {p q r : I} (a : p ⟶ q) (b : q ⟶ r)
    (u : (D.overlap.obj p).obj zero) :
    moved D (a ≫ b) u = moved D b (moved D a u) := by
  simp only [moved, Functor.map_comp]
  rfl

private theorem coefficientMap_comp {p q r : I} (a : p ⟶ q) (b : q ⟶ r)
    (v : Fin ((D.degree.obj p).len + 1)) :
    coefficientMap D (a ≫ b) v = coefficientMap D b (coefficientMap D a v) := by
  simp only [coefficientMap, Functor.map_comp]
  rfl

/-- The pulled-back rigid constraints are stable under all original operators. -/
theorem stableAllowed_mapsTo {p q : I} (a : p ⟶ q) (u : (D.overlap.obj p).obj zero) :
    Set.MapsTo (coefficientMap D a) (stableAllowed D p u)
      (stableAllowed D q (moved D a u)) := by
  intro v hv
  constructor
  · intro r b hr
    have h := hv.1 r (a ≫ b)
    rw [moved_comp D a b u] at h
    rw [← coefficientMap_comp D a b v]
    exact h hr
  · intro r b hr
    have h := hv.2 r (a ≫ b)
    rw [moved_comp D a b u] at h
    rw [← coefficientMap_comp D a b v]
    exact h hr

private theorem leftValue_natural {p q : I} (a : p ⟶ q)
    (u : (D.overlap.obj p).obj zero) :
    leftValue D q (moved D a u) = coefficientMap D a (leftValue D p u) := by
  have hn := congrFun (NatTrans.congr_app
    ((D.leftInclusion ≫ D.leftReference).naturality a) zero) u
  change (D.leftReference.app q).app zero (leftImage D q (moved D a u)) =
    (J.map (D.degree.map a)).app zero
      ((D.leftReference.app p).app zero (leftImage D p u)) at hn
  change JTCodiscreteParameterPairing.coord (D.degree.obj q) zero
      ((D.leftReference.app q).app zero (leftImage D q (moved D a u))) 0 = _
  rw [hn, JTCodiscreteParameterPairing.coord_map]

private theorem rightValue_natural {p q : I} (a : p ⟶ q)
    (u : (D.overlap.obj p).obj zero) :
    rightValue D q (moved D a u) = coefficientMap D a (rightValue D p u) := by
  have hn := congrFun (NatTrans.congr_app
    ((D.rightInclusion ≫ D.rightReference).naturality a) zero) u
  change (D.rightReference.app q).app zero (rightImage D q (moved D a u)) =
    (J.map (D.degree.map a)).app zero
      ((D.rightReference.app p).app zero (rightImage D p u)) at hn
  change JTCodiscreteParameterPairing.coord (D.degree.obj q) zero
      ((D.rightReference.app q).app zero (rightImage D q (moved D a u))) 0 = _
  rw [hn, JTCodiscreteParameterPairing.coord_map]

/-- A left downstream fiber includes the operator and its rigid witness. -/
abbrev LeftTest (p : I) (u : (D.overlap.obj p).obj zero) :=
  {qa : Σ q : I, p ⟶ q //
    JTGraphParameterSourceRestriction.RigidVertex (D.leftCode qa.1) (D.leftNative qa.1)
      (leftImage D qa.1 (moved D qa.2 u))}

/-- A right downstream fiber may use a different outgoing operator. -/
abbrev RightTest (p : I) (u : (D.overlap.obj p).obj zero) :=
  {qa : Σ q : I, p ⟶ q //
    JTGraphParameterSourceRestriction.RigidVertex (D.rightCode qa.1) (D.rightNative qa.1)
      (rightImage D qa.1 (moved D qa.2 u))}

def constraint (p : I) (u : (D.overlap.obj p).obj zero)
    (i : LeftTest D p u ⊕ RightTest D p u) :
    Set (Fin ((D.degree.obj p).len + 1)) :=
  match i with
  | .inl ⟨⟨q, a⟩, _⟩ => {v | coefficientMap D a v = leftValue D q (moved D a u)}
  | .inr ⟨⟨q, a⟩, _⟩ => {v | coefficientMap D a v = rightValue D q (moved D a u)}

private theorem constraint_ordConnected (p : I) (u : (D.overlap.obj p).obj zero)
    (i : LeftTest D p u ⊕ RightTest D p u) :
    (constraint D p u i).OrdConnected := by
  rcases i with ⟨⟨q, a⟩, _⟩ | ⟨⟨q, a⟩, _⟩
  · exact JTFiniteOrdinalConstraints.ordConnected_fiber (coefficientMap D a) _
  · exact JTFiniteOrdinalConstraints.ordConnected_fiber (coefficientMap D a) _

private theorem leftValue_mem_leftConstraint (p : I) (u : (D.overlap.obj p).obj zero)
    (i : LeftTest D p u) : leftValue D p u ∈ constraint D p u (.inl i) := by
  rcases i with ⟨⟨q, a⟩, _⟩
  exact (leftValue_natural D a u).symm

private theorem rightValue_mem_rightConstraint (p : I) (u : (D.overlap.obj p).obj zero)
    (i : RightTest D p u) : rightValue D p u ∈ constraint D p u (.inr i) := by
  rcases i with ⟨⟨q, a⟩, _⟩
  exact (rightValue_natural D a u).symm

/-- Pairwise compatibility of a left and a right downstream fiber is the
sharp condition for existence of a common coefficient. -/
def PairwiseFiberAgreement : Prop :=
  ∀ (p : I) (u : (D.overlap.obj p).obj zero)
    (l : LeftTest D p u) (r : RightTest D p u),
    (constraint D p u (.inl l) ∩ constraint D p u (.inr r)).Nonempty

theorem stableAllowed_nonempty_iff_pairwise :
    (∀ p u, (stableAllowed D p u).Nonempty) ↔ PairwiseFiberAgreement D := by
  constructor
  · intro h p u l r
    obtain ⟨v, hv⟩ := h p u
    rcases l with ⟨⟨q, a⟩, hl⟩
    rcases r with ⟨⟨q', b⟩, hr⟩
    exact ⟨v, hv.1 q a hl, hv.2 q' b hr⟩
  · intro h p u
    have hpairs : ∀ i j,
        (constraint D p u i ∩ constraint D p u j).Nonempty := by
      rintro (l | r) (l' | r')
      · exact ⟨leftValue D p u,
          leftValue_mem_leftConstraint D p u l,
          leftValue_mem_leftConstraint D p u l'⟩
      · exact h p u l r'
      · rw [Set.inter_comm]
        exact h p u l' r
      · exact ⟨rightValue D p u,
          rightValue_mem_rightConstraint D p u r,
          rightValue_mem_rightConstraint D p u r'⟩
    obtain ⟨v, hv⟩ := JTFiniteOrdinalConstraints.exists_least_common
      (constraint D p u) (constraint_ordConnected D p u) hpairs
    refine ⟨v, ?_, ?_⟩
    · intro q a hl
      exact hv.1 (.inl ⟨⟨q, a⟩, hl⟩)
    · intro q a hr
      exact hv.1 (.inr ⟨⟨q, a⟩, hr⟩)

/-- The two original reference coefficients agree whenever both sides are
forced, perhaps along different outgoing arrows. -/
def CrossAgreement : Prop :=
  ∀ (p : I) (u : (D.overlap.obj p).obj zero),
    LeftForced D p u → RightForced D p u →
    leftValue D p u = rightValue D p u

theorem stableAllowed_nonempty (h : CrossAgreement D)
    (p : I) (u : (D.overlap.obj p).obj zero) : (stableAllowed D p u).Nonempty := by
  by_cases hL : LeftForced D p u
  · refine ⟨leftValue D p u, ?_, ?_⟩
    · intro q a _
      exact (leftValue_natural D a u).symm
    · intro q a hr
      rw [h p u hL ⟨q, a, hr⟩]
      exact (rightValue_natural D a u).symm
  · refine ⟨rightValue D p u, ?_, ?_⟩
    · intro q a hl
      exact (hL ⟨q, a, hl⟩).elim
    · intro q a _
      exact (rightValue_natural D a u).symm

/-- A pointwise trivial fibration of the whole overlap diagram. -/
abbrev cover := JTVertexAssignmentCover.cover D.overlap D.degree
  (stableAllowed D) (stableAllowed_mapsTo D)

abbrev projection : cover D ⟶ D.overlap :=
  JTVertexAssignmentCover.projection _ _ _ (stableAllowed_mapsTo D)

/-- The natural common coefficient parameter on that cover. -/
abbrev trace : cover D ⟶ D.degree ⋙ J :=
  JTVertexAssignmentCover.trace _ _ _ (stableAllowed_mapsTo D)

theorem projection_trivialFibration (h : CrossAgreement D) (p : I) :
    trivialFibrations SSet.{0} ((projection D).app p) :=
  JTVertexAssignmentCover.projection_trivialFibration _ _ _
    (stableAllowed_mapsTo D) (stableAllowed_nonempty D h) p

private theorem trivialFibration_surjective_vertices {E B : SSet.{0}} (f : E ⟶ B)
    (hf : trivialFibrations SSet.{0} f) : Function.Surjective (f.app zero) := by
  rw [← cofibrations_rlp] at hf
  have hi : cofibrations SSet.{0} (SSet.boundary 0).ι := by
    change (monomorphisms SSet.{0}) (SSet.boundary 0).ι
    exact monomorphisms.infer_property _
  have hlift : HasLiftingProperty (SSet.boundary 0).ι f := hf _ hi
  intro y
  have sq : CommSq (SSet.boundary.isInitial.to _) (SSet.boundary 0).ι f
      (SSet.yonedaEquiv.symm y) := ⟨by ext⟩
  exact ⟨SSet.yonedaEquiv sq.lift,
    by rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]⟩

/-- A weak cover has a pointwise trivial fibration and a natural common
trace satisfying all the pulled-back rigid assignments. -/
structure CommonCover where
  source : I ⥤ SSet.{0}
  projection : source ⟶ D.overlap
  trace : source ⟶ D.degree ⋙ J
  trivialFibration : ∀ p, trivialFibrations SSet.{0} (projection.app p)
  forced : ∀ p (u : (source.obj p).obj zero),
    JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
      ((trace.app p).app zero u) 0 ∈
      stableAllowed D p ((projection.app p).app zero u)

/-- Pointwise nonemptiness is equivalent to the existence of a weak
cover carrying a natural trace with all rigid assignments. -/
theorem nonempty_iff_commonCover :
    (∀ p u, (stableAllowed D p u).Nonempty) ↔ Nonempty (CommonCover D) := by
  constructor
  · intro h
    refine ⟨⟨cover D, projection D, trace D, ?_, ?_⟩⟩
    · intro p
      exact JTVertexAssignmentCover.projection_trivialFibration _ _ _
        (stableAllowed_mapsTo D) h p
    · intro p u
      exact JTVertexAssignmentCover.trace_allowed D.overlap D.degree
        (stableAllowed D) (stableAllowed_mapsTo D) p u
  · rintro ⟨C⟩ p u
    have hs := trivialFibration_surjective_vertices (C.projection.app p)
      (C.trivialFibration p)
    obtain ⟨v, hv⟩ := hs u
    exact ⟨JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
      ((C.trace.app p).app zero v) 0, hv ▸ C.forced p v⟩

/-- The pairwise fiber test is equivalent to a weak common-trace cover. -/
theorem pairwise_iff_commonCover :
    PairwiseFiberAgreement D ↔ Nonempty (CommonCover D) := by
  rw [← nonempty_iff_commonCover D]
  exact (stableAllowed_nonempty_iff_pairwise D).symm

/-- The easy cross-agreement condition constructs the common weak cover. -/
theorem commonCover_of_crossAgreement (h : CrossAgreement D) :
    Nonempty (CommonCover D) :=
  (nonempty_iff_commonCover D).mp (stableAllowed_nonempty D h)

/-- The cover trace obeys both rigid assignment systems at every vertex. -/
theorem trace_forced (p : I) (u : ((cover D).obj p).obj zero) :
    (∀ (q : I) (a : p ⟶ q),
      JTGraphParameterSourceRestriction.RigidVertex (D.leftCode q) (D.leftNative q)
        (leftImage D q (moved D a (((projection D).app p).app zero u))) →
      coefficientMap D a
        (JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
          (((trace D).app p).app zero u) 0) =
        leftValue D q (moved D a (((projection D).app p).app zero u))) ∧
    (∀ (q : I) (a : p ⟶ q),
      JTGraphParameterSourceRestriction.RigidVertex (D.rightCode q) (D.rightNative q)
        (rightImage D q (moved D a (((projection D).app p).app zero u))) →
      coefficientMap D a
        (JTCodiscreteParameterPairing.coord (D.degree.obj p) zero
          (((trace D).app p).app zero u) 0) =
        rightValue D q (moved D a (((projection D).app p).app zero u))) :=
  JTVertexAssignmentCover.trace_allowed D.overlap D.degree
    (stableAllowed D) (stableAllowed_mapsTo D) p u

end

end DaggerModels.PartII.JTRigidOverlapDiagram
