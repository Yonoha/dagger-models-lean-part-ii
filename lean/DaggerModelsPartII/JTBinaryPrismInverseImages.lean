import DaggerModelsPartII.JTBinaryPrismParameter

/-! Compare full binary parameters after any map into the joined necklace. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismInverseImages

open JTBinaryPrismParameter (parameter parameter_left parameter_middle parameter_right connector)

noncomputable section

private abbrev A := single 1
private abbrev J := GroupoidSimplex.parameter

variable {T U : NecklaceCode} {X Y I : SSet.{0}}
variable (h : X ⟶ (JTOrderedLabelBinaryGlue.code T U).toSSet)

private abbrev leftι := tripleRightT.{0} T A U
private abbrev middleι := tripleRightU.{0} T A U
private abbrev rightι := tripleRightV.{0} T A U

private theorem lift_simplex {A B X : SSet.{0}} (h : X ⟶ B) (i : A ⟶ B) (n : ℕ)
    (x : X.obj (op ⦋n⦌)) (a : A.obj (op ⦋n⦌)) (w : h.app _ x = i.app _ a) :
    ∃ z, (pullback.fst h i).app (op ⦋n⦌) z = x := by
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback h i).map ((evaluation _ _).obj (op ⦋n⦌))) x a w
  exact ⟨z, hz⟩

/-- The actual three inverse images cover the whole source in every degree. -/
theorem inverseImages_cover (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (∃ z, (pullback.fst h (leftι (T := T) (U := U))).app (op ⦋n⦌) z = x) ∨
      (∃ z, (pullback.fst h (middleι (T := T) (U := U))).app (op ⦋n⦌) z = x) ∨
      (∃ z, (pullback.fst h (rightι (T := T) (U := U))).app (op ⦋n⦌) z = x) := by
  rcases wedge_degree_cover T (wedge A U) (h.app (op ⦋n⦌) x) with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Or.inl (lift_simplex h _ n x a ha.symm)
  · rcases wedge_degree_cover A U b with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inr (Or.inl (lift_simplex h _ n x a
        ((congrArg ((wedgeιRight T (wedge A U)).app (op ⦋n⦌)) ha).trans hb).symm))
    · exact Or.inr (Or.inr (lift_simplex h _ n x a
        ((congrArg ((wedgeιRight T (wedge A U)).app (op ⦋n⦌)) ha).trans hb).symm))

/-- Equality over arbitrary source and time reduces to equality on the
three inverse images, including the inverse image of the inserted connector. -/
theorem inverseImages_tensor_hom_ext {p q : X ⊗ I ⟶ Y}
    (hl : (pullback.fst h (leftι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
      (pullback.fst h (leftι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ q)
    (hm : (pullback.fst h (middleι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
      (pullback.fst h (middleι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ q)
    (hr : (pullback.fst h (rightι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
      (pullback.fst h (rightι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ q) : p = q := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  funext xt
  rcases xt with ⟨x, t⟩
  rcases inverseImages_cover h n x with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hl (op ⦋n⦌)) (z, t)
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hm (op ⦋n⦌)) (z, t)
  · simpa only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply, NatTrans.id_app,
      types_id_apply] using congrFun (NatTrans.congr_app hr (op ⦋n⦌)) (z, t)

private theorem tensor_pull {B C : SSet.{0}} (h : X ⟶ B) (i : C ⟶ B)
    (p : B ⊗ I ⟶ Y) :
    (pullback.fst h i ⊗ₘ 𝟙 I) ≫ (h ⊗ₘ 𝟙 I) ≫ p =
      (pullback.snd h i ⊗ₘ 𝟙 I) ≫ (i ⊗ₘ 𝟙 I) ≫ p := by
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, pullback.condition]

/-- The exact compatibility test for a parameter on any source mapping into
the joined code. The middle equation keeps its full time-dependent connector. -/
theorem reindex_parameter_iff (K : SimplexCategory)
    (s : T.toSSet ⊗ I ⟶ J.obj K) (t : U.toSSet ⊗ I ⟶ J.obj K) (p : X ⊗ I ⟶ J.obj K) :
    p = (h ⊗ₘ 𝟙 I) ≫ parameter T U K I s t ↔
      (pullback.fst h (leftι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (leftι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ s ∧
      (pullback.fst h (middleι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (middleι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ connector T U K I s t ∧
      (pullback.fst h (rightι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (rightι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ t := by
  have hs := parameter_left T U K I s t
  have hm := parameter_middle T U K I s t
  have ht := parameter_right T U K I s t
  constructor
  · intro eq
    refine ⟨?_, ?_, ?_⟩ <;> rw [eq, tensor_pull]
    · exact congrArg (_ ≫ ·) hs
    · exact congrArg (_ ≫ ·) hm
    · exact congrArg (_ ≫ ·) ht
  · rintro ⟨hl, hc, hr⟩
    apply inverseImages_tensor_hom_ext h <;> rw [tensor_pull]
    · exact hl.trans (congrArg (_ ≫ ·) hs).symm
    · exact hc.trans (congrArg (_ ≫ ·) hm).symm
    · exact hr.trans (congrArg (_ ≫ ·) ht).symm


/-- With a time operator, the same criterion uses the pullback projections
on the three native pieces and the given time operator on each piece. -/
theorem reindex_parameter_time_iff {I' : SSet.{0}} (j : I ⟶ I') (K : SimplexCategory)
    (s : T.toSSet ⊗ I' ⟶ J.obj K) (t : U.toSSet ⊗ I' ⟶ J.obj K)
    (p : X ⊗ I ⟶ J.obj K) :
    p = (h ⊗ₘ j) ≫ parameter T U K I' s t ↔
      (pullback.fst h (leftι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (leftι (T := T) (U := U)) ⊗ₘ j) ≫ s ∧
      (pullback.fst h (middleι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (middleι (T := T) (U := U)) ⊗ₘ j) ≫ connector T U K I' s t ∧
      (pullback.fst h (rightι (T := T) (U := U)) ⊗ₘ 𝟙 I) ≫ p =
        (pullback.snd h (rightι (T := T) (U := U)) ⊗ₘ j) ≫ t := by
  have square {B C : SSet.{0}} (g : B ⟶ C) (q : C ⊗ I' ⟶ J.obj K) :
      (g ⊗ₘ 𝟙 I) ≫ (𝟙 C ⊗ₘ j) ≫ q = (g ⊗ₘ j) ≫ q := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  simpa only [← JTBinaryPrismParameter.parameter_mapTime, JTBinaryPrismParameter.connector_mapTime,
    square] using
      (reindex_parameter_iff h K ((𝟙 T.toSSet ⊗ₘ j) ≫ s) ((𝟙 U.toSSet ⊗ₘ j) ≫ t) p)

end

end DaggerModels.PartII.JTBinaryPrismInverseImages
