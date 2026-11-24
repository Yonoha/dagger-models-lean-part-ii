import DaggerModelsPartII.JTSubcomplexRangeUnion
import DaggerModelsPartII.JTInterleavedParameter

/-! Two simplex faces with a common vertex have weakly contractible union. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open SSet.Subcomplex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTwoFaceUnionWeak

noncomputable section

private abbrev simple (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m
private abbrev one := (Δ[0] : SSet.{0})
private abbrev term (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

private theorem face_point_weak {m : ℕ} (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    WeakEquivalence (term ((SSet.stdSimplex.face S : (simple ⦋m⦌).Subcomplex).toSSet)) := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hS.card_ne_zero
  let a := SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy S l (Finset.orderIsoOfFin S hl))
  let p : simple ⦋l⦌ ⟶ one :=
    SSet.stdSimplex.map (SimplexCategory.const ⦋l⦌ ⦋0⦌ 0)
  letI : WeakEquivalence p := JTInterleavedParameter.standardMap_weak _
  exact weakEquivalence_of_precomp_of_fac (SSet.stdSimplex.isTerminalObj₀.hom_ext
    (a.hom ≫ term _) p)

private theorem simplex_point_weak (m : ℕ) : WeakEquivalence (term (simple ⦋m⦌)) := by
  let p : simple ⦋m⦌ ⟶ one :=
    SSet.stdSimplex.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0)
  letI : WeakEquivalence p := JTInterleavedParameter.standardMap_weak _
  have h : p = term (simple ⦋m⦌) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← h]
  infer_instance

private theorem face_inclusion_weak {m : ℕ}
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    WeakEquivalence ((SSet.stdSimplex.face S : (simple ⦋m⦌).Subcomplex).ι) := by
  letI : WeakEquivalence (term
      ((SSet.stdSimplex.face S : (simple ⦋m⦌).Subcomplex).toSSet)) :=
    face_point_weak S hS
  letI : WeakEquivalence (term (simple ⦋m⦌)) := simplex_point_weak m
  exact weakEquivalence_of_postcomp_of_fac
    (SSet.stdSimplex.isTerminalObj₀.hom_ext
      ((SSet.stdSimplex.face S : (simple ⦋m⦌).Subcomplex).ι ≫ term _) (term _))

variable {m : ℕ} (S T : Finset (Fin (m + 1)))

private abbrev left : (simple ⦋m⦌).Subcomplex := SSet.stdSimplex.face S
private abbrev right : (simple ⦋m⦌).Subcomplex := SSet.stdSimplex.face T

private theorem intersection_point_weak (hI : (S ⊓ T).Nonempty) :
    WeakEquivalence (term ((left S ⊓ right T).toSSet)) := by
  rw [show left S ⊓ right T = SSet.stdSimplex.face (S ⊓ T) from
    SSet.stdSimplex.face_inter_face S T]
  exact face_point_weak (S ⊓ T) hI

private theorem intersection_to_right_weak (hT : T.Nonempty)
    (hI : (S ⊓ T).Nonempty) :
    WeakEquivalence (SSet.Subcomplex.homOfLE
      (inf_le_right : left S ⊓ right T ≤ right T)) := by
  letI : WeakEquivalence (term ((left S ⊓ right T).toSSet)) :=
    intersection_point_weak S T hI
  letI : WeakEquivalence (term (right T).toSSet) := face_point_weak T hT
  exact weakEquivalence_of_postcomp_of_fac
    (SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.Subcomplex.homOfLE (inf_le_right : left S ⊓ right T ≤ right T) ≫
        term _) (term _))

/-- The inclusion of two nonempty ordinal faces with a common vertex is Kan weak. -/
theorem union_weak (hS : S.Nonempty) (hT : T.Nonempty)
    (hI : (S ⊓ T).Nonempty) :
    WeakEquivalence ((left S ⊔ right T).ι) := by
  let sq : SSet.Subcomplex.BicartSq (left S ⊓ right T) (left S) (right T)
      (left S ⊔ right T) := ⟨rfl, rfl⟩
  have hcof : Cofibration
      (SSet.Subcomplex.homOfLE (inf_le_left : left S ⊓ right T ≤ left S)) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  have hright : WeakEquivalence
      (SSet.Subcomplex.homOfLE (inf_le_right : left S ⊓ right T ≤ right T)) :=
    intersection_to_right_weak S T hT hI
  have hleft : WeakEquivalence
      (SSet.Subcomplex.homOfLE (le_sup_left : left S ≤ left S ⊔ right T)) :=
    (weakEquivalence_iff _).mpr
      (kanLeftProper sq.isPushout ((cofibration_iff _).mp hcof)
        ((weakEquivalence_iff _).mp hright))
  have hface : WeakEquivalence (left S).ι := face_inclusion_weak S hS
  exact weakEquivalence_of_precomp_of_fac (show
    SSet.Subcomplex.homOfLE (le_sup_left : left S ≤ left S ⊔ right T) ≫
      (left S ⊔ right T).ι = (left S).ι from rfl)

/-- A specified vertex shared by both faces suffices for the weak inclusion. -/
theorem union_weak_of_common_vertex (v : Fin (m + 1)) (hvS : v ∈ S) (hvT : v ∈ T) :
    WeakEquivalence ((left S ⊔ right T).ι) :=
  union_weak S T ⟨v, hvS⟩ ⟨v, hvT⟩ ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩

end
end DaggerModels.PartII.JTTwoFaceUnionWeak

