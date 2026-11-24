import DaggerModelsPartII.SegalLocalizers
import DaggerModelsPartII.IndexKanExtensions

/-! The Part I free dagger simplex is the reversal-simplex representable. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor Opposite Simplicial

universe u

namespace DaggerModels.PartII.SegalRepresentables

noncomputable section

open SegalLocalizers

/-- The free dagger simplices as a cosimplicial diagram of discrete reversal spaces. -/
def freeSimplices : SimplexCategory ⥤ ReverseDaggerSpace.{u} :=
  SSet.stdSimplex ⋙ freeDagger ⋙ discreteDagger

/-- Objectwise Yoneda comparison, using the Part I presheaf equivalence and Kan extension. -/
def freeSimplexRepresentable (n : ℕ) :
    daggerSimplex.{u} n ≅
      (simplicialYoneda.{0, u} ReverseSimplex).obj ⟨n⟩ := by
  let P := (ReverseSimplex.inclusion.op.lan).obj (Δ[n] : SSet.{u})
  let d := discretePresheaf.{0, u} ReverseSimplex
  let e := ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u}
    ReverseSimplex.inclusion).app ⦋n⦌).symm
  exact d.mapIso (ReversePresheaf.counitIso.app P) ≪≫ d.mapIso e

/-- The objectwise comparison is natural in the ordinary simplex variable. -/
def freeSimplicesRepresentable :
    freeSimplices.{u} ≅
      ReverseSimplex.inclusion ⋙ simplicialYoneda.{0, u} ReverseSimplex := by
  let K : (SimplexCategoryᵒᵖ ⥤ Type u) ⥤ (ReverseSimplexᵒᵖ ⥤ Type u) :=
    ReverseSimplex.inclusion.op.lan
  let C := ReversePresheaf.toDaggerSSet.{u}
  let D := DaggerSSet.toPresheaf.{u}
  let E := discretePresheaf.{0, u} ReverseSimplex
  let Y := SSet.stdSimplex.{u}
  let comparison := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u}
    ReverseSimplex.inclusion
  change (Y ⋙ (K ⋙ C)) ⋙ (D ⋙ E) ≅
    ReverseSimplex.inclusion ⋙ (uliftYoneda.{u} ⋙ E)
  exact (Functor.associator Y (K ⋙ C) (D ⋙ E)) ≪≫
    isoWhiskerLeft Y ((Functor.associator K C (D ⋙ E)) ≪≫
      isoWhiskerLeft K ((Functor.associator C D E).symm ≪≫
        isoWhiskerRight ReversePresheaf.counitIso E ≪≫
        Functor.leftUnitor E)) ≪≫
    (Functor.associator Y K E).symm ≪≫
    isoWhiskerRight comparison.symm E ≪≫
    Functor.associator ReverseSimplex.inclusion uliftYoneda.{u} E

/-- The natural comparison has the same chosen objectwise components. -/
theorem freeSimplicesRepresentable_app (n : ℕ) :
    freeSimplicesRepresentable.{u}.app ⦋n⦌ = freeSimplexRepresentable.{u} n := by
  rfl

/-- A free dagger zero-simplex has a unique simplex in every outer and inner degree. -/
theorem subsingleton_daggerSimplex_zero (a : ReverseSimplexᵒᵖ)
    (q : SimplexCategoryᵒᵖ) :
    Subsingleton (((daggerSimplex.{u} 0).obj a).obj q) := by
  let e := freeSimplexRepresentable.{u} 0
  have htarget : Subsingleton
      ((((simplicialYoneda.{0, u} ReverseSimplex).obj ⟨0⟩).obj a).obj q) := by
    constructor
    intro x y
    apply ULift.ext
    apply ReverseSimplex.Hom.ext
    intro i
    apply Fin.ext
    have hx := (x.down.toFun i).isLt
    have hy := (y.down.toFun i).isLt
    dsimp at hx hy
    omega
  constructor
  intro x y
  have hinj : Function.Injective ((e.hom.app a).app q) :=
    (mono_iff_injective _).mp inferInstance
  exact hinj (Subsingleton.elim _ _)

/-- The completeness map is levelwise monic, independently of the Segal maps. -/
theorem unitaryCompletenessMap_mono :
    Mono unitaryCompletenessMap.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  letI := subsingleton_daggerSimplex_zero.{u} a q
  intro x y _
  exact Subsingleton.elim x y

/-- Every map in `S_rev` is monic in the reversal diagram category. -/
theorem S_rev_mono {s : Σ A B : ReverseDaggerSpace.{u}, A ⟶ B}
    (hs : s ∈ S_rev.{u}) : Mono s.2.2 := by
  obtain ⟨i, rfl⟩ := hs
  cases i with
  | inl n => exact segalMap_mono n
  | inr _ => exact unitaryCompletenessMap_mono

/-- Every map in `S_rev` is a monomorphism at each reversal-simplex degree. -/
theorem S_rev_levelwise_mono {s : Σ A B : ReverseDaggerSpace.{u}, A ⟶ B}
    (hs : s ∈ S_rev.{u}) (a : ReverseSimplexᵒᵖ) : Mono (s.2.2.app a) :=
  (NatTrans.mono_iff_mono_app _).mp (S_rev_mono hs) a

end

end DaggerModels.PartII.SegalRepresentables
