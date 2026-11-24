import DaggerModelsPartII.ReedyDegreeFactorization

/-! Transport the relative maps along identifications of the lower diagram and new object. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ}

/-- Equality of the degree data, with the legs written in their original types. -/
structure DegreeIdentification {W Z : BelowDegree n ⥤ C}
    (E : DegreeExtension W) (F : DegreeExtension Z) where
  lower : W = Z
  obj : E.obj = F.obj
  latching : E.fromLatching ≫ eqToHom obj =
    eqToHom (congrArg (lowerLatching n).obj lower) ≫ F.fromLatching
  matching : E.toMatching ≫ eqToHom (congrArg (lowerMatching n).obj lower) =
    eqToHom obj ≫ F.toMatching

def DegreeIdentification.refl {W : BelowDegree n ⥤ C} (E : DegreeExtension W) :
    DegreeIdentification E E where
  lower := rfl
  obj := rfl
  latching := by simp
  matching := by simp

theorem DegreeIdentification.eq_of_same_lower {W : BelowDegree n ⥤ C}
    {E F : DegreeExtension W} (h : DegreeIdentification E F) : E = F := by
  cases E with
  | mk A i p hi =>
    cases F with
    | mk B j q hj =>
      have ho : A = B := h.obj
      subst B
      have hl := h.latching
      have hm := h.matching
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hl hm
      subst j
      subst q
      rfl

/-- The two relative maps are invariant under the identified degree data. -/
theorem relativeMaps_mem_iff_of_identification
    {W V W' V' : BelowDegree n ⥤ C}
    {E : DegreeExtension W} {F : DegreeExtension V}
    {E' : DegreeExtension W'} {F' : DegreeExtension V'}
    {a : W ⟶ V} {a' : W' ⟶ V'}
    (f : DegreeExtension.Hom a E F) (f' : DegreeExtension.Hom a' E' F')
    (hE : DegreeIdentification E E') (hF : DegreeIdentification F F')
    (ha : a ≫ eqToHom hF.lower = eqToHom hE.lower ≫ a')
    (hf : f.app ≫ eqToHom hF.obj = eqToHom hE.obj ≫ f'.app)
    (P Q : MorphismProperty C) :
    (P f.relativeLatching ↔ P f'.relativeLatching) ∧
      (Q f.relativeMatching ↔ Q f'.relativeMatching) := by
  have hW := hE.lower
  have hV := hF.lower
  subst W'
  subst V'
  have h := hE.eq_of_same_lower
  subst E'
  have h := hF.eq_of_same_lower
  subst F'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha hf
  subst a'
  cases f
  cases f'
  dsimp at hf
  subst hf
  exact ⟨Iff.rfl, Iff.rfl⟩

end

end DaggerModels.PartII
