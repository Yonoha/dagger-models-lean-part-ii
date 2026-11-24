import DaggerModelsPartII.ReedyExtensionIndex

/-!
# Operators determined by the degree-extension data

The lower diagram gives the action on old objects. The maps from latching
and to matching supply, respectively, the new direct and inverse operators.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ} {Z : BelowDegree n ⥤ C}

def extensionObj (E : DegreeExtension Z) : ExtensionIndex n → C
  | none => E.obj
  | some s => Z.obj s

def extensionOldArrow {s t : BelowDegree n}
    (f : extensionIndexLower s ⟶ extensionIndexLower t) : s ⟶ t :=
  ObjectProperty.homMk f.hom

def extensionMatchingIndex {t : BelowDegree n}
    (f : extensionIndexTop n ⟶ extensionIndexLower t) (hf : Mono f.hom.unop) :
    MatchingIndex n :=
  ⟨StructuredArrow.mk f.hom, ⟨t.property, hf⟩⟩

def extensionLatchingIndex {s : BelowDegree n}
    (f : extensionIndexLower s ⟶ extensionIndexTop n) (hf : Epi f.hom.unop) :
    LatchingIndex n :=
  ⟨CostructuredArrow.mk f.hom, ⟨s.property, hf⟩⟩

theorem extensionInverse_not_raise {s : BelowDegree n}
    (f : extensionIndexLower s ⟶ extensionIndexTop n) (hf : Mono f.hom.unop) : False := by
  letI := hf
  have h : n ≤ s.obj.unop.len := SimplexCategory.len_le_of_mono f.hom.unop
  exact (Nat.not_le_of_lt s.property) h

theorem extensionDirect_not_lower {t : BelowDegree n}
    (f : extensionIndexTop n ⟶ extensionIndexLower t) (hf : Epi f.hom.unop) : False := by
  letI := hf
  have h : n ≤ t.obj.unop.len := SimplexCategory.len_le_of_epi f.hom.unop
  exact (Nat.not_le_of_lt t.property) h

theorem extensionInverse_endomorphism_eq_id {s : ExtensionIndex n} (f : s ⟶ s)
    (hf : Mono f.hom.unop) : f = 𝟙 s := by
  letI := hf
  exact InducedCategory.hom_ext (Quiver.Hom.unop_inj (SimplexCategory.eq_id_of_mono f.hom.unop))

theorem extensionDirect_endomorphism_eq_id {s : ExtensionIndex n} (f : s ⟶ s)
    (hf : Epi f.hom.unop) : f = 𝟙 s := by
  letI := hf
  exact InducedCategory.hom_ext (Quiver.Hom.unop_inj (SimplexCategory.eq_id_of_epi f.hom.unop))

/-- Action on an inverse arrow. -/
def extensionInverseMap (E : DegreeExtension Z) {s t : ExtensionIndex n}
    (f : s ⟶ t) (hf : Mono f.hom.unop) : extensionObj E s ⟶ extensionObj E t := by
  cases s with
  | none =>
    cases t with
    | none => exact 𝟙 _
    | some t => exact E.toMatching ≫ limit.π (matchingBelow n ⋙ Z) (extensionMatchingIndex f hf)
  | some s =>
    cases t with
    | none => exact (extensionInverse_not_raise f hf).elim
    | some t => exact Z.map (extensionOldArrow f)

/-- Action on a direct arrow. -/
def extensionDirectMap (E : DegreeExtension Z) {s t : ExtensionIndex n}
    (f : s ⟶ t) (hf : Epi f.hom.unop) : extensionObj E s ⟶ extensionObj E t := by
  cases s with
  | none =>
    cases t with
    | none => exact 𝟙 _
    | some t => exact (extensionDirect_not_lower f hf).elim
  | some s =>
    cases t with
    | none => exact colimit.ι (latchingBelow n ⋙ Z) (extensionLatchingIndex f hf) ≫ E.fromLatching
    | some t => exact Z.map (extensionOldArrow f)

theorem extensionInverse_mono_comp {s t u : ExtensionIndex n}
    (f : s ⟶ t) (g : t ⟶ u) (hf : Mono f.hom.unop) (hg : Mono g.hom.unop) :
    Mono (f ≫ g).hom.unop := by
  letI := hf
  letI := hg
  change Mono (g.hom.unop ≫ f.hom.unop)
  infer_instance

theorem extensionDirect_epi_comp {s t u : ExtensionIndex n}
    (f : s ⟶ t) (g : t ⟶ u) (hf : Epi f.hom.unop) (hg : Epi g.hom.unop) :
    Epi (f ≫ g).hom.unop := by
  letI := hf
  letI := hg
  change Epi (g.hom.unop ≫ f.hom.unop)
  infer_instance

theorem extensionInverseMap_id (E : DegreeExtension Z) (s : ExtensionIndex n)
    (h : Mono (𝟙 s : s ⟶ s).hom.unop) : extensionInverseMap E (𝟙 s) h = 𝟙 _ := by
  cases s with
  | none => rfl
  | some s => exact Z.map_id s

theorem extensionDirectMap_id (E : DegreeExtension Z) (s : ExtensionIndex n)
    (h : Epi (𝟙 s : s ⟶ s).hom.unop) : extensionDirectMap E (𝟙 s) h = 𝟙 _ := by
  cases s with
  | none => rfl
  | some s => exact Z.map_id s

/-- The matching cone enforces composition of inverse arrows. -/
theorem extensionInverseMap_comp (E : DegreeExtension Z) {s t u : ExtensionIndex n}
    (f : s ⟶ t) (g : t ⟶ u) (hf : Mono f.hom.unop) (hg : Mono g.hom.unop) :
    extensionInverseMap E (f ≫ g) (extensionInverse_mono_comp f g hf hg) =
      extensionInverseMap E f hf ≫ extensionInverseMap E g hg := by
  cases s with
  | none =>
    cases t with
    | none =>
      have he := extensionInverse_endomorphism_eq_id f hf
      subst f
      simp only [Category.id_comp, extensionInverseMap_id]
    | some t =>
      cases u with
      | none => exact (extensionInverse_not_raise g hg).elim
      | some u =>
        let q : extensionMatchingIndex f hf ⟶
            extensionMatchingIndex (f ≫ g) (extensionInverse_mono_comp f g hf hg) :=
          ObjectProperty.homMk (StructuredArrow.homMk g.hom rfl)
        have w := limit.w (matchingBelow n ⋙ Z) q
        change limit.π (matchingBelow n ⋙ Z) (extensionMatchingIndex f hf) ≫
            Z.map (extensionOldArrow g) =
          limit.π (matchingBelow n ⋙ Z)
            (extensionMatchingIndex (f ≫ g) (extensionInverse_mono_comp f g hf hg)) at w
        change E.toMatching ≫ limit.π (matchingBelow n ⋙ Z)
            (extensionMatchingIndex (f ≫ g) (extensionInverse_mono_comp f g hf hg)) =
          (E.toMatching ≫ limit.π (matchingBelow n ⋙ Z) (extensionMatchingIndex f hf)) ≫
            Z.map (extensionOldArrow g)
        rw [Category.assoc, w]
  | some s =>
    cases t with
    | none => exact (extensionInverse_not_raise f hf).elim
    | some t =>
      cases u with
      | none => exact (extensionInverse_not_raise g hg).elim
      | some u => exact Z.map_comp (extensionOldArrow f) (extensionOldArrow g)

/-- The latching cocone enforces composition of direct arrows. -/
theorem extensionDirectMap_comp (E : DegreeExtension Z) {s t u : ExtensionIndex n}
    (f : s ⟶ t) (g : t ⟶ u) (hf : Epi f.hom.unop) (hg : Epi g.hom.unop) :
    extensionDirectMap E (f ≫ g) (extensionDirect_epi_comp f g hf hg) =
      extensionDirectMap E f hf ≫ extensionDirectMap E g hg := by
  cases s with
  | none =>
    cases t with
    | none =>
      have he := extensionDirect_endomorphism_eq_id f hf
      subst f
      simp only [Category.id_comp, extensionDirectMap_id]
    | some t => exact (extensionDirect_not_lower f hf).elim
  | some s =>
    cases t with
    | none =>
      cases u with
      | none =>
        have he := extensionDirect_endomorphism_eq_id g hg
        subst g
        simp only [Category.comp_id, extensionDirectMap_id]
      | some u => exact (extensionDirect_not_lower g hg).elim
    | some t =>
      cases u with
      | none =>
        let q : extensionLatchingIndex (f ≫ g) (extensionDirect_epi_comp f g hf hg) ⟶
            extensionLatchingIndex g hg :=
          ObjectProperty.homMk (CostructuredArrow.homMk f.hom rfl)
        have w := colimit.w (latchingBelow n ⋙ Z) q
        change Z.map (extensionOldArrow f) ≫
            colimit.ι (latchingBelow n ⋙ Z) (extensionLatchingIndex g hg) =
          colimit.ι (latchingBelow n ⋙ Z)
            (extensionLatchingIndex (f ≫ g) (extensionDirect_epi_comp f g hf hg)) at w
        change colimit.ι (latchingBelow n ⋙ Z)
            (extensionLatchingIndex (f ≫ g) (extensionDirect_epi_comp f g hf hg)) ≫ E.fromLatching =
          Z.map (extensionOldArrow f) ≫
            colimit.ι (latchingBelow n ⋙ Z) (extensionLatchingIndex g hg) ≫ E.fromLatching
        rw [← Category.assoc, w]
      | some u => exact Z.map_comp (extensionOldArrow f) (extensionOldArrow g)

/-- A new degeneracy followed by a new face acts by the lower composite. -/
theorem extensionDirect_inverse_through_top (E : DegreeExtension Z) {s t : BelowDegree n}
    (f : extensionIndexLower s ⟶ extensionIndexTop n)
    (g : extensionIndexTop n ⟶ extensionIndexLower t)
    (hf : Epi f.hom.unop) (hg : Mono g.hom.unop) :
    extensionDirectMap E f hf ≫ extensionInverseMap E g hg = Z.map (extensionOldArrow (f ≫ g)) := by
  change (colimit.ι (latchingBelow n ⋙ Z) (extensionLatchingIndex f hf) ≫ E.fromLatching) ≫
      E.toMatching ≫ limit.π (matchingBelow n ⋙ Z) (extensionMatchingIndex g hg) = _
  rw [Category.assoc, ← Category.assoc E.fromLatching, E.boundary]
  simp only [lowerBoundaryMap, colimit.ι_desc_assoc, lowerBoundaryCocone, limit.lift_π]
  rfl

end

end DaggerModels.PartII
