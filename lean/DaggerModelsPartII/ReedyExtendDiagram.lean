import DaggerModelsPartII.ReedyExtensionOperators

/-!
# Extending the simplicial diagram through one degree

Map an arbitrary operator by its inverse/direct factorization. Composition
uses the inverse and direct composition laws and the boundary compatibility
for a direct operator followed by an inverse operator.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ} {Z : BelowDegree n ⥤ C}
  (E : DegreeExtension Z)

/-- Action on an arbitrary operator in the extended index. -/
def extensionMap {s t : ExtensionIndex n} (f : s ⟶ t) :
    extensionObj E s ⟶ extensionObj E t :=
  let F := extensionIndexFactor f
  extensionInverseMap E F.inverse F.inverse_mono ≫ extensionDirectMap E F.direct F.direct_epi

theorem extensionMap_of_factor {s t : ExtensionIndex n} {f : s ⟶ t}
    (F : ExtensionIndexFactor f) :
    extensionMap E f =
      extensionInverseMap E F.inverse F.inverse_mono ≫
        extensionDirectMap E F.direct F.direct_epi :=
  congrArg (fun F : ExtensionIndexFactor f ↦
    extensionInverseMap E F.inverse F.inverse_mono ≫ extensionDirectMap E F.direct F.direct_epi)
    (Subsingleton.elim (extensionIndexFactor f) F)

theorem extensionMap_of_inverse {s t : ExtensionIndex n} (f : s ⟶ t) (hf : Mono f.hom.unop) :
    extensionMap E f = extensionInverseMap E f hf := by
  have hId : Epi (𝟙 t : t ⟶ t).hom.unop := by
    change Epi (𝟙 (extensionIndexObj n t).unop)
    infer_instance
  let F : ExtensionIndexFactor f := ⟨t, f, 𝟙 t, hf, hId, Category.comp_id f⟩
  rw [extensionMap_of_factor E F]
  change extensionInverseMap E f hf ≫ extensionDirectMap E (𝟙 t) hId = _
  rw [extensionDirectMap_id, Category.comp_id]

theorem extensionMap_of_direct {s t : ExtensionIndex n} (f : s ⟶ t) (hf : Epi f.hom.unop) :
    extensionMap E f = extensionDirectMap E f hf := by
  have hId : Mono (𝟙 s : s ⟶ s).hom.unop := by
    change Mono (𝟙 (extensionIndexObj n s).unop)
    infer_instance
  let F : ExtensionIndexFactor f := ⟨s, 𝟙 s, f, hId, hf, Category.id_comp f⟩
  rw [extensionMap_of_factor E F]
  change extensionInverseMap E (𝟙 s) hId ≫ extensionDirectMap E f hf = _
  rw [extensionInverseMap_id, Category.id_comp]

/-- In the old degrees the map is the map of the lower diagram. -/
theorem extensionMap_old {s t : BelowDegree n}
    (f : extensionIndexLower s ⟶ extensionIndexLower t) :
    extensionMap E f = Z.map (extensionOldArrow f) := by
  let F := extensionIndexFactor f
  rw [extensionMap_of_factor E F]
  obtain ⟨m, l, r, hl, hr, h⟩ := F
  cases m with
  | none => exact (extensionInverse_not_raise l hl).elim
  | some m =>
    change Z.map (extensionOldArrow l) ≫ Z.map (extensionOldArrow r) =
      Z.map (extensionOldArrow f)
    rw [← Z.map_comp]
    exact congrArg Z.map (congrArg extensionOldArrow h)

/-- A direct arrow followed by an inverse arrow acts by the normalized composite. -/
theorem extensionDirect_inverse_eq_map {s t u : ExtensionIndex n}
    (f : s ⟶ t) (g : t ⟶ u) (hf : Epi f.hom.unop) (hg : Mono g.hom.unop) :
    extensionDirectMap E f hf ≫ extensionInverseMap E g hg = extensionMap E (f ≫ g) := by
  cases t with
  | none =>
    cases s with
    | none =>
      have he := extensionDirect_endomorphism_eq_id f hf
      subst f
      simp only [extensionDirectMap_id, Category.id_comp, extensionMap_of_inverse E g hg]
    | some s =>
      cases u with
      | none =>
        have he := extensionInverse_endomorphism_eq_id g hg
        subst g
        simp only [extensionInverseMap_id, Category.comp_id, extensionMap_of_direct E f hf]
      | some u =>
        exact (extensionDirect_inverse_through_top E f g hf hg).trans
          (extensionMap_old E (f ≫ g)).symm
  | some t =>
    cases s with
    | none => exact (extensionDirect_not_lower f hf).elim
    | some s =>
      cases u with
      | none => exact (extensionInverse_not_raise g hg).elim
      | some u =>
        exact (Z.map_comp (extensionOldArrow f) (extensionOldArrow g)).symm.trans
          (extensionMap_old E (f ≫ g)).symm

theorem extensionMap_id (s : ExtensionIndex n) : extensionMap E (𝟙 s) = 𝟙 _ := by
  have h : Mono (𝟙 s : s ⟶ s).hom.unop := by
    change Mono (𝟙 (extensionIndexObj n s).unop)
    infer_instance
  rw [extensionMap_of_inverse E (𝟙 s) h, extensionInverseMap_id]

/-- Composition follows from normalizing the middle direct/inverse pair. -/
theorem extensionMap_comp {s t u : ExtensionIndex n} (f : s ⟶ t) (g : t ⟶ u) :
    extensionMap E (f ≫ g) = extensionMap E f ≫ extensionMap E g := by
  let F := extensionIndexFactor f
  let G := extensionIndexFactor g
  let H := extensionIndexFactor (F.direct ≫ G.inverse)
  let K : ExtensionIndexFactor (f ≫ g) :=
    ⟨H.mid, F.inverse ≫ H.inverse, H.direct ≫ G.direct,
      extensionInverse_mono_comp _ _ F.inverse_mono H.inverse_mono,
      extensionDirect_epi_comp _ _ H.direct_epi G.direct_epi, by
        calc
          (F.inverse ≫ H.inverse) ≫ (H.direct ≫ G.direct) =
              F.inverse ≫ (H.inverse ≫ H.direct) ≫ G.direct := by simp only [Category.assoc]
          _ = (F.inverse ≫ F.direct) ≫ (G.inverse ≫ G.direct) := by
            rw [H.fac]
            simp only [Category.assoc]
          _ = f ≫ g := by rw [F.fac, G.fac]⟩
  have hm : extensionInverseMap E H.inverse H.inverse_mono ≫
      extensionDirectMap E H.direct H.direct_epi =
      extensionDirectMap E F.direct F.direct_epi ≫ extensionInverseMap E G.inverse G.inverse_mono :=
    (extensionMap_of_factor E H).symm.trans
      (extensionDirect_inverse_eq_map E _ _ F.direct_epi G.inverse_mono).symm
  rw [extensionMap_of_factor E K]
  change extensionInverseMap E (F.inverse ≫ H.inverse) _ ≫
    extensionDirectMap E (H.direct ≫ G.direct) _ = _
  rw [extensionInverseMap_comp E F.inverse H.inverse F.inverse_mono H.inverse_mono,
    extensionDirectMap_comp E H.direct G.direct H.direct_epi G.direct_epi]
  calc
    (extensionInverseMap E F.inverse F.inverse_mono ≫
        extensionInverseMap E H.inverse H.inverse_mono) ≫
      (extensionDirectMap E H.direct H.direct_epi ≫
        extensionDirectMap E G.direct G.direct_epi) =
        extensionInverseMap E F.inverse F.inverse_mono ≫
          (extensionInverseMap E H.inverse H.inverse_mono ≫
            extensionDirectMap E H.direct H.direct_epi) ≫
          extensionDirectMap E G.direct G.direct_epi := by simp only [Category.assoc]
    _ = extensionMap E f ≫ extensionMap E g := by
      rw [hm, extensionMap_of_factor E F, extensionMap_of_factor E G]
      simp only [Category.assoc]

/-- The degree extension defines a genuine functor on the extended index. -/
def extendedDiagram : ExtensionIndex n ⥤ C where
  obj := extensionObj E
  map := extensionMap E
  map_id := extensionMap_id E
  map_comp := extensionMap_comp E

section NaturalTransformation

variable {T : BelowDegree n ⥤ C} {F : DegreeExtension T} {a : Z ⟶ T}
  (f : DegreeExtension.Hom a E F)

def extensionTransformationApp :
    (s : ExtensionIndex n) → extensionObj E s ⟶ extensionObj F s
  | none => f.app
  | some s => a.app s

theorem extensionTransformation_natural_inverse {s t : ExtensionIndex n}
    (g : s ⟶ t) (hg : Mono g.hom.unop) :
    extensionInverseMap E g hg ≫ extensionTransformationApp E f t =
      extensionTransformationApp E f s ≫ extensionInverseMap F g hg := by
  cases s with
  | none =>
    cases t with
    | none => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | some t =>
      let j := extensionMatchingIndex g hg
      have h := congrArg (fun k ↦ k ≫ limit.π (matchingBelow n ⋙ T) j)
        f.matching_naturality
      change (f.app ≫ F.toMatching) ≫ limit.π _ j =
        (E.toMatching ≫ limMap (Functor.whiskerLeft (matchingBelow n) a)) ≫ limit.π _ j at h
      simp only [Category.assoc, limMap_π] at h
      exact (Category.assoc _ _ _).trans h.symm
  | some s =>
    cases t with
    | none => exact (extensionInverse_not_raise g hg).elim
    | some t => exact a.naturality (extensionOldArrow g)

theorem extensionTransformation_natural_direct {s t : ExtensionIndex n}
    (g : s ⟶ t) (hg : Epi g.hom.unop) :
    extensionDirectMap E g hg ≫ extensionTransformationApp E f t =
      extensionTransformationApp E f s ≫ extensionDirectMap F g hg := by
  cases s with
  | none =>
    cases t with
    | none => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | some t => exact (extensionDirect_not_lower g hg).elim
  | some s =>
    cases t with
    | none =>
      let j := extensionLatchingIndex g hg
      have h := congrArg (fun k ↦ colimit.ι (latchingBelow n ⋙ Z) j ≫ k)
        f.latching_naturality
      change colimit.ι _ j ≫ colimMap (Functor.whiskerLeft (latchingBelow n) a) ≫ F.fromLatching =
        colimit.ι _ j ≫ E.fromLatching ≫ f.app at h
      simp only [ι_colimMap_assoc] at h
      exact (Category.assoc _ _ _).trans h.symm
    | some t => exact a.naturality (extensionOldArrow g)

/-- Compatible degree maps give natural transformations of the extended diagrams. -/
def extendedTransformation : extendedDiagram E ⟶ extendedDiagram F where
  app := extensionTransformationApp E f
  naturality s t g := by
    let G := extensionIndexFactor g
    change extensionMap E g ≫ extensionTransformationApp E f t =
      extensionTransformationApp E f s ≫ extensionMap F g
    rw [extensionMap_of_factor E G, extensionMap_of_factor F G, Category.assoc,
      extensionTransformation_natural_direct E f G.direct G.direct_epi,
      ← Category.assoc (extensionInverseMap E G.inverse G.inverse_mono),
      extensionTransformation_natural_inverse E f G.inverse G.inverse_mono, Category.assoc]

end NaturalTransformation

end

end DaggerModels.PartII
