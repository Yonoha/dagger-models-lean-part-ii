import DaggerModelsPartII.JTCommonCoefficientPrism
import DaggerModelsPartII.JTCommonCoefficientLiftChoices
import DaggerModelsPartII.JTPrismTimeFaceExtension
import DaggerModelsPartII.JTFiniteSubcomplexPreimageGluing
import DaggerModelsPartII.JTInterleavedTimeFace

/-! The actual time boundary in the ordered common-base parameter. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)
open SSet.Subcomplex

noncomputable section

variable {b : SimplexCategory} {k : ℕ} (c : ⦋k⦌ ⟶ b) (n : ℕ)

private abbrev simple (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m
private abbrev one := (Δ[0] : SSet.{0})
private abbrev term (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

private def timeVertices (S : Finset (Fin (n + 1))) :=
  (Finset.univ : Finset (Fin ((common ⦋k⦌ ⦋n⦌).len + 1))).filter
    (fun a ↦ ((vertexEquiv c ⦋n⦌).symm a).2 ∈ S)

/-- The face consisting of the common-base vertices with the prescribed times. -/
def timeFace (S : Finset (Fin (n + 1))) : (simple (common ⦋k⦌ ⦋n⦌)).Subcomplex :=
  SSet.stdSimplex.face (timeVertices c n S)

private theorem mem_timeFace (S : Finset (Fin (n + 1))) {m : ℕ}
    (z : (simple (common ⦋k⦌ ⦋n⦌)).obj (op ⦋m⦌)) :
    z ∈ (timeFace c n S).obj _ ↔
      ∀ a : Fin (m + 1), ((vertexEquiv c ⦋n⦌).symm
        ((SSet.stdSimplex.objEquiv z).toOrderHom a)).2 ∈ S := by
  change z ∈ (SSet.stdSimplex.face (timeVertices c n S)).obj _ ↔ _
  rw [SSet.stdSimplex.mem_face_iff]
  simp only [timeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- The genuine preimage is the product with the ordinary time face,
including when the coefficient map is a noninjective ordinal operator. -/
theorem timeFace_preimage (S : Finset (Fin (n + 1))) :
    (timeFace c n S).preimage (prism c ⦋n⦌) =
      (⊤ : (simple ⦋k⦌).Subcomplex).prod (SSet.stdSimplex.face S) := by
  ext q z
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ m =>
      rw [preimage_obj, Set.mem_preimage, mem_timeFace]
      change (∀ a : Fin (m + 1), ((vertexEquiv c ⦋n⦌).symm
          ((SSet.stdSimplex.objEquiv ((prism c ⦋n⦌).app _ z)).toOrderHom a)).2 ∈ S) ↔
        z.1 ∈ (⊤ : (simple ⦋k⦌).Subcomplex).obj _ ∧
          z.2 ∈ (SSet.stdSimplex.face S).obj (op ⦋m⦌)
      rw [SSet.stdSimplex.mem_face_iff]
      have h (a : Fin (m + 1)) :
          ((vertexEquiv c ⦋n⦌).symm
            ((SSet.stdSimplex.objEquiv ((prism c ⦋n⦌).app (op ⦋m⦌) z)).toOrderHom a)).2 =
            z.2 a := by
        have h₁ := congrArg (fun v ↦ ((vertexEquiv c ⦋n⦌).symm v).2)
          (prism_apply k n m c z a)
        exact h₁.trans (congrArg Prod.snd (Equiv.symm_apply_apply _ _))
      simp only [h, Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and]


theorem timeFace_inf (S T : Finset (Fin (n + 1))) :
    timeFace c n (S ⊓ T) = timeFace c n S ⊓ timeFace c n T := by
  unfold timeFace
  rw [SSet.stdSimplex.face_inter_face]
  congr 1
  ext a
  simp [timeVertices]

private theorem timeFace_univ : timeFace c n Finset.univ = ⊤ := by
  ext q z
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ m =>
      rw [mem_timeFace]
      simp

private theorem timeFace_finset_inf {ι : Type} (s : Finset ι) (F : ι → Finset (Fin (n + 1))) :
    timeFace c n (s.inf F) = s.inf (fun i ↦ timeFace c n (F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.inf_empty] using timeFace_univ c n
  | @insert i s hi ih =>
      simp only [Finset.inf_insert, timeFace_inf, ih]

private theorem face_point_weak {m : ℕ} (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    WeakEquivalence (term ((SSet.stdSimplex.face S : (simple ⦋m⦌).Subcomplex).toSSet)) := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hS.card_ne_zero
  let a := SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy S l (Finset.orderIsoOfFin S hl))
  let p : simple ⦋l⦌ ⟶ one := SSet.stdSimplex.map (SimplexCategory.const ⦋l⦌ ⦋0⦌ 0)
  letI : WeakEquivalence p := JTInterleavedParameter.standardMap_weak _
  exact weakEquivalence_of_precomp_of_fac (SSet.stdSimplex.isTerminalObj₀.hom_ext
    (a.hom ≫ term _) p)

private theorem timeFace_point_weak (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    WeakEquivalence (term (timeFace c n S).toSSet) := by
  obtain ⟨t, ht⟩ := hS
  have hv : (timeVertices c n S).Nonempty := by
    refine ⟨vertexEquiv c ⦋n⦌ (0, t), ?_⟩
    simpa [timeVertices] using ht
  exact face_point_weak _ hv

private theorem timeFace_empty (z : (timeFace c n ∅).toSSet.obj (op ⦋0⦌)) : False :=
  False.elim (by simpa using (mem_timeFace c n ∅ z.val).mp z.property (0 : Fin 1))

private theorem empty_weak :
    WeakEquivalence ((timeFace c n ∅).fromPreimage (prism c ⦋n⦌)) := by
  haveI : IsIso ((timeFace c n ∅).fromPreimage (prism c ⦋n⦌)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro q
    apply (isIso_iff_bijective _).2
    have h : IsEmpty ((timeFace c n ∅).toSSet.obj q) := by
      rcases q with ⟨q⟩
      exact ⟨fun z ↦ timeFace_empty c n
        ((timeFace c n ∅).toSSet.map (SimplexCategory.const ⦋0⦌ q 0).op z)⟩
    letI := h
    constructor
    · intro a _ _
      exact isEmptyElim (((timeFace c n ∅).fromPreimage (prism c ⦋n⦌)).app q a)
    · intro a
      exact isEmptyElim a
  infer_instance

/-- The comparison of each time face and its actual prism preimage is Kan weak. -/
theorem timeFaceComparison_weak (S : Finset (Fin (n + 1))) :
    WeakEquivalence ((timeFace c n S).fromPreimage (prism c ⦋n⦌)) := by
  by_cases hS : S.Nonempty
  · let e := JTPrismTimeFaceExtension.preimageIso (prism c ⦋n⦌)
      (timeFace c n S) (SSet.stdSimplex.face S) (timeFace_preimage c n S)
    let A := (SSet.stdSimplex.face S : (simple ⦋n⦌).Subcomplex).toSSet
    let p := snd (simple ⦋k⦌) A
    letI : WeakEquivalence p := DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence k _
    letI : WeakEquivalence (term A) := face_point_weak S hS
    haveI : WeakEquivalence (term ((timeFace c n S).preimage (prism c ⦋n⦌)).toSSet) :=
      weakEquivalence_of_precomp_of_fac (SSet.stdSimplex.isTerminalObj₀.hom_ext
        (e.hom ≫ term _) (p ≫ term A))
    letI : WeakEquivalence (term (timeFace c n S).toSSet) := timeFace_point_weak c n S hS
    exact weakEquivalence_of_postcomp_of_fac (SSet.stdSimplex.isTerminalObj₀.hom_ext
      (((timeFace c n S).fromPreimage (prism c ⦋n⦌)) ≫ term _) (term _))
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact empty_weak c n

/-- The enlarged time boundary is the union of its actual faces. -/
def timeBoundary : (simple (common ⦋k⦌ ⦋n⦌)).Subcomplex :=
  Finset.univ.sup (fun a : Fin (n + 1) ↦ timeFace c n (Finset.univ.erase a))

/-- The full time boundary is weakly equivalent to its original prism preimage. -/
theorem timeBoundary_fromPreimage_weak :
    WeakEquivalence ((timeBoundary c n).fromPreimage (prism c ⦋n⦌)) := by
  apply JTFiniteSubcomplexPreimageGluing.weak_finset_sup
  intro s _ _
  rw [← timeFace_finset_inf]
  exact timeFaceComparison_weak c n _


section TimeOperator

variable {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)

/-- Restrict the time parameter at a fixed supported coefficient. -/
def timeOperator : common ⦋k⦌ ⦋m⦌ ⟶ common ⦋k⦌ ⦋n⦌ :=
  map (𝟙 ⦋k⦌) (Category.id_comp c) j hj

private theorem timeOperator_vertex (x : Fin (k + 1) × Fin (m + 1)) :
    (timeOperator c n j hj).toOrderHom (vertexEquiv c ⦋m⦌ x) =
      vertexEquiv c ⦋n⦌ (x.1, j.toOrderHom x.2) := by
  unfold timeOperator
  rw [map_vertexEquiv]
  rfl

private theorem timeOperator_injective : Function.Injective (timeOperator c n j hj).toOrderHom := by
  intro u v h
  obtain ⟨u, rfl⟩ := (vertexEquiv c ⦋m⦌).surjective u
  obtain ⟨v, rfl⟩ := (vertexEquiv c ⦋m⦌).surjective v
  rw [timeOperator_vertex, timeOperator_vertex] at h
  have hp := (vertexEquiv c ⦋n⦌).injective h
  have h₁ := congrArg (fun p : Fin (k + 1) × Fin (n + 1) ↦ p.1) hp
  have h₂ := congrArg (fun p : Fin (k + 1) × Fin (n + 1) ↦ p.2) hp
  exact congrArg (vertexEquiv c ⦋m⦌) (Prod.ext h₁ (hj h₂))

private abbrev timeImage : Finset (Fin (n + 1)) := Finset.univ.image j.toOrderHom

private theorem timeOperator_range :
    Set.range (timeOperator c n j hj).toOrderHom = (timeVertices c n (timeImage n j) : Set _) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨u, rfl⟩ := (vertexEquiv c ⦋m⦌).surjective u
    rw [timeOperator_vertex]
    simp [timeVertices, timeImage]
  · intro hv
    obtain ⟨⟨a, t⟩, rfl⟩ := (vertexEquiv c ⦋n⦌).surjective v
    have ht : t ∈ timeImage n j := by simpa [timeVertices] using hv
    obtain ⟨t', _, he⟩ := Finset.mem_image.mp ht
    exact ⟨vertexEquiv c ⦋m⦌ (a, t'), (timeOperator_vertex c n j hj _).trans
      (congrArg (fun t ↦ vertexEquiv c ⦋n⦌ (a, t)) he)⟩

private def timeOperatorOrderEmbedding :
    Fin ((common ⦋k⦌ ⦋m⦌).len + 1) ↪o Fin ((common ⦋k⦌ ⦋n⦌).len + 1) :=
  OrderEmbedding.ofStrictMono (timeOperator c n j hj).toOrderHom
    ((timeOperator c n j hj).toOrderHom.monotone.strictMono_of_injective (timeOperator_injective c n j hj))

private def timeVerticesOrderIso :
    Fin ((common ⦋k⦌ ⦋m⦌).len + 1) ≃o timeVertices c n (timeImage n j) :=
  (timeOperatorOrderEmbedding c n j hj).orderIso.trans
    (OrderIso.setCongr _ _ (by
      simpa only [timeOperatorOrderEmbedding, OrderEmbedding.coe_ofStrictMono] using
        timeOperator_range c n j hj))

/-- The enlarged time operator embeds its entire simplex as the corresponding
face, with the actual vertex order of the common coefficient. -/
theorem timeOperator_face :
    SSet.Subcomplex.range (SSet.stdSimplex.{0}.map (timeOperator c n j hj)) =
      timeFace c n (Finset.univ.image j.toOrderHom) := by
  rw [SSet.Subcomplex.range_eq_ofSimplex, timeFace,
    SSet.stdSimplex.face_eq_ofSimplex _ _ (timeVerticesOrderIso c n j hj)]
  congr 1

end TimeOperator

section TimeFaceGeometry

open JTHigherInterleavedParameter (timeDegree timeInclusion timeInclusion_injective
  timeInclusion_range stdSimplex_map_mono_of_mono)

/-- The time boundary is covered by its genuine codimension-one faces. -/
theorem timeBoundary_eq_iSup :
    timeBoundary c n = ⨆ a : Fin (n + 1), timeFace c n (Finset.univ.erase a) :=
  Finset.sup_univ_eq_iSup _

/-- Restricting the set of times restricts the corresponding face. -/
theorem timeFace_mono {S T : Finset (Fin (n + 1))} (h : S ⊆ T) :
    timeFace c n S ≤ timeFace c n T := by
  have he : S ⊓ T = S := inf_eq_left.mpr h
  have ht := timeFace_inf c n S T
  rw [he] at ht
  exact inf_eq_left.mp ht.symm

/-- Empty time supports give the empty simplicial face. -/
theorem timeFace_eq_bot (S : Finset (Fin (n + 1))) (hS : ¬ S.Nonempty) :
    timeFace c n S = ⊥ := by
  have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
  subst S
  ext q x
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ d =>
      constructor
      · intro hx
        have h := (mem_timeFace c n ∅ x).1 hx
        simpa using h (0 : Fin (d + 1))
      · intro hx
        exact False.elim hx

theorem timeOperator_comp {l m : ℕ} (a : ⦋l⦌ ⟶ ⦋m⦌) (j : ⦋m⦌ ⟶ ⦋n⦌)
    (ha : Function.Injective a.toOrderHom) (hj : Function.Injective j.toOrderHom) :
    timeOperator c n (a ≫ j) (hj.comp ha) =
      timeOperator c m a ha ≫ timeOperator c n j hj := by
  unfold timeOperator
  rw [← map_comp]
  simp only [Category.id_comp]

private theorem timeInclusion_image (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    Finset.univ.image (timeInclusion S hS).toOrderHom = S := by
  ext a
  rw [Finset.mem_image]
  change (∃ v, v ∈ Finset.univ ∧ (timeInclusion S hS).toOrderHom v = a) ↔ a ∈ S
  simp only [Finset.mem_univ, true_and]
  exact Set.ext_iff.mp (timeInclusion_range S hS) a

/-- The enlarged simplex on a nonempty time support identifies with the whole face. -/
def timeFaceIso (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    simple (common ⦋k⦌ (timeDegree S)) ≅ (timeFace c n S).toSSet := by
  let j := timeInclusion S hS
  let a := timeOperator c n j (timeInclusion_injective S hS)
  letI : Mono a := SimplexCategory.mono_iff_injective.mpr
    (timeOperator_injective c n j (timeInclusion_injective S hS))
  let f : simple (common ⦋k⦌ (timeDegree S)) ⟶ simple (common ⦋k⦌ ⦋n⦌) :=
    SSet.stdSimplex.map a
  letI : Mono f := stdSimplex_map_mono_of_mono a
  have h : SSet.Subcomplex.range f = timeFace c n S := by
    change SSet.Subcomplex.range (SSet.stdSimplex.{0}.map
      (timeOperator c n (timeInclusion S hS) (timeInclusion_injective S hS))) = _
    rw [timeOperator_face]
    exact congrArg (timeFace c n) (timeInclusion_image n S hS)
  exact asIso (SSet.Subcomplex.toRange f) ≪≫ SSet.Subcomplex.eqToIso h

/-- The face comparison uses the original injective operator on the whole simplex. -/
theorem timeFaceIso_ι (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    (timeFaceIso c n S hS).hom ≫ (timeFace c n S).ι =
      SSet.stdSimplex.map
        (timeOperator c n (timeInclusion S hS) (timeInclusion_injective S hS)) := by
  simp [timeFaceIso, Category.assoc]

end TimeFaceGeometry

section Relative

open JTFixedLiftSpaceTimeEquiv
variable {A X Y : SSet.{0}} {i : A ⟶ simple ⦋k⦌}
variable {t : A ⟶ X} {p : X ⟶ Y} [Fibration p] {g : simple b ⟶ Y}
variable (sq : CommSq t i p (SSet.stdSimplex.map c ≫ g))

/-- Retain the original normalization simplex and its prescribed compatible
enlarged time boundary during extension over the whole common coefficient. -/
theorem exists_extension_relative
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋n⦌))
    (G : (timeBoundary c n).toSSet ⟶ X)
    (hG : G ≫ p = (timeBoundary c n).ι ≫ SSet.stdSimplex.map (base c ⦋n⦌) ≫ g)
    (hV : ((timeBoundary c n).preimage (prism c ⦋n⦌)).ι ≫ timeMap sq ⦋n⦌ v =
      (timeBoundary c n).fromPreimage (prism c ⦋n⦌) ≫ G) :
    ∃ E : JTCommonCoefficientLiftChoices.Extension sq ⦋n⦌,
      prism c ⦋n⦌ ≫ E.map = timeMap sq ⦋n⦌ v ∧ (timeBoundary c n).ι ≫ E.map = G := by
  letI := prism_weak.{0} c ⦋n⦌
  have hv : timeMap sq ⦋n⦌ v ≫ p =
      prism c ⦋n⦌ ≫ SSet.stdSimplex.map (base c ⦋n⦌) ≫ g := by
    rw [← Category.assoc (prism c ⦋n⦌), prism_base, Category.assoc]
    exact (timeMap_conditions sq ⦋n⦌ v).2
  obtain ⟨L, hL, hF, hq⟩ := JTPrismSubcomplexExtension.exists_extension
    (prism c ⦋n⦌) (timeBoundary c n) (timeBoundary_fromPreimage_weak c n)
    (SSet.stdSimplex.map (base c ⦋n⦌) ≫ g) (timeMap sq ⦋n⦌ v) G hv hG hV
  refine ⟨⟨L, ?_, hq⟩, hL, hF⟩
  rw [hL]
  exact (timeMap_conditions sq ⦋n⦌ v).1

end Relative

end
end DaggerModels.PartII.JTCommonCoefficientParameter
