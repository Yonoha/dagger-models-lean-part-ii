import DaggerModelsPartII.JTHigherInterleavedOperators
import Mathlib.Data.Finset.Sort

/-!
# Faces in the time coordinate of an interleaved parameter

The face `timeFace k n S` retains precisely those vertices whose time
coordinate belongs to `S`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTHigherInterleavedParameter

noncomputable section

/-- The vertices of the common simplex with time coordinate in `S`. -/
def timeVertices (k n : ℕ) (S : Finset (Fin (n + 1))) :
    Finset (Fin ((common ⦋k⦌ ⦋n⦌).len + 1)) :=
  Finset.univ.filter (fun v ↦ ((vertexEquiv ⦋k⦌ ⦋n⦌).symm v).2 ∈ S)

/-- The face supported on a set of time vertices. -/
def timeFace (k n : ℕ) (S : Finset (Fin (n + 1))) :
    (SSet.stdSimplex.obj (common ⦋k⦌ ⦋n⦌) : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face (timeVertices k n S)

@[simp] theorem mem_timeVertices (k n : ℕ) (S : Finset (Fin (n + 1)))
    (v : Fin ((common ⦋k⦌ ⦋n⦌).len + 1)) :
    v ∈ timeVertices k n S ↔ ((vertexEquiv ⦋k⦌ ⦋n⦌).symm v).2 ∈ S := by
  simp [timeVertices]

@[simp] theorem mem_timeVertices_vertexEquiv (k n : ℕ) (S : Finset (Fin (n + 1)))
    (a : Fin (k + 1)) (t : Fin (n + 1)) :
    vertexEquiv ⦋k⦌ ⦋n⦌ (a, t) ∈ timeVertices k n S ↔ t ∈ S := by
  simp

theorem timeVertices_inf (k n : ℕ) (S T : Finset (Fin (n + 1))) :
    timeVertices k n (S ⊓ T) = timeVertices k n S ⊓ timeVertices k n T := by
  ext v
  simp

@[simp] theorem timeVertices_empty (k n : ℕ) :
    timeVertices k n (∅ : Finset (Fin (n + 1))) = ∅ := by
  ext v
  simp

/-- The simplex degree of a nonempty finite time face. -/
def timeDegree {n : ℕ} (S : Finset (Fin (n + 1))) : SimplexCategory :=
  ⦋S.card - 1⦌

private theorem timeCard {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    S.card = (timeDegree S).len + 1 := by
  change S.card = S.card - 1 + 1
  have := Finset.card_pos.mpr hS
  omega

/-- The order preserving enumeration of a nonempty time face. -/
def timeInclusion {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    timeDegree S ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    ((S.orderEmbOfFin (timeCard S hS)).toOrderHom)

theorem timeInclusion_range {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    Set.range (timeInclusion S hS).toOrderHom = (S : Set (Fin (n + 1))) := by
  unfold timeInclusion
  exact Finset.range_orderEmbOfFin S (timeCard S hS)

theorem timeInclusion_injective {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) : Function.Injective (timeInclusion S hS).toOrderHom := by
  change Function.Injective (S.orderEmbOfFin (timeCard S hS))
  exact (S.orderEmbOfFin (timeCard S hS)).injective

theorem mapTime_injective (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) (hf : Function.Injective f.toOrderHom) :
    Function.Injective (mapTime k f).toOrderHom := by
  intro v w h
  obtain ⟨x, rfl⟩ := (vertexEquiv k n).surjective v
  obtain ⟨y, rfl⟩ := (vertexEquiv k n).surjective w
  simp only [mapTime_vertexEquiv] at h
  have hp := (vertexEquiv k m).injective h
  have hfst : x.1 = y.1 := congrArg (fun z ↦ z.1) hp
  have hsnd : f.toOrderHom x.2 = f.toOrderHom y.2 := congrArg (fun z ↦ z.2) hp
  apply congrArg (vertexEquiv k n)
  exact Prod.ext hfst (hf hsnd)

instance mapTime_mono_of_mono (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) [Mono f] : Mono (mapTime k f) :=
  SimplexCategory.mono_iff_injective.mpr
    (mapTime_injective k f (SimplexCategory.mono_iff_injective.mp inferInstance))

instance timeInclusion_mono {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) : Mono (timeInclusion S hS) :=
  SimplexCategory.mono_iff_injective.mpr (timeInclusion_injective S hS)

instance stdSimplex_map_mono_of_mono {n m : SimplexCategory}
    (f : n ⟶ m) [Mono f] :
    Mono (SSet.stdSimplex.map f : SSet.stdSimplex.obj n ⟶
      (SSet.stdSimplex.obj m : SSet.{u})) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y h
  apply SSet.stdSimplex.objEquiv.injective
  apply (cancel_mono f).1
  exact congrArg SSet.stdSimplex.objEquiv h

instance stdSimplex_mapTime_mono (k : SimplexCategory) {n m : SimplexCategory}
    (f : n ⟶ m) [Mono f] : Mono (SSet.stdSimplex.map (mapTime k f) :
      SSet.stdSimplex.obj (common k n) ⟶ (SSet.stdSimplex.obj (common k m) : SSet.{u})) := by
  infer_instance

instance whiskerLeft_timeInclusion_mono (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    Mono ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y h
  change (x.1, (SSet.stdSimplex.map (timeInclusion S hS)).app q x.2) =
    (y.1, (SSet.stdSimplex.map (timeInclusion S hS)).app q y.2) at h
  apply Prod.ext
  · exact congrArg (fun z ↦ z.1) h
  · apply (mono_iff_injective _).mp
      (inferInstance : Mono ((SSet.stdSimplex.map (timeInclusion S hS) :
        SSet.stdSimplex.obj (timeDegree S) ⟶
          (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u})).app q))
    exact congrArg (fun z ↦ z.2) h

theorem mapTime_timeInclusion_range (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    Set.range (mapTime ⦋k⦌ (timeInclusion S hS)).toOrderHom =
      (timeVertices k n S : Set (Fin ((common ⦋k⦌ ⦋n⦌).len + 1))) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := (vertexEquiv ⦋k⦌ (timeDegree S)).surjective w
    rw [mapTime_vertexEquiv]
    change vertexEquiv ⦋k⦌ ⦋n⦌ (x.1, (timeInclusion S hS).toOrderHom x.2) ∈
      timeVertices k n S
    simp only [mem_timeVertices, Equiv.symm_apply_apply]
    change (timeInclusion S hS).toOrderHom x.2 ∈ (S : Set (Fin (n + 1)))
    rw [← timeInclusion_range S hS]
    exact Set.mem_range_self x.2
  · intro hv
    obtain ⟨x, rfl⟩ := (vertexEquiv ⦋k⦌ ⦋n⦌).surjective v
    change vertexEquiv ⦋k⦌ ⦋n⦌ x ∈ timeVertices k n S at hv
    simp only [mem_timeVertices, Equiv.symm_apply_apply] at hv
    have ht : x.2 ∈ Set.range (timeInclusion S hS).toOrderHom := by
      rw [timeInclusion_range]
      exact hv
    obtain ⟨t, ht⟩ := ht
    refine ⟨vertexEquiv ⦋k⦌ (timeDegree S) (x.1, t), ?_⟩
    rw [mapTime_vertexEquiv, ht]

private def mapTimeOrderEmbedding (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    Fin ((common ⦋k⦌ (timeDegree S)).len + 1) ↪o
      Fin ((common ⦋k⦌ ⦋n⦌).len + 1) :=
  OrderEmbedding.ofStrictMono
    (mapTime ⦋k⦌ (timeInclusion S hS)).toOrderHom
    ((mapTime ⦋k⦌ (timeInclusion S hS)).toOrderHom.monotone.strictMono_of_injective
      (mapTime_injective ⦋k⦌ (timeInclusion S hS) (timeInclusion_injective S hS)))

private def timeVerticesOrderIso (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    Fin ((common ⦋k⦌ (timeDegree S)).len + 1) ≃o timeVertices k n S :=
  (mapTimeOrderEmbedding k n S hS).orderIso.trans
    (OrderIso.setCongr _ _ (by
      simpa only [mapTimeOrderEmbedding, OrderEmbedding.coe_ofStrictMono] using
        mapTime_timeInclusion_range k n S hS))

theorem timeFace_range_mapTime (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    SSet.Subcomplex.range
      (SSet.stdSimplex.map (mapTime ⦋k⦌ (timeInclusion S hS)) :
        SSet.stdSimplex.obj (common ⦋k⦌ (timeDegree S)) ⟶
          (SSet.stdSimplex.obj (common ⦋k⦌ ⦋n⦌) : SSet.{u})) =
      timeFace k n S := by
  rw [SSet.Subcomplex.range_eq_ofSimplex, timeFace,
    SSet.stdSimplex.face_eq_ofSimplex
      (timeVertices k n S) (common ⦋k⦌ (timeDegree S)).len
      (timeVerticesOrderIso k n S hS)]
  congr 1

theorem timeFace_range_timeInclusion (n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    SSet.Subcomplex.range (SSet.stdSimplex.map (timeInclusion S hS) :
      SSet.stdSimplex.obj (timeDegree S) ⟶ (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u})) =
      SSet.stdSimplex.face S := by
  rw [SSet.Subcomplex.range_eq_ofSimplex,
    SSet.stdSimplex.face_eq_ofSimplex S (timeDegree S).len
      (S.orderIsoOfFin (timeCard S hS))]
  congr 1

theorem timeFace_inf (k n : ℕ) (S T : Finset (Fin (n + 1))) :
    timeFace.{u} k n (S ⊓ T) = timeFace k n S ⊓ timeFace k n T := by
  simp only [timeFace, timeVertices_inf]
  exact (SSet.stdSimplex.face_inter_face _ _).symm

@[simp] theorem mem_timeFace_iff (k n : ℕ) (S : Finset (Fin (n + 1)))
    {d : ℕ} (x : (SSet.stdSimplex.obj (common ⦋k⦌ ⦋n⦌) : SSet.{u}) _⦋d⦌) :
    x ∈ (timeFace k n S).obj _ ↔
      ∀ i : Fin (d + 1),
        ((vertexEquiv ⦋k⦌ ⦋n⦌).symm
          ((SSet.stdSimplex.objEquiv x).toOrderHom i)).2 ∈ S := by
  change x ∈ (SSet.stdSimplex.face (timeVertices k n S)).obj _ ↔ _
  rw [SSet.stdSimplex.mem_face_iff]
  simp only [mem_timeVertices]
  rfl

@[simp] theorem timeFace_empty (k n : ℕ) :
    timeFace.{u} k n (∅ : Finset (Fin (n + 1))) = ⊥ := by
  ext q x
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ d =>
      constructor
      · intro hx
        have h := (mem_timeFace_iff k n (∅ : Finset (Fin (n + 1))) x).1 hx
        simpa using h 0
      · intro hx
        exact False.elim hx

@[simp] theorem mem_timeFace_preimage_iff (k n : ℕ) (S : Finset (Fin (n + 1)))
    {d : ℕ} (x : ((Δ[k] : SSet.{u}) ⊗ Δ[n]).obj (Opposite.op ⦋d⦌)) :
    x ∈ ((timeFace k n S).preimage (prism.{u} ⦋k⦌ ⦋n⦌)).obj _ ↔
      ∀ i : Fin (d + 1), (SSet.stdSimplex.objEquiv x.2).toOrderHom i ∈ S := by
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage, mem_timeFace_iff]
  change (∀ i : Fin (d + 1),
    ((vertexEquiv ⦋k⦌ ⦋n⦌).symm
      (vertexEquiv ⦋k⦌ ⦋n⦌ (SSet.prodStdSimplex.objEquiv x i))).2 ∈ S) ↔ _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem timeFace_preimage_range (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    SSet.Subcomplex.range
      ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS)) =
      (timeFace k n S).preimage (prism.{u} ⦋k⦌ ⦋n⦌) := by
  rw [show ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS)) =
      (𝟙 (Δ[k] : SSet.{u})) ⊗ₘ SSet.stdSimplex.map (timeInclusion S hS) from rfl,
    SSet.Subcomplex.range_tensorHom, SSet.Subcomplex.range_eq_top,
    timeFace_range_timeInclusion n S hS]
  ext q x
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ d =>
      change (x.1 ∈ (⊤ : (Δ[k] : SSet.{u}).Subcomplex).obj _ ∧
        x.2 ∈ (SSet.stdSimplex.face S).obj _) ↔
        x ∈ ((timeFace k n S).preimage (prism ⦋k⦌ ⦋n⦌)).obj _
      rw [mem_timeFace_preimage_iff, SSet.stdSimplex.mem_face_iff]
      simp

/-- The smaller prism is the preimage of a nonempty time face. -/
def timeFacePreimageIso (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    ((Δ[k] : SSet.{u}) ⊗ SSet.stdSimplex.obj (timeDegree S)) ≅
      ((timeFace k n S).preimage (prism.{u} ⦋k⦌ ⦋n⦌) : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange
    ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS))) ≪≫
      SSet.Subcomplex.eqToIso (timeFace_preimage_range k n S hS)

/-- The smaller common simplex is the nonempty time face. -/
def timeFaceIso (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    (SSet.stdSimplex.obj (common ⦋k⦌ (timeDegree S)) : SSet.{u}) ≅
      (timeFace k n S : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange
    (SSet.stdSimplex.map (mapTime ⦋k⦌ (timeInclusion S hS)) :
      SSet.stdSimplex.obj (common ⦋k⦌ (timeDegree S)) ⟶
        (SSet.stdSimplex.obj (common ⦋k⦌ ⦋n⦌) : SSet.{u}))) ≪≫
      SSet.Subcomplex.eqToIso (timeFace_range_mapTime k n S hS)

theorem timeFaceIso_ι (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    (timeFaceIso.{u} k n S hS).hom ≫ (timeFace k n S).ι =
      SSet.stdSimplex.map (mapTime ⦋k⦌ (timeInclusion S hS)) := by
  simp [timeFaceIso, Category.assoc]

theorem timeFacePreimageIso_ι (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    (timeFacePreimageIso.{u} k n S hS).hom ≫
        ((timeFace k n S).preimage (prism ⦋k⦌ ⦋n⦌)).ι =
      ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS)) := by
  simp [timeFacePreimageIso, Category.assoc]

theorem timeFacePreimageIso_compare (k n : ℕ) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) :
    (timeFacePreimageIso.{u} k n S hS).hom ≫
        (timeFace k n S).fromPreimage (prism ⦋k⦌ ⦋n⦌) =
      prism ⦋k⦌ (timeDegree S) ≫ (timeFaceIso k n S hS).hom := by
  apply (cancel_mono (timeFace k n S).ι).1
  calc
    _ = ((timeFacePreimageIso.{u} k n S hS).hom ≫
        ((timeFace k n S).preimage (prism ⦋k⦌ ⦋n⦌)).ι) ≫
          prism ⦋k⦌ ⦋n⦌ := by
            simp only [Category.assoc, SSet.Subcomplex.fromPreimage_ι]
    _ = ((Δ[k] : SSet.{u}) ◁ SSet.stdSimplex.map (timeInclusion S hS)) ≫
          prism ⦋k⦌ ⦋n⦌ := by rw [timeFacePreimageIso_ι]
    _ = prism ⦋k⦌ (timeDegree S) ≫
          SSet.stdSimplex.map (mapTime ⦋k⦌ (timeInclusion S hS)) :=
            (prism_mapTime ⦋k⦌ (timeInclusion S hS)).symm
    _ = (prism ⦋k⦌ (timeDegree S) ≫ (timeFaceIso k n S hS).hom) ≫
          (timeFace k n S).ι := by rw [Category.assoc, timeFaceIso_ι]

theorem timeFaceComparison_weak_nonempty (k n : ℕ)
    (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    WeakEquivalence ((timeFace.{u} k n S).fromPreimage (prism ⦋k⦌ ⦋n⦌)) := by
  haveI : WeakEquivalence (prism.{u} ⦋k⦌ (timeDegree S)) :=
    prism_weak ⦋k⦌ (timeDegree S)
  exact weakEquivalence_of_precomp_of_fac
    (timeFacePreimageIso_compare.{u} k n S hS)

@[simp] theorem timeFace_empty_preimage (k n : ℕ) :
    (timeFace.{u} k n (∅ : Finset (Fin (n + 1)))).preimage
      (prism ⦋k⦌ ⦋n⦌) = ⊥ := by
  rw [timeFace_empty]
  rfl

theorem timeFaceComparison_weak_empty (k n : ℕ) :
    WeakEquivalence ((timeFace.{u} k n (∅ : Finset (Fin (n + 1)))).fromPreimage
      (prism ⦋k⦌ ⦋n⦌)) := by
  haveI : IsIso ((timeFace.{u} k n (∅ : Finset (Fin (n + 1)))).fromPreimage
      (prism ⦋k⦌ ⦋n⦌)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro q
    apply (isIso_iff_bijective _).2
    constructor
    · intro x y _
      have hx : False := by
        simpa only [timeFace_empty_preimage] using x.property
      exact False.elim hx
    · intro y
      have hy : False := by
        simpa only [timeFace_empty] using y.property
      exact False.elim hy
  infer_instance

/-- The prism comparison is a Kan weak equivalence on every time face. -/
theorem timeFaceComparison_weak (k n : ℕ) (S : Finset (Fin (n + 1))) :
    WeakEquivalence ((timeFace.{u} k n S).fromPreimage
      (prism ⦋k⦌ ⦋n⦌)) := by
  by_cases hS : S.Nonempty
  · exact timeFaceComparison_weak_nonempty k n S hS
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact timeFaceComparison_weak_empty k n

end

end DaggerModels.PartII.JTHigherInterleavedParameter
