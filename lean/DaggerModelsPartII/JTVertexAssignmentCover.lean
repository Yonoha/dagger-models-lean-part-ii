import DaggerModelsPartII.JTJointRelativeParameters
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# A weak simplicial cover retaining all admissible vertex assignments

For a diagram of allowed values on vertices, the right adjoint to
evaluation at zero gives an objectwise trivial fibration adding choices
to all simplices. The tautological assignment is natural on this cover.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTVertexAssignmentCover

open JTJointRelativeParameters (parameterOfNaturalVertices parameterOfNaturalVertices_coord)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev V := SSet.evaluation.{0}.obj zero
private abbrev R := evaluationRightAdjoint (Type 0) zero
private abbrev adj := evaluationAdjunctionLeft (Type 0) zero
private abbrev J := GroupoidSimplex.parameter

private theorem rightAdjoint_trivialFibration {A B : Type} {f : A ⟶ B}
    (hf : Function.Surjective f) : trivialFibrations SSet.{0} (R.map f) := by
  rw [← cofibrations_rlp]
  intro C D i hi
  haveI : Cofibration i := (cofibration_iff i).mpr hi
  have hi' : Function.Injective (i.app zero) := (mono_iff_injective _).mp inferInstance
  apply (adj.hasLiftingProperty_iff i f).mp
  constructor
  intro u v sq
  let g := Function.extend (i.app zero) u (fun x ↦ Function.surjInv hf (v x))
  refine CommSq.HasLift.mk' ⟨g, ?_, ?_⟩
  · funext a
    change g (i.app zero a) = u a
    exact hi'.extend_apply _ _ _
  · funext b
    change f (g b) = v b
    by_cases hb : b ∈ Set.range (i.app zero)
    · obtain ⟨a, rfl⟩ := hb
      have he : g (i.app zero a) = u a := hi'.extend_apply _ _ _
      rw [he]
      exact congrFun sq.w a
    · unfold g
      rw [Function.extend_apply' _ _ _ hb]
      exact Function.surjInv_eq hf (v b)

variable {I : Type} [SmallCategory I] (X : I ⥤ SSet.{0}) (k : I ⥤ SimplexCategory)
variable (allowed : ∀ p, (X.obj p).obj zero → Set (Fin ((k.obj p).len + 1)))
variable (stable : ∀ {p p' : I} (a : p ⟶ p') (u : (X.obj p).obj zero),
  Set.MapsTo (k.map a).toOrderHom (allowed p u) (allowed p' ((X.map a).app zero u)))

include stable in
/-- The actual vertex choices together with the original vertices and operators. -/
def choices : I ⥤ Type where
  obj p := {z : (X.obj p).obj zero × Fin ((k.obj p).len + 1) // z.2 ∈ allowed p z.1}
  map {p p'} a z := ⟨((X.map a).app zero z.val.1, (k.map a).toOrderHom z.val.2),
    stable a z.val.1 z.property⟩
  map_id p := by
    funext z
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (X.map_id p) zero) z.val.1
    · change (k.map (𝟙 p)).toOrderHom z.val.2 = z.val.2
      rw [k.map_id, SimplexCategory.id_toOrderHom]
      rfl
  map_comp {p p' p''} a b := by
    funext z
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (X.map_comp a b) zero) z.val.1
    · change (k.map (a ≫ b)).toOrderHom z.val.2 = _
      rw [k.map_comp]
      rfl

/-- Forget only the coefficient value, retaining the original vertex. -/
def forgetChoice : choices X k allowed stable ⟶ X ⋙ V where
  app _ z := z.val.1
  naturality _ _ _ := rfl

private abbrev unit := Functor.whiskerLeft X adj.unit
private abbrev forgetCoskeleton := Functor.whiskerRight (forgetChoice X k allowed stable) R

/-- Adjoin a choice at each vertex of every original simplex. -/
abbrev cover := pullback (unit X) (forgetCoskeleton X k allowed stable)

/-- The natural projection to the original simplicial diagram. -/
abbrev projection : cover X k allowed stable ⟶ X :=
  pullback.fst (unit X) (forgetCoskeleton X k allowed stable)

/-- The choices carried by a vertex of the cover. -/
def coveredChoice : cover X k allowed stable ⋙ V ⟶ choices X k allowed stable :=
  Functor.whiskerRight (pullback.snd (unit X) (forgetCoskeleton X k allowed stable)) V ≫
    Functor.whiskerLeft (choices X k allowed stable) adj.counit

/-- The original vertex of a covered choice is exactly its projected vertex. -/
theorem coveredChoice_vertex (p : I) (u : ((cover X k allowed stable).obj p).obj zero) :
    ((coveredChoice X k allowed stable).app p u).val.1 =
      ((projection X k allowed stable).app p).app zero u := by
  let g := (forgetChoice X k allowed stable).app p
  let r := (pullback.snd (unit X) (forgetCoskeleton X k allowed stable)).app p
  have h : (projection X k allowed stable).app p ≫ adj.unit.app (X.obj p) = r ≫ R.map g :=
    NatTrans.congr_app pullback.condition p
  have h' := congrArg (fun f ↦ V.map f ≫ adj.counit.app ((X ⋙ V).obj p)) h
  dsimp only at h'
  have hl : V.map (adj.unit.app (X.obj p)) ≫ adj.counit.app ((X ⋙ V).obj p) = 𝟙 _ :=
    adj.left_triangle_components (X.obj p)
  have hr : V.map (R.map g) ≫ adj.counit.app ((X ⋙ V).obj p) =
      adj.counit.app ((choices X k allowed stable).obj p) ≫ g :=
    adj.counit.naturality g
  rw [V.map_comp, V.map_comp, Category.assoc, Category.assoc, hl, hr] at h'
  exact (congrFun h' u).symm

/-- Nonempty vertex choices give an actual componentwise trivial fibration. -/
theorem projection_trivialFibration (h : ∀ p u, (allowed p u).Nonempty) (p : I) :
    trivialFibrations SSet.{0} ((projection X k allowed stable).app p) := by
  letI : (trivialFibrations SSet.{0}).IsStableUnderBaseChange := by
    rw [← rlp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    infer_instance
  have hs : Function.Surjective ((forgetChoice X k allowed stable).app p) := by
    intro u
    obtain ⟨v, hv⟩ := h p u
    exact ⟨⟨(u, v), hv⟩, rfl⟩
  exact (trivialFibrations SSet.{0}).of_isPullback
    ((IsPullback.of_hasPullback (unit X) (forgetCoskeleton X k allowed stable)).flip.map
      ((evaluation I _).obj p)) (rightAdjoint_trivialFibration hs)

private abbrev chosenVertex (p : I) (u : ((cover X k allowed stable).obj p).obj zero) :=
  ((coveredChoice X k allowed stable).app p u).val.2

private theorem chosenVertex_natural {p p' : I} (a : p ⟶ p')
    (u : ((cover X k allowed stable).obj p).obj zero) :
    chosenVertex X k allowed stable p' (((cover X k allowed stable).map a).app zero u) =
      (k.map a).toOrderHom (chosenVertex X k allowed stable p u) :=
  congrArg (fun z ↦ z.val.2) (congrFun ((coveredChoice X k allowed stable).naturality a) u)

/-- The tautological trace on the cover is natural under all original operators. -/
def trace : cover X k allowed stable ⟶ k ⋙ J :=
  parameterOfNaturalVertices _ k (chosenVertex X k allowed stable)
    (chosenVertex_natural X k allowed stable)

/-- The tautological trace satisfies the original constraints at every covered vertex. -/
theorem trace_allowed (p : I) (u : ((cover X k allowed stable).obj p).obj zero) :
    coord (k.obj p) zero (((trace X k allowed stable).app p).app zero u) 0 ∈
      allowed p (((projection X k allowed stable).app p).app zero u) := by
  have h := parameterOfNaturalVertices_coord _ k (chosenVertex X k allowed stable)
    (chosenVertex_natural X k allowed stable) p u
  change coord (k.obj p) zero (((trace X k allowed stable).app p).app zero u) 0 =
    chosenVertex X k allowed stable p u at h
  rw [h, ← coveredChoice_vertex X k allowed stable]
  exact ((coveredChoice X k allowed stable).app p u).property

section Lift

variable (A : I ⥤ SSet.{0}) (c : A ⟶ X)
variable (φ : ∀ p, (A.obj p).obj zero → Fin ((k.obj p).len + 1))
variable (hφ : ∀ {p p' : I} (f : p ⟶ p') (u : (A.obj p).obj zero),
  φ p' ((A.map f).app zero u) = (k.map f).toOrderHom (φ p u))
variable (h : ∀ p u, φ p u ∈ allowed p ((c.app p).app zero u))

include hφ h in
private def assignment : A ⋙ V ⟶ choices X k allowed stable where
  app p u := ⟨((c.app p).app zero u, φ p u), h p u⟩
  naturality p p' f := by
    funext u
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (c.naturality f) zero) u
    · exact hφ f u

private abbrev intoCoskeleton :=
  unit A ≫ Functor.whiskerRight (assignment X k allowed stable A c φ hφ h) R

private theorem assignment_square :
    c ≫ unit X = intoCoskeleton X k allowed stable A c φ hφ h ≫
      forgetCoskeleton X k allowed stable := by
  apply NatTrans.ext
  funext p
  change c.app p ≫ adj.unit.app (X.obj p) =
    (adj.unit.app (A.obj p) ≫ R.map ((assignment X k allowed stable A c φ hφ h).app p)) ≫
      R.map ((forgetChoice X k allowed stable).app p)
  have hn : c.app p ≫ adj.unit.app (X.obj p) =
    adj.unit.app (A.obj p) ≫ R.map (V.map (c.app p)) := adj.unit.naturality (c.app p)
  rw [hn, Category.assoc, ← R.map_comp]
  rfl

/-- Lift a simplicial diagram by a natural admissible assignment on its vertices. -/
def liftOfAssignments : A ⟶ cover X k allowed stable :=
  pullback.lift c (intoCoskeleton X k allowed stable A c φ hφ h)
    (assignment_square X k allowed stable A c φ hφ h)

@[reassoc]
theorem liftOfAssignments_projection :
    liftOfAssignments X k allowed stable A c φ hφ h ≫ projection X k allowed stable = c :=
  pullback.lift_fst _ _ _

private theorem liftOfAssignments_choice (p : I) (v : (A.obj p).obj zero) :
    (coveredChoice X k allowed stable).app p
        (((liftOfAssignments X k allowed stable A c φ hφ h).app p).app zero v) =
      (assignment X k allowed stable A c φ hφ h).app p v := by
  let l := liftOfAssignments X k allowed stable A c φ hφ h
  let r := pullback.snd (unit X) (forgetCoskeleton X k allowed stable)
  let f := (assignment X k allowed stable A c φ hφ h).app p
  let D := (choices X k allowed stable).obj p
  have hl : l ≫ r = intoCoskeleton X k allowed stable A c φ hφ h :=
    pullback.lift_snd _ _ _
  have hl' : l.app p ≫ r.app p = adj.unit.app (A.obj p) ≫ R.map f :=
    NatTrans.congr_app hl p
  have he : V.map (l.app p) ≫ V.map (r.app p) ≫ adj.counit.app D = f := by
    rw [← Category.assoc, ← V.map_comp, hl']
    have e := (adj.homEquiv (A.obj p) D).symm_apply_apply f
    rw [adj.homEquiv_apply, adj.homEquiv_symm_apply] at e
    exact e
  exact congrFun he v

/-- The tautological parameter on a lifted diagram recovers its prescribed
coefficient at every vertex. -/
theorem liftOfAssignments_trace_vertex (p : I) (v : (A.obj p).obj zero) :
    coord (k.obj p) zero (((trace X k allowed stable).app p).app zero
      (((liftOfAssignments X k allowed stable A c φ hφ h).app p).app zero v)) 0 = φ p v := by
  let u := ((liftOfAssignments X k allowed stable A c φ hφ h).app p).app zero v
  exact (parameterOfNaturalVertices_coord _ k (chosenVertex X k allowed stable)
    (chosenVertex_natural X k allowed stable) p u).trans
      (congrArg (fun z ↦ z.val.2) (liftOfAssignments_choice X k allowed stable A c φ hφ h p v))

/-- An assignment lift commutes with restriction of its underlying diagram. -/
theorem comp_liftOfAssignments {A' : I ⥤ SSet.{0}} (a : A' ⟶ A) (c' : A' ⟶ X)
    (hc : a ≫ c = c')
    (ψ : ∀ p, (A'.obj p).obj zero → Fin ((k.obj p).len + 1))
    (hψ : ∀ {p p' : I} (f : p ⟶ p') (v : (A'.obj p).obj zero),
      ψ p' ((A'.map f).app zero v) = (k.map f).toOrderHom (ψ p v))
    (ha : ∀ p v, ψ p v ∈ allowed p ((c'.app p).app zero v))
    (e : ∀ p v, ψ p v = φ p ((a.app p).app zero v)) :
    a ≫ liftOfAssignments X k allowed stable A c φ hφ h =
      liftOfAssignments X k allowed stable A' c' ψ hψ ha := by
  subst c'
  apply pullback.hom_ext
  · simp only [liftOfAssignments, Category.assoc, pullback.lift_fst]
  · simp only [liftOfAssignments, Category.assoc, pullback.lift_snd]
    apply NatTrans.ext
    funext p
    let f := (assignment X k allowed stable A c φ hφ h).app p
    let g := (assignment X k allowed stable A' (a ≫ c) ψ hψ ha).app p
    change a.app p ≫ adj.unit.app (A.obj p) ≫ R.map f =
      adj.unit.app (A'.obj p) ≫ R.map g
    have hfg : V.map (a.app p) ≫ f = g := by
      funext v
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (e p v).symm
    have hn : a.app p ≫ adj.unit.app (A.obj p) =
        adj.unit.app (A'.obj p) ≫ R.map (V.map (a.app p)) := adj.unit.naturality (a.app p)
    rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, hfg]

end Lift

section ExtendAllowed

variable {I : Type} [SmallCategory I] {M X : I ⥤ SSet.{0}} {k : I ⥤ SimplexCategory}
variable (a : M ⟶ X) (original : X ⟶ k ⋙ J)
variable (allowed : ∀ p, (M.obj p).obj zero → Set (Fin ((k.obj p).len + 1)))

/-- Impose the original coefficient away from the distinguished subdiagram
and all admissible assignments on its image. -/
def extendAllowed (p : I) (v : (X.obj p).obj zero) : Set (Fin ((k.obj p).len + 1)) :=
  {c | (∀ u : (M.obj p).obj zero, (a.app p).app zero u = v → c ∈ allowed p u) ∧
    (v ∉ Set.range ((a.app p).app zero) → c = coord (k.obj p) zero ((original.app p).app zero v) 0)}

theorem extendAllowed_on (p : I) (u : (M.obj p).obj zero)
    {c : Fin ((k.obj p).len + 1)} (hc : c ∈ extendAllowed a original allowed p ((a.app p).app zero u)) :
    c ∈ allowed p u :=
  hc.1 u rfl

theorem extendAllowed_off (p : I) (v : (X.obj p).obj zero)
    (hv : v ∉ Set.range ((a.app p).app zero)) :
    extendAllowed a original allowed p v = {coord (k.obj p) zero ((original.app p).app zero v) 0} := by
  ext c
  constructor
  · intro hc
    exact hc.2 hv
  · intro hc
    exact ⟨fun u hu ↦ (hv ⟨u, hu⟩).elim, fun _ ↦ hc⟩

theorem extendAllowed_nonempty
    (injective : ∀ p, Function.Injective ((a.app p).app zero))
    (nonempty : ∀ p u, (allowed p u).Nonempty)
    (p : I) (v : (X.obj p).obj zero) : (extendAllowed a original allowed p v).Nonempty := by
  by_cases hv : v ∈ Set.range ((a.app p).app zero)
  · obtain ⟨u, rfl⟩ := hv
    obtain ⟨c, hc⟩ := nonempty p u
    exact ⟨c, ⟨fun u' hu ↦ (injective p hu).symm ▸ hc, fun h ↦ (h ⟨u, rfl⟩).elim⟩⟩
  · rw [extendAllowed_off a original allowed p v hv]
    exact Set.singleton_nonempty _

/-- The allowed sets extend functorially when membership in the subdiagram
is reflected along operators and its vertex inclusions are injective. -/
theorem extendAllowed_mapsTo
    (injective : ∀ p, Function.Injective ((a.app p).app zero))
    (reflects : ∀ {p p' : I} (f : p ⟶ p') (v : (X.obj p).obj zero),
      (X.map f).app zero v ∈ Set.range ((a.app p').app zero) →
        v ∈ Set.range ((a.app p).app zero))
    (stable : ∀ {p p' : I} (f : p ⟶ p') (u : (M.obj p).obj zero),
      Set.MapsTo (k.map f).toOrderHom (allowed p u) (allowed p' ((M.map f).app zero u)))
    {p p' : I} (f : p ⟶ p') (v : (X.obj p).obj zero) :
    Set.MapsTo (k.map f).toOrderHom (extendAllowed a original allowed p v)
      (extendAllowed a original allowed p' ((X.map f).app zero v)) := by
  intro c hc
  constructor
  · intro u' hu'
    obtain ⟨u, hu⟩ := reflects f v ⟨u', hu'⟩
    have hn := congrFun (NatTrans.congr_app (a.naturality f) zero) u
    change (a.app p').app zero ((M.map f).app zero u) =
      (X.map f).app zero ((a.app p).app zero u) at hn
    rw [hu, ← hu'] at hn
    rw [← injective p' hn]
    exact stable f u (hc.1 u hu)
  · intro h
    have hv : v ∉ Set.range ((a.app p).app zero) := by
      rintro ⟨u, rfl⟩
      apply h
      exact ⟨(M.map f).app zero u, congrFun (NatTrans.congr_app (a.naturality f) zero) u⟩
    have he := congrFun (NatTrans.congr_app (original.naturality f) zero) v
    change (original.app p').app zero ((X.map f).app zero v) =
      (J.map (k.map f)).app zero ((original.app p).app zero v) at he
    rw [hc.2 hv, he, JTCodiscreteParameterPairing.coord_map]

end ExtendAllowed

end

end DaggerModels.PartII.JTVertexAssignmentCover
