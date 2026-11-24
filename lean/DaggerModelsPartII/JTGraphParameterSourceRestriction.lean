import DaggerModelsPartII.JTGraphParameterFiber
import DaggerModelsPartII.JTNecklaceCylinderConnector

/-! Exact extension of graph parameters prescribed on source subcomplexes. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphParameterSourceRestriction

open JTNecklaceEndpointCylinder

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

noncomputable section

/-- A simplex whose native image is not in the ordered endpoint boundary
forces every exact graph parameter to have the same restriction. -/
theorem exact_parameter_eq_on_nonboundary
    {X : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (s t : X ⟶ J.obj k)
    (h : lift f s ≫ (cylinder T).app k =
      lift f t ≫ (cylinder T).app k)
    (d : ℕ) (z : (Δ[d] : SSet.{0}) ⟶ X)
    (hn : ¬ ∃ a : B.obj (op ⦋d⦌),
      (endpointInclusion T).app (op ⦋d⦌) a =
        SSet.yonedaEquiv (z ≫ f)) :
    z ≫ s = z ≫ t := by
  have hz := congrArg (fun u ↦ z ≫ u) h
  have hp :
      ((cylinder T).app k).app (op ⦋d⦌)
          (SSet.yonedaEquiv (z ≫ f), SSet.yonedaEquiv (z ≫ s)) =
        ((cylinder T).app k).app (op ⦋d⦌)
          (SSet.yonedaEquiv (z ≫ f), SSet.yonedaEquiv (z ≫ t)) := by
    simpa only [SSet.yonedaEquiv_comp, Category.assoc,
      CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd] using
      congrArg SSet.yonedaEquiv hz
  obtain heq | ⟨a, ha⟩ :=
    JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary
      T k d
      (SSet.yonedaEquiv (z ≫ f), SSet.yonedaEquiv (z ≫ s))
      (SSet.yonedaEquiv (z ≫ f), SSet.yonedaEquiv (z ≫ t)) hp
  · exact SSet.yonedaEquiv.injective heq
  · exact (hn ⟨a, ha⟩).elim

/-- A vertex touching any simplex outside the ordered boundary is rigid,
even if the vertex itself lies in a collapsed joint interval. -/
theorem exact_parameter_eq_at_incident_vertex
    {X : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (s t : X ⟶ J.obj k)
    (h : lift f s ≫ (cylinder T).app k =
      lift f t ≫ (cylinder T).app k)
    (d : ℕ) (z : (Δ[d] : SSet.{0}) ⟶ X)
    (hn : ¬ ∃ a : B.obj (op ⦋d⦌),
      (endpointInclusion T).app (op ⦋d⦌) a =
        SSet.yonedaEquiv (z ≫ f))
    (v : (Δ[0] : SSet.{0}) ⟶ (Δ[d] : SSet.{0})) :
    v ≫ z ≫ s = v ≫ z ≫ t := by
  simpa only [Category.assoc] using
    congrArg (fun u ↦ v ≫ u)
      (exact_parameter_eq_on_nonboundary T k f s t h d z hn)

/-- If a whole subcomplex maps to the boundary, the reduced-cylinder image
cannot detect its parameter at all. -/
theorem exact_parameter_free_on_boundary
    {A : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (b : A ⟶ B) (s t : A ⟶ J.obj k) :
    lift (b ≫ endpointInclusion T) s ≫ (cylinder T).app k =
      lift (b ≫ endpointInclusion T) t ≫ (cylinder T).app k := by
  rw [JTNecklaceCylinderConnector.boundary_collapse,
    JTNecklaceCylinderConnector.boundary_collapse]

/-- Exact source restriction fails to extend any boundary parameter that
disagrees at a vertex incident to a non-boundary simplex. -/
theorem no_extension_at_incident_vertex
    {X A : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (t : X ⟶ J.obj k)
    (a : A ⟶ X) (p : A ⟶ J.obj k)
    (d : ℕ) (z : (Δ[d] : SSet.{0}) ⟶ X)
    (hn : ¬ ∃ c : B.obj (op ⦋d⦌),
      (endpointInclusion T).app (op ⦋d⦌) c =
        SSet.yonedaEquiv (z ≫ f))
    (v : (Δ[0] : SSet.{0}) ⟶ (Δ[d] : SSet.{0}))
    (w : (Δ[0] : SSet.{0}) ⟶ A)
    (hw : w ≫ a = v ≫ z)
    (hp : w ≫ p ≠ w ≫ a ≫ t) :
    ¬ ∃ s : X ⟶ J.obj k,
      lift f s ≫ (cylinder T).app k =
        lift f t ≫ (cylinder T).app k ∧ a ≫ s = p := by
  rintro ⟨s, hs, hsa⟩
  apply hp
  calc
    w ≫ p = w ≫ a ≫ s := by rw [← hsa]
    _ = v ≫ z ≫ s := by
      simpa only [Category.assoc] using congrArg (· ≫ s) hw
    _ = v ≫ z ≫ t :=
      exact_parameter_eq_at_incident_vertex T k f s t hs d z hn v
    _ = w ≫ a ≫ t := by
      simpa only [Category.assoc] using (congrArg (· ≫ t) hw).symm

/-- Exact graph equality is precisely equality of parameters on all
source simplices that do not map entirely to an endpoint. -/
theorem exact_parameter_graph_eq_iff
    {X : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (s t : X ⟶ J.obj k) :
    lift f s ≫ (cylinder T).app k =
        lift f t ≫ (cylinder T).app k ↔
      ∀ (d : ℕ) (z : (Δ[d] : SSet.{0}) ⟶ X),
        (¬ ∃ a : B.obj (op ⦋d⦌),
          (endpointInclusion T).app (op ⦋d⦌) a =
            SSet.yonedaEquiv (z ≫ f)) → z ≫ s = z ≫ t := by
  constructor
  · intro h d z hn
    exact exact_parameter_eq_on_nonboundary T k f s t h d z hn
  · intro h
    apply NatTrans.ext
    funext q
    induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      funext x
      let z : (Δ[d] : SSet.{0}) ⟶ X := SSet.yonedaEquiv.symm x
      have hl (u : X ⟶ J.obj k) :
          z ≫ lift f u = lift (z ≫ f) (z ≫ u) := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, lift_fst]
        · simp only [Category.assoc, lift_snd]
      by_cases hb : ∃ a : B.obj (op ⦋d⦌),
          (endpointInclusion T).app (op ⦋d⦌) a =
            SSet.yonedaEquiv (z ≫ f)
      · obtain ⟨a, ha⟩ := hb
        let b : (Δ[d] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm a
        have hbf : b ≫ endpointInclusion T = z ≫ f := by
          apply SSet.yonedaEquiv.injective
          rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
          exact ha
        have hh := exact_parameter_free_on_boundary T k b (z ≫ s) (z ≫ t)
        rw [hbf] at hh
        have he : z ≫ lift f s ≫ (cylinder T).app k =
            z ≫ lift f t ≫ (cylinder T).app k := by
          simp only [← Category.assoc, hl]
          exact hh
        have he' := congrArg SSet.yonedaEquiv he
        simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
          Category.assoc, z] using he'

      · have hs := h d z hb
        have he : z ≫ lift f s ≫ (cylinder T).app k =
            z ≫ lift f t ≫ (cylinder T).app k := by
          simp only [← Category.assoc, hl, hs]
        have he' := congrArg SSet.yonedaEquiv he
        simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
          Category.assoc, z] using he'

private abbrev cod (k : SimplexCategory) :=
  DaggerModels.PartII.GroupoidSimplex.parameterCodiscreteIso.app k

private theorem vertexLabels_mapOfVertices {V : Type} (X : SSet.{0})
    (φ : X.obj (op ⦋0⦌) → V) (x : X.obj (op ⦋0⦌)) :
    DaggerOriginalCodiscreteNerveInjective.vertexLabels
      (DaggerOriginalCodiscreteNerveInjective.mapOfVertices X φ) x = φ x := by
  change φ (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) = φ x
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

private theorem hom_ext_vertices {X : SSet.{0}} {k : SimplexCategory}
    {s t : X ⟶ J.obj k}
    (h : ∀ x : X.obj (op ⦋0⦌),
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (s ≫ (cod k).hom) x =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t ≫ (cod k).hom) x) : s = t := by
  apply (cancel_mono (cod k).hom).mp
  apply NatTrans.ext
  funext q z
  apply nerve.ext_of_isThin
  funext v
  apply Codiscrete.ext
  calc
    (((s ≫ (cod k).hom).app q z).obj v).as =
        DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (s ≫ (cod k).hom)
          (X.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z) :=
      (DaggerOriginalCodiscreteNerveInjective.vertexLabels_natural
        (s ≫ (cod k).hom) q z v).symm
    _ = DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (t ≫ (cod k).hom)
          (X.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z) := h _
    _ = (((t ≫ (cod k).hom).app q z).obj v).as :=
      DaggerOriginalCodiscreteNerveInjective.vertexLabels_natural
        (t ≫ (cod k).hom) q z v

/-- Source vertices touched by a simplex whose native image is not in the
ordered endpoint boundary. -/
def RigidVertex {X : SSet.{0}} (T : NecklaceCode) (f : X ⟶ T.toSSet)
    (x : X.obj (op ⦋0⦌)) : Prop :=
  ∃ (d : ℕ) (z : (Δ[d] : SSet.{0}) ⟶ X)
      (v : (Δ[0] : SSet.{0}) ⟶ (Δ[d] : SSet.{0})),
    (¬ ∃ b : B.obj (op ⦋d⦌),
      (endpointInclusion T).app (op ⦋d⦌) b =
        SSet.yonedaEquiv (z ≫ f)) ∧ SSet.yonedaEquiv (v ≫ z) = x

private theorem vertexLabels_precomp {A X : SSet.{0}} {k : SimplexCategory}
    (a : A ⟶ X) (s : X ⟶ J.obj k) (x : A.obj (op ⦋0⦌)) :
    DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (a ≫ s ≫ (cod k).hom) x =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (s ≫ (cod k).hom) (a.app (op ⦋0⦌) x) := by
  rfl

private theorem vertexLabels_yoneda {X : SSet.{0}} {k : SimplexCategory}
    (s : X ⟶ J.obj k) (v : (Δ[0] : SSet.{0}) ⟶ X) :
    DaggerOriginalCodiscreteNerveInjective.vertexLabels
      (s ≫ (cod k).hom) (SSet.yonedaEquiv v) =
    DaggerOriginalCodiscreteNerveInjective.vertexLabels
      (v ≫ s ≫ (cod k).hom)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) := by
  rw [vertexLabels_precomp]
  congr 1

/-- An exact parameter on a mono subcomplex extends with the same complete
graph image exactly when it agrees on vertices incident to non-boundary
simplices in the ambient source. -/
theorem exact_parameter_extension_iff
    {X A : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (t : X ⟶ J.obj k)
    (a : A ⟶ X) [Mono a] (p : A ⟶ J.obj k) :
    (∃ s : X ⟶ J.obj k,
      (lift f s ≫ (cylinder T).app k =
        lift f t ≫ (cylinder T).app k) ∧ a ≫ s = p) ↔
    (∀ x : A.obj (op ⦋0⦌),
      RigidVertex T f (a.app (op ⦋0⦌) x) →
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (p ≫ (cod k).hom) x =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t ≫ (cod k).hom) (a.app (op ⦋0⦌) x)) := by
  constructor
  · rintro ⟨s, hs, hsp⟩ x ⟨d, z, v, hn, hv⟩
    have he := exact_parameter_eq_at_incident_vertex T k f s t hs d z hn v
    have hv' : v ≫ z = SSet.yonedaEquiv.symm (a.app (op ⦋0⦌) x) := by
      apply SSet.yonedaEquiv.injective
      simpa only [Equiv.apply_symm_apply] using hv
    have he' := congrArg (fun u ↦ u ≫ (cod k).hom) he
    have he'' := congrArg SSet.yonedaEquiv he'
    have hlabel : DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (s ≫ (cod k).hom) (a.app (op ⦋0⦌) x) =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t ≫ (cod k).hom) (a.app (op ⦋0⦌) x) := by
      rw [← hv, vertexLabels_yoneda, vertexLabels_yoneda]
      exact congrArg (fun u ↦ DaggerOriginalCodiscreteNerveInjective.vertexLabels u
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))))
        (by simpa only [Category.assoc] using he')
    rw [← hsp, Category.assoc, vertexLabels_precomp]
    exact hlabel
  · intro hc
    let φA : A.obj (op ⦋0⦌) → Fin (k.len + 1) :=
      DaggerOriginalCodiscreteNerveInjective.vertexLabels (p ≫ (cod k).hom)
    let φT : X.obj (op ⦋0⦌) → Fin (k.len + 1) :=
      DaggerOriginalCodiscreteNerveInjective.vertexLabels (t ≫ (cod k).hom)
    let φ : X.obj (op ⦋0⦌) → Fin (k.len + 1) :=
      Function.extend (a.app (op ⦋0⦌)) φA φT
    let s : X ⟶ J.obj k :=
      DaggerOriginalCodiscreteNerveInjective.mapOfVertices X φ ≫ (cod k).inv
    have hmono : Function.Injective (a.app (op ⦋0⦌)) :=
      (mono_iff_injective (a.app (op ⦋0⦌))).1 inferInstance
    have hslabel (x : X.obj (op ⦋0⦌)) :
        DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (s ≫ (cod k).hom) x = φ x := by
      change DaggerOriginalCodiscreteNerveInjective.vertexLabels
        ((DaggerOriginalCodiscreteNerveInjective.mapOfVertices X φ ≫ (cod k).inv) ≫
          (cod k).hom) x = _
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact vertexLabels_mapOfVertices X φ x
    have hres : a ≫ s = p := by
      apply hom_ext_vertices
      intro x
      rw [Category.assoc, vertexLabels_precomp, hslabel]
      exact hmono.extend_apply φA φT x
    refine ⟨s, ?_, hres⟩
    apply (exact_parameter_graph_eq_iff T k f s t).2
    intro d z hn
    apply hom_ext_vertices
    intro x
    let v : (Δ[0] : SSet.{0}) ⟶ (Δ[d] : SSet.{0}) := SSet.yonedaEquiv.symm x
    let y : X.obj (op ⦋0⦌) := SSet.yonedaEquiv (v ≫ z)
    have hy : RigidVertex T f y := ⟨d, z, v, hn, rfl⟩
    have hy' : φ y = φT y := by
      by_cases e : ∃ u : A.obj (op ⦋0⦌), a.app (op ⦋0⦌) u = y
      · obtain ⟨u, hu⟩ := e
        rw [← hu]
        exact (hmono.extend_apply φA φT u).trans (hc u (hu ▸ hy))
      · dsimp only [φ]
        exact Function.extend_apply' _ _ _ e
    have he : DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (s ≫ (cod k).hom) y =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t ≫ (cod k).hom) y := (hslabel y).trans hy'
    simpa only [vertexLabels_precomp, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply, y, v] using he

/-- Agreement at vertices incident to non-boundary simplices on both sides
allows exact matching on the whole common overlap. -/
theorem paired_exact_parameter_extension
    {A X₁ X₂ : SSet.{0}} (T₁ T₂ : NecklaceCode) (k : SimplexCategory)
    (f₁ : X₁ ⟶ T₁.toSSet) (f₂ : X₂ ⟶ T₂.toSSet)
    (t₁ : X₁ ⟶ J.obj k) (t₂ : X₂ ⟶ J.obj k)
    (a₁ : A ⟶ X₁) [Mono a₁] (a₂ : A ⟶ X₂) [Mono a₂]
    (h : ∀ x : A.obj (op ⦋0⦌),
      RigidVertex T₁ f₁ (a₁.app (op ⦋0⦌) x) →
      RigidVertex T₂ f₂ (a₂.app (op ⦋0⦌) x) →
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (a₁ ≫ t₁ ≫ (cod k).hom) x =
        DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (a₂ ≫ t₂ ≫ (cod k).hom) x) :
    ∃ (s₁ : X₁ ⟶ J.obj k) (s₂ : X₂ ⟶ J.obj k),
      (lift f₁ s₁ ≫ (cylinder T₁).app k =
        lift f₁ t₁ ≫ (cylinder T₁).app k) ∧
      (lift f₂ s₂ ≫ (cylinder T₂).app k =
        lift f₂ t₂ ≫ (cylinder T₂).app k) ∧
      a₁ ≫ s₁ = a₂ ≫ s₂ := by
  classical
  let φ₁ : A.obj (op ⦋0⦌) → Fin (k.len + 1) :=
    DaggerOriginalCodiscreteNerveInjective.vertexLabels (a₁ ≫ t₁ ≫ (cod k).hom)
  let φ₂ : A.obj (op ⦋0⦌) → Fin (k.len + 1) :=
    DaggerOriginalCodiscreteNerveInjective.vertexLabels (a₂ ≫ t₂ ≫ (cod k).hom)
  let φ : A.obj (op ⦋0⦌) → Fin (k.len + 1) := fun x ↦
    if RigidVertex T₁ f₁ (a₁.app (op ⦋0⦌) x) then φ₁ x
    else if RigidVertex T₂ f₂ (a₂.app (op ⦋0⦌) x) then φ₂ x else 0
  let p : A ⟶ J.obj k :=
    DaggerOriginalCodiscreteNerveInjective.mapOfVertices A φ ≫ (cod k).inv
  have hp (x : A.obj (op ⦋0⦌)) :
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (p ≫ (cod k).hom) x = φ x := by
    change DaggerOriginalCodiscreteNerveInjective.vertexLabels
      ((DaggerOriginalCodiscreteNerveInjective.mapOfVertices A φ ≫ (cod k).inv) ≫
        (cod k).hom) x = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact vertexLabels_mapOfVertices A φ x
  have h₁ : ∀ x : A.obj (op ⦋0⦌),
      RigidVertex T₁ f₁ (a₁.app (op ⦋0⦌) x) →
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (p ≫ (cod k).hom) x =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t₁ ≫ (cod k).hom) (a₁.app (op ⦋0⦌) x) := by
    intro x hx
    rw [hp]
    change φ x = φ₁ x
    simp only [φ, if_pos hx]
  have h₂ : ∀ x : A.obj (op ⦋0⦌),
      RigidVertex T₂ f₂ (a₂.app (op ⦋0⦌) x) →
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (p ≫ (cod k).hom) x =
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
        (t₂ ≫ (cod k).hom) (a₂.app (op ⦋0⦌) x) := by
    intro x hx
    rw [hp]
    change φ x = φ₂ x
    by_cases hy : RigidVertex T₁ f₁ (a₁.app (op ⦋0⦌) x)
    · simp only [φ, if_pos hy]
      exact h x hy hx
    · simp only [φ, if_neg hy, if_pos hx]
  obtain ⟨s₁, hs₁, hr₁⟩ := (exact_parameter_extension_iff T₁ k f₁ t₁ a₁ p).2 h₁
  obtain ⟨s₂, hs₂, hr₂⟩ := (exact_parameter_extension_iff T₂ k f₂ t₂ a₂ p).2 h₂
  exact ⟨s₁, s₂, hs₁, hs₂, hr₁.trans hr₂.symm⟩

/-- While both full graph images are fixed, this compatibility on vertices incident on both
sides characterizes exact matching on the overlap. -/
theorem paired_exact_parameter_extension_iff
    {A X₁ X₂ : SSet.{0}} (T₁ T₂ : NecklaceCode) (k : SimplexCategory)
    (f₁ : X₁ ⟶ T₁.toSSet) (f₂ : X₂ ⟶ T₂.toSSet)
    (t₁ : X₁ ⟶ J.obj k) (t₂ : X₂ ⟶ J.obj k)
    (a₁ : A ⟶ X₁) [Mono a₁] (a₂ : A ⟶ X₂) [Mono a₂] :
    (∃ (s₁ : X₁ ⟶ J.obj k) (s₂ : X₂ ⟶ J.obj k),
      (lift f₁ s₁ ≫ (cylinder T₁).app k =
        lift f₁ t₁ ≫ (cylinder T₁).app k) ∧
      (lift f₂ s₂ ≫ (cylinder T₂).app k =
        lift f₂ t₂ ≫ (cylinder T₂).app k) ∧
      a₁ ≫ s₁ = a₂ ≫ s₂) ↔
    ∀ x : A.obj (op ⦋0⦌),
      RigidVertex T₁ f₁ (a₁.app (op ⦋0⦌) x) →
      RigidVertex T₂ f₂ (a₂.app (op ⦋0⦌) x) →
      DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (a₁ ≫ t₁ ≫ (cod k).hom) x =
        DaggerOriginalCodiscreteNerveInjective.vertexLabels
          (a₂ ≫ t₂ ≫ (cod k).hom) x := by
  constructor
  · rintro ⟨s₁, s₂, hs₁, hs₂, h⟩ x hx₁ hx₂
    let p := a₁ ≫ s₁
    have h₁ := (exact_parameter_extension_iff T₁ k f₁ t₁ a₁ p).mp ⟨s₁, hs₁, rfl⟩ x hx₁
    have h₂ := (exact_parameter_extension_iff T₂ k f₂ t₂ a₂ p).mp ⟨s₂, hs₂, h.symm⟩ x hx₂
    rw [vertexLabels_precomp, vertexLabels_precomp]
    exact h₁.symm.trans h₂
  · exact paired_exact_parameter_extension T₁ T₂ k f₁ f₂ t₁ t₂ a₁ a₂

end

end DaggerModels.PartII.JTGraphParameterSourceRestriction
