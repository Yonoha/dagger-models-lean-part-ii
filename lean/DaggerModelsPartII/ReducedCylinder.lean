import NativeSimplicialPushoutTensorMono
import DaggerModelsPartII.JTXiEndpointCollapse
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Reduced cylinders under a fixed simplicial boundary

For an inclusion `j : A ⟶ B`, the reduced cylinder of `K` is the
pushout of `A × K ⟶ B × K` and `A × K ⟶ A`, considered under `A`.
The comparison associated with a monomorphism `K ⟶ L` is a cobase
change of the literal cartesian pushout product. This construction
retains the fixed boundary object and its ordered inclusion.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial

namespace DaggerModels.PartII.ReducedCylinder

noncomputable section

universe u

/-- The fixed boundary times the variable simplicial set. -/
def boundaryTensor (A : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  tensorLeft A

/-- The fixed interval times the variable simplicial set. -/
def intervalTensor (B : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  tensorLeft B

/-- Tensoring an inclusion with the variable simplicial set. -/
def tensorInclusion {A B : SSet.{u}} (j : A ⟶ B) :
    boundaryTensor A ⟶ intervalTensor B :=
  (tensoringLeft SSet.{u}).map j

/-- Collapse the entire boundary cylinder to the same fixed boundary. -/
def tensorProjection (A : SSet.{u}) :
    boundaryTensor A ⟶ (Functor.const SSet.{u}).obj A where
  app K := CartesianMonoidalCategory.fst A K
  naturality {K L} f := by
    change (𝟙 A ⊗ₘ f) ≫ CartesianMonoidalCategory.fst A L =
      CartesianMonoidalCategory.fst A K
    simpa only [Category.comp_id] using
      CartesianMonoidalCategory.tensorHom_fst (𝟙 A) f

/-- The literal reduced-cylinder pushout, before recording its boundary. -/
def value {A B : SSet.{u}} (j : A ⟶ B) : SSet.{u} ⥤ SSet.{u} :=
  pushout (tensorInclusion j) (tensorProjection A)

/-- The fixed boundary map into the reduced cylinder. -/
def boundary {A B : SSet.{u}} (j : A ⟶ B) :
    (Functor.const SSet.{u}).obj A ⟶ value j :=
  pushout.inr (tensorInclusion j) (tensorProjection A)

/-- The uncollapsed interval-cylinder map. -/
def cylinder {A B : SSet.{u}} (j : A ⟶ B) :
    intervalTensor B ⟶ value j :=
  pushout.inl (tensorInclusion j) (tensorProjection A)

/-- The reduced cylinder as an actual functor into the undercategory. -/
def functor {A B : SSet.{u}} (j : A ⟶ B) : SSet.{u} ⥤ Under A :=
  Under.lift (value j) (boundary j)

/-- The moving interval-cylinder leg of the fixed-boundary cobase, in the
exact form required by the generic colimit-preservation theorem. -/
def left {A B : SSet.{u}} (j : A ⟶ B) :
    intervalTensor B ⟶ functor j ⋙ Under.forget A :=
  cylinder j

/-- The pointwise square defining the reduced cylinder is a pushout. -/
theorem value_isPushout {A B K : SSet.{u}} (j : A ⟶ B) :
    IsPushout ((tensorInclusion j).app K) ((tensorProjection A).app K)
      ((cylinder j).app K) ((boundary j).app K) :=
  (IsPushout.of_hasPushout (tensorInclusion j) (tensorProjection A)).map
    ((evaluation SSet.{u} SSet.{u}).obj K)

/-- The same pointwise universal property in the exact `Under A` form. -/
theorem functor_isPushout {A B K : SSet.{u}} (j : A ⟶ B) :
    IsPushout ((tensorInclusion j).app K) ((tensorProjection A).app K)
      ((left j).app K) ((functor j).obj K).hom :=
  value_isPushout j

section GenericAttachment

variable {C : Type u} [Category C]
variable {S₀ S₁ X₀ X₁ A P R₀ R₁ : C}
variable (j₀ : S₀ ⟶ X₀) (j₁ : S₁ ⟶ X₁)
  (fS : S₀ ⟶ S₁) (fX : X₀ ⟶ X₁)
  (a₀ : S₀ ⟶ A) (a₁ : S₁ ⟶ A)
  (pX : X₀ ⟶ P) (pS : S₁ ⟶ P)
  (x₀ : X₀ ⟶ R₀) (b₀ : A ⟶ R₀)
  (x₁ : X₁ ⟶ R₁) (b₁ : A ⟶ R₁)
  (hX : j₀ ≫ fX = fS ≫ j₁)
  (hA : fS ≫ a₁ = a₀)
  (hp : IsPushout j₀ fS pX pS)
  (h₀ : IsPushout j₀ a₀ x₀ b₀)
  (h₁ : IsPushout j₁ a₁ x₁ b₁)

private def attachingSource : P ⟶ R₀ :=
  hp.desc x₀ (a₁ ≫ b₀) (by rw [h₀.w, ← hA, Category.assoc])

private def attachingCell : P ⟶ X₁ :=
  hp.desc fX j₁ hX

private def reducedMap : R₀ ⟶ R₁ :=
  h₀.desc (fX ≫ x₁) b₁ (by
    calc
      j₀ ≫ fX ≫ x₁ = (j₀ ≫ fX) ≫ x₁ := (Category.assoc _ _ _).symm
      _ = (fS ≫ j₁) ≫ x₁ := congrArg (fun z ↦ z ≫ x₁) hX
      _ = fS ≫ (j₁ ≫ x₁) := Category.assoc _ _ _
      _ = fS ≫ (a₁ ≫ b₁) := congrArg (fun z ↦ fS ≫ z) h₁.w
      _ = (fS ≫ a₁) ≫ b₁ := (Category.assoc _ _ _).symm
      _ = a₀ ≫ b₁ := congrArg (fun z ↦ z ≫ b₁) hA)

/-- Changing the parameter attaches precisely the pushout-product cell. -/
private theorem genericAttachment_isPushout :
    IsPushout
      (attachingSource (a₁ := a₁) (b₀ := b₀) (hA := hA) (hp := hp) (h₀ := h₀))
      (attachingCell (fX := fX) (j₁ := j₁) (hX := hX) (hp := hp))
      (reducedMap (fX := fX) (x₁ := x₁) (b₁ := b₁)
        (hX := hX) (hA := hA) (h₀ := h₀) (h₁ := h₁))
      x₁ := by
  let s := attachingSource (a₁ := a₁) (b₀ := b₀) (hA := hA) (hp := hp) (h₀ := h₀)
  let t := attachingCell (fX := fX) (j₁ := j₁) (hX := hX) (hp := hp)
  let r := reducedMap (fX := fX) (x₁ := x₁) (b₁ := b₁)
    (hX := hX) (hA := hA) (h₀ := h₀) (h₁ := h₁)
  have hsX : pX ≫ s = x₀ := hp.inl_desc _ _ _
  have hsS : pS ≫ s = a₁ ≫ b₀ := hp.inr_desc _ _ _
  have htX : pX ≫ t = fX := hp.inl_desc _ _ _
  have htS : pS ≫ t = j₁ := hp.inr_desc _ _ _
  have hrX : x₀ ≫ r = fX ≫ x₁ := h₀.inl_desc _ _ _
  have hrB : b₀ ≫ r = b₁ := h₀.inr_desc _ _ _
  have hw : s ≫ r = t ≫ x₁ := by
    apply hp.hom_ext
    · calc
        pX ≫ (s ≫ r) = (pX ≫ s) ≫ r := (Category.assoc _ _ _).symm
        _ = x₀ ≫ r := congrArg (fun z ↦ z ≫ r) hsX
        _ = fX ≫ x₁ := hrX
        _ = (pX ≫ t) ≫ x₁ := congrArg (fun z ↦ z ≫ x₁) htX.symm
        _ = pX ≫ (t ≫ x₁) := Category.assoc _ _ _
    · calc
        pS ≫ (s ≫ r) = (pS ≫ s) ≫ r := (Category.assoc _ _ _).symm
        _ = (a₁ ≫ b₀) ≫ r := congrArg (fun z ↦ z ≫ r) hsS
        _ = a₁ ≫ (b₀ ≫ r) := Category.assoc _ _ _
        _ = a₁ ≫ b₁ := congrArg (fun z ↦ a₁ ≫ z) hrB
        _ = j₁ ≫ x₁ := h₁.w.symm
        _ = (pS ≫ t) ≫ x₁ := congrArg (fun z ↦ z ≫ x₁) htS.symm
        _ = pS ≫ (t ≫ x₁) := Category.assoc _ _ _
  let descend (c : PushoutCocone s t) : R₁ ⟶ c.pt :=
    h₁.desc c.inr (b₀ ≫ c.inl) (by
      have hc := congrArg (fun z ↦ pS ≫ z) c.condition
      change pS ≫ (s ≫ c.inl) = pS ≫ (t ≫ c.inr) at hc
      rw [← Category.assoc, hsS, ← Category.assoc, htS] at hc
      simpa only [Category.assoc] using hc.symm)
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk r x₁ hw)
  refine PushoutCocone.IsColimit.mk hw descend ?_ ?_ ?_
  · intro c
    apply h₀.hom_ext
    · rw [← Category.assoc, hrX, Category.assoc, h₁.inl_desc]
      have hc := congrArg (fun z ↦ pX ≫ z) c.condition
      change pX ≫ (s ≫ c.inl) = pX ≫ (t ≫ c.inr) at hc
      rw [← Category.assoc, hsX, ← Category.assoc, htX] at hc
      exact hc.symm
    · rw [← Category.assoc, hrB, h₁.inr_desc]
  · intro c
    exact h₁.inl_desc _ _ _
  · intro c q hqR hqX
    apply h₁.hom_ext
    · exact hqX.trans (h₁.inl_desc _ _ _).symm
    · calc
        b₁ ≫ q = (b₀ ≫ r) ≫ q := congrArg (fun z ↦ z ≫ q) hrB.symm
        _ = b₀ ≫ (r ≫ q) := Category.assoc _ _ _
        _ = b₀ ≫ c.inl := congrArg (fun z ↦ b₀ ≫ z) hqR
        _ = b₁ ≫ descend c := (h₁.inr_desc _ _ _).symm

end GenericAttachment

/-- The native cartesian pushout-product square for a fixed boundary map
and a variable parameter map. -/
def tensorSquare {A B K L : SSet.{u}} (j : A ⟶ B) (f : K ⟶ L) :
    SSet.PushoutTensor j f :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The pushout-product source maps to the smaller reduced cylinder: the
`B × K` leg uses the interval-cylinder inclusion, while the `A × L` leg
collapses to the same fixed copy of `A`. -/
def attachment {A B K L : SSet.{u}} (j : A ⟶ B) (f : K ⟶ L) :
    (tensorSquare j f).pt ⟶ (value j).obj K := by
  let t := tensorSquare j f
  apply t.isPushout.desc ((cylinder j).app K)
    ((tensorProjection A).app L ≫ (boundary j).app K)
  calc
    (j ▷ K) ≫ (cylinder j).app K =
        (tensorProjection A).app K ≫ (boundary j).app K :=
          (value_isPushout j).w
    _ = (A ◁ f) ≫ (tensorProjection A).app L ≫
        (boundary j).app K := by
          rw [← Category.assoc]
          have h : (A ◁ f) ≫ (tensorProjection A).app L =
              (tensorProjection A).app K := by
            simpa only [Functor.const_obj_map, Category.comp_id] using
              (tensorProjection A).naturality f
          exact congrArg (fun g ↦ g ≫ (boundary j).app K)
            h.symm

private theorem tensor_hX {A B K L : SSet.{u}}
    (j : A ⟶ B) (f : K ⟶ L) :
    (j ▷ K) ≫ (B ◁ f) = (A ◁ f) ≫ (j ▷ L) :=
  MonoidalCategory.whisker_exchange j f

private theorem tensor_hA {A K L : SSet.{u}} (f : K ⟶ L) :
    (A ◁ f) ≫ (tensorProjection A).app L =
      (tensorProjection A).app K := by
  simpa only [Functor.const_obj_map, Category.comp_id] using
    (tensorProjection A).naturality f

/-- The reduced-cylinder comparison is the cobase of the literal native
cartesian pushout-product corner. -/
theorem attachment_isPushout {A B K L : SSet.{u}}
    (j : A ⟶ B) (f : K ⟶ L) :
    IsPushout (attachment j f) (tensorSquare j f).ι
      ((functor j).map f).right ((cylinder j).app L) := by
  let t := tensorSquare j f
  let hK := value_isPushout j (K := K)
  let hL := value_isPushout j (K := L)
  have hmap :
      reducedMap (fX := B ◁ f) (x₁ := (cylinder j).app L)
        (b₁ := (boundary j).app L) (hX := tensor_hX j f)
        (hA := tensor_hA f) (h₀ := hK) (h₁ := hL) =
      ((functor j).map f).right := by
    change _ = (value j).map f
    apply hK.hom_ext
    · rw [reducedMap, hK.inl_desc]
      simpa only [intervalTensor] using (cylinder j).naturality f
    · rw [reducedMap, hK.inr_desc]
      have h := (boundary j).naturality f
      simpa only [Functor.const_obj_map, Category.id_comp] using h
  change IsPushout
    (attachingSource (a₁ := (tensorProjection A).app L)
      (b₀ := (boundary j).app K) (hA := tensor_hA f)
      (hp := t.isPushout) (h₀ := hK))
    (attachingCell (fX := B ◁ f) (j₁ := j ▷ L)
      (hX := tensor_hX j f) (hp := t.isPushout))
    ((functor j).map f).right ((cylinder j).app L)
  rw [← hmap]
  exact genericAttachment_isPushout
    (j₀ := j ▷ K) (j₁ := j ▷ L) (fS := A ◁ f) (fX := B ◁ f)
    (a₀ := (tensorProjection A).app K)
    (a₁ := (tensorProjection A).app L)
    (pX := t.inl) (pS := t.inr)
    (x₀ := (cylinder j).app K) (b₀ := (boundary j).app K)
    (x₁ := (cylinder j).app L) (b₁ := (boundary j).app L)
    (hX := tensor_hX j f) (hA := tensor_hA f)
    (hp := t.isPushout) (h₀ := hK) (h₁ := hL)

/-- A reduced cylinder sends every parameter monomorphism to a
monomorphism on its actual underlying simplicial-set map. -/
theorem map_mono {A B K L : SSet.{u}}
    (j : A ⟶ B) [Mono j] (f : K ⟶ L) [Mono f] :
    Mono ((functor j).map f).right := by
  let t := tensorSquare j f
  haveI : Mono t.ι :=
    DaggerNativeSimplicialPushoutTensorMono.mono_ι j f t
  have ht : (MorphismProperty.monomorphisms SSet.{u}) t.ι := by
    change Mono t.ι
    infer_instance
  have hm := (MorphismProperty.monomorphisms SSet.{u}).of_isPushout
    (attachment_isPushout j f) ht
  change Mono ((functor j).map f).right at hm
  exact hm

end

end DaggerModels.PartII.ReducedCylinder
