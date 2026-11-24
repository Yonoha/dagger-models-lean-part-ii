import DaggerModelsPartII.BorelInvariantSplit

/-!
# Strict orbit sets split along an invariant subset

The complement and the invariant subset form the literal coproduct of constant
simplicial orbit sets. This retains the specified orbit-inclusion maps.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.InvariantOrbitSets

open DaggerModels.FreeInvolution DiscreteOrbitSubobject
  DiagonalInvolutionOrbits InvariantDiagonalOrbits

noncomputable section

variable {X : Type u} (τ : X ≃ X) (hτ : Function.Involutive τ)
  (A : Set X) (hA : ∀ x ∈ A, τ x ∈ A)

abbrev subsetOrbitSet := Orbit (subsetInvolution τ hτ A hA)
  (subsetInvolutive τ hτ A hA)

abbrev complementOrbitSet := Orbit (complementInvolution τ hτ A hA)
  (complementInvolutive τ hτ A hA)

abbrev subsetOrbitInclusion : subsetOrbitSet τ hτ A hA → Orbit τ hτ :=
  orbitInclusion τ hτ A hA

abbrev complementOrbitInclusion : complementOrbitSet τ hτ A hA → Orbit τ hτ :=
  orbitInclusion τ hτ {x | x ∉ A} (complement_invariant τ A hτ hA)

private def unitInvolution : Unit ≃ Unit := Equiv.refl Unit

private theorem unitInvolutive : Function.Involutive unitInvolution := by
  intro x
  rfl

/-- A diagonal orbit with a trivial unit factor is the strict orbit set. -/
def unitDiagonalOrbitEquiv :
    DiagonalOrbit τ hτ unitInvolution unitInvolutive ≃ Orbit τ hτ where
  toFun := projection τ hτ unitInvolution unitInvolutive
  invFun := Quotient.map' (fun x : X ↦ (x, ())) (by
    intro x y hxy
    rcases hxy with h | h
    · exact Or.inl (congrArg (fun x : X ↦ (x, ())) h)
    · exact Or.inr (Prod.ext h rfl))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨x, u⟩
      cases u
      rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-- The strict orbit split is the unit-factor specialization of the diagonal split. -/
def strictOrbitSplitEquiv : Orbit τ hτ ≃
    subsetOrbitSet τ hτ A hA ⊕ complementOrbitSet τ hτ A hA :=
  (unitDiagonalOrbitEquiv τ hτ).symm.trans
    ((splitEquiv τ hτ A hA unitInvolution unitInvolutive).trans
      (Equiv.sumCongr
        (unitDiagonalOrbitEquiv (subsetInvolution τ hτ A hA)
          (subsetInvolutive τ hτ A hA))
        (unitDiagonalOrbitEquiv (complementInvolution τ hτ A hA)
          (complementInvolutive τ hτ A hA))))

@[simp] theorem strictOrbitSplitEquiv_subsetInclusion (q : subsetOrbitSet τ hτ A hA) :
    strictOrbitSplitEquiv τ hτ A hA (subsetOrbitInclusion τ hτ A hA q) =
      Sum.inl q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change _ = Sum.inl (orbit _ _ x)
    simp only [strictOrbitSplitEquiv, Equiv.trans_apply]
    change (Equiv.sumCongr _ _) (splitEquiv τ hτ A hA unitInvolution
      unitInvolutive (subsetInclusion τ hτ A hA unitInvolution unitInvolutive
        (orbit _ _ (x, ())))) = _
    rw [splitEquiv_subsetInclusion]
    rfl

@[simp] theorem strictOrbitSplitEquiv_complementInclusion
    (q : complementOrbitSet τ hτ A hA) :
    strictOrbitSplitEquiv τ hτ A hA (complementOrbitInclusion τ hτ A hA q) =
      Sum.inr q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change _ = Sum.inr (orbit _ _ x)
    simp only [strictOrbitSplitEquiv, Equiv.trans_apply]
    change (Equiv.sumCongr _ _) (splitEquiv τ hτ A hA unitInvolution
      unitInvolutive (complementInclusion τ hτ A hA unitInvolution unitInvolutive
        (orbit _ _ (x, ())))) = _
    rw [splitEquiv_complementInclusion]
    rfl

private abbrev constOrbit (T : Type u) : SSet.{u} :=
  (SimplicialObject.const (Type u)).obj T

/-- A constant simplicial map induced by the strict orbit inclusion. -/
def subsetConstantInclusion :
    constOrbit (subsetOrbitSet τ hτ A hA) ⟶ constOrbit (Orbit τ hτ) :=
  (SimplicialObject.const (Type u)).map (subsetOrbitInclusion τ hτ A hA)

/-- A constant simplicial map induced by the complement orbit inclusion. -/
def complementConstantInclusion :
    constOrbit (complementOrbitSet τ hτ A hA) ⟶ constOrbit (Orbit τ hτ) :=
  (SimplicialObject.const (Type u)).map (complementOrbitInclusion τ hτ A hA)

private def constantSplitDesc {Z : SSet.{u}}
    (f : constOrbit (subsetOrbitSet τ hτ A hA) ⟶ Z)
    (g : constOrbit (complementOrbitSet τ hτ A hA) ⟶ Z) :
    constOrbit (Orbit τ hτ) ⟶ Z where
  app n q := Sum.elim (f.app n) (g.app n) (strictOrbitSplitEquiv τ hτ A hA q)
  naturality n m α := by
    funext q
    change Sum.elim (f.app m) (g.app m) (strictOrbitSplitEquiv τ hτ A hA q) =
      Z.map α (Sum.elim (f.app n) (g.app n) (strictOrbitSplitEquiv τ hτ A hA q))
    cases strictOrbitSplitEquiv τ hτ A hA q with
    | inl a => exact congrFun (f.naturality α) a
    | inr c => exact congrFun (g.naturality α) c

private theorem subsetInclusion_constantSplitDesc {Z : SSet.{u}}
    (f : constOrbit (subsetOrbitSet τ hτ A hA) ⟶ Z)
    (g : constOrbit (complementOrbitSet τ hτ A hA) ⟶ Z) :
    subsetConstantInclusion τ hτ A hA ≫ constantSplitDesc τ hτ A hA f g = f := by
  apply NatTrans.ext
  funext n q
  change Sum.elim (f.app n) (g.app n)
    (strictOrbitSplitEquiv τ hτ A hA (subsetOrbitInclusion τ hτ A hA q)) = _
  rw [strictOrbitSplitEquiv_subsetInclusion]
  rfl

private theorem complementInclusion_constantSplitDesc {Z : SSet.{u}}
    (f : constOrbit (subsetOrbitSet τ hτ A hA) ⟶ Z)
    (g : constOrbit (complementOrbitSet τ hτ A hA) ⟶ Z) :
    complementConstantInclusion τ hτ A hA ≫ constantSplitDesc τ hτ A hA f g = g := by
  apply NatTrans.ext
  funext n q
  change Sum.elim (f.app n) (g.app n)
    (strictOrbitSplitEquiv τ hτ A hA (complementOrbitInclusion τ hτ A hA q)) = _
  rw [strictOrbitSplitEquiv_complementInclusion]
  rfl

/-- The two constant orbit inclusions form a binary coproduct cocone. -/
def constantSplitIsColimit : IsColimit (BinaryCofan.mk
    (subsetConstantInclusion τ hτ A hA)
    (complementConstantInclusion τ hτ A hA)) :=
  BinaryCofan.isColimitMk
    (fun s ↦ constantSplitDesc τ hτ A hA s.inl s.inr)
    (fun s ↦ subsetInclusion_constantSplitDesc τ hτ A hA s.inl s.inr)
    (fun s ↦ complementInclusion_constantSplitDesc τ hτ A hA s.inl s.inr) (by
      intro s m hmA hmC
      apply NatTrans.ext
      funext n q
      let e := strictOrbitSplitEquiv τ hτ A hA
      obtain ⟨r, rfl⟩ := e.symm.surjective q
      rcases r with a | c
      · have he : e.symm (Sum.inl a) = subsetOrbitInclusion τ hτ A hA a := by
          apply e.injective
          exact (e.apply_symm_apply (Sum.inl a)).trans
            (strictOrbitSplitEquiv_subsetInclusion τ hτ A hA a).symm
        rw [he]
        change m.app n (subsetOrbitInclusion τ hτ A hA a) =
          Sum.elim _ _ (e (subsetOrbitInclusion τ hτ A hA a))
        rw [strictOrbitSplitEquiv_subsetInclusion]
        exact congrFun (congr_app hmA n) a
      · have he : e.symm (Sum.inr c) = complementOrbitInclusion τ hτ A hA c := by
          apply e.injective
          exact (e.apply_symm_apply (Sum.inr c)).trans
            (strictOrbitSplitEquiv_complementInclusion τ hτ A hA c).symm
        rw [he]
        change m.app n (complementOrbitInclusion τ hτ A hA c) =
          Sum.elim _ _ (e (complementOrbitInclusion τ hτ A hA c))
        rw [strictOrbitSplitEquiv_complementInclusion]
        exact congrFun (congr_app hmC n) c)

/-- The literal coproduct comparison for constant strict orbit sets. -/
def constantOrbitCoproductIso :
    (constOrbit (subsetOrbitSet τ hτ A hA) ⨿
      constOrbit (complementOrbitSet τ hτ A hA)) ≅ constOrbit (Orbit τ hτ) :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (constantSplitIsColimit τ hτ A hA)

@[reassoc (attr := simp)] theorem inl_constantOrbitCoproductIso :
    coprod.inl ≫ (constantOrbitCoproductIso τ hτ A hA).hom =
      subsetConstantInclusion τ hτ A hA :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (constOrbit (subsetOrbitSet τ hτ A hA))
      (constOrbit (complementOrbitSet τ hτ A hA)))
    (constantSplitIsColimit τ hτ A hA) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem inr_constantOrbitCoproductIso :
    coprod.inr ≫ (constantOrbitCoproductIso τ hτ A hA).hom =
      complementConstantInclusion τ hτ A hA :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (constOrbit (subsetOrbitSet τ hτ A hA))
      (constOrbit (complementOrbitSet τ hτ A hA)))
    (constantSplitIsColimit τ hτ A hA) ⟨WalkingPair.right⟩

end

end DaggerModels.PartII.InvariantOrbitSets
