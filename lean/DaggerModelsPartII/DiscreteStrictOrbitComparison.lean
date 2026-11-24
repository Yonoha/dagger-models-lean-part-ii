import DaggerModelsPartII.DiscreteBorelOrbitComparison

/-!
# Native strict orbits of discrete involutive diagrams

The categorical strict orbit of the native discrete action is compared with
the explicit strict-orbit diagram. The comparison respects invariant subsets.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalDaggerRealizationC2Action
open DaggerModels.FreeInvolution
open DaggerModels.PartII.C2InvolutionOrbits
open DaggerModels.PartII.DiscreteBorelDiagram
open DaggerModels.PartII.DiscreteBorelOrbitComparison

namespace DaggerModels.PartII.DiscreteStrictOrbitComparison

universe u

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- The generator on a discrete action in each degree is the specified involution. -/
theorem discreteAction_generator_degree (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ) :
    generatorEquiv (degreeAction
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (C2InvolutionActions.discreteAction X τ hτ)).obj c) q) =
      valueEquiv X τ c := by
  ext x
  rfl

/-- Degreewise comparison with the explicit involution orbit. -/
def discreteOrbitDegreeEquiv (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ) :
    ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (C2InvolutionActions.discreteAction X τ hτ)).obj c)).obj q ≃
      ((strictOrbitDiagram X τ hτ).obj c).obj q :=
  (nativeDegreeEquiv _ q).trans
    (orbitEquivOfEq _ _ _ _ (discreteAction_generator_degree C X τ hτ c q))

/-- The comparison sends a native cocone representative to its orbit class. -/
theorem discreteOrbitDegreeEquiv_ι (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ)
    (x : X.obj c) :
    discreteOrbitDegreeEquiv C X τ hτ c q
      ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj
        (((BorelDiagramFreeCells.actionDiagram C).obj
          (C2InvolutionActions.discreteAction X τ hτ)).obj c))
        (SingleObj.star C2.{u})).app q x) =
      orbit (valueEquiv X τ c) (valueInvolutive X τ hτ c) x := by
  rw [discreteOrbitDegreeEquiv, Equiv.trans_apply, nativeDegreeEquiv_ι]
  exact orbitEquivOfEq_orbit _ _ _ _
    (discreteAction_generator_degree C X τ hτ c q) x

/-- The degreewise comparison commutes with all simplicial operators. -/
def pointwiseDiscreteStrictOrbitComponent (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (C2InvolutionActions.discreteAction X τ hτ)).obj c) ≅
      (strictOrbitDiagram X τ hτ).obj c :=
  NatIso.ofComponents
    (fun q ↦ Equiv.toIso (discreteOrbitDegreeEquiv C X τ hτ c q)) (by
      intro q r f
      funext z
      let Ac := ((BorelDiagramFreeCells.actionDiagram C).obj
        (C2InvolutionActions.discreteAction X τ hτ)).obj c
      obtain ⟨x, rfl⟩ := degree_cocone_surjective Ac q z
      have hnat := congrFun
        ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
          (SingleObj.star C2.{u})).naturality f) x
      change ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
          (SingleObj.star C2.{u})).app r) (Ac.V.map f x) =
        ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj Ac).map f
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app q) x) at hnat
      change discreteOrbitDegreeEquiv C X τ hτ c r
          (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj Ac).map f
            (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
              (SingleObj.star C2.{u})).app q) x)) = _
      rw [← hnat]
      change discreteOrbitDegreeEquiv C X τ hτ c r
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app r) x) =
        ((strictOrbitDiagram X τ hτ).obj c).map f
          (discreteOrbitDegreeEquiv C X τ hτ c q
            (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
              (SingleObj.star C2.{u})).app q) x))
      rw [discreteOrbitDegreeEquiv_ι, discreteOrbitDegreeEquiv_ι]
      rfl)

/-- The objectwise strict-orbit comparison is natural in the diagram index. -/
def pointwiseDiscreteStrictOrbitIso (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    ((BorelDiagramFreeCells.actionDiagram C).obj
      (C2InvolutionActions.discreteAction X τ hτ)) ⋙
      ActionStrictOrbits.orbit SSet.{u} C2.{u} ≅
      strictOrbitDiagram X τ hτ :=
  NatIso.ofComponents (pointwiseDiscreteStrictOrbitComponent C X τ hτ) (by
    intro c d f
    apply NatTrans.ext
    funext q z
    let D := C2InvolutionActions.discreteAction X τ hτ
    let Dc := ((BorelDiagramFreeCells.actionDiagram C).obj D).obj c
    let Dd := ((BorelDiagramFreeCells.actionDiagram C).obj D).obj d
    let fD := ((BorelDiagramFreeCells.actionDiagram C).obj D).map f
    obtain ⟨x, rfl⟩ := degree_cocone_surjective Dc q z
    have hmap := congrFun
      (NatTrans.congr_app (colimit.ι_map
        ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.map fD)
        (SingleObj.star C2.{u})) q) x
    change ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fD).app q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dc)
          (SingleObj.star C2.{u})).app q) x) =
      ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dd)
        (SingleObj.star C2.{u})).app q) (fD.hom.app q x) at hmap
    change discreteOrbitDegreeEquiv C X τ hτ d q
        (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fD).app q
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dc)
            (SingleObj.star C2.{u})).app q) x)) =
      ((strictOrbitDiagram X τ hτ).map f).app q
        (discreteOrbitDegreeEquiv C X τ hτ c q
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dc)
            (SingleObj.star C2.{u})).app q) x))
    rw [hmap, discreteOrbitDegreeEquiv_ι, discreteOrbitDegreeEquiv_ι]
    rfl)

/-- The native categorical orbit is the explicit strict-orbit diagram. -/
def nativeDiscreteStrictOrbitIso (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).obj
      (C2InvolutionActions.discreteAction X τ hτ) ≅
      strictOrbitDiagram X τ hτ :=
  ((BorelDiagramFreeCells.orbitDiagramNatIso C).app
    (C2InvolutionActions.discreteAction X τ hτ)).trans
      (pointwiseDiscreteStrictOrbitIso C X τ hτ)

/-- The objectwise strict-orbit comparison respects invariant-subset inclusion. -/
theorem pointwiseDiscreteStrictOrbitIso_subset_natural
    (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
    (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c) :
    Functor.whiskerRight ((BorelDiagramFreeCells.actionDiagram C).map
        (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA))
        (ActionStrictOrbits.orbit SSet.{u} C2.{u}) ≫
      (pointwiseDiscreteStrictOrbitIso C X τ hτ).hom =
    (pointwiseDiscreteStrictOrbitIso C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)).hom ≫
      subsetStrictOrbitInclusion X τ hτ A hA := by
  apply NatTrans.ext
  funext c
  apply NatTrans.ext
  funext q z
  let B := C2InvolutionActions.discreteAction A.toFunctor
    (subsetAction X τ hτ A hA) (subsetAction_involutive X τ hτ A hA)
  let Bc := ((BorelDiagramFreeCells.actionDiagram C).obj B).obj c
  let Dc := ((BorelDiagramFreeCells.actionDiagram C).obj
    (C2InvolutionActions.discreteAction X τ hτ)).obj c
  let fc := ((BorelDiagramFreeCells.actionDiagram C).map
    (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA)).app c
  obtain ⟨x, rfl⟩ := degree_cocone_surjective Bc q z
  have hmap := congrFun
    (NatTrans.congr_app (colimit.ι_map
      ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.map fc)
      (SingleObj.star C2.{u})) q) x
  change ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fc).app q
      (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
        (SingleObj.star C2.{u})).app q) x) =
    ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dc)
      (SingleObj.star C2.{u})).app q) (fc.hom.app q x) at hmap
  change discreteOrbitDegreeEquiv C X τ hτ c q
      (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fc).app q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
          (SingleObj.star C2.{u})).app q) x)) =
    ((subsetStrictOrbitInclusion X τ hτ A hA).app c).app q
      (discreteOrbitDegreeEquiv C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) c q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
          (SingleObj.star C2.{u})).app q) x))
  rw [hmap, discreteOrbitDegreeEquiv_ι, discreteOrbitDegreeEquiv_ι]
  rfl

/-- The native strict-orbit comparison respects invariant-subset inclusions. -/
theorem nativeDiscreteStrictOrbitIso_subset_naturality
    (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
    (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
        (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA) ≫
      (nativeDiscreteStrictOrbitIso C X τ hτ).hom =
    (nativeDiscreteStrictOrbitIso C A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA)).hom ≫
      subsetStrictOrbitInclusion X τ hτ A hA := by
  dsimp only [nativeDiscreteStrictOrbitIso, Iso.trans_hom]
  change ((ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
      (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA) ≫
      (BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
        (C2InvolutionActions.discreteAction X τ hτ)) ≫
      (pointwiseDiscreteStrictOrbitIso C X τ hτ).hom =
    ((BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
      (C2InvolutionActions.discreteAction A.toFunctor
        (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)) ≫
      (pointwiseDiscreteStrictOrbitIso C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)).hom) ≫
      subsetStrictOrbitInclusion X τ hτ A hA
  rw [(BorelDiagramFreeCells.orbitDiagramNatIso C).hom.naturality
    (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA)]
  rw [Category.assoc, Category.assoc]
  exact congrArg
    ((BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
      (C2InvolutionActions.discreteAction A.toFunctor
        (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)) ≫ ·)
    (pointwiseDiscreteStrictOrbitIso_subset_natural C X τ hτ A hA)

end

end DaggerModels.PartII.DiscreteStrictOrbitComparison
