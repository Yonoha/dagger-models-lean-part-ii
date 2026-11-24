import DaggerModelsPartII.C2InvolutionActions
import DaggerModelsPartII.BorelDiagramFreeCells
import DaggerModelsPartII.EquivariantDiagramMapping
import Mathlib.CategoryTheory.Action.Monoidal

/-!
# Native strict C₂ orbits and explicit discrete Borel quotients

The orbit of the native diagonal action on a discrete involutive diagram
and the original simplicial `EC₂` is compared with the explicit pointwise
Borel quotient, preserving simplicial and external diagram maps.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalDaggerRealizationC2Action
open DaggerModels.FreeInvolution
open DaggerModels.PartII.C2InvolutionOrbits
open DaggerModels.PartII.DiscreteBorelDiagram
open DaggerModels.PartII.BorelDiscreteOrbits
open DaggerModels.PartII.EquivariantDiagramMapping

namespace DaggerModels.PartII.DiscreteBorelOrbitComparison

universe u

noncomputable section

/-- Evaluation of a simplicial C₂-action at one simplicial degree. -/
def degreeAction (V : Action SSet.{u} C2.{u})
    (q : SimplexCategoryᵒᵖ) : Action (Type u) C2.{u} where
  V := V.V.obj q
  ρ := {
    toFun g := End.of ((V.ρ g).app q)
    map_one' := by
      apply End.ext
      funext x
      have h := congrFun (NatTrans.congr_app (Action.ρ_one V) q) x
      exact h
    map_mul' := by
      intro g h
      apply End.ext
      funext x
      have hh := congrFun (NatTrans.congr_app (V.ρ.map_mul g h) q) x
      simpa only [End.mul_def] using hh }

/-- Simplicial operators are equivariant between their degree actions. -/
def degreeActionMap (V : Action SSet.{u} C2.{u})
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    degreeAction V q ⟶ degreeAction V r where
  hom := V.V.map f
  comm g := by
    funext x
    exact (congrFun ((V.ρ g).naturality f) x).symm

/-- The native strict orbit in each simplicial degree is exactly the
generator-involution orbit set. -/
def nativeDegreeEquiv (V : Action SSet.{u} C2.{u})
    (q : SimplexCategoryᵒᵖ) :
    ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V).obj q ≃
      Orbit (generatorEquiv (degreeAction V q))
        (generatorInvolutive (degreeAction V q)) :=
  (ActionStrictOrbits.simplicialDegreeEquiv V q).trans
    (orbitQuotientEquiv (degreeAction V q))

/-- The simplicial orbit set obtained degreewise from the generator. -/
def involutionOrbitSSet (V : Action SSet.{u} C2.{u}) : SSet.{u} where
  obj q := Orbit (generatorEquiv (degreeAction V q))
    (generatorInvolutive (degreeAction V q))
  map {q r} f :=
    DiscreteBorelDiagram.strictOrbitMap
      (generatorEquiv (degreeAction V q))
      (generatorInvolutive (degreeAction V q))
      (generatorEquiv (degreeAction V r))
      (generatorInvolutive (degreeAction V r))
      (V.V.map f) (generatorEquiv_comm (degreeActionMap V f))
  map_id q := by
    funext x
    induction x using Quotient.inductionOn with
    | _ x =>
      change orbit _ _ (V.V.map (𝟙 q) x) = orbit _ _ x
      rw [V.V.map_id]
      rfl
  map_comp f g := by
    funext x
    induction x using Quotient.inductionOn with
    | _ x =>
      change orbit _ _ (V.V.map (f ≫ g) x) =
        orbit _ _ (V.V.map g (V.V.map f x))
      rw [V.V.map_comp]
      rfl

theorem nativeDegreeEquiv_ι (V : Action SSet.{u} C2.{u})
    (q : SimplexCategoryᵒᵖ) (x : V.V.obj q) :
    nativeDegreeEquiv V q
      ((colimit.ι
        ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj V)
        (SingleObj.star C2.{u})).app q x) =
      orbit (generatorEquiv (degreeAction V q))
        (generatorInvolutive (degreeAction V q)) x := by
  let J := (Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj V
  change strictOrbitEquiv (degreeAction V q)
    ((colimitObjIsoColimitCompEvaluation J q).hom
      ((colimit.ι J (SingleObj.star C2.{u})).app q x)) = _
  have hh := congrFun
    (colimitObjIsoColimitCompEvaluation_ι_app_hom J
      (SingleObj.star C2.{u}) q) x
  change (colimitObjIsoColimitCompEvaluation J q).hom
      ((colimit.ι J (SingleObj.star C2.{u})).app q x) =
    colimit.ι (J ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj q)
      (SingleObj.star C2.{u}) x at hh
  rw [hh]
  exact strictOrbitEquiv_ι (degreeAction V q) x

theorem degree_cocone_surjective (V : Action SSet.{u} C2.{u})
    (q : SimplexCategoryᵒᵖ)
    (z : ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V).obj q) :
    ∃ x : V.V.obj q,
      ((colimit.ι
        ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj V)
        (SingleObj.star C2.{u})).app q) x = z := by
  let J := (Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj V
  let e := colimitObjIsoColimitCompEvaluation J q
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective'
    (F := J ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj q) (e.hom z)
  cases j
  refine ⟨x, ?_⟩
  apply e.toEquiv.injective
  have hh := congrFun
    (colimitObjIsoColimitCompEvaluation_ι_app_hom J
      (SingleObj.star C2.{u}) q) x
  change e.hom ((colimit.ι J (SingleObj.star C2.{u})).app q x) =
    colimit.ι (J ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj q)
      (SingleObj.star C2.{u}) x at hh
  exact hh.trans hx

theorem nativeDegreeEquiv_natural (V : Action SSet.{u} C2.{u})
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    (z : ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V).obj q) :
    nativeDegreeEquiv V r
      (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V).map f z) =
      (involutionOrbitSSet V).map f (nativeDegreeEquiv V q z) := by
  obtain ⟨x, rfl⟩ := degree_cocone_surjective V q z
  let J := (Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj V
  have hh := congrFun ((colimit.ι J (SingleObj.star C2.{u})).naturality f) x
  change ((colimit.ι J (SingleObj.star C2.{u})).app r)
      (V.V.map f x) =
    (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V).map f)
      (((colimit.ι J (SingleObj.star C2.{u})).app q) x) at hh
  rw [← hh, nativeDegreeEquiv_ι, nativeDegreeEquiv_ι]
  rfl

/-- The native categorical strict orbit is naturally the explicit
involution-orbit simplicial set, for every simplicial C₂-action. -/
def nativeOrbitIso (V : Action SSet.{u} C2.{u}) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj V ≅
      involutionOrbitSSet V :=
  NatIso.ofComponents
    (fun q ↦ Equiv.toIso (nativeDegreeEquiv V q)) (by
      intro q r f
      funext z
      exact nativeDegreeEquiv_natural V f z)

/-- The native action on a constant set with the prescribed involution. -/
def discreteSetAction {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) : Action SSet.{u} C2.{u} :=
  ((SimplicialObject.const (Type u)).mapAction C2.{u}).obj
    (C2InvolutionActions.ofInvolution τ.toFun (by
      funext x
      exact hτ x))

/-- The native diagonal action used in the discrete Borel construction. -/
def diagonalSetAction {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) : Action SSet.{u} C2.{u} :=
  discreteSetAction τ hτ ⊗ DaggerOriginalEC2SimplicialAction.simplicialAction

theorem diagonalSetAction_generator {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) (q : SimplexCategoryᵒᵖ) :
    generatorEquiv (degreeAction (diagonalSetAction τ hτ) q) =
      DiagonalInvolutionOrbits.diagonal τ
        (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
          BorelDiscreteOrbits.ec2Involution q) := by
  ext p
  rfl

/-- Change the presentation of an involution orbit quotient along equality
of the underlying involutions. -/
def orbitEquivOfEq {Z : Type u} (α β : Z ≃ Z)
    (hα : Function.Involutive α) (hβ : Function.Involutive β)
    (e : α = β) : Orbit α hα ≃ Orbit β hβ := by
  cases e
  exact Equiv.refl _

theorem orbitEquivOfEq_orbit {Z : Type u} (α β : Z ≃ Z)
    (hα : Function.Involutive α) (hβ : Function.Involutive β)
    (e : α = β) (z : Z) :
    orbitEquivOfEq α β hα hβ e (orbit α hα z) = orbit β hβ z := by
  cases e
  rfl

/-- The orbit comparison in one simplicial degree of the diagonal action. -/
def diagonalOrbitDegreeEquiv {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) (q : SimplexCategoryᵒᵖ) :
    Orbit (generatorEquiv (degreeAction (diagonalSetAction τ hτ) q))
      (generatorInvolutive (degreeAction (diagonalSetAction τ hτ) q)) ≃
    DiagonalInvolutionOrbits.DiagonalOrbit τ hτ
      (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
        BorelDiscreteOrbits.ec2Involution q)
      (degree_involutive _ _ BorelDiscreteOrbits.ec2Involution_square q) :=
  orbitEquivOfEq
    (generatorEquiv (degreeAction (diagonalSetAction τ hτ) q))
    (DiagonalInvolutionOrbits.diagonal τ
      (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
        BorelDiscreteOrbits.ec2Involution q))
    (generatorInvolutive (degreeAction (diagonalSetAction τ hτ) q))
    (DiagonalInvolutionOrbits.diagonal_involutive τ hτ
      (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
        BorelDiscreteOrbits.ec2Involution q)
      (degree_involutive _ _ BorelDiscreteOrbits.ec2Involution_square q))
    (diagonalSetAction_generator τ hτ q)

theorem diagonalOrbitDegreeEquiv_orbit {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) (q : SimplexCategoryᵒᵖ)
    (p : X × DaggerOriginalEC2SimplicialAction.simplicialEC2.obj q) :
    diagonalOrbitDegreeEquiv τ hτ q
      (orbit (generatorEquiv (degreeAction (diagonalSetAction τ hτ) q))
        (generatorInvolutive (degreeAction (diagonalSetAction τ hτ) q)) p) =
    orbit (DiagonalInvolutionOrbits.diagonal τ
      (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
        BorelDiscreteOrbits.ec2Involution q))
      (DiagonalInvolutionOrbits.diagonal_involutive τ hτ
        (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
          BorelDiscreteOrbits.ec2Involution q)
        (degree_involutive _ _ BorelDiscreteOrbits.ec2Involution_square q)) p :=
  orbitEquivOfEq_orbit _ _ _ _ (diagonalSetAction_generator τ hτ q) p

/-- The generator-orbit simplicial set of the native diagonal action is
the explicit Borel quotient. -/
def diagonalBorelIso {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) :
    involutionOrbitSSet (diagonalSetAction τ hτ) ≅
      borel DaggerOriginalEC2SimplicialAction.simplicialEC2
        BorelDiscreteOrbits.ec2Involution
        BorelDiscreteOrbits.ec2Involution_square τ hτ :=
  NatIso.ofComponents
    (fun q ↦ Equiv.toIso (diagonalOrbitDegreeEquiv τ hτ q)) (by
      intro q r f
      funext z
      induction z using Quotient.inductionOn with
      | _ p =>
        change diagonalOrbitDegreeEquiv τ hτ r
          (orbit _ _ ((diagonalSetAction τ hτ).V.map f p)) =
          (borel DaggerOriginalEC2SimplicialAction.simplicialEC2
            BorelDiscreteOrbits.ec2Involution
            BorelDiscreteOrbits.ec2Involution_square τ hτ).map f
            (diagonalOrbitDegreeEquiv τ hτ q (orbit _ _ p))
        rw [diagonalOrbitDegreeEquiv_orbit, diagonalOrbitDegreeEquiv_orbit]
        rfl)

/-- The native categorical strict orbit of the diagonal C₂-action is the
explicit Borel simplicial set, including all simplicial operators. -/
def nativeDiagonalBorelIso {X : Type u} (τ : X ≃ X)
    (hτ : Function.Involutive τ) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj
      (diagonalSetAction τ hτ) ≅
    borel DaggerOriginalEC2SimplicialAction.simplicialEC2
      BorelDiscreteOrbits.ec2Involution
      BorelDiscreteOrbits.ec2Involution_square τ hτ :=
  (nativeOrbitIso (diagonalSetAction τ hτ)).trans
    (diagonalBorelIso τ hτ)

variable (C : Type u) [Category.{u} C]

/-- The native diagonal C₂-action on a discrete involutive diagram and
the actual simplicial `EC₂`. -/
def nativeBorelAction (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    Action (C ⥤ SSet.{u}) C2.{u} :=
  C2InvolutionActions.discreteAction X τ hτ ⊗
    ((Functor.const C).mapAction C2.{u}).obj
      DaggerOriginalEC2SimplicialAction.simplicialAction

/-- Evaluating the native diagram action gives the literal diagonal
action on the corresponding set. -/
theorem nativeBorelAction_eval (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) :
    ((BorelDiagramFreeCells.actionDiagram C).obj
      (nativeBorelAction C X τ hτ)).obj c =
      diagonalSetAction (valueEquiv X τ c) (valueInvolutive X τ hτ c) := by
  change Action.mk _ _ = Action.mk _ _
  congr 1
  ext g
  change ((nativeBorelAction C X τ hτ).ρ g).app c =
    (diagonalSetAction (valueEquiv X τ c)
      (valueInvolutive X τ hτ c)).ρ g
  rcases c2_cases g with rfl | rfl
  · rfl
  · rfl

theorem nativeBorelAction_generator_degree (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ) :
    generatorEquiv (degreeAction
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (nativeBorelAction C X τ hτ)).obj c) q) =
      DiagonalInvolutionOrbits.diagonal (valueEquiv X τ c)
        (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
          BorelDiscreteOrbits.ec2Involution q) := by
  ext p
  rfl

/-- Degreewise native orbit comparison at an external diagram value. -/
def pointwiseDegreeEquiv (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ) :
    ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (nativeBorelAction C X τ hτ)).obj c)).obj q ≃
      ((actualBorelDiagram X τ hτ).obj c).obj q :=
  (nativeDegreeEquiv _ q).trans
    (orbitEquivOfEq _ _ _ _
      (nativeBorelAction_generator_degree C X τ hτ c q))

/-- A representative in the native categorical colimit maps to its
literal class in the Borel quotient. -/
theorem pointwiseDegreeEquiv_ι (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) (q : SimplexCategoryᵒᵖ)
    (p : X.obj c × DaggerOriginalEC2SimplicialAction.simplicialEC2.obj q) :
    pointwiseDegreeEquiv C X τ hτ c q
      ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj
        (((BorelDiagramFreeCells.actionDiagram C).obj
          (nativeBorelAction C X τ hτ)).obj c))
        (SingleObj.star C2.{u})).app q p) =
      orbit
        (DiagonalInvolutionOrbits.diagonal (valueEquiv X τ c)
          (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
            BorelDiscreteOrbits.ec2Involution q))
        (DiagonalInvolutionOrbits.diagonal_involutive
          (valueEquiv X τ c) (valueInvolutive X τ hτ c)
          (degreeEquiv DaggerOriginalEC2SimplicialAction.simplicialEC2
            BorelDiscreteOrbits.ec2Involution q)
          (degree_involutive _ _ BorelDiscreteOrbits.ec2Involution_square q)) p := by
  rw [pointwiseDegreeEquiv, Equiv.trans_apply, nativeDegreeEquiv_ι,
    ]
  exact orbitEquivOfEq_orbit _ _ _ _
    (nativeBorelAction_generator_degree C X τ hτ c q) p

/-- The objectwise comparison, obtained from the exact evaluated native
action and the simplicial Borel comparison. -/
def pointwiseBorelComponent (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (c : C) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj
      (((BorelDiagramFreeCells.actionDiagram C).obj
        (nativeBorelAction C X τ hτ)).obj c) ≅
      (actualBorelDiagram X τ hτ).obj c :=
  NatIso.ofComponents
    (fun q ↦ Equiv.toIso (pointwiseDegreeEquiv C X τ hτ c q)) (by
      intro q r f
      funext z
      let Ac := ((BorelDiagramFreeCells.actionDiagram C).obj
        (nativeBorelAction C X τ hτ)).obj c
      obtain ⟨p, rfl⟩ := degree_cocone_surjective Ac q z
      have hnat := congrFun
        ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
          (SingleObj.star C2.{u})).naturality f) p
      change ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
          (SingleObj.star C2.{u})).app r) (Ac.V.map f p) =
        ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj Ac).map f
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app q) p) at hnat
      change pointwiseDegreeEquiv C X τ hτ c r
          (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj Ac).map f
            (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
              (SingleObj.star C2.{u})).app q) p)) = _
      rw [← hnat, pointwiseDegreeEquiv_ι]
      change _ = ((actualBorelDiagram X τ hτ).obj c).map f
        (pointwiseDegreeEquiv C X τ hτ c q
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app q) p))
      rw [pointwiseDegreeEquiv_ι]
      rfl)

/-- The pointwise comparison is natural in the external diagram index. -/
def pointwiseBorelIso (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    ((BorelDiagramFreeCells.actionDiagram C).obj
      (nativeBorelAction C X τ hτ)) ⋙
      ActionStrictOrbits.orbit SSet.{u} C2.{u} ≅
      actualBorelDiagram X τ hτ :=
  NatIso.ofComponents (pointwiseBorelComponent C X τ hτ) (by
    intro c d f
    apply NatTrans.ext
    funext q z
    let A := nativeBorelAction C X τ hτ
    let Ac := ((BorelDiagramFreeCells.actionDiagram C).obj A).obj c
    let Ad := ((BorelDiagramFreeCells.actionDiagram C).obj A).obj d
    let fA := ((BorelDiagramFreeCells.actionDiagram C).obj A).map f
    obtain ⟨p, rfl⟩ := degree_cocone_surjective Ac q z
    have hmap := congrFun
      (NatTrans.congr_app (colimit.ι_map
        ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.map fA)
        (SingleObj.star C2.{u})) q) p
    change ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fA).app q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
          (SingleObj.star C2.{u})).app q) p) =
      ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ad)
        (SingleObj.star C2.{u})).app q) (fA.hom.app q p) at hmap
    change pointwiseDegreeEquiv C X τ hτ d q
        (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fA).app q
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app q) p)) =
      ((actualBorelDiagram X τ hτ).map f).app q
        (pointwiseDegreeEquiv C X τ hτ c q
          (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Ac)
            (SingleObj.star C2.{u})).app q) p))
    rw [hmap, pointwiseDegreeEquiv_ι, pointwiseDegreeEquiv_ι]
    rfl)

/-- The native categorical strict orbit of the Borel action is the explicit
diagram-valued Borel quotient. -/
def nativeBorelDiagramIso (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).obj
      (nativeBorelAction C X τ hτ) ≅ actualBorelDiagram X τ hτ :=
  ((BorelDiagramFreeCells.orbitDiagramNatIso C).app
    (nativeBorelAction C X τ hτ)).trans (pointwiseBorelIso C X τ hτ)

/-- The native diagonal action map induced by an invariant subset. -/
def subsetBorelActionMap (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c) :
    nativeBorelAction C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) ⟶
      nativeBorelAction C X τ hτ :=
  C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA ⊗ₘ
    𝟙 (((Functor.const C).mapAction C2.{u}).obj
      DaggerOriginalEC2SimplicialAction.simplicialAction)

/-- The pointwise orbit comparison respects an invariant subset inclusion. -/
theorem pointwiseBorelIso_subset_natural (X : C ⥤ Type u) (τ : X ≅ X)
    (hτ : τ.hom ≫ τ.hom = 𝟙 X) (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c) :
    Functor.whiskerRight ((BorelDiagramFreeCells.actionDiagram C).map
        (subsetBorelActionMap C X τ hτ A hA))
        (ActionStrictOrbits.orbit SSet.{u} C2.{u}) ≫
      (pointwiseBorelIso C X τ hτ).hom =
    (pointwiseBorelIso C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)).hom ≫
      subsetBorelDiagramInclusion X τ hτ
        DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square A hA := by
  apply NatTrans.ext
  funext c
  apply NatTrans.ext
  funext q z
  let B := nativeBorelAction C A.toFunctor (subsetAction X τ hτ A hA)
    (subsetAction_involutive X τ hτ A hA)
  let Bc := ((BorelDiagramFreeCells.actionDiagram C).obj B).obj c
  let Dc := ((BorelDiagramFreeCells.actionDiagram C).obj
    (nativeBorelAction C X τ hτ)).obj c
  let fc := ((BorelDiagramFreeCells.actionDiagram C).map
    (subsetBorelActionMap C X τ hτ A hA)).app c
  obtain ⟨p, rfl⟩ := degree_cocone_surjective Bc q z
  have hmap := congrFun
    (NatTrans.congr_app (colimit.ι_map
      ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.map fc)
      (SingleObj.star C2.{u})) q) p
  change ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fc).app q
      (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
        (SingleObj.star C2.{u})).app q) p) =
    ((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Dc)
      (SingleObj.star C2.{u})).app q) (fc.hom.app q p) at hmap
  change pointwiseDegreeEquiv C X τ hτ c q
      (((ActionStrictOrbits.orbit SSet.{u} C2.{u}).map fc).app q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
          (SingleObj.star C2.{u})).app q) p)) =
    ((subsetBorelDiagramInclusion X τ hτ
      DaggerOriginalEC2SimplicialAction.simplicialEC2
      ec2Involution ec2Involution_square A hA).app c).app q
      (pointwiseDegreeEquiv C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA) c q
        (((colimit.ι ((Action.functorCategoryEquivalence SSet.{u} C2.{u}).functor.obj Bc)
          (SingleObj.star C2.{u})).app q) p))
  rw [hmap, pointwiseDegreeEquiv_ι, pointwiseDegreeEquiv_ι]
  rfl

/-- The native Borel comparison respects invariant-subset inclusions. -/
theorem nativeBorelDiagramIso_subset_naturality
    (X : C ⥤ Type u) (τ : X ≅ X) (hτ : τ.hom ≫ τ.hom = 𝟙 X)
    (A : Subfunctor X)
    (hA : ∀ c x, x ∈ A.obj c → valueEquiv X τ c x ∈ A.obj c) :
    ((orbitTensorBifunctor C).map
      (C2InvolutionActions.discreteSubsetInclusion X τ hτ A hA)).app
        DaggerOriginalEC2SimplicialAction.simplicialAction ≫
      (nativeBorelDiagramIso C X τ hτ).hom =
    (nativeBorelDiagramIso C A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA)).hom ≫
      subsetBorelDiagramInclusion X τ hτ
        DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square A hA := by
  change (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
      (subsetBorelActionMap C X τ hτ A hA) ≫
      (nativeBorelDiagramIso C X τ hτ).hom =
    (nativeBorelDiagramIso C A.toFunctor (subsetAction X τ hτ A hA)
      (subsetAction_involutive X τ hτ A hA)).hom ≫
      subsetBorelDiagramInclusion X τ hτ
        DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square A hA
  dsimp only [nativeBorelDiagramIso, Iso.trans_hom]
  change ((ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
      (subsetBorelActionMap C X τ hτ A hA) ≫
      (BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
        (nativeBorelAction C X τ hτ)) ≫
      (pointwiseBorelIso C X τ hτ).hom =
    ((BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
      (nativeBorelAction C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)) ≫
      (pointwiseBorelIso C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)).hom) ≫
      subsetBorelDiagramInclusion X τ hτ
        DaggerOriginalEC2SimplicialAction.simplicialEC2
        ec2Involution ec2Involution_square A hA
  rw [(BorelDiagramFreeCells.orbitDiagramNatIso C).hom.naturality
    (subsetBorelActionMap C X τ hτ A hA)]
  rw [Category.assoc, Category.assoc]
  exact congrArg
    ((BorelDiagramFreeCells.orbitDiagramNatIso C).hom.app
      (nativeBorelAction C A.toFunctor (subsetAction X τ hτ A hA)
        (subsetAction_involutive X τ hτ A hA)) ≫ ·)
    (pointwiseBorelIso_subset_natural C X τ hτ A hA)

end

end DaggerModels.PartII.DiscreteBorelOrbitComparison
