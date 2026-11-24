import DaggerModelsPartII.BorelFreeCellOrbits
import OriginalEC2SimplicialProjectiveCofibrancy
import OriginalSimplicialCategoryBarCoproductDegrees
import Mathlib.CategoryTheory.Action.Monoidal

/-!
# Diagonal Borel free-cell cancellation

For a simplicial C₂-action V and a simplicial set K, the diagonal action
on V times the native free action on K is isomorphic to the native free
action on the underlying product. The isomorphism uses the regular label
g to send (v, (g, k)) to (g, (g⁻¹v, k)). Its naturality in both V and K
and the resulting strict-orbit cancellation are proved below.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2FreeCellAction
open DaggerOriginalSimplicialActionFreeGenerators
open DaggerOriginalSimplicialCategoryBarCoproductDegrees

universe u

namespace DaggerModels.PartII.BorelDiagonalFreeAction

noncomputable section

variable (V : Action SSet.{u} C2.{u}) (K : SSet.{u})

private theorem rho_inv_apply (g : C2.{u}) (n : SimplexCategoryᵒᵖ)
    (v : V.V.obj n) :
    (V.ρ g⁻¹).app n ((V.ρ g).app n v) = v := by
  have h := (V.ρAut g).hom_inv_id
  have h' : V.ρ g ≫ V.ρ g⁻¹ = 𝟙 V.V := h
  exact congrFun (NatTrans.congr_app h' n) v

private theorem inv_rho_apply (g : C2.{u}) (n : SimplexCategoryᵒᵖ)
    (v : V.V.obj n) :
    (V.ρ g).app n ((V.ρ g⁻¹).app n v) = v := by
  have h := (V.ρAut g).inv_hom_id
  have h' : V.ρ g⁻¹ ≫ V.ρ g = 𝟙 V.V := h
  exact congrFun (NatTrans.congr_app h' n) v

private theorem rho_mul_apply (g h : C2.{u}) (n : SimplexCategoryᵒᵖ)
    (v : V.V.obj n) :
    (V.ρ g).app n ((V.ρ h).app n v) =
      (V.ρ (g * h)).app n v := by
  have h := V.ρ.map_mul g h
  exact (congrFun (NatTrans.congr_app h n) v).symm

/-- The diagonal action is untwisted degreewise by moving the group label
to the free factor. -/
def twistDegreeEquiv (n : SimplexCategoryᵒᵖ) :
    ((V ⊗ freeCellAction K).V).obj n ≃
      ((freeCellAction (V.V ⊗ K)).V).obj n where
  toFun x :=
    let p := (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).symm x.2
    coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n
      ⟨p.1, ((V.ρ p.1⁻¹).app n x.1, p.2)⟩
  invFun x :=
    let p := (coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n).symm x
    ((V.ρ p.1).app n p.2.1,
      coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨p.1, p.2.2⟩)
  left_inv x := by
    rcases x with ⟨v, x⟩
    obtain ⟨⟨g, k⟩, rfl⟩ :=
      (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).surjective x
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext (inv_rho_apply V g n v) rfl
  right_inv x := by
    obtain ⟨⟨g, ⟨v, k⟩⟩, rfl⟩ :=
      (coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n).surjective x
    simp only [Equiv.symm_apply_apply]
    rw [rho_inv_apply V g n v]

@[simp] theorem twistDegreeEquiv_apply (n : SimplexCategoryᵒᵖ)
    (g : C2.{u}) (v : V.V.obj n) (k : K.obj n) :
    twistDegreeEquiv V K n
      (v, coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩) =
    coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n
      ⟨g, ((V.ρ g⁻¹).app n v, k)⟩ := by
  simp [twistDegreeEquiv]

/-- The degreewise untwisting is simplicial. -/
def twistHom :
    (V ⊗ freeCellAction K).V ⟶ (freeCellAction (V.V ⊗ K)).V where
  app n := twistDegreeEquiv V K n
  naturality n m f := by
    funext x
    rcases x with ⟨v, y⟩
    obtain ⟨⟨g, k⟩, rfl⟩ :=
      (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).surjective y
    change
      (twistDegreeEquiv V K m)
        ((V.V.map f v),
          (∐ (fun (_ : C2.{u}) => K)).map f
            (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩)) =
      (∐ (fun (_ : C2.{u}) => V.V ⊗ K)).map f
        (twistDegreeEquiv V K n
          (v, coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩))
    rw [coproductDegreeEquiv_map]
    rw [twistDegreeEquiv_apply]
    rw [twistDegreeEquiv_apply]
    rw [coproductDegreeEquiv_map]
    congr 1
    congr 1
    change
      ((V.ρ g⁻¹).app m (V.V.map f v), K.map f k) =
        (V.V.map f ((V.ρ g⁻¹).app n v), K.map f k)
    exact Prod.ext (congrFun ((V.ρ g⁻¹).naturality f) v) rfl

/-- The simplicial untwisting commutes with the C₂-action. -/
theorem twistHom_equivariant (h : C2.{u}) :
    (V ⊗ freeCellAction K).ρ h ≫ twistHom V K =
      twistHom V K ≫ (freeCellAction (V.V ⊗ K)).ρ h := by
  apply NatTrans.ext
  funext n x
  rcases x with ⟨v, y⟩
  obtain ⟨⟨g, k⟩, rfl⟩ :=
    (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).surjective y
  change
    twistDegreeEquiv V K n
      ((V.ρ h).app n v,
        ((freeCellAction K).ρ h).app n
          (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩)) =
    ((freeCellAction (V.V ⊗ K)).ρ h).app n
      (twistDegreeEquiv V K n
        (v, coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩))
  have hsrc : ((freeCellAction K).ρ h).app n
        (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩) =
      coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨h * g, k⟩ :=
    congrFun (NatTrans.congr_app (freeCellAction_ι K h g) n) k
  have htar (a : (V.V ⊗ K).obj n) :
      ((freeCellAction (V.V ⊗ K)).ρ h).app n
        (coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n ⟨g, a⟩) =
      coproductDegreeEquiv (fun (_ : C2.{u}) => V.V ⊗ K) n ⟨h * g, a⟩ :=
    congrFun (NatTrans.congr_app (freeCellAction_ι (V.V ⊗ K) h g) n) a
  rw [hsrc, twistDegreeEquiv_apply, twistDegreeEquiv_apply, htar]
  congr 1
  congr 1
  rw [rho_mul_apply V (h * g)⁻¹ h n v]
  congr 1
  group

/-- Diagonal action on a free simplicial cell is a free action on the
underlying product. -/
def twistIso :
    V ⊗ freeCellAction K ≅ freeCellAction (V.V ⊗ K) :=
  Action.mkIso
    (NatIso.ofComponents
      (fun n => (twistDegreeEquiv V K n).toIso)
      (by
        intro n m f
        exact (twistHom V K).naturality f))
    (twistHom_equivariant V K)

theorem twistIso_hom_hom :
    (twistIso V K).hom.hom = twistHom V K := rfl

private theorem freeCellMap_app {A B : SSet.{u}} (f : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (g : C2.{u}) (a : A.obj n) :
    (freeCellMap f).hom.app n
      (coproductDegreeEquiv (fun (_ : C2.{u}) => A) n ⟨g, a⟩) =
    coproductDegreeEquiv (fun (_ : C2.{u}) => B) n ⟨g, f.app n a⟩ :=
  congrFun (NatTrans.congr_app (Limits.Sigma.ι_map (fun (_ : C2.{u}) => f) g) n) a

/-- The free-cell untwisting is natural in every simplicial cell map. -/
theorem twistIso_natural_cell {L : SSet.{u}} (f : K ⟶ L) :
    (𝟙 V ⊗ₘ freeCellMap f) ≫ (twistIso V L).hom =
      (twistIso V K).hom ≫ freeCellMap (V.V ◁ f) := by
  apply Action.hom_ext
  apply NatTrans.ext
  funext n x
  rcases x with ⟨v, y⟩
  obtain ⟨⟨g, k⟩, rfl⟩ :=
    (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).surjective y
  change
    twistDegreeEquiv V L n
      (v, (freeCellMap f).hom.app n
        (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩)) =
      (freeCellMap (V.V ◁ f)).hom.app n
        (twistDegreeEquiv V K n
          (v, coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩))
  rw [freeCellMap_app]
  rw [twistDegreeEquiv_apply, twistDegreeEquiv_apply]
  rw [freeCellMap_app]
  rfl

/-- The free-cell untwisting is natural in equivariant maps of the
other factor. -/
theorem twistIso_natural_action {W : Action SSet.{u} C2.{u}}
    (φ : V ⟶ W) :
    (φ ⊗ₘ 𝟙 (freeCellAction K)) ≫ (twistIso W K).hom =
      (twistIso V K).hom ≫ freeCellMap (φ.hom ▷ K) := by
  apply Action.hom_ext
  apply NatTrans.ext
  funext n x
  rcases x with ⟨v, y⟩
  obtain ⟨⟨g, k⟩, rfl⟩ :=
    (coproductDegreeEquiv (fun (_ : C2.{u}) => K) n).surjective y
  change
    twistDegreeEquiv W K n
      (φ.hom.app n v,
        coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩) =
      (freeCellMap (φ.hom ▷ K)).hom.app n
        (twistDegreeEquiv V K n
          (v, coproductDegreeEquiv (fun (_ : C2.{u}) => K) n ⟨g, k⟩))
  rw [twistDegreeEquiv_apply, twistDegreeEquiv_apply]
  rw [freeCellMap_app]
  congr 1
  congr 1
  change ((W.ρ g⁻¹).app n (φ.hom.app n v), k) =
    (φ.hom.app n ((V.ρ g⁻¹).app n v), k)
  congr 1
  change (W.ρ g⁻¹).app n (φ.hom.app n v) =
    φ.hom.app n ((V.ρ g⁻¹).app n v)
  exact (congrFun (NatTrans.congr_app (φ.comm g⁻¹) n) v).symm

/-- The same diagonal untwisting for the native free-action functor. -/
def nativeTwistIso :
    V ⊗ free.obj K ≅ free.obj (V.V ⊗ K) := by
  change V ⊗ freeCellAction K ≅ freeCellAction (V.V ⊗ K)
  exact twistIso V K

theorem nativeTwistIso_natural_cell {L : SSet.{u}} (f : K ⟶ L) :
    (𝟙 V ⊗ₘ free.map f) ≫ (nativeTwistIso V L).hom =
      (nativeTwistIso V K).hom ≫ free.map (V.V ◁ f) := by
  change
    (𝟙 V ⊗ₘ freeCellMap f) ≫ (twistIso V L).hom =
      (twistIso V K).hom ≫ freeCellMap (V.V ◁ f)
  exact twistIso_natural_cell V K f

theorem nativeTwistIso_natural_action {W : Action SSet.{u} C2.{u}}
    (φ : V ⟶ W) :
    (φ ⊗ₘ 𝟙 (free.obj K)) ≫ (nativeTwistIso W K).hom =
      (nativeTwistIso V K).hom ≫ free.map (φ.hom ▷ K) := by
  change
    (φ ⊗ₘ 𝟙 (freeCellAction K)) ≫ (twistIso W K).hom =
      (twistIso V K).hom ≫ freeCellMap (φ.hom ▷ K)
  exact twistIso_natural_action V K φ

/-- Strict orbits cancel the diagonal native free cell. -/
def orbitDiagonalFreeIso :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).obj (V ⊗ free.obj K) ≅
      V.V ⊗ K :=
  ((ActionStrictOrbits.orbit SSet.{u} C2.{u}).mapIso (nativeTwistIso V K)).trans
    ((BorelFreeCellOrbits.freeOrbitIso SSet.{u} C2.{u}).app (V.V ⊗ K))

/-- Orbit cancellation respects every cell map, including a boundary
inclusion. -/
theorem orbitDiagonalFreeIso_natural_cell {L : SSet.{u}} (f : K ⟶ L) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).map
        (𝟙 V ⊗ₘ free.map f) ≫ (orbitDiagonalFreeIso V L).hom =
      (orbitDiagonalFreeIso V K).hom ≫ (V.V ◁ f) := by
  let O := ActionStrictOrbits.orbit SSet.{u} C2.{u}
  let η := BorelFreeCellOrbits.freeOrbitIso SSet.{u} C2.{u}
  change
    O.map (𝟙 V ⊗ₘ free.map f) ≫
      (O.map (nativeTwistIso V L).hom ≫ η.hom.app (V.V ⊗ L)) =
    (O.map (nativeTwistIso V K).hom ≫ η.hom.app (V.V ⊗ K)) ≫
      (V.V ◁ f)
  rw [← Category.assoc, ← Functor.map_comp,
    nativeTwistIso_natural_cell V K f, Functor.map_comp]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact η.hom.naturality (V.V ◁ f)

theorem orbitDiagonalFreeIso_natural_action
    {W : Action SSet.{u} C2.{u}} (φ : V ⟶ W) :
    (ActionStrictOrbits.orbit SSet.{u} C2.{u}).map
        (φ ⊗ₘ 𝟙 (free.obj K)) ≫ (orbitDiagonalFreeIso W K).hom =
      (orbitDiagonalFreeIso V K).hom ≫ (φ.hom ▷ K) := by
  let O := ActionStrictOrbits.orbit SSet.{u} C2.{u}
  let η := BorelFreeCellOrbits.freeOrbitIso SSet.{u} C2.{u}
  change
    O.map (φ ⊗ₘ 𝟙 (free.obj K)) ≫
      (O.map (nativeTwistIso W K).hom ≫ η.hom.app (W.V ⊗ K)) =
    (O.map (nativeTwistIso V K).hom ≫ η.hom.app (V.V ⊗ K)) ≫
      (φ.hom ▷ K)
  rw [← Category.assoc, ← Functor.map_comp,
    nativeTwistIso_natural_action V K φ, Functor.map_comp]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact η.hom.naturality (φ.hom ▷ K)

end
end DaggerModels.PartII.BorelDiagonalFreeAction
