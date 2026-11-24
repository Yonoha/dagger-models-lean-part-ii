import DaggerModelsPartII.JTOrdinalInverseFaceDiagram
import DaggerModelsPartII.JTOrdinalFaceParameterPullback

/-! Natural groupoid parameters on full inverse-image ordinal faces. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTOrdinalInverseFaceParameterDiagram

open JTJointRelativeParameters (parameter_ext)
open JTCodiscreteParameterPairing (coord coord_map)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev zero := op (⦋0⦌ : SimplexCategory)

variable {I : Type} [SmallCategory I]
variable (S K D : I ⥤ SimplexCategory) (u : S ⟶ K) (α : D ⟶ K)
variable (hu : ∀ i : I, Mono (u.app i))
variable (hα : ∀ i : I, Function.Surjective (α.app i).toOrderHom)
variable (X : I ⥤ SSet.{0}) (θ : X ⟶ D ⋙ J) (q : X ⟶ S ⋙ J)
variable (h : θ ≫ Functor.whiskerRight α J = q ≫ Functor.whiskerRight u J)

private abbrev P := JTOrdinalInverseFaceDiagram.supportDiagram S K D u α hu hα
private abbrev inc := JTOrdinalInverseFaceDiagram.inclNat S K D u α hu hα
private abbrev old := JTOrdinalInverseFaceDiagram.toFaceNat S K D u α hu hα

include θ q h in

private theorem square_at (i : I) :
    θ.app i ≫ J.map (α.app i) = q.app i ≫ J.map (u.app i) := by
  exact congrArg (fun η : X ⟶ K ⋙ J ↦ η.app i) h

private theorem parameter_map_injective {s d : SimplexCategory} (v : s ⟶ d)
    (hv : Function.Injective v.toOrderHom) {Y : SSet.{0}}
    {f g : Y ⟶ J.obj s} (he : f ≫ J.map v = g ≫ J.map v) : f = g := by
  apply parameter_ext
  intro x
  apply hv
  have he₀ := congrArg (fun t ↦ coord d zero t 0)
    (congrFun (NatTrans.congr_app he zero) x)
  simpa only [NatTrans.comp_app, types_comp_apply, coord_map] using he₀

include θ q h

/-- The objectwise factor keeps the complete parameter, without choosing a
new lift of its ordinal vertices. -/
def factorApp (i : I) : X.obj i ⟶ J.obj ((P S K D u α hu hα).obj i) :=
  JTOrdinalFaceParameterPullback.factor (u.app i) (α.app i) (hα i)
    (θ.app i) (q.app i) (square_at S K D u α X θ q h i)

/-- The factor still projects to the exact original coefficient parameter. -/
theorem factorApp_incl (i : I) :
    factorApp S K D u α hu hα X θ q h i ≫
      J.map ((inc S K D u α hu hα).app i) = θ.app i :=
  JTOrdinalFaceParameterPullback.factor_incl (u.app i) (α.app i) (hα i)
    (θ.app i) (q.app i) (square_at S K D u α X θ q h i)

/-- The old support-face parameter is retained literally. -/
theorem factorApp_toOld (i : I) :
    factorApp S K D u α hu hα X θ q h i ≫
      J.map ((old S K D u α hu hα).app i) = q.app i :=
  JTOrdinalFaceParameterPullback.factor_toFace (u.app i) (α.app i) (hα i)
    (θ.app i) (q.app i)
    (SimplexCategory.mono_iff_injective.mp (hu i))
    (square_at S K D u α X θ q h i)

/-- The factors are natural under every original diagram arrow. -/
theorem factorApp_natural {i j : I} (f : i ⟶ j) :
    X.map f ≫ factorApp S K D u α hu hα X θ q h j =
      factorApp S K D u α hu hα X θ q h i ≫
        J.map ((P S K D u α hu hα).map f) := by
  apply parameter_map_injective
    ((inc S K D u α hu hα).app j)
    (SimplexCategory.mono_iff_injective.mp
      (JTOrdinalInverseFaceDiagram.incl_mono S K D u α hu hα j))
  calc
    (X.map f ≫ factorApp S K D u α hu hα X θ q h j) ≫
        J.map ((inc S K D u α hu hα).app j) =
      X.map f ≫ θ.app j := by
        rw [Category.assoc, factorApp_incl]
    _ = θ.app i ≫ J.map (D.map f) := by
      simpa only [Functor.comp_map] using θ.naturality f
    _ = (factorApp S K D u α hu hα X θ q h i ≫
        J.map ((P S K D u α hu hα).map f)) ≫
          J.map ((inc S K D u α hu hα).app j) := by
      rw [Category.assoc, ← J.map_comp,
        (inc S K D u α hu hα).naturality f,
        J.map_comp, ← Category.assoc, factorApp_incl]

/-- A natural full inverse-image parameter over the original entire diagram. -/
def factor (θ : X ⟶ D ⋙ J) (q : X ⟶ S ⋙ J)
    (h : θ ≫ Functor.whiskerRight α J = q ≫ Functor.whiskerRight u J) :
    X ⟶ P S K D u α hu hα ⋙ J where
  app := factorApp S K D u α hu hα X θ q h
  naturality := by
    intro i j f
    change X.map f ≫ factorApp S K D u α hu hα X θ q h j =
      factorApp S K D u α hu hα X θ q h i ≫
        J.map ((P S K D u α hu hα).map f)
    exact factorApp_natural S K D u α hu hα X θ q h f

/-- Inclusion recovers the exact original parameter naturally. -/
theorem factor_incl :
    factor S K D u α hu hα X θ q h ≫ Functor.whiskerRight
      (inc S K D u α hu hα) J = θ := by
  apply NatTrans.ext
  funext i
  exact factorApp_incl S K D u α hu hα X θ q h i

/-- The old face coordinate also remains the prescribed natural parameter. -/
theorem factor_toOld :
    factor S K D u α hu hα X θ q h ≫ Functor.whiskerRight
      (old S K D u α hu hα) J = q := by
  apply NatTrans.ext
  funext i
  exact factorApp_toOld S K D u α hu hα X θ q h i

/-- A natural factor with the same original coefficient projection is unique. -/
theorem factor_unique (ψ : X ⟶ P S K D u α hu hα ⋙ J)
    (hψ : ψ ≫ Functor.whiskerRight (inc S K D u α hu hα) J = θ) :
    ψ = factor S K D u α hu hα X θ q h := by
  apply NatTrans.ext
  funext i
  apply parameter_map_injective
    ((inc S K D u α hu hα).app i)
    (SimplexCategory.mono_iff_injective.mp
      (JTOrdinalInverseFaceDiagram.incl_mono S K D u α hu hα i))
  have hi := congrArg (fun η : X ⟶ D ⋙ J ↦ η.app i) hψ
  change ψ.app i ≫ J.map ((inc S K D u α hu hα).app i) = θ.app i at hi
  rw [hi]
  exact (factorApp_incl S K D u α hu hα X θ q h i).symm

end
end DaggerModels.PartII.JTOrdinalInverseFaceParameterDiagram
