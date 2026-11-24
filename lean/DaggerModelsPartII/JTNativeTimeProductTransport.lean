import DaggerModelsPartII.JTGraphCoveredProductInterface

/-!
Transport literal native/time products along an actual native natural
isomorphism. The proof is generic in the code functors, so specializing it
does not recheck the internal construction of a coefficient family.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeTimeProductTransport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev SF := NecklaceCode.simplicialFunctor

variable {I : Type} [SmallCategory I] {N M : I ⥤ NecklaceCode}
variable (e : N ≅ M) (time : I ⥤ SimplexCategory)

/-- The original native isomorphism and unchanged time form an isomorphism
of pairs, before applying the simplicial tensor functor. -/
def pairIso : (N ⋙ SF).prod' (time ⋙ J) ≅ (M ⋙ SF).prod' (time ⋙ J) :=
  NatIso.ofComponents (fun a ↦ Iso.prod (SF.mapIso (e.app a)) (Iso.refl _)) (by
    intro a b f
    apply Prod.ext
    · change SF.map (N.map f) ≫ SF.map (e.hom.app b) =
        SF.map (e.hom.app a) ≫ SF.map (M.map f)
      rw [← SF.map_comp, ← SF.map_comp, e.hom.naturality]
    · change J.map (time.map f) ≫ 𝟙 _ = 𝟙 _ ≫ J.map (time.map f)
      rw [Category.comp_id, Category.id_comp])

/-- The complete native/time product retains both original coordinates. -/
def iso : JTGraphCoveredProductInterface.product N time ≅
    JTGraphCoveredProductInterface.product M time :=
  Functor.isoWhiskerRight (pairIso e time) (MonoidalCategory.tensor SSet.{0})

/-- The forward component is the given native component tensored with the
identity of the entire original time simplex. -/
theorem hom_app (a : I) :
    (iso e time).hom.app a = (e.hom.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a)) := rfl

/-- The inverse component has the same unchanged time coordinate. -/
theorem inv_app (a : I) :
    (iso e time).inv.app a = (e.inv.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a)) := rfl

end
end DaggerModels.PartII.JTNativeTimeProductTransport
