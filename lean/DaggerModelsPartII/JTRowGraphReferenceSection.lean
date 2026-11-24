import DaggerModelsPartII.JTSimplicialTargetRowGraphResolution
import DaggerModelsPartII.JTRowGraphDegeneracyNormalization

/-! A coherent coefficient reference in the resolution of a simplicial target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTSimplicialTargetRowGraphResolution

open OrdinaryJTRealization JTRowGraphResolution JTRowGraphFiber JTRowGraphCategory
open JTRowGraphParameterSupport JTRowGraphNormalForm JTRowGraphDegeneracyNormalization

noncomputable section

variable {W : BiPresheaf} {X : SSet.{0}} (q : X ⟶ realization.obj W)

/-- The canonical coefficient at each simplex, with its exact raw value. -/
def referenceObj (P : X.Elements) : Resolution q :=
  ⟨P, op (center (value q P))⟩

/-- The compatibility needed to use the canonical reference on every horizontal restriction. -/
def ReferenceCompatible {B : Type} [SmallCategory B] (base : B ⥤ X.Elements) : Prop :=
  ∀ {P Q : B} (f : P ⟶ Q),
    restrictGraph (base.map f).val.unop (canonical (value q (base.obj P))) =
      canonical (value q (base.obj Q))

variable {B : Type} [SmallCategory B] {base : B ⥤ X.Elements}

private theorem ext_of_surjective {P Q : Resolution q}
    (hs : Function.Surjective (label Q.fiber.unop.obj.parameter))
    {f g : P ⟶ Q} (h : f.base = g.base) : f = g := by
  apply Grothendieck.ext f g h
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  exact hom_ext_of_label_surjective hs _ _

private theorem reference_ext {P : Resolution q} (Q : X.Elements)
    {f g : P ⟶ referenceObj q Q} (h : f.base = g.base) : f = g := by
  apply ext_of_surjective q (Q := referenceObj q Q) _ h
  change Function.Surjective (label (canonical (value q Q)).parameter)
  exact normal_parameter_surjective _

private def referenceMap (h : ReferenceCompatible q base) {P Q : B} (f : P ⟶ Q) :
    referenceObj q (base.obj P) ⟶ referenceObj q (base.obj Q) :=
  ⟨base.map f, Quiver.Hom.op ⟨eqToHom (h f).symm⟩⟩

/-- Compatible canonical graphs give a reference retaining every horizontal operator. -/
def reference (h : ReferenceCompatible q base) : B ⥤ Resolution q where
  obj P := referenceObj q (base.obj P)
  map f := referenceMap q h f
  map_id P := reference_ext q (base.obj P) (base.map_id P)
  map_comp {_ _ R} f g := reference_ext q (base.obj R) (base.map_comp f g)

theorem reference_forget (h : ReferenceCompatible q base) :
    reference q h ⋙ Grothendieck.forget (diagram q) = base := by
  cases base
  rfl

private abbrev toZero (d : SimplexCategory) := SimplexCategory.isTerminalZero.from d

private theorem canonical_eq_of_point (p : (Δ[0] : SSet.{0}) ⟶ realization.obj W)
    {P : X.Elements}
    (h : value q P = SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj P.1.unop) ≫ p) :
    canonical (value q P) = restrictGraph (toZero P.1.unop) (canonical p) := by
  have ht := SSet.stdSimplex.isTerminalObj₀.hom_ext
    (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj P.1.unop))
    (SSet.stdSimplex.map (toZero P.1.unop))
  rw [h, ht]
  let a := toZero P.1.unop
  let b := SimplexCategory.const ⦋0⦌ P.1.unop 0
  exact canonical_restrictGraph_of_splitEpi a b (SimplexCategory.isTerminalZero.hom_ext _ _) p

/-- When all raw simplices restrict from the same point, their canonical graphs
commute with all the original operators. -/
theorem referenceCompatible_of_point (p : (Δ[0] : SSet.{0}) ⟶ realization.obj W)
    (h : ∀ P, value q (base.obj P) =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj (base.obj P).1.unop) ≫ p) :
    ReferenceCompatible q base := by
  intro P Q f
  let a := (base.map f).val.unop
  rw [canonical_eq_of_point q p (h P), canonical_eq_of_point q p (h Q)]
  have hcomp := Functor.congr_obj (restrict_comp W a (toZero (base.obj P).1.unop)) (canonical p)
  have hz := SimplexCategory.isTerminalZero.hom_ext (a ≫ toZero (base.obj P).1.unop)
    (toZero (base.obj Q).1.unop)
  exact hcomp.symm.trans (congrArg (fun b ↦ restrictGraph b (canonical p)) hz)

/-- In a constant-raw diagram every canonical graph uses the same coefficient,
pulled back in its own horizontal degree. -/
theorem reference_of_point_obj (p : (Δ[0] : SSet.{0}) ⟶ realization.obj W)
    (h : ∀ P, value q (base.obj P) =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj (base.obj P).1.unop) ≫ p)
    (P : B) :
    ((reference q (referenceCompatible_of_point q p h)).obj P).fiber.unop.obj =
      restrictGraph (toZero (base.obj P).1.unop) (canonical p) :=
  canonical_eq_of_point q p (h P)

private def compareAt (P : Resolution q)
    (hs : Function.Surjective (label P.fiber.unop.obj.parameter)) :
    referenceObj q P.base ⟶ P :=
  ⟨𝟙 P.base, Quiver.Hom.op ⟨toCanonicalOfSurjective P.fiber.unop.obj hs ≫
    eqToHom (congrArg canonical P.fiber.unop.property) ≫
    eqToHom (Functor.congr_obj (restrict_id W P.base.1.unop) (center (value q P.base)).obj).symm⟩⟩

/-- Compare a canonical reference naturally to a diagram whose graphs already
use every vertex of their respective coefficients. -/
def referenceComparison (F : B ⥤ Resolution q)
    (h : ReferenceCompatible q (F ⋙ Grothendieck.forget (diagram q)))
    (hs : ∀ P, Function.Surjective (label (F.obj P).fiber.unop.obj.parameter)) :
    reference q h ⟶ F where
  app P := compareAt q (F.obj P) (hs P)
  naturality _ Q f := ext_of_surjective q (hs Q) ((Category.comp_id (F.map f).base).trans
    (Category.id_comp (F.map f).base).symm)

/-- The comparison is vertical over the identity on the same raw simplex. -/
theorem referenceComparison_base (F : B ⥤ Resolution q)
    (h : ReferenceCompatible q (F ⋙ Grothendieck.forget (diagram q)))
    (hs : ∀ P, Function.Surjective (label (F.obj P).fiber.unop.obj.parameter)) (P : B) :
    ((referenceComparison q F h hs).app P).base = 𝟙 (F.obj P).base := rfl

end

end DaggerModels.PartII.JTSimplicialTargetRowGraphResolution
