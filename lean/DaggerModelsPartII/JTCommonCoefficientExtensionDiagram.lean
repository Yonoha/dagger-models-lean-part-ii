import DaggerModelsPartII.JTCommonCoefficientNormalization
import DaggerModelsPartII.JTCommonCoefficientPrism
import Mathlib.CategoryTheory.Functor.Currying

/-! Exact common-coefficient extension choices over a diagram of coefficient
operators and injective time operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTCommonCoefficientExtensionDiagram

noncomputable section

private abbrev simplex := SSet.stdSimplex.{0}
private abbrev time := SemiSimplexCategory.toSimplexCategory

variable {I : Type} [SmallCategory I] {b : SimplexCategory}
variable (K : I ⥤ Over b)
variable {A X Y : SSet.{0}} {t : A ⟶ X} {p : X ⟶ Y} {g : simplex.obj b ⟶ Y}
variable (i : ∀ P, A ⟶ simplex.obj (K.obj P).left)
variable (hi : ∀ {P P'} (f : P ⟶ P'), i P ≫ simplex.map (K.map f).left = i P')
variable (sq : ∀ P, CommSq t (i P) p (simplex.map (K.obj P).hom ≫ g))

private abbrev enlarged (K : I ⥤ Over b) :=
  (K.prod (𝟭 SemiSimplexCategory)) ⋙ JTCommonCoefficientParameter.parameter b ⋙ simplex

/-- The exact choices in every graph and every time degree. -/
abbrev Choice (P : I × SemiSimplexCategory) :=
  JTCommonCoefficientLiftChoices.Extension (sq P.1) (time.obj P.2)

private def restrict {P P' : I × SemiSimplexCategory} (f : P ⟶ P') :
    Choice K i sq P' → Choice K i sq P :=
  JTCommonCoefficientLiftChoices.restrict (sq P.1) (sq P'.1)
    (K.map f.1).left (Over.w (K.map f.1)) (hi f.1)
    (time.map f.2) (SemiSimplexCategory.homEquiv f.2).injective

private theorem restrict_map {P P' : I × SemiSimplexCategory} (f : P ⟶ P')
    (E : Choice K i sq P') :
    (restrict K i hi sq f E).map = (enlarged K).map f ≫ E.map := rfl

/-- All enlarged choices are natural under the original coefficient arrows and all
injective time operators, including when coefficient arrows identify vertices. -/
def diagram : (I × SemiSimplexCategory)ᵒᵖ ⥤ Type where
  obj P := Choice K i sq P.unop
  map f := restrict K i hi sq f.unop
  map_id P := by
    funext E
    apply JTCommonCoefficientLiftChoices.Extension.ext
    change (restrict K i hi sq (𝟙 P.unop) E).map = E.map
    rw [restrict_map, (enlarged K).map_id, Category.id_comp]
  map_comp f g := by
    funext E
    apply JTCommonCoefficientLiftChoices.Extension.ext
    change (restrict K i hi sq (g.unop ≫ f.unop) E).map =
      (restrict K i hi sq g.unop (restrict K i hi sq f.unop E)).map
    rw [restrict_map, restrict_map, restrict_map, (enlarged K).map_comp, Category.assoc]

private abbrev baseMap {P P' : I} (f : P ⟶ P') :=
  simplex.map (K.map f).left

private def originalRestrict {P P' : I} (f : P ⟶ P') :
    (SSet.ihomToPullbackFiber (sq P') : SSet.{0}) ⟶ SSet.ihomToPullbackFiber (sq P) :=
  JTFixedLiftSpacePrecomp.precomp (sq P) (sq P') (baseMap K f) (hi f)
    (JTCommonCoefficientLiftChoices.base_precomp (g := g) (K.map f).left (Over.w (K.map f)))

private theorem baseMap_id (P : I) : baseMap K (𝟙 P) = 𝟙 _ := by
  unfold baseMap
  rw [K.map_id]
  exact simplex.map_id _

private theorem baseMap_comp {P P' P'' : I} (f : P ⟶ P') (f' : P' ⟶ P'') :
    baseMap K f ≫ baseMap K f' = baseMap K (f ≫ f') := by
  unfold baseMap
  rw [K.map_comp]
  exact (simplex.map_comp (K.map f).left (K.map f').left).symm

/-- The original simplicial normalization spaces over the supported coefficient diagram. -/
def originalSpaces : Iᵒᵖ ⥤ SSet.{0} where
  obj P := SSet.ihomToPullbackFiber (sq P.unop)
  map f := originalRestrict K i hi sq f.unop
  map_id P :=
    JTFixedLiftSpacePrecomp.precomp_id_of_eq _ _ (baseMap_id K P.unop) _ _
  map_comp f f' :=
    (JTFixedLiftSpacePrecomp.precomp_comp_of_fac _ _ _ _ _ _
      (baseMap_comp K f'.unop f.unop) _ _ _ _ _ _).symm

private abbrev timeRestriction : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj time.op

/-- Evaluate the original coefficient diagram in each injective time degree. -/
def original : (I × SemiSimplexCategory)ᵒᵖ ⥤ Type :=
  (prodOpEquiv (C := I) (D := SemiSimplexCategory)).functor ⋙
    Functor.uncurry.obj (originalSpaces K i hi sq ⋙ timeRestriction)

/-- Forgetting the enlarged prism is natural simultaneously in the original
coefficient arrow and the original injective time arrow. -/
def forget : diagram K i hi sq ⟶ original K i hi sq where
  app P := JTCommonCoefficientLiftChoices.underlying (sq P.unop.1)
  naturality {P P'} f := by
    funext E
    change JTCommonCoefficientLiftChoices.underlying (sq P'.unop.1)
        (restrict K i hi sq f.unop E) =
      (SSet.ihomToPullbackFiber (sq P'.unop.1) : SSet.{0}).map
        (time.map f.unop.2).op
        ((originalRestrict K i hi sq f.unop.1).app _
          (JTCommonCoefficientLiftChoices.underlying (sq P.unop.1) E))
    exact JTCommonCoefficientLiftChoices.underlying_restrict (sq P'.unop.1) (sq P.unop.1)
      (K.map f.unop.1).left (Over.w (K.map f.unop.1)) (hi f.unop.1)
      (time.map f.unop.2) (SemiSimplexCategory.homEquiv f.unop.2).injective E

private abbrev timePair :=
  (prodOpEquiv (C := I) (D := SemiSimplexCategory)).inverse

/-- Organize the exact enlarged choices as a semisimplicial presheaf
at each original coefficient. -/
def degreeDiagram : Iᵒᵖ ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  Functor.curryObj (timePair ⋙ diagram K i hi sq)

/-- The fiber over a coefficient uses literally the same enlarged choices
and the same injective time maps as the fixed-coefficient construction. -/
def fixedIso (P : I) :
    (degreeDiagram K i hi sq).obj (op P) ≅
      JTCommonCoefficientNormalization.choices
        (k := (K.obj P).left.len) (c := (K.obj P).hom) (g := g) (sq P) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro m n j
    funext E
    apply JTCommonCoefficientLiftChoices.Extension.ext
    let j₀ := time.map j.unop
    have hj : Function.Injective j₀.toOrderHom :=
      (SemiSimplexCategory.homEquiv j.unop).injective
    have he := congrArg (fun a : K.obj P ⟶ K.obj P ↦
      JTCommonCoefficientParameter.map a.left (Over.w a) j₀ hj) (K.map_id P)
    change SSet.stdSimplex.{0}.map (JTCommonCoefficientParameter.map
        (K.map (𝟙 P)).left (Over.w (K.map (𝟙 P))) j₀ hj) ≫ E.map =
      SSet.stdSimplex.{0}.map (JTCommonCoefficientParameter.map
        (𝟙 (K.obj P).left) (Category.id_comp (K.obj P).hom) j₀ hj) ≫ E.map
    exact congrArg (fun f ↦ SSet.stdSimplex.{0}.map f ≫ E.map) he)

/-- The mixed forgetful transformation, curried in its coefficient variable. -/
def degreeForget : degreeDiagram K i hi sq ⟶ originalSpaces K i hi sq ⋙ timeRestriction :=
  Functor.curry.map (Functor.whiskerLeft timePair (forget K i hi sq)) ≫
    (Functor.currying.unitIso.app (originalSpaces K i hi sq ⋙ timeRestriction)).inv

/-- The curried forgetful transformation has exactly the fixed-coefficient
forgetful map for its component. -/
theorem degreeForget_fixed (P : I) :
    (degreeForget K i hi sq).app (op P) =
      (fixedIso K i hi sq P).hom ≫
        JTCommonCoefficientNormalization.forget
          (k := (K.obj P).left.len) (c := (K.obj P).hom) (g := g) (sq P) := by
  ext n E
  rfl

/-- The mixed map obtained from the curried coefficient diagram still
precomposes with the exact original common-coefficient time operator. -/
theorem degreeDiagram_uncurry_map {P P' : I × SemiSimplexCategory} (u : P ⟶ P')
    (E : Choice K i sq P') :
    ((Functor.uncurry.obj (degreeDiagram K i hi sq)).map
        ((prodOpEquiv (C := I) (D := SemiSimplexCategory)).functor.map u.op) E).map =
      simplex.map (JTCommonCoefficientParameter.map (K.map u.1).left
        (Over.w (K.map u.1)) (time.map u.2) (SemiSimplexCategory.homEquiv u.2).injective) ≫
        E.map := by
  let F := timePair ⋙ diagram K i hi sq
  let e := Functor.currying.counitIso.app F
  let v := (prodOpEquiv (C := I) (D := SemiSimplexCategory)).functor.map u.op
  have h := congrFun (e.hom.naturality v) E
  change (Functor.uncurry.obj (degreeDiagram K i hi sq)).map v E =
    restrict K i hi sq u E at h
  exact (congrArg JTCommonCoefficientLiftChoices.Extension.map h).trans
    (restrict_map K i hi sq u E)

end
end DaggerModels.PartII.JTCommonCoefficientExtensionDiagram
