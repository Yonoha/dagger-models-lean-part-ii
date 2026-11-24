import DaggerModelsPartII.DaggerJTRealization
import DaggerModelsPartII.JTParameterZero
import DaggerModelsPartII.IndexKanExtensions
import DaggerModels.ForgetfulReflection

/-!
# Dagger JT realization of vertically constant input

The actual coend collapses to the restriction of the reversal presheaf.
The collapse evaluates the horizontal generator and forgets its groupoid
parameter. Its inverse on simplices uses the terminal zero parameter.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
  CartesianMonoidalCategory DaggerModels

namespace DaggerModels.PartII.DaggerJTConstantRealization

open OrdinaryJTRealization JTReversalInput JTRealizationGenerators
  DaggerJTRealization JTParameterZero

noncomputable section

/-- The literal vertically constant input associated to a reversal presheaf. -/
def constantInput (F : ReverseSimplexᵒᵖ ⥤ Type) : SegalLocalizers.ReverseDaggerSpace.{0} :=
  (discretePresheaf.{0, 0} ReverseSimplex).obj F

/-- The ordinary two-index restriction of this constant input. -/
def constantBiInput (F : ReverseSimplexᵒᵖ ⥤ Type) : BiPresheaf :=
  ordinaryInput.obj (constantInput F)

/-- The underlying ordinary restriction of the original presheaf. -/
def restrictedInput (F : ReverseSimplexᵒᵖ ⥤ Type) : SSet.{0} :=
  ReverseSimplex.inclusion.op ⋙ F

@[simp] theorem constantBiInput_map (F : ReverseSimplexᵒᵖ ⥤ Type)
    {p q : Index} (f : p ⟶ q) (w : (constantBiInput F).obj (op q)) :
    (constantBiInput F).map f.op w =
      F.map (ReverseSimplex.inclusion.map f.1).op w := rfl

/-- Evaluate the horizontal generator and discard the vertical parameter. -/
def collapseLeg (F : ReverseSimplexᵒᵖ ⥤ Type)
    (σ : SimplexIndex (constantBiInput F)) :
    tFunctor.obj σ.left ⟶ restrictedInput F :=
  fst (SSet.stdSimplex.obj σ.left.1) (GroupoidSimplex.parameter.obj σ.left.2) ≫
    (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm
      (uliftYonedaEquiv.{0} (C := Index) σ.hom)

/-- The evaluation legs respect both original coend relations. -/
def collapseCocone (F : ReverseSimplexᵒᵖ ⥤ Type) :
    Cocone (simplexDiagram (constantBiInput F)) where
  pt := restrictedInput F
  ι := {
    app := collapseLeg F
    naturality := by
      intro σ τ f
      have hw : uliftYonedaEquiv.{0} (C := Index) σ.hom =
          (restrictedInput F).map f.left.1.op
            (uliftYonedaEquiv.{0} (C := Index) τ.hom) :=
        ((uliftYonedaEquiv_naturality τ.hom f.left.op).trans
          (congrArg uliftYonedaEquiv.{0} (CostructuredArrow.w f))).symm
      change tFunctor.map f.left ≫ collapseLeg F τ = collapseLeg F σ
      unfold collapseLeg
      rw [← Category.assoc, tFunctor_map, tensorHom_fst, Category.assoc]
      have hy : SSet.stdSimplex.map f.left.1 ≫
          (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm
            (uliftYonedaEquiv.{0} (C := Index) τ.hom) =
          (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm
            ((restrictedInput F).map f.left.1.op
              (uliftYonedaEquiv.{0} (C := Index) τ.hom)) :=
        (uliftYonedaEquiv_symm_map.{0} (F := restrictedInput F) f.left.1.op
          (uliftYonedaEquiv.{0} (C := Index) (F := constantBiInput F) τ.hom)).symm
      rw [hy]
      exact congrArg (fun w ↦ fst _ _ ≫
        (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm w)
          hw.symm }

/-- Collapse on the actual fixed ordinary realization. -/
def collapse (F : ReverseSimplexᵒᵖ ⥤ Type) :
    realization.obj (constantBiInput F) ⟶ restrictedInput F :=
  (simplexCoconeIsColimit (constantBiInput F)).desc (collapseCocone F)

/-- Collapse is evaluation on each actual coend generator. -/
theorem generator_collapse (F : ReverseSimplexᵒᵖ ⥤ Type) (p : Index)
    (w : (constantBiInput F).obj (op p)) :
    generator (constantBiInput F) p w ≫ collapse F =
      fst (SSet.stdSimplex.obj p.1) (GroupoidSimplex.parameter.obj p.2) ≫
        (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm w := by
  have h := (simplexCoconeIsColimit (constantBiInput F)).fac (collapseCocone F)
    (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w))
  change generator (constantBiInput F) p w ≫ collapse F =
    fst (SSet.stdSimplex.obj p.1) (GroupoidSimplex.parameter.obj p.2) ≫
      (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm
        (uliftYonedaEquiv.{0} (C := Index)
          (uliftYonedaEquiv.{0} (C := Index).symm w)) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- The explicit evaluation formula on a generator simplex. -/
theorem collapse_generator_app (F : ReverseSimplexᵒᵖ ⥤ Type)
    (m k n : SimplexCategory) (w : F.obj (op (ReverseSimplex.inclusion.obj m)))
    (α : (SSet.stdSimplex.obj m).obj (op n))
    (ξ : (GroupoidSimplex.parameter.obj k).obj (op n)) :
    (collapse F).app (op n)
        ((generator (constantBiInput F) (m, k) w).app (op n) (α, ξ)) =
      F.map (ReverseSimplex.inclusion.map (SSet.stdSimplex.objEquiv α)).op w :=
  congrFun (NatTrans.congr_app (generator_collapse F (m, k) w) (op n)) (α, ξ)

/-- The unique simplex of the actual zero groupoid parameter. -/
def zeroParameter (n : SimplexCategory) :
    (GroupoidSimplex.parameter.obj ⦋0⦌).obj (op n) :=
  uliftYonedaEquiv.{0} (parameterZeroIsTerminal.from (SSet.stdSimplex.obj n))

theorem zeroParameter_unique (n : SimplexCategory)
    (ξ : (GroupoidSimplex.parameter.obj ⦋0⦌).obj (op n)) : ξ = zeroParameter n :=
  uliftYonedaEquiv.{0}.symm.injective (parameterZeroIsTerminal.hom_ext _ _)

/-- A pointwise inverse candidate, using an identity horizontal generator. -/
def liftSimplex (F : ReverseSimplexᵒᵖ ⥤ Type) (n : SimplexCategory)
    (w : (restrictedInput F).obj (op n)) :
    (realization.obj (constantBiInput F)).obj (op n) :=
  (generator (constantBiInput F) (n, ⦋0⦌) w).app (op n)
    (SSet.stdSimplex.objEquiv.symm (𝟙 n), zeroParameter n)

theorem collapse_liftSimplex (F : ReverseSimplexᵒᵖ ⥤ Type) (n : SimplexCategory)
    (w : (restrictedInput F).obj (op n)) :
    (collapse F).app (op n) (liftSimplex F n w) = w := by
  rw [liftSimplex, collapse_generator_app]
  simp

/-- The vertical terminal map and horizontal coend relation normalize every generator. -/
theorem generator_normalForm (F : ReverseSimplexᵒᵖ ⥤ Type)
    (m k n : SimplexCategory) (w : F.obj (op (ReverseSimplex.inclusion.obj m)))
    (α : (SSet.stdSimplex.obj m).obj (op n))
    (ξ : (GroupoidSimplex.parameter.obj k).obj (op n)) :
    (generator (constantBiInput F) (m, k) w).app (op n) (α, ξ) =
      liftSimplex F n
        (F.map (ReverseSimplex.inclusion.map (SSet.stdSimplex.objEquiv α)).op w) := by
  let v : (m, k) ⟶ (m, ⦋0⦌) := (𝟙 m, SimplexCategory.isTerminalZero.from k)
  have hv := congrFun (NatTrans.congr_app
    (generator_relation (constantBiInput F) v w) (op n)) (α, ξ)
  have hvcoef : (constantBiInput F).map v.op w = w := by
    change F.map (ReverseSimplex.inclusion.map (𝟙 m)).op w = w
    simp
  rw [hvcoef] at hv
  change (generator (constantBiInput F) (m, ⦋0⦌) w).app (op n)
      ((SSet.stdSimplex.map (𝟙 m)).app (op n) α,
        (GroupoidSimplex.parameter.map (SimplexCategory.isTerminalZero.from k)).app
          (op n) ξ) =
    (generator (constantBiInput F) (m, k) w).app (op n) (α, ξ) at hv
  rw [zeroParameter_unique n
    ((GroupoidSimplex.parameter.map (SimplexCategory.isTerminalZero.from k)).app
      (op n) ξ)] at hv
  let h : (n, ⦋0⦌) ⟶ (m, ⦋0⦌) := (SSet.stdSimplex.objEquiv α, 𝟙 ⦋0⦌)
  have hh := congrFun (NatTrans.congr_app
    (generator_relation (constantBiInput F) h w) (op n))
      (SSet.stdSimplex.objEquiv.symm (𝟙 n), zeroParameter n)
  change (generator (constantBiInput F) (m, ⦋0⦌) w).app (op n)
      (SSet.stdSimplex.objEquiv.symm ((𝟙 n) ≫ SSet.stdSimplex.objEquiv α),
        (GroupoidSimplex.parameter.map (𝟙 ⦋0⦌)).app (op n) (zeroParameter n)) =
    liftSimplex F n
      (F.map (ReverseSimplex.inclusion.map (SSet.stdSimplex.objEquiv α)).op w) at hh
  simp only [Category.id_comp, Equiv.symm_apply_apply] at hh
  have hi₁ := congrFun (NatTrans.congr_app
    (CategoryTheory.Functor.map_id SSet.stdSimplex m) (op n)) α
  have hi₂ := congrFun (NatTrans.congr_app
    (GroupoidSimplex.parameter.map_id ⦋0⦌) (op n)) (zeroParameter n)
  exact hv.symm.trans ((congrArg
    (fun s : (tFunctor.obj (m, ⦋0⦌)).obj (op n) ↦
      (generator (constantBiInput F) (m, ⦋0⦌) w).app (op n) s)
      (Prod.ext hi₁ hi₂.symm)).trans hh)

theorem collapse_bijective (F : ReverseSimplexᵒᵖ ⥤ Type) (n : SimplexCategory) :
    Function.Bijective ((collapse F).app (op n)) := by
  have hleft : ∀ x, liftSimplex F n ((collapse F).app (op n) x) = x := by
    intro x
    obtain ⟨⟨m, k⟩, w, ⟨α, ξ⟩, hx⟩ := exists_generator (constantBiInput F) (op n) x
    rw [← hx, collapse_generator_app]
    exact (generator_normalForm F m k n w α ξ).symm
  constructor
  · intro x y h
    exact (hleft x).symm.trans ((congrArg (liftSimplex F n) h).trans (hleft y))
  · intro w
    exact ⟨liftSimplex F n w, collapse_liftSimplex F n w⟩

instance collapse_isIso (F : ReverseSimplexᵒᵖ ⥤ Type) : IsIso (collapse F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact (isIso_iff_bijective _).mpr (collapse_bijective F n.unop)

/-- The same collapse is natural in every map of reversal presheaves. -/
theorem collapse_naturality {F G : ReverseSimplexᵒᵖ ⥤ Type} (f : F ⟶ G) :
    realization.map (ordinaryInput.map
        ((discretePresheaf.{0, 0} ReverseSimplex).map f)) ≫ collapse G =
      collapse F ≫ presheafRestriction.map f := by
  suffices h : ∀ (p : Index) (w : (constantBiInput F).obj (op p)),
      generator (constantBiInput F) p w ≫
          (realization.map (ordinaryInput.map
            ((discretePresheaf.{0, 0} ReverseSimplex).map f)) ≫ collapse G) =
        generator (constantBiInput F) p w ≫ (collapse F ≫ presheafRestriction.map f) by
    apply (simplexCoconeIsColimit (constantBiInput F)).hom_ext
    intro σ
    simpa only [simplexCocone_leg, generator, Equiv.symm_apply_apply] using
      h σ.left (uliftYonedaEquiv.{0} (C := Index) σ.hom)
  intro p w
  change generator (constantBiInput F) p w ≫
      (realization.map (ordinaryInput.map
        ((discretePresheaf.{0, 0} ReverseSimplex).map f)) ≫ collapse G) =
    generator (constantBiInput F) p w ≫ (collapse F ≫ presheafRestriction.map f)
  rw [← Category.assoc, generator_naturality]
  change generator (constantBiInput G) p
      (f.app (op (ReverseSimplex.inclusion.obj p.1)) w) ≫ collapse G =
    generator (constantBiInput F) p w ≫ (collapse F ≫ presheafRestriction.map f)
  rw [generator_collapse G, ← Category.assoc, generator_collapse F, Category.assoc]
  apply congrArg (fun g ↦ fst (SSet.stdSimplex.obj p.1)
    (GroupoidSimplex.parameter.obj p.2) ≫ g)
  apply (uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput G)).injective
  simpa only [Equiv.apply_symm_apply] using
    (uliftYonedaEquiv_comp (F := restrictedInput F) (G := restrictedInput G)
      ((uliftYonedaEquiv.{0} (C := SimplexCategory) (F := restrictedInput F)).symm w)
      (presheafRestriction.map f)).symm

/-- Evaluation intertwines the actual coend dagger and the original presheaf reversal. -/
theorem collapse_dagger (F : ReverseSimplexᵒᵖ ⥤ Type) (n : SimplexCategory)
    (x : (realization.obj (constantBiInput F)).obj (op n)) :
    (collapse F).app (op n)
        (SSet.opObjEquiv ((toOpposite (constantInput F)).app (op n) x)) =
      F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n)).op
        ((collapse F).app (op n) x) := by
  obtain ⟨⟨m, k⟩, w, ⟨α, ξ⟩, hx⟩ := exists_generator (constantBiInput F) (op n) x
  rw [← hx]
  have hr : ReverseSimplex.inclusion.map
      (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α)) ≫
        ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m) =
      ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n) ≫
        ReverseSimplex.inclusion.map (SSet.stdSimplex.objEquiv α) := by
    simpa only [SimplexCategory.rev_map_rev_map] using
      ReverseSimplex.reversal_naturality
        (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α))
  have hF : F.map (ReverseSimplex.inclusion.map
      (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α))).op
        (F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m)).op w) =
      F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n)).op
        (F.map (ReverseSimplex.inclusion.map (SSet.stdSimplex.objEquiv α)).op w) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, hr]
  calc
    _ = (collapse F).app (op n)
        ((generator (constantBiInput F) (m, k)
          (JTRealizationVertices.horizontalReversalCoefficient (constantInput F) m k w)).app
            (op n) (SSet.stdSimplex.objEquiv.symm
              (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α)),
              (GroupoidSimplexReversal.daggerParameter.obj k).daggerSimplex
                (n := n.len) ξ)) :=
      congrArg ((collapse F).app (op n))
        (toOpposite_generator_app (constantInput F) m k n w α ξ)
    _ = F.map (ReverseSimplex.inclusion.map
        (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α))).op
          (F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m)).op w) :=
      collapse_generator_app F m k n _ _ _
    _ = _ := hF
    _ = _ := congrArg
      (F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n)).op)
        (collapse_generator_app F m k n w α ξ).symm

/-- The collapse as a morphism of the actual dagger simplicial sets. -/
def collapseDagger (F : ReverseSimplexᵒᵖ ⥤ Type) :
    daggerRealization.obj (constantInput F) ⟶ ReversePresheaf.toDaggerSSet.obj F where
  hom := collapse F
  comm := by
    ext n x
    exact (collapse_dagger F n.unop x).symm

instance collapseDagger_isIso (F : ReverseSimplexᵒᵖ ⥤ Type) :
    IsIso (collapseDagger F) := by
  letI : DaggerSSet.forget.{0}.ReflectsIsomorphisms :=
    DaggerSSet.forget_reflectsIsomorphisms
  haveI : IsIso (DaggerSSet.forget.map (collapseDagger F)) := by
    change IsIso (collapse F)
    infer_instance
  exact isIso_of_reflects_iso (collapseDagger F) DaggerSSet.forget

/-- Realizing vertically constant input recovers the original dagger restriction,
naturally in the full reversal presheaf. -/
def constantRealizationIso :
    discretePresheaf.{0, 0} ReverseSimplex ⋙ daggerRealization ≅
      ReversePresheaf.toDaggerSSet :=
  NatIso.ofComponents (fun F ↦ asIso (collapseDagger F)) (by
    intro F G f
    apply DaggerSSet.Hom.ext
    exact collapse_naturality f)

end

end DaggerModels.PartII.DaggerJTConstantRealization
