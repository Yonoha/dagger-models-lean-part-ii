import DaggerModelsPartII.JTEndpointArrowReplacement
import DaggerModelsPartII.ReedyCoefficientChange
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# The projective Arrow corner and the relative cosimplicial latching map

Pointwise colimits in the Arrow category and opposite pushouts identify the
projective corner of the Reedy matching map with the relative cosimplicial
latching map of its source-to-target arrow. The comparison applies to the
actual zero-fixed Gamma and Xi replacements at every degree, including zero.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels.PartII

universe v u

namespace DaggerModels.PartII.ArrowReedyCornerInterchange

noncomputable section

variable {C : Type u} [Category.{v} C] [HasColimits C]

/-- The source diagram of an opposite Arrow-valued simplicial diagram. -/
def sourceOpp (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ Cᵒᵖ :=
  D ⋙ (Arrow.leftFunc (C := C)).op

/-- The target diagram of the same opposite Arrow-valued diagram. -/
def targetOpp (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ Cᵒᵖ :=
  D ⋙ (Arrow.rightFunc (C := C)).op

/-- The original source-to-target cosimplicial arrow, reversed into the
coefficient opposite category. -/
def structureOpp (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) :
    targetOpp D ⟶ sourceOpp D :=
  Functor.whiskerLeft D
    (NatTrans.op (Arrow.leftToRight : Arrow.leftFunc (C := C) ⟶ Arrow.rightFunc))

omit [HasColimits C] in
/-- The structure map in a degree is the actual internal map of that Arrow object. -/
theorem structureOpp_app_unop (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ)
    (n : ℕ) :
    ((structureOpp D).app (op ⦋n⦌)).unop = (D.obj (op ⦋n⦌)).unop.hom := rfl

/-- Pointwise Arrow colimits identify the matching Arrow object with the
arrow of matching source and target objects after taking opposites. The
component isomorphisms are `ReedyCoefficientChange.matchingObjectIso` for
`Arrow.leftFunc.op` and `Arrow.rightFunc.op`; their compatibility is the
limit of the natural transformation `Arrow.leftToRight`. -/
private def matchingObjectArrowIso
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) (n : ℕ) :
    ((matchingFunctor n).obj D).unop ≅
      Arrow.mk (((matchingFunctor n).map (structureOpp D)).unop) := by
  let L := (Arrow.leftFunc (C := C)).op
  let R := (Arrow.rightFunc (C := C)).op
  let η : R ⟶ L := NatTrans.op
    (Arrow.leftToRight : Arrow.leftFunc (C := C) ⟶ Arrow.rightFunc)
  letI : PreservesColimitsOfSize.{0, 0} (Arrow.leftFunc (C := C)) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  letI : PreservesColimitsOfSize.{0, 0} (Arrow.rightFunc (C := C)) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  letI : PreservesLimitsOfSize.{0, 0} L := preservesLimitsOfSize_op _
  letI : PreservesLimitsOfSize.{0, 0} R := preservesLimitsOfSize_op _
  let eL := ReedyCoefficientChange.matchingObjectIso L n D
  let eR := ReedyCoefficientChange.matchingObjectIso R n D
  have hcompat :
      η.app ((matchingFunctor n).obj D) ≫ eL.hom =
        eR.hom ≫ (matchingFunctor n).map (structureOpp D) := by
    apply limit.hom_ext
    intro s
    dsimp only [eL, eR, ReedyCoefficientChange.matchingObjectIso]
    change (η.app (limit (matchingProjection n ⋙ D)) ≫
        (preservesLimitIso L (matchingProjection n ⋙ D)).hom) ≫
          limit.π ((matchingProjection n ⋙ D) ⋙ L) s =
      ((preservesLimitIso R (matchingProjection n ⋙ D)).hom ≫
        limMap (Functor.whiskerLeft (matchingProjection n) (structureOpp D))) ≫
          limit.π ((matchingProjection n ⋙ D) ⋙ L) s
    let πD := limit.π (matchingProjection n ⋙ D) s
    let πL := limit.π ((matchingProjection n ⋙ D) ⋙ L) s
    let πR := limit.π ((matchingProjection n ⋙ D) ⋙ R) s
    have hL : (preservesLimitIso L (matchingProjection n ⋙ D)).hom ≫ πL =
        L.map πD := preservesLimitIso_hom_π L (matchingProjection n ⋙ D) s
    have hR : (preservesLimitIso R (matchingProjection n ⋙ D)).hom ≫ πR =
        R.map πD := preservesLimitIso_hom_π R (matchingProjection n ⋙ D) s
    have hM : limMap (Functor.whiskerLeft (matchingProjection n)
        (structureOpp D)) ≫ πL =
        πR ≫ η.app ((matchingProjection n ⋙ D).obj s) :=
      limMap_π (Functor.whiskerLeft (matchingProjection n) (structureOpp D)) s
    calc
      (η.app (limit (matchingProjection n ⋙ D)) ≫
          (preservesLimitIso L (matchingProjection n ⋙ D)).hom) ≫ πL =
        η.app (limit (matchingProjection n ⋙ D)) ≫ L.map πD := by
          rw [Category.assoc, hL]
      _ = R.map πD ≫ η.app ((matchingProjection n ⋙ D).obj s) :=
        (η.naturality πD).symm
      _ = ((preservesLimitIso R (matchingProjection n ⋙ D)).hom ≫
          limMap (Functor.whiskerLeft (matchingProjection n) (structureOpp D))) ≫
            πL := by
          rw [Category.assoc, hM, ← Category.assoc, hR]
  have hcompat' :
      (matchingFunctor n).map (structureOpp D) ≫ eL.inv =
        eR.inv ≫ η.app ((matchingFunctor n).obj D) := by
    calc
      _ = eR.inv ≫ (eR.hom ≫ (matchingFunctor n).map (structureOpp D)) ≫
          eL.inv := by simp [Category.assoc]
      _ = eR.inv ≫ (η.app ((matchingFunctor n).obj D) ≫ eL.hom) ≫
          eL.inv := by rw [← hcompat]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Arrow.isoMk eL.unop.symm eR.unop.symm ?_
  have h := congrArg Quiver.Hom.unop hcompat'
  change (eL.unop.symm).hom ≫ ((matchingFunctor n).map (structureOpp D)).unop =
    ((matchingFunctor n).obj D).unop.hom ≫ (eR.unop.symm).hom at h
  exact h

/-- The relative matching map to a terminal diagram has the same arrow as
the absolute matching comparison, after the canonical pullback projection.
This removes the terminal factor before interchanging Arrow and matching. -/
private def terminalMatchingArrowIso
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) (n : ℕ) :
    Arrow.mk ((relativeMatchingMap n (terminal.from D)).unop) ≅
      Arrow.mk (((matchingComparison n).app D).unop) := by
  let T := ⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ)
  let f : D ⟶ T := terminal.from D
  letI : PreservesLimit (Functor.empty.{0} _)
      (matchingFunctor (C := (Arrow C)ᵒᵖ) n) := by
    unfold matchingFunctor
    infer_instance
  have hT : IsTerminal ((matchingFunctor n).obj T) :=
    terminalIsTerminal.isTerminalObj (matchingFunctor n) T
  have hTn : IsTerminal (T.obj (op ⦋n⦌)) :=
    terminalIsTerminal.isTerminalObj
      ((evaluation _ (Arrow C)ᵒᵖ).obj (op ⦋n⦌)) T
  letI : IsIso ((matchingComparison n).app T) :=
    isIso_of_isTerminal hTn hT _
  let π := pullback.fst ((matchingFunctor n).map f) ((matchingComparison n).app T)
  letI : IsIso π := pullback_fst_iso_of_right_iso _ _
  let e : (pullback ((matchingFunctor n).map f)
      ((matchingComparison n).app T)).unop ≅
        ((matchingFunctor n).obj D).unop := (asIso π).unop.symm
  have hπ : relativeMatchingMap n f ≫ π = (matchingComparison n).app D :=
    pullback.lift_fst _ _ _
  refine Arrow.isoMk e (Iso.refl _) ?_
  have hπ' := congrArg Quiver.Hom.unop hπ
  change π.unop ≫ (relativeMatchingMap n f).unop =
    ((matchingComparison n).app D).unop at hπ'
  change e.hom ≫ ((matchingComparison n).app D).unop =
    (relativeMatchingMap n f).unop ≫ 𝟙 _
  rw [Category.comp_id, ← hπ', ← Category.assoc]
  have he : e.hom ≫ π.unop = 𝟙 _ := by
    change (inv π).unop ≫ π.unop = 𝟙 _
    rw [← unop_comp, IsIso.hom_inv_id, unop_id]
  rw [he, Category.id_comp]

/-- The relative-latching square formed by the matching maps of the source
and target of the original cosimplicial arrow. -/
private def matchingStructureSquare
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) (n : ℕ) :
    Arrow.mk (((matchingFunctor n).map (structureOpp D)).unop) ⟶
      Arrow.mk (((structureOpp D).app (op ⦋n⦌)).unop) := by
  refine Arrow.homMk
    (((matchingComparison n).app (sourceOpp D)).unop)
    (((matchingComparison n).app (targetOpp D)).unop) ?_
  have h := congrArg Quiver.Hom.unop
    ((matchingComparison n).naturality (structureOpp D))
  simpa only [unop_comp] using h

/-- The ordinary matching comparison in `Arrow C` is the componentwise
matching square, after pointwise matching-object isomorphism. -/
private def matchingSquareIso
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) (n : ℕ) :
    Arrow.mk (((matchingComparison n).app D).unop) ≅
      Arrow.mk (matchingStructureSquare D n) := by
  let eM := matchingObjectArrowIso D n
  let eN : (D.obj (op ⦋n⦌)).unop ≅
      Arrow.mk (((structureOpp D).app (op ⦋n⦌)).unop) :=
    Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      change 𝟙 _ ≫ ((structureOpp D).app (op ⦋n⦌)).unop =
        (D.obj (op ⦋n⦌)).unop.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, structureOpp_app_unop])
  refine Arrow.isoMk eM eN ?_
  apply Arrow.hom_ext
  · let L := (Arrow.leftFunc (C := C)).op
    letI : PreservesColimitsOfSize.{0, 0} (Arrow.leftFunc (C := C)) :=
      ⟨fun {_} _ ↦ inferInstance⟩
    letI : PreservesLimitsOfSize.{0, 0} L := preservesLimitsOfSize_op _
    let eL := ReedyCoefficientChange.matchingObjectIso L n D
    have h := congrArg Quiver.Hom.unop
      (ReedyCoefficientChange.matchingComparison_map L n D)
    simp only [Arrow.comp_left, Arrow.mk_hom] at *
    symm
    change (eL.hom).unop ≫ (((matchingComparison n).app D).unop).left =
      ((matchingComparison n).app (sourceOpp D)).unop at h
    change (((matchingComparison n).app D).unop).left ≫ 𝟙 _ =
      (eL.inv).unop ≫ ((matchingComparison n).app (sourceOpp D)).unop
    rw [Category.comp_id]
    calc
      _ = (eL.inv).unop ≫ ((eL.hom).unop ≫
          (((matchingComparison n).app D).unop).left) := by
            rw [← Category.assoc, ← unop_comp, Iso.hom_inv_id,
              unop_id, Category.id_comp]
      _ = _ := by rw [h]
  · let R := (Arrow.rightFunc (C := C)).op
    letI : PreservesColimitsOfSize.{0, 0} (Arrow.rightFunc (C := C)) :=
      ⟨fun {_} _ ↦ inferInstance⟩
    letI : PreservesLimitsOfSize.{0, 0} R := preservesLimitsOfSize_op _
    let eR := ReedyCoefficientChange.matchingObjectIso R n D
    have h := congrArg Quiver.Hom.unop
      (ReedyCoefficientChange.matchingComparison_map R n D)
    simp only [Arrow.comp_right, Arrow.mk_hom] at *
    symm
    change (eR.hom).unop ≫ (((matchingComparison n).app D).unop).right =
      ((matchingComparison n).app (targetOpp D)).unop at h
    change (((matchingComparison n).app D).unop).right ≫ 𝟙 _ =
      (eR.inv).unop ≫ ((matchingComparison n).app (targetOpp D)).unop
    rw [Category.comp_id]
    calc
      _ = (eR.inv).unop ≫ ((eR.hom).unop ≫
          (((matchingComparison n).app D).unop).right) := by
            rw [← Category.assoc, ← unop_comp, Iso.hom_inv_id,
              unop_id, Category.id_comp]
      _ = _ := by rw [h]

variable [ModelCategory C]

/-- The corner of the componentwise square is the literal opposite
relative matching map of the source-to-target structure transformation. -/
private def matchingCornerRelativeIso
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ) (n : ℕ) :
    Arrow.mk (ProjectiveArrowFactorization.corner
      (matchingStructureSquare D n)) ≅
      Arrow.mk ((relativeMatchingMap n (structureOpp D)).unop) := by
  let f := ((matchingFunctor n).map (structureOpp D)).unop
  let g := ((matchingComparison n).app (sourceOpp D)).unop
  let e := pushoutIsoUnopPullback f g
  refine Arrow.isoMk e (Iso.refl _) ?_
  apply pushout.hom_ext
  · change pushout.inl f g ≫ e.hom ≫
        (relativeMatchingMap n (structureOpp D)).unop =
        pushout.inl f g ≫ ProjectiveArrowFactorization.corner
          (matchingStructureSquare D n) ≫ 𝟙 _
    simp only [← Category.assoc]
    rw [Category.comp_id, pushoutIsoUnopPullback_inl_hom,
      ProjectiveArrowFactorization.corner, pushout.inl_desc]
    rw [← unop_comp]
    exact congrArg Quiver.Hom.unop
      (pullback.lift_fst ((matchingComparison n).app (targetOpp D))
        ((structureOpp D).app (op ⦋n⦌)) _)
  · change pushout.inr f g ≫ e.hom ≫
        (relativeMatchingMap n (structureOpp D)).unop =
        pushout.inr f g ≫ ProjectiveArrowFactorization.corner
          (matchingStructureSquare D n) ≫ 𝟙 _
    simp only [← Category.assoc]
    rw [Category.comp_id, pushoutIsoUnopPullback_inr_hom,
      ProjectiveArrowFactorization.corner, pushout.inr_desc]
    rw [← unop_comp]
    exact congrArg Quiver.Hom.unop
      (pullback.lift_snd ((matchingComparison n).app (targetOpp D))
        ((structureOpp D).app (op ⦋n⦌)) _)

/-- The exact missing interchange. Its source is the pushout corner used by
`projectiveArrowCofibrations`; its target is the actual relative latching map
of `structureOpp D`, expressed using the retained opposite Reedy API. -/
def cornerInterchangeIso (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ)
    (n : ℕ) :
    Arrow.mk (ProjectiveArrowFactorization.corner
      ((relativeMatchingMap n (terminal.from D)).unop)) ≅
      Arrow.mk ((relativeMatchingMap n (structureOpp D)).unop) := by
  let F := relativeLatchingArrows
    (Arrow.leftToRight : Arrow.leftFunc (C := C) ⟶ Arrow.rightFunc)
  exact F.mapIso (terminalMatchingArrowIso D n) ≪≫
    F.mapIso (matchingSquareIso D n) ≪≫ matchingCornerRelativeIso D n

/-- A projective Arrow relative matching condition yields the literal
relative cosimplicial latching cofibration, including in degree zero. -/
theorem structure_relativeCofibration
    (D : SimplexCategoryᵒᵖ ⥤ (Arrow C)ᵒᵖ)
    (h : ∀ n : ℕ, ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((relativeMatchingMap n (terminal.from D)).unop)) (n : ℕ) :
    cofibrations C ((relativeMatchingMap n (structureOpp D)).unop) := by
  exact ((cofibrations C).arrow_mk_iso_iff (cornerInterchangeIso D n)).1 (h n).2

end

namespace Actual

open JTEndpointArrowReplacement
open JTRelativeReedyFrame

noncomputable section

private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The first actual zero-fixed arrow replacement has the relative Reedy
cofibration of source into target at every degree, including zero. -/
theorem QG_relativeCofibration (n : ℕ) :
    cofibrations Coefficient
      ((relativeMatchingMap n (structureOpp QGop)).unop) := by
  apply structure_relativeCofibration QGop
  intro m
  have h : firstRight = terminal.from QGop := Subsingleton.elim _ _
  rw [← h]
  have hm := firstRight_relative m
  change ProjectiveArrowFactorization.projectiveArrowCofibrations
    ((relativeMatchingMap m firstRight).unop) at hm
  exact hm

/-- The second actual replacement has the same relative Reedy cofibration,
using the proved composite right-class matching witness. -/
theorem QX_relativeCofibration (n : ℕ) :
    cofibrations Coefficient
      ((relativeMatchingMap n (structureOpp QXop)).unop) := by
  apply structure_relativeCofibration QXop
  intro m
  have h : secondRight ≫ firstRight = terminal.from QXop :=
    Subsingleton.elim _ _
  rw [← h]
  have hm := QX_terminal_relativeMatching m
  change ProjectiveArrowFactorization.projectiveArrowCofibrations
    ((relativeMatchingMap m (secondRight ≫ firstRight)).unop) at hm
  exact hm

end

end Actual

end DaggerModels.PartII.ArrowReedyCornerInterchange
