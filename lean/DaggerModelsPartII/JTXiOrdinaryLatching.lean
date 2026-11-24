import DaggerModelsPartII.JTParameterLatchingMono
import DaggerModelsPartII.RigidifiedJTFrames
import DaggerModelsPartII.ReedyCoefficientChange
import OrdinaryRigidificationCof
import NativeIhomRelativeSectionsWeak
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Ordinary latching cofibrations of the actual rigidified JT frame

The actual completed-simplex face-latching monomorphism is tensored with the
underlying reversal simplex and sent through the original ordinary
rigidification. Opposite matching objects encode cosimplicial latching objects.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
  MonoidalClosed Opposite Simplicial MorphismProperty DaggerModels
open DaggerModels.PartII
open DaggerModels.PartII.GroupoidSimplex
open DaggerModels.PartII.JTParameterLatchingMono
open DaggerModels.PartII.DaggerJTFrameUnderlying
open DaggerModels.PartII.RigidifiedJTFrames
open DaggerModels.OrdinaryRigidification
open DaggerOrdinaryRigidificationCof

namespace DaggerModels.PartII.JTXiOrdinaryLatching

noncomputable section

private local instance : HasColimits SimplicialCat.{0, 0} := simplicialCatHasColimits
private local instance : HasLimits SimplicialCat.{0, 0}ᵒᵖ := inferInstance

/-- The native opposite matching object is the opposite of the literal
proper-face colimit of the completed-simplex parameter. -/
def parameterMatchingIso (n : ℕ) :
    (matchingFunctor n).obj GroupoidSimplex.parameter.op ≅
      op (colimit (faceDiagram n)) :=
  limit.isoLimitCone ⟨coneOfCoconeLeftOp
    (F := matchingProjection n ⋙ GroupoidSimplex.parameter.op)
    (colimit.cocone (faceDiagram n)),
    isLimitConeOfCoconeLeftOp _ (colimit.isColimit (faceDiagram n))⟩

/-- The native matching comparison is precisely the opposite of the
actual face-latching map, under the preceding canonical isomorphism. -/
theorem parameterMatchingIso_comp (n : ℕ) :
    (matchingComparison n).app GroupoidSimplex.parameter.op ≫
      (parameterMatchingIso n).hom = (faceLatchingMap n).op := by
  apply Quiver.Hom.unop_inj
  apply (colimit.isColimit (faceDiagram n)).hom_ext
  intro s
  apply Quiver.Hom.op_inj
  rw [op_comp, op_comp]
  simp only [Quiver.Hom.op_unop]
  have hfac : (colimit.cocone (faceDiagram n)).ι.app s ≫
      faceLatchingMap n = (faceCocone n).ι.app s :=
    colimit.ι_desc (faceCocone n) s
  conv_rhs => rw [← op_comp, hfac]
  change ((matchingComparison n).app GroupoidSimplex.parameter.op ≫
      (parameterMatchingIso n).hom) ≫
      (colimit.ι (faceDiagram n) s).op =
    (GroupoidSimplex.parameter.map s.unop.obj.hom.unop).op
  rw [Category.assoc]
  have hlim : (parameterMatchingIso n).hom ≫
      (colimit.ι (faceDiagram n) s).op =
        limit.π (matchingProjection n ⋙ GroupoidSimplex.parameter.op) s.unop :=
    limit.isoLimitCone_hom_π
      ⟨coneOfCoconeLeftOp
        (F := matchingProjection n ⋙ GroupoidSimplex.parameter.op)
        (colimit.cocone (faceDiagram n)),
        isLimitConeOfCoconeLeftOp _ (colimit.isColimit (faceDiagram n))⟩ s.unop
  rw [hlim]
  exact limit.lift_π _ _

/-- Tensor with the fixed underlying reversal simplex, then apply the
original ordinary rigidification. -/
def coefficientFunctor (m : ReverseSimplex) : SSet.{0} ⥤ SimplicialCat.{0, 0} :=
  tensorLeft (underlyingSimplex.obj m) ⋙ rigidification

private local instance (m : ReverseSimplex) :
    PreservesColimitsOfSize.{0, 0} (coefficientFunctor m) := by
  letI : PreservesColimitsOfSize.{0, 0} (tensorLeft (underlyingSimplex.obj m)) :=
    (ihom.adjunction (underlyingSimplex.obj m)).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} rigidification.{0} :=
    rigidificationCoherentNerveAdjunction.leftAdjoint_preservesColimits
  dsimp [coefficientFunctor]
  infer_instance

private local instance (m : ReverseSimplex) :
    PreservesLimitsOfSize.{0, 0} (coefficientFunctor m).op := by
  exact preservesLimitsOfSize_op _

/-- Conditional form separating the J-latching monomorphism input from the
coefficient-change and ordinary Bergner cofibration arguments. -/
theorem normalizedXi_matching_cofibration_of_mono (m : ReverseSimplex) (n : ℕ)
    (hmono : Mono (faceLatchingMap n)) :
    ordinaryCofibrations
      (((matchingComparison n).app
        (GroupoidSimplex.parameter ⋙ coefficientFunctor m).op).unop) := by
  let P : MorphismProperty SimplicialCat.{0, 0}ᵒᵖ := ordinaryCofibrations.op
  have : P.RespectsIso := by
    dsimp [P, ordinaryCofibrations]
    infer_instance
  let G := (coefficientFunctor m).op
  let W := GroupoidSimplex.parameter.op
  let e := parameterMatchingIso n
  let e' := ReedyCoefficientChange.matchingObjectIso G n W
  have hten : Mono ((tensorLeft (underlyingSimplex.obj m)).map (faceLatchingMap n)) := by
    letI : Mono (faceLatchingMap n) := hmono
    exact DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono
      (underlyingSimplex.obj m) (faceLatchingMap n)
  have hcof : ordinaryCofibrations
      ((coefficientFunctor m).map (faceLatchingMap n)) := by
    change ordinaryCofibrations
      (rigidification.map ((tensorLeft (underlyingSimplex.obj m)).map
        (faceLatchingMap n)))
    letI : Mono ((tensorLeft (underlyingSimplex.obj m)).map
        (faceLatchingMap n)) := hten
    exact mono_rigidification_cofibration _
  have hface : P (G.map (faceLatchingMap n).op) := hcof
  have hsource : P (G.map ((matchingComparison n).app W)) := by
    apply ((P.cancel_right_of_respectsIso _ (G.map e.hom)).mp)
    rw [← G.map_comp, parameterMatchingIso_comp]
    exact hface
  have htarget : P ((matchingComparison n).app (W ⋙ G)) := by
    have hc : P (G.map ((matchingComparison n).app W) ≫ e'.hom) := by
      letI : IsIso e'.hom := inferInstance
      exact RespectsIso.postcomp P e'.hom _ hsource
    rw [ReedyCoefficientChange.matchingComparison_map] at hc
    exact hc
  change P ((matchingComparison n).app
    (GroupoidSimplex.parameter ⋙ coefficientFunctor m).op) at htarget
  exact htarget

/-- The all-degree normalized ordinary Xi latching condition, supplied by
the monomorphism of the actual completed-simplex face latching map. -/
theorem normalizedXi_matching_cofibration (m : ReverseSimplex) (n : ℕ) :
    ordinaryCofibrations
      (((matchingComparison n).app
        (GroupoidSimplex.parameter ⋙ coefficientFunctor m).op).unop) :=
  normalizedXi_matching_cofibration_of_mono m n (faceLatchingMap_mono n)

/-- The original full-index Xi diagram with the reversal index fixed,
followed by the actual dagger-forgetful functor. -/
def actualOrdinaryXi (m : ReverseSimplex) :
    SimplexCategory ⥤ SimplicialCat.{0, 0} :=
  (CategoryTheory.Prod.sectR m SimplexCategory ⋙ Xi) ⋙ DaggerSimplicialCat.forget

/-- The product formula at one fixed reversal index, still natural in the
ordinary simplex index. -/
def productSectionIso (m : ReverseSimplex) :
    CategoryTheory.Prod.sectR m SimplexCategory ⋙
        DaggerJTFrameUnderlying.frameParameter ≅
      GroupoidSimplex.parameter ⋙ tensorLeft (underlyingSimplex.obj m) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro k l f
    change underlyingSimplex.map (𝟙 m) ⊗ₘ GroupoidSimplex.parameter.map f =
      (𝟙 (underlyingSimplex.obj m)) ⊗ₘ GroupoidSimplex.parameter.map f
    rw [underlyingSimplex.map_id])

/-- The actual Xi-underlying comparison, restricted to a fixed reversal
index and followed by the literal product parameter formula. -/
def actualOrdinaryXiIso (m : ReverseSimplex) :
    actualOrdinaryXi m ≅
      GroupoidSimplex.parameter ⋙ coefficientFunctor m :=
  Functor.associator (CategoryTheory.Prod.sectR m SimplexCategory)
      Xi DaggerSimplicialCat.forget ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.sectR m SimplexCategory)
      XiUnderlyingIso ≪≫
    (Functor.associator (CategoryTheory.Prod.sectR m SimplexCategory)
      DaggerJTFrameUnderlying.frameParameter rigidification).symm ≪≫
    Functor.isoWhiskerRight (productSectionIso m) rigidification ≪≫
    Functor.associator GroupoidSimplex.parameter
      (tensorLeft (underlyingSimplex.obj m)) rigidification

/-- Invariance of a matching-map property under a natural isomorphism of
opposite diagrams, expressed by the native arrow-category isomorphism. -/
private theorem matching_cofibration_of_natIso
    {X Y : SimplexCategoryᵒᵖ ⥤ SimplicialCat.{0, 0}ᵒᵖ}
    (e : X ≅ Y) (n : ℕ)
    (hX : ordinaryCofibrations (((matchingComparison n).app X).unop)) :
    ordinaryCofibrations (((matchingComparison n).app Y).unop) := by
  let P : MorphismProperty SimplicialCat.{0, 0}ᵒᵖ := ordinaryCofibrations.op
  have : P.RespectsIso := by
    dsimp [P, ordinaryCofibrations]
    infer_instance
  let a : Arrow.mk ((matchingComparison n).app X) ≅
      Arrow.mk ((matchingComparison n).app Y) :=
    Arrow.isoMk (asIso (e.hom.app (op ⦋n⦌)))
      (asIso ((matchingFunctor n).map e.hom))
      ((matchingComparison n).naturality e.hom)
  exact (P.arrow_mk_iso_iff a).mp hX

/-- The actual, uncurried Xi after forgetting dagger has every ordinary
cosimplicial latching map in the original Bergner cofibration LLP class. -/
theorem actualOrdinaryXi_matching_cofibration (m : ReverseSimplex) (n : ℕ) :
    ordinaryCofibrations
      (((matchingComparison n).app (actualOrdinaryXi m).op).unop) := by
  let e := NatIso.op (actualOrdinaryXiIso m)
  exact matching_cofibration_of_natIso e n
    (normalizedXi_matching_cofibration m n)

end

end DaggerModels.PartII.JTXiOrdinaryLatching
