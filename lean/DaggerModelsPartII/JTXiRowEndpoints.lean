import DaggerModelsPartII.JTProjectiveGeneratorRealization
import DaggerModelsPartII.JTEndpointHom
import DaggerModelsPartII.EndpointMappingFiber
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# The original composite Xi nerve row and its ordered endpoint fiber

The actual composite nerve row is identified with Hom from the original
rigidified Xi frame. Its horizontal vertex operators, rather than a
transported substitute, define the endpoint arrow. The literal two-copy
source and the chosen ordered boundary point identify its strict fiber
with the original Xi ordered Hom simplicial set.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiRowEndpoints

open JTCoendMate JTCoendMateFormula JTProjectiveGeneratorRealization
open JTRelativeReedyFrame JTActualCosimplicialFrame
open JTOrderedFrameMate JTEndpointHom JTEndpointObjects JTZeroObjects

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The row of the original composite dagger coherent nerve, with no
replacement of the right adjoint. -/
def xiRow (C : DaggerSimplicialCat.{0, 0}) (m : ReverseSimplex) : SSet.{0} :=
  (compositeNerve.obj C).obj (op m)

/-- Remove only the universe lift from the retained actual Xi nerve row. -/
private def xiLiftToMappingIso (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) :
    (Presheaf.restrictedULiftYoneda.{0} (xiVertical m)).obj C ≅
      EndpointMappingFiber.mapping (Z := C) (xiVertical m) :=
  NatIso.ofComponents
    (fun k => (Equiv.ulift :
      ULift ((xiVertical m).obj k.unop ⟶ C) ≃
        ((xiVertical m).obj k.unop ⟶ C)).toIso)
    (by
      intro j k θ
      ext f
      rfl)

/-- The original composite-nerve row is naturally the actual Xi Hom row.
Naturality includes every vertical simplex operator. -/
def xiRowMappingIso (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) :
    xiRow C m ≅ EndpointMappingFiber.mapping (Z := C) (xiVertical m) :=
  (xiNerveIso m).app C ≪≫ xiLiftToMappingIso C m

/-- The row identification sends a horizontal original-nerve vertex map
to precomposition by the corresponding literal Xi vertex map. -/
theorem xiRowMappingIso_vertex (C : DaggerSimplicialCat.{0, 0})
    (i : Fin 2) (k : SimplexCategory)
    (z : (xiRow C oneIndex).obj (op k)) :
    (xiRowMappingIso C zeroIndex).hom.app (op k)
        (((compositeNerve.obj C).map (vertex i).op).app (op k) z) =
      (XiCurried.obj k).map (vertex i) ≫
        (xiRowMappingIso C oneIndex).hom.app (op k) z := by
  let p : (zeroIndex, k) ⟶ (oneIndex, k) := (vertex i, 𝟙 k)
  change (DaggerActualRigidificationQuillen.adjunction.homEquiv
      (DaggerJTAdjunction.frame.obj (zeroIndex, k)) C).symm
        (DaggerJTAdjunction.frame.map p ≫ z.down) =
      RigidifiedJTFrames.Xi.map p ≫
        (DaggerActualRigidificationQuillen.adjunction.homEquiv
          (DaggerJTAdjunction.frame.obj (oneIndex, k)) C).symm z.down
  exact DaggerActualRigidificationQuillen.adjunction.homEquiv_naturality_left_symm
    (DaggerJTAdjunction.frame.map p) z.down

/-- The literal ordered product of the two original outer-zero nerve rows. -/
def xiZeroPairRow (C : DaggerSimplicialCat.{0, 0}) : SSet.{0} :=
  FunctorToTypes.prod (xiRow C zeroIndex) (xiRow C zeroIndex)

/-- The endpoint arrow is defined by the two ORIGINAL horizontal cofaces
of the composite nerve, in the order zero then one. -/
def xiEndpointPairArrow (C : DaggerSimplicialCat.{0, 0}) :
    xiRow C oneIndex ⟶ xiZeroPairRow C :=
  FunctorToTypes.prod.lift ((compositeNerve.obj C).map (vertex 0).op)
    ((compositeNerve.obj C).map (vertex 1).op)

theorem xiEndpointPairArrow_zero (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointPairArrow C ≫ FunctorToTypes.prod.fst =
      (compositeNerve.obj C).map (vertex 0).op :=
  FunctorToTypes.prod.lift_fst _ _

theorem xiEndpointPairArrow_one (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointPairArrow C ≫ FunctorToTypes.prod.snd =
      (compositeNerve.obj C).map (vertex 1).op :=
  FunctorToTypes.prod.lift_snd _ _

/-- Hom from the literal two-copy endpoint source, with its actual
cosimplicial operators. -/
def endpointSourceRow (C : DaggerSimplicialCat.{0, 0}) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := C) (endpointSource XiCurried)

/-- Identify the original pair of nerve rows with Hom from the actual
two-copy endpoint source, preserving both ordered coprojections. -/
def xiZeroPairIso (C : DaggerSimplicialCat.{0, 0}) :
    xiZeroPairRow C ≅ endpointSourceRow C :=
  NatIso.ofComponents
    (fun k =>
      let e := (xiRowMappingIso C zeroIndex).app k
      (show (xiZeroPairRow C).obj k ≃ (endpointSourceRow C).obj k from
        { toFun := fun p => coprod.desc (e.hom p.1) (e.hom p.2)
          invFun := fun f => (e.inv (coprod.inl ≫ f), e.inv (coprod.inr ≫ f))
          left_inv := by
            intro p
            apply Prod.ext
            · simpa only [coprod.inl_desc] using hom_inv_id_apply e p.1
            · simpa only [coprod.inr_desc] using hom_inv_id_apply e p.2
          right_inv := by
            intro f
            apply coprod.hom_ext
            · simpa only [coprod.inl_desc] using inv_hom_id_apply e (coprod.inl ≫ f)
            · simpa only [coprod.inr_desc] using inv_hom_id_apply e (coprod.inr ≫ f) }).toIso)
    (by
      intro j k θ
      ext p
      apply coprod.hom_ext
      · change coprod.inl ≫
            (coprod.desc
              ((xiRowMappingIso C zeroIndex).hom.app k
                (((xiRow C zeroIndex).map θ) p.1))
              ((xiRowMappingIso C zeroIndex).hom.app k
                (((xiRow C zeroIndex).map θ) p.2))) =
          coprod.inl ≫
            ((endpointSource XiCurried).map θ.unop ≫
              coprod.desc ((xiRowMappingIso C zeroIndex).hom.app j p.1)
                ((xiRowMappingIso C zeroIndex).hom.app j p.2))
        dsimp only [endpointSource]
        rw [coprod.inl_desc, ← Category.assoc, coprod.inl_map, Category.assoc,
          coprod.inl_desc]
        exact congrFun ((xiRowMappingIso C zeroIndex).hom.naturality θ) p.1
      · change coprod.inr ≫
            (coprod.desc
              ((xiRowMappingIso C zeroIndex).hom.app k
                (((xiRow C zeroIndex).map θ) p.1))
              ((xiRowMappingIso C zeroIndex).hom.app k
                (((xiRow C zeroIndex).map θ) p.2))) =
          coprod.inr ≫
            ((endpointSource XiCurried).map θ.unop ≫
              coprod.desc ((xiRowMappingIso C zeroIndex).hom.app j p.1)
                ((xiRowMappingIso C zeroIndex).hom.app j p.2))
        dsimp only [endpointSource]
        rw [coprod.inr_desc, ← Category.assoc, coprod.inr_map, Category.assoc,
          coprod.inr_desc]
        exact congrFun ((xiRowMappingIso C zeroIndex).hom.naturality θ) p.2)

/-- The literal coface-defined endpoint arrow commutes with restriction
along the original Xi endpoint-face coproduct. -/
theorem xiEndpointPairArrow_square (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointPairArrow C ≫ (xiZeroPairIso C).hom =
      (xiRowMappingIso C oneIndex).hom ≫
        EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried) := by
  apply NatTrans.ext
  funext k z
  apply coprod.hom_ext
  ·
    dsimp [xiEndpointPairArrow, xiZeroPairIso, EndpointMappingFiber.precomp,
      FunctorToTypes.prod.lift]
    simp only [coprod.inl_desc]
    dsimp only [endpointFaces]
    rw [coprod.inl_desc_assoc]
    change (xiRowMappingIso C zeroIndex).hom.app k
        (((compositeNerve.obj C).map (vertex 0).op).app k z) =
      (XiCurried.obj k.unop).map (vertex 0) ≫
        (xiRowMappingIso C oneIndex).hom.app k z
    exact xiRowMappingIso_vertex C 0 k.unop z
  ·
    dsimp [xiEndpointPairArrow, xiZeroPairIso, EndpointMappingFiber.precomp,
      FunctorToTypes.prod.lift]
    simp only [coprod.inr_desc]
    dsimp only [endpointFaces]
    rw [coprod.inr_desc_assoc]
    change (xiRowMappingIso C zeroIndex).hom.app k
        (((compositeNerve.obj C).map (vertex 1).op).app k z) =
      (XiCurried.obj k.unop).map (vertex 1) ≫
        (xiRowMappingIso C oneIndex).hom.app k z
    exact xiRowMappingIso_vertex C 1 k.unop z

/-- The ordered point is the original boundary target transported through
the calibrated product identification, not a chosen unrelated point. -/
def pairBoundaryPoint (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    (Δ[0] : SSet.{0}) ⟶ xiZeroPairRow C :=
  EndpointMappingFiber.endpointPoint
      (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y) ≫
    (xiZeroPairIso C).inv

theorem pairBoundaryPoint_square (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) :
    pairBoundaryPoint C x y ≫ (xiZeroPairIso C).hom =
      EndpointMappingFiber.endpointPoint
        (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y) := by
  dsimp only [pairBoundaryPoint]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The strict fiber of the original composite-nerve coface arrow at the
original ordered boundary point is the manuscript's Xi ordered Hom. -/
def xiPairStrictFiberIso (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    XiOrdered C x y ≅ pullback (xiEndpointPairArrow C) (pairBoundaryPoint C x y) := by
  let e := xiRowMappingIso C oneIndex
  let d := xiZeroPairIso C
  let q := EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried)
  let b := EndpointMappingFiber.endpointPoint
    (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y)
  have h₁ : q ≫ d.inv = e.inv ≫ xiEndpointPairArrow C := by
    apply (cancel_mono d.hom).mp
    calc
      (q ≫ d.inv) ≫ d.hom = q := by simp only [Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      _ = e.inv ≫ (e.hom ≫ q) := by simp only [Iso.inv_hom_id_assoc]
      _ = e.inv ≫ (xiEndpointPairArrow C ≫ d.hom) := by
        rw [xiEndpointPairArrow_square]
      _ = (e.inv ≫ xiEndpointPairArrow C) ≫ d.hom :=
        (Category.assoc _ _ _).symm
  have h₂ : b ≫ d.inv = (𝟙 _) ≫ pairBoundaryPoint C x y := by
    change b ≫ d.inv = b ≫ d.inv
    rfl
  let f : pullback q b ≅ pullback (xiEndpointPairArrow C) (pairBoundaryPoint C x y) :=
    asIso (pullback.map q b (xiEndpointPairArrow C) (pairBoundaryPoint C x y)
      e.inv (𝟙 _) d.inv h₁ h₂)
  exact (orderedHomSSetIso XiAugmentationCurried C x y).symm ≪≫
    EndpointMappingFiber.underFiberIso
      (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
      (boundaryTarget C x y) ≪≫ f

/-- The categorical product of the two original outer-zero composite-nerve
rows. The explicit pointwise pair above is its canonical presentation. -/
def xiCategoricalZeroPairRow (C : DaggerSimplicialCat.{0, 0}) : SSet.{0} :=
  xiRow C zeroIndex ⨯ xiRow C zeroIndex

/-- The ORIGINAL categorical-product endpoint arrow is the product lift
of the two horizontal composite-nerve coface maps. -/
def xiEndpointArrow (C : DaggerSimplicialCat.{0, 0}) :
    xiRow C oneIndex ⟶ xiCategoricalZeroPairRow C :=
  prod.lift ((compositeNerve.obj C).map (vertex 0).op)
    ((compositeNerve.obj C).map (vertex 1).op)

theorem xiEndpointArrow_zero (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointArrow C ≫ prod.fst =
      (compositeNerve.obj C).map (vertex 0).op :=
  prod.lift_fst _ _

theorem xiEndpointArrow_one (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointArrow C ≫ prod.snd =
      (compositeNerve.obj C).map (vertex 1).op :=
  prod.lift_snd _ _

/-- The native pointwise-product comparison, with its canonical
projections to the same two original nerve rows. -/
def xiCategoricalPairIso (C : DaggerSimplicialCat.{0, 0}) :
    xiCategoricalZeroPairRow C ≅ xiZeroPairRow C :=
  FunctorToTypes.binaryProductIso (xiRow C zeroIndex) (xiRow C zeroIndex)

/-- The explicit pair arrow is exactly the native product comparison of
the categorical original-coface arrow. -/
theorem xiEndpointPairArrow_toCategorical (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointPairArrow C ≫ (xiCategoricalPairIso C).inv =
      xiEndpointArrow C := by
  apply prod.hom_ext
  · dsimp only [xiCategoricalPairIso]
    rw [Category.assoc,
      FunctorToTypes.binaryProductIso_inv_comp_fst,
      xiEndpointPairArrow_zero, xiEndpointArrow_zero]
  · dsimp only [xiCategoricalPairIso]
    rw [Category.assoc,
      FunctorToTypes.binaryProductIso_inv_comp_snd,
      xiEndpointPairArrow_one, xiEndpointArrow_one]

theorem xiEndpointArrow_pair (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointArrow C ≫ (xiCategoricalPairIso C).hom =
      xiEndpointPairArrow C := by
  apply (cancel_mono (xiCategoricalPairIso C).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (xiEndpointPairArrow_toCategorical C).symm

/-- The original ordered point, now in the categorical product row. -/
def boundaryPoint (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    (Δ[0] : SSet.{0}) ⟶ xiCategoricalZeroPairRow C :=
  pairBoundaryPoint C x y ≫ (xiCategoricalPairIso C).inv

theorem boundaryPoint_pair (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    boundaryPoint C x y ≫ (xiCategoricalPairIso C).hom =
      pairBoundaryPoint C x y := by
  dsimp only [boundaryPoint]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Calibration of the original categorical endpoint arrow against the
actual Xi endpoint-face coproduct, with no replacement arrow. -/
theorem xiEndpointArrow_square (C : DaggerSimplicialCat.{0, 0}) :
    xiEndpointArrow C ≫ (xiCategoricalPairIso C).hom ≫
        (xiZeroPairIso C).hom =
      (xiRowMappingIso C oneIndex).hom ≫
        EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried) := by
  rw [← Category.assoc, xiEndpointArrow_pair]
  exact xiEndpointPairArrow_square C

/-- The ordered boundary point in the categorical product still has the
same literal x-then-y endpoint restrictions. -/
theorem boundaryPoint_square (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    boundaryPoint C x y ≫ (xiCategoricalPairIso C).hom ≫
        (xiZeroPairIso C).hom =
      EndpointMappingFiber.endpointPoint
        (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y) := by
  rw [← Category.assoc, boundaryPoint_pair]
  exact pairBoundaryPoint_square C x y

/-- The original Xi ordered Hom is the strict fiber of the categorical
composite-nerve endpoint arrow at the original ordered point. -/
def xiStrictFiberIso (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    XiOrdered C x y ≅ pullback (xiEndpointArrow C) (boundaryPoint C x y) := by
  let e := xiCategoricalPairIso C
  have h₁ : xiEndpointPairArrow C ≫ e.inv = (𝟙 _) ≫ xiEndpointArrow C := by
    rw [xiEndpointPairArrow_toCategorical, Category.id_comp]
  have h₂ : pairBoundaryPoint C x y ≫ e.inv = (𝟙 _) ≫ boundaryPoint C x y := by
    change pairBoundaryPoint C x y ≫ e.inv = pairBoundaryPoint C x y ≫ e.inv
    rfl
  let f : pullback (xiEndpointPairArrow C) (pairBoundaryPoint C x y) ≅
      pullback (xiEndpointArrow C) (boundaryPoint C x y) :=
    asIso (pullback.map (xiEndpointPairArrow C) (pairBoundaryPoint C x y)
      (xiEndpointArrow C) (boundaryPoint C x y) (𝟙 _) (𝟙 _) e.inv h₁ h₂)
  exact xiPairStrictFiberIso C x y ≪≫ f

/-- The literal strict Xi fiber projects to the original nerve-row value of
the underlying ordered Hom element. -/
theorem xiStrictFiberIso_fst_app (C : Coefficient) (x y : C.Obj)
    (k : SimplexCategory) (f : (XiOrdered C x y).obj (op k)) :
    (((xiStrictFiberIso C x y).hom ≫
      pullback.fst (xiEndpointArrow C) (boundaryPoint C x y)).app (op k)) f =
      (xiRowMappingIso C oneIndex).inv.app (op k) f.val := by
  simp only [xiStrictFiberIso, xiPairStrictFiberIso, Iso.trans_hom,
    Category.assoc, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  let e := orderedHomSSetIso XiAugmentationCurried C x y
  let z := e.inv.app (op k) f
  have h := EndpointMappingFiber.underFiberIso_hom_fst_app
    (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
    (boundaryTarget C x y) k z
  have hz : orderedHomEquiv XiAugmentationCurried C x y k z = f :=
    (orderedHomEquiv XiAugmentationCurried C x y k).apply_symm_apply f
  have hv := orderedHomEquiv_val XiAugmentationCurried C x y k z
  have hf := h.trans (hv.symm.trans (congrArg Subtype.val hz))
  simp only [← Category.assoc]
  exact congrArg ((xiRowMappingIso C oneIndex).inv.app (op k)) hf

end

end DaggerModels.PartII.JTXiRowEndpoints
