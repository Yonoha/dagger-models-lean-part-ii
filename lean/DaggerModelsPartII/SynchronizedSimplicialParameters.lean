import DaggerModelsPartII.TotalElementsWeakComparison
import DaggerModelsPartII.GrothendieckContractibleFibers
import OriginalGateHomValueCollapseReconciledRecovered
import OriginalNerveProduct

/-! Synchronize independent simplicial parameter diagrams at the same simplex degree. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open CartesianMonoidalCategory DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal pointMap_tensor_GW)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SynchronizedSimplicialParameters

open GrothendieckTotalElements (totalDiagram elementDiagram)

noncomputable section

private abbrev Ord := SimplexCategoryᵒᵖ

variable {C D : Type} [SmallCategory C] [SmallCategory D]
variable (G : C ⥤ SSet.{0}) (H : D ⥤ SSet.{0})

/-- Take the product in each pair of original base parameters. -/
abbrev pairSpace := G.prod H ⋙ MonoidalCategory.tensor SSet.{0}

/-- Objects consist of two full parameters at one common time degree. -/
abbrev Index := (totalDiagram (pairSpace G H)).Elementsᵒᵖ

private def leftNat : pairSpace G H ⟶ CategoryTheory.Prod.fst C D ⋙ G where
  app p := fst (G.obj p.1) (H.obj p.2)
  naturality _ _ f := tensorHom_fst (G.map f.1) (H.map f.2)

private def rightNat : pairSpace G H ⟶ CategoryTheory.Prod.snd C D ⋙ H where
  app p := snd (G.obj p.1) (H.obj p.2)
  naturality _ _ f := tensorHom_snd (G.map f.1) (H.map f.2)

private def reindex {B E : Type} [SmallCategory B] [SmallCategory E]
    (F : B ⥤ E) (X : E ⥤ SSet.{0}) :
    (totalDiagram (F ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(F.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(F.map f.val.1, f.val.2), f.property⟩
  map_id p := by
    apply CategoryOfElements.ext
    exact Prod.ext (F.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (F.map_comp f.val.1 g.val.1) rfl

/-- Forget the right parameter, keeping the exact common time operator. -/
def left : Index G H ⥤ (totalDiagram G).Elementsᵒᵖ :=
  (((Functor.uncurry.map (leftNat G H)).mapElements) ⋙ reindex (CategoryTheory.Prod.fst C D) G).op

/-- Forget the left parameter, keeping the exact common time operator. -/
def right : Index G H ⥤ (totalDiagram H).Elementsᵒᵖ :=
  (((Functor.uncurry.map (rightNat G H)).mapElements) ⋙ reindex (CategoryTheory.Prod.snd C D) H).op

/-- The unchanged positive time operator of a full parameter choice. -/
abbrev time {B : Type} [SmallCategory B] (X : B ⥤ SSet.{0}) :
    (totalDiagram X).Elementsᵒᵖ ⥤ SimplexCategory :=
  (CategoryOfElements.π (totalDiagram X) ⋙ CategoryTheory.Prod.snd B Ord).leftOp

theorem left_time : left G H ⋙ time G = time (pairSpace G H) := rfl

theorem right_time : right G H ⋙ time H = time (pairSpace G H) := rfl

/-- Opposite indexing retains the weak contractibility of the nerve. -/
theorem point_op_iff (B : Type) [SmallCategory B] :
    GW (pointMap (nerve Bᵒᵖ)) ↔ GW (pointMap (nerve B)) := by
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso B
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let i := (IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal).uniqueUpToIso
    pointIsTerminal
  have he : e.inv ≫ SSet.opFunctor.map (pointMap (nerve B)) ≫ i.hom =
      pointMap (nerve Bᵒᵖ) := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← he]
  rw [weakEquivalence_precomp_iff e.inv, weakEquivalence_postcomp_iff _ i.hom]
  exact DaggerNativeSimplicialOppositeKanWeak.weak_op_iff _

private theorem elements_point_GW (X : SSet.{0}) (h : GW (pointMap X)) :
    GW (pointMap (nerve X.Elements)) := by
  apply (point_op_iff _).mp
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  letI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  letI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  letI : WeakEquivalence (pointMap X) := (weakEquivalence_iff_GW _).mpr h
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff e _).mp
  rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (a ≫ pointMap X)]
  infer_instance

/-- The projection from the total category of simplices to the original base
is a weak equivalence when every simplicial fiber is weakly contractible. -/
theorem projection_weak {B : Type} [SmallCategory B] (X : B ⥤ SSet.{0})
    (hX : ∀ b, GW (pointMap (X.obj b))) :
    WeakEquivalence (nerveMap
      (CategoryOfElements.π (totalDiagram X) ⋙ CategoryTheory.Prod.fst B Ord)) := by
  let e := GrothendieckTotalElements.equivalence X
  haveI : WeakEquivalence (nerveMap e.functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget (elementDiagram X))) :=
    GrothendieckContractibleFibers.projection_weak _ (fun b ↦ elements_point_GW _ (hX b))
  apply (weakEquivalence_precomp_iff (nerveMap e.functor) _).mp
  change WeakEquivalence (nerveMap (GrothendieckTotalElements.toTotal X ⋙
    CategoryOfElements.π (totalDiagram X) ⋙ CategoryTheory.Prod.fst _ _))
  rw [GrothendieckTotalElements.forget_square]
  infer_instance

private theorem total_point_GW {B : Type} [SmallCategory B] (X : B ⥤ SSet.{0})
    (hB : GW (pointMap (nerve B))) (hX : ∀ b, GW (pointMap (X.obj b))) :
    GW (pointMap (nerve (totalDiagram X).Elements)) := by
  let P := CategoryOfElements.π (totalDiagram X) ⋙ CategoryTheory.Prod.fst B Ord
  haveI : WeakEquivalence (nerveMap P) := projection_weak X hX
  haveI : WeakEquivalence (pointMap (nerve B)) := (weakEquivalence_iff_GW _).mpr hB
  have h : nerveMap P ≫ pointMap (nerve B) =
      pointMap (nerve (totalDiagram X).Elements) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- A product of two bases with weakly contractible nerves has a weakly contractible nerve. -/
theorem bases_point_GW (hC : GW (pointMap (nerve C))) (hD : GW (pointMap (nerve D))) :
    GW (pointMap (nerve (C × D))) := by
  let i := DaggerOriginalNerveProduct.nerveProductIso C D
  have h : i.hom ≫ pointMap (nerve C ⊗ nerve D) = pointMap (nerve (C × D)) :=
    pointIsTerminal.hom_ext _ _
  letI : WeakEquivalence (pointMap (nerve C ⊗ nerve D)) :=
    (weakEquivalence_iff_GW _).mpr (pointMap_tensor_GW hC hD)
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- Adding all times to a pointwise weakly contractible diagram preserves weak contractibility. -/
theorem index_point_GW_of {B : Type} [SmallCategory B] (X : B ⥤ SSet.{0})
    (hB : GW (pointMap (nerve B))) (hX : ∀ b, GW (pointMap (X.obj b))) :
    GW (pointMap (nerve (totalDiagram X).Elementsᵒᵖ)) :=
  (point_op_iff _).mpr (total_point_GW X hB hX)

/-- Independent weakly contractible parameter spaces and bases give a
weakly contractible synchronized category, with all common time arrows. -/
theorem index_point_GW (hC : GW (pointMap (nerve C))) (hD : GW (pointMap (nerve D)))
    (hG : ∀ c, GW (pointMap (G.obj c))) (hH : ∀ d, GW (pointMap (H.obj d))) :
    GW (pointMap (nerve (Index G H))) :=
  index_point_GW_of (pairSpace G H) (bases_point_GW hC hD)
    (fun p ↦ pointMap_tensor_GW (hG p.1) (hH p.2))

end

end DaggerModels.PartII.SynchronizedSimplicialParameters
