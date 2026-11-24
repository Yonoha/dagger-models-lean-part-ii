import DaggerModelsPartII.JTGraphCylinderSimplexSpan
import DaggerModelsPartII.SimplicialResolutionFunctor
import DaggerModelsPartII.JTTargetCommaPullbackBar
import NativeOverNerveWeakContractibility
import NativeSimplicialOppositeKanWeak

/-! The simplex-map span index has the weak homotopy type of the simplex category. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphCylinderSpanProjection

noncomputable section

variable (D : Type) [SmallCategory D]

private abbrev H := Functor.hom D
private abbrev U := StructuredArrow.functor (𝟭 D)

/-- Repack the two operators of a hom element as a base arrow and an under-arrow. -/
def fromElements : (H D).Elements ⥤ Grothendieck (U D) where
  obj x := ⟨x.fst.1, Under.mk x.snd⟩
  map f := ⟨f.val.1, Under.homMk f.val.2 (by
    change (f.val.1.unop ≫ _) ≫ f.val.2 = _
    rw [Category.assoc]
    exact f.property)⟩
  map_id x := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    apply Under.UnderMorphism.ext
    let X : Under x.fst.1.unop := Under.mk x.snd
    have hx : (Under.map (𝟙 x.fst.1.unop)).obj X = X := by
      change Under.mk (𝟙 _ ≫ x.snd) = Under.mk x.snd
      rw [Category.id_comp]
    change 𝟙 x.fst.2 = (eqToHom hx).right
    rw [Under.eqToHom_right]
    rfl
  map_comp {x y z} f g := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    apply Under.UnderMorphism.ext
    let X : Under x.fst.1.unop := Under.mk x.snd
    have hx : (Under.map (f.val.1 ≫ g.val.1).unop).obj X =
        (Under.map g.val.1.unop).obj ((Under.map f.val.1.unop).obj X) := by
      change Under.mk ((g.val.1.unop ≫ f.val.1.unop) ≫ x.snd) =
        Under.mk (g.val.1.unop ≫ f.val.1.unop ≫ x.snd)
      rw [Category.assoc]
    change f.val.2 ≫ g.val.2 = (eqToHom hx).right ≫ f.val.2 ≫ g.val.2
    rw [Under.eqToHom_right]
    change f.val.2 ≫ g.val.2 = 𝟙 x.fst.2 ≫ f.val.2 ≫ g.val.2
    rw [Category.id_comp]

private theorem fromElements_full : (fromElements D).Full where
  map_surjective {x y} f := by
    refine ⟨⟨(f.base, f.fiber.right), ?_⟩, ?_⟩
    · change f.base.unop ≫ x.snd ≫ f.fiber.right = y.snd
      rw [← Category.assoc]
      exact Under.w f.fiber
    · refine Grothendieck.ext _ _ rfl ?_
      apply Under.UnderMorphism.ext
      rw [eqToHom_refl, Category.id_comp]
      rfl

private theorem fromElements_faithful : (fromElements D).Faithful where
  map_injective {x y} _ _ h := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun f ↦ Grothendieck.Hom.base f) h
    · exact congrArg (fun f ↦ (f.fiber.right : x.fst.2 ⟶ y.fst.2)) h

private theorem fromElements_surjective : Function.Surjective (fromElements D).obj := by
  rintro ⟨d, X⟩
  exact ⟨⟨(d, X.right), X.hom⟩, rfl⟩

private theorem under_point_GW (d : D) : GW (pointMap (nerve (Under d))) := by
  let e := Over.opEquivOpUnder d
  haveI : WeakEquivalence (pointMap (nerve (Over (op d)))) :=
    (weakEquivalence_iff_GW _).mpr (DaggerNativeOverNerveWeakContractibility.point_GW (op d))
  let h := (opOpEquivalence (Under d)).inverse ⋙ e.inverse.op
  haveI : WeakEquivalence (nerveMap h) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence h
  haveI := DaggerNativeSimplicialOppositeKanWeak.op_weak
    (pointMap (nerve (Over (op d))))
  let i := DaggerNativeNerveOppositeIso.nerveOppositeIso (Over (op d))
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let t := (IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal).uniqueUpToIso
    pointIsTerminal
  have hp : nerveMap h ≫ i.inv ≫ SSet.opFunctor.map (pointMap (nerve (Over (op d)))) ≫ t.hom =
      pointMap (nerve (Under d)) := pointIsTerminal.hom_ext _ _
  rw [← hp, ← weakEquivalence_iff_GW]
  infer_instance

private theorem sourceProjection_weak : WeakEquivalence
    (nerveMap (fromElements D ⋙ Grothendieck.forget (U D))) := by
  letI : (fromElements D).Full := fromElements_full D
  letI : (fromElements D).Faithful := fromElements_faithful D
  letI : (fromElements D).EssSurj := Functor.essSurj_of_surj (fromElements_surjective D)
  letI : (fromElements D).IsEquivalence := {}
  haveI : WeakEquivalence (nerveMap (fromElements D)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence (fromElements D)
  haveI := GrothendieckContractibleFibers.projection_weak (U D) (fun d ↦ under_point_GW D d.unop)
  change WeakEquivalence (nerveMap (fromElements D) ≫ nerveMap (Grothendieck.forget (U D)))
  infer_instance

/-- The exact source projection of the hom category of elements is Kan weak. -/
theorem homElements_source_weak :
    WeakEquivalence (nerveMap (CategoryOfElements.π (Functor.hom D) ⋙
      CategoryTheory.Prod.fst Dᵒᵖ D)) :=
  sourceProjection_weak D

/-- Reversing the factorizations gives the original forward projection to the smaller simplex. -/
theorem smaller_weak (C : Type) [SmallCategory C] :
    WeakEquivalence (nerveMap (JTGraphCylinderSimplexSpan.smaller C)) := by
  let D := JTGraphCylinderSimplexSpan.Simplices C
  let F := fromElements D ⋙ Grothendieck.forget (U D)
  haveI : WeakEquivalence (nerveMap F) := sourceProjection_weak D
  haveI := DaggerNativeSimplicialOppositeKanWeak.op_weak (nerveMap F)
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso (H D).Elements
  let e' := DaggerNativeNerveOppositeIso.nerveOppositeIso Dᵒᵖ
  have h : SSet.opFunctor.map (nerveMap F) ≫ e'.hom = e.hom ≫ nerveMap F.op :=
    DaggerNativeNerveOppositeIso.nerveOppositeNatIso.hom.naturality F.toCatHom
  have he : nerveMap F.op = e.inv ≫ SSet.opFunctor.map (nerveMap F) ≫ e'.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  change WeakEquivalence (nerveMap (F.op ⋙ unopUnop D))
  haveI : WeakEquivalence (nerveMap F.op) := by rw [he]; infer_instance
  haveI : WeakEquivalence (nerveMap (unopUnop D)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence (unopUnop D)
  change WeakEquivalence (nerveMap F.op ≫ nerveMap (unopUnop D))
  infer_instance

section Original

open JTGraphCylinderSimplexSpan (Simplices fibers smaller)

variable (C : Type) [SmallCategory C] (L : C ⥤ NecklaceCode)

/-- Forget the common source fiber and retain the smaller simplex. -/
def toSimplices : Grothendieck (fibers C L) ⥤ Simplices C :=
  Grothendieck.forget (fibers C L) ⋙ smaller C

/-- The whole resolution by the cylinder fibers has Kan weak nerve projection. -/
theorem toSimplices_weak : WeakEquivalence (nerveMap (toSimplices C L)) := by
  haveI := JTGraphCylinderSimplexSpan.projection_weak C L
  haveI := smaller_weak C
  change WeakEquivalence (nerveMap (Grothendieck.forget (fibers C L)) ≫ nerveMap (smaller C))
  infer_instance

private theorem point_iff {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    GW (pointMap X) ↔ GW (pointMap Y) := by
  have h : f ≫ pointMap Y = pointMap X := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← h]
  exact weakEquivalence_precomp_iff f _

/-- Weak contractibility of the entire cylinder-fiber resolution is equivalent
to weak contractibility of the original nerve. -/
theorem cylinder_point_iff :
    GW (pointMap (nerve (Grothendieck (fibers C L)))) ↔ GW (pointMap (nerve C)) := by
  let f := nerveMap (toSimplices C L)
  let g := SimplicialResolutionFunctor.elementsProjection.app (nerve C)
  let h := SimplicialResolutionFunctor.augmentation.app (nerve C)
  haveI : WeakEquivalence f := toSimplices_weak C L
  haveI : WeakEquivalence g := SimplicialResolutionFunctor.elementsProjection_weak (nerve C)
  haveI : WeakEquivalence h := SimplicialResolutionFunctor.augmentation_weak (nerve C)
  exact (point_iff f).trans ((point_iff g).symm.trans (point_iff h))

end Original

section FixedTarget

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphCylinderSimplexSpan (fibers)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- The native code of each original comma object and the exact code map of each arrow. -/
def nativeCode : TargetComma Q ⥤ NecklaceCode :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

/-- Contracting the original fixed-target cylinder resolution suffices for,
and is equivalent to, contracting the whole original target comma. -/
theorem targetComma_point_iff :
    GW (pointMap (nerve (Grothendieck (fibers (TargetComma Q) (nativeCode Q))))) ↔
      GW (pointMap (nerve (TargetComma Q))) :=
  cylinder_point_iff (TargetComma Q) (nativeCode Q)

/-- The cylinder-fiber contraction supplies exactly the original bar hypothesis. -/
theorem cylinder_point_iff_bar_point :
    GW (pointMap (nerve (Grothendieck (fibers (TargetComma Q) (nativeCode Q))))) ↔
      GW (pointMap (JTTargetCommaPullbackBar.bar W x y Q)) :=
  (targetComma_point_iff Q).trans (JTTargetCommaPullbackBar.comma_point_iff_bar_point W x y Q)

/-- Contracting the original cylinder resolutions gives weakness of the original evaluator. -/
theorem evaluator_weak_of_cylinder_point
    (h : ∀ Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y),
      GW (pointMap (nerve (Grothendieck (fibers (TargetComma Q) (nativeCode Q)))))) :
    WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) :=
  JTTargetCommaPullbackBar.evaluator_weak_of_bar_point W x y
    (fun Q ↦ (cylinder_point_iff_bar_point Q).mp (h Q))

end FixedTarget

end

end DaggerModels.PartII.JTGraphCylinderSpanProjection
