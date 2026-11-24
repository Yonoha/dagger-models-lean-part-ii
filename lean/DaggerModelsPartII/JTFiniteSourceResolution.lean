import DaggerModelsPartII.JTGraphVariableResolutionCategory
import NativeOverNerveWeakContractibility
import Mathlib.Data.Finite.Sigma

/-! Restrict the original cylinder diagram to native collapses supplied by its arrows. -/
set_option autoImplicit false

open CategoryTheory Limits

namespace DaggerModels.PartII.FiniteSourceSlice

noncomputable section

variable {B N : Type} [SmallCategory B] [SmallCategory N]
variable (F : B ⥤ N)

/-- Retain all original native collapses supplied by arrows into the indicated diagram object. -/
def sources (b : B) : ObjectProperty (Over (F.obj b)) :=
  fun P ↦ ∃ (a : B) (f : a ⟶ b), Over.mk (F.map f) = P

abbrev slice (b : B) := (sources F b).FullSubcategory

/-- The identity collapse belongs to the restricted native slice. -/
def identity (b : B) : slice F b :=
  ⟨Over.mk (𝟙 _), ⟨b, 𝟙 b, congrArg Over.mk (F.map_id b)⟩⟩

/-- The restricted native slice has the same terminal identity collapse. -/
def identityTerminal (b : B) : IsTerminal (identity F b) :=
  IsTerminal.ofUniqueHom
    (fun P ↦ ObjectProperty.homMk (Over.mkIdTerminal.from P.obj))
    (fun P f ↦ ObjectProperty.hom_ext (sources F b) (Over.mkIdTerminal.hom_ext f.hom
      (Over.mkIdTerminal.from P.obj)))

/-- Only finitely many native collapses occur over a vertex of a finite diagram. -/
theorem finite_sources [Finite B] (h : ∀ a b : B, Finite (a ⟶ b)) (b : B) :
    Finite (slice F b) := by
  letI (a : B) : Finite (a ⟶ b) := h a b
  apply Finite.of_surjective
    (f := fun p : Σ a : B, a ⟶ b ↦ ⟨Over.mk (F.map p.2), ⟨p.1, p.2, rfl⟩⟩)
  intro P
  obtain ⟨a, f, hf⟩ := P.property
  exact ⟨⟨a, f⟩, ObjectProperty.FullSubcategory.ext hf⟩

variable {b c : B}

/-- Postcompose a retained native collapse with the original diagram arrow. -/
def post (f : b ⟶ c) : slice F b ⥤ slice F c :=
  (sources F c).lift ((sources F b).ι ⋙ Over.map (F.map f)) (by
    intro P
    obtain ⟨a, g, hg⟩ := P.property
    refine ⟨a, g ≫ f, ?_⟩
    change Over.mk (F.map (g ≫ f)) = (Over.map (F.map f)).obj P.obj
    rw [F.map_comp, ← hg]
    rfl)

end
end DaggerModels.PartII.FiniteSourceSlice

open Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open DaggerSSetGluing DaggerOriginalProductGadget DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteSourceSlice

noncomputable section

variable {B N : Type} [SmallCategory B] [SmallCategory N]
variable (F : B ⥤ N) (b : B)

/-- The finite native source slice is weakly contractible via its terminal collapse. -/
theorem slice_point_GW : GW (pointMap (nerve (slice F b))) := by
  let C := slice F b
  let t := identity F b
  let e := Over.equivalenceOfIsTerminal (identityTerminal F b)
  let q := nerveMap e.functor
  let r := pointMap (nerve C)
  haveI : WeakEquivalence q := DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence (pointMap (nerve (Over t))) :=
    (weakEquivalence_iff_GW _).mpr (DaggerNativeOverNerveWeakContractibility.point_GW t)
  have h : q ≫ r = pointMap (nerve (Over t)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff q r).mp
  rw [h]
  infer_instance

end
end DaggerModels.PartII.FiniteSourceSlice

namespace DaggerModels.PartII.FiniteSourceSlice

noncomputable section

open JTGraphLiftTransport JTProjectiveOrderedFiberComparison
open DaggerOriginalCodiscreteNerveInjective

private theorem finite_parameter (S : NecklaceCode) (k : SimplexCategory) :
    Finite (S.toSSet ⟶ GroupoidSimplex.parameter.obj k) := by
  letI : Finite (S.toSSet.obj (op ⦋0⦌)) :=
    Finite.of_injective S.verticesEquiv S.verticesEquiv.injective
  letI : Finite (GroupoidSimplex.vertices.obj k) :=
    inferInstanceAs (Finite (Fin (k.len + 1)))
  let e := GroupoidSimplex.parameterCodiscreteIso.app k
  apply Finite.of_injective (f := fun f : S.toSSet ⟶ GroupoidSimplex.parameter.obj k ↦
    vertexLabels (f ≫ e.hom))
  intro f g h
  apply (cancel_mono e.hom).mp
  apply NatTrans.ext
  funext m a
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  rw [← vertexLabels_natural, ← vertexLabels_natural]
  exact congrFun h _

/-- There are finitely many exact parameter choices for a fixed native source and collapse. -/
theorem finite_graph_lifts
    {W : SegalLocalizers.ReverseDaggerSpace.{0}}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    {Q : NecklacesOver (OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W))
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)}
    (U : JTGraphFactoredPresentation.TargetComma Q)
    {S : NecklaceCode} (c : S ⟶ U.left.fiber.left) :
    Finite (JTGraphParameterTimeResolution.Lifts U c) := by
  letI : Finite (S.toSSet ⟶ GroupoidSimplex.parameter.obj (degree U.left)) :=
    finite_parameter S (degree U.left)
  apply Finite.of_injective
    (f := fun D : JTGraphParameterTimeResolution.Lifts U c ↦ D.val.parameter)
  intro D E h
  apply Subtype.ext
  exact GraphLift.ext (D.property.trans E.property.symm) h

/-- The finite source list is closed under the actual resolution transport. -/
theorem transport_source
    {W : SegalLocalizers.ReverseDaggerSpace.{0}}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    {Q : NecklacesOver (OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W))
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)}
    {B : Type} [SmallCategory B] (D : B ⥤ JTGraphFactoredPresentation.TargetComma Q)
    {b b' : B} (f : b ⟶ b') (P : JTGraphVariableTimeIndex.Index (D.obj b))
    (h : sources (D ⋙ CostructuredArrow.proj _ Q ⋙
      BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y))
      b ((JTGraphVariableTimeIndex.toNative (D.obj b)).obj P)) :
    sources (D ⋙ CostructuredArrow.proj _ Q ⋙
      BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y))
      b' ((JTGraphVariableTimeIndex.toNative (D.obj b')).obj
        ((JTGraphVariableTimeTransport.transport (D.map f)).obj P)) := by
  let N := D ⋙ CostructuredArrow.proj _ Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)
  let p : slice N b := ⟨(JTGraphVariableTimeIndex.toNative (D.obj b)).obj P, h⟩
  exact ((post N f).obj p).property


end
end DaggerModels.PartII.FiniteSourceSlice

namespace DaggerModels.PartII.FiniteSourceSlice

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex
noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q) (P : ObjectProperty (NativeSlice U))

private abbrev time := P.ι.op ⋙ timeDiagram U
private abbrev total := GrothendieckTotalElements.totalDiagram (time U P)
private abbrev fullTotal := GrothendieckTotalElements.totalDiagram (timeDiagram U)

private def indexInclusionAux : (total U P).Elements ⥤ (fullTotal U).Elements where
  obj A := ⟨(op A.fst.1.unop.obj, A.fst.2), A.snd⟩
  map f := CategoryOfElements.homMk _ _ (P.ι.op.map f.val.1, f.val.2) f.property

private def indexInclusionFF : (indexInclusionAux U P).FullyFaithful where
  preimage f := CategoryOfElements.homMk _ _
    (((P.fullyFaithfulι.op).preimage f.val.1), f.val.2) f.property
  map_preimage f := by
    apply CategoryOfElements.ext
    apply Prod.ext
    · exact (P.fullyFaithfulι.op).map_preimage f.val.1
    · rfl
  preimage_map f := by
    apply CategoryOfElements.ext
    apply Prod.ext
    · exact (P.fullyFaithfulι.op).preimage_map f.val.1
    · rfl

/-- Keep precisely the native sources satisfying the selected object property. -/
def indexProperty : ObjectProperty (Index U) :=
  fun A ↦ P ((toNative U).obj A)

private def indexLift : (total U P).Elementsᵒᵖ ⥤ (indexProperty U P).FullSubcategory :=
  (indexProperty U P).lift (indexInclusionAux U P).op (fun A ↦ A.unop.fst.1.unop.property)

private def indexLiftEquivalence :
    (total U P).Elementsᵒᵖ ≌ (indexProperty U P).FullSubcategory := by
  haveI : (indexInclusionAux U P).Full := (indexInclusionFF U P).full
  haveI : (indexInclusionAux U P).Faithful := (indexInclusionFF U P).faithful
  let F := indexLift U P
  haveI : F.Full := by dsimp only [F, indexLift]; infer_instance
  haveI : F.Faithful := by dsimp only [F, indexLift]; infer_instance
  haveI : F.EssSurj := ⟨fun A ↦
    ⟨op ⟨(op ⟨A.obj.unop.fst.1.unop, A.property⟩, A.obj.unop.fst.2), A.obj.unop.snd⟩,
      ⟨eqToIso (ObjectProperty.FullSubcategory.ext rfl)⟩⟩⟩
  letI : F.IsEquivalence := { }
  exact F.asEquivalence

private theorem timeElements_point (A : NativeSlice U) :
    GW (pointMap (nerve (JTGraphParameterTimeResolution.timeSpace U A.hom).Elements)) := by
  let X := JTGraphParameterTimeResolution.timeSpace U A.hom
  let p := pointMap X
  haveI : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    ((JTHomotopyTargetTimeResolution.point_GW_iff _ _).mp
      (JTGraphParameterTimeResolution.resolution_point_GW U A.hom (lifts_nonempty U A).some))
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  haveI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  haveI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  haveI : WeakEquivalence (pointMap (nerve X.Elementsᵒᵖ)) := by
    apply (weakEquivalence_precomp_iff e _).mp
    rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (a ≫ p)]
    infer_instance
  let j := DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements
  letI : SSet.opFunctor.{0}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let ht := IsTerminal.isTerminalObj SSet.opFunctor.{0} _ pointIsTerminal
  let t := ht.uniqueUpToIso pointIsTerminal
  apply (weakEquivalence_iff_GW _).mp
  apply (DaggerNativeSimplicialOppositeKanWeak.weak_op_iff _).mp
  rw [ht.hom_ext (SSet.opFunctor.map (pointMap (nerve X.Elements)))
    (j.hom ≫ pointMap (nerve X.Elementsᵒᵖ) ≫ t.inv)]
  infer_instance

private abbrev forgetNative : (indexProperty U P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((indexProperty U P).ι ⋙ toNative U) (fun A ↦ A.property)

private abbrev restrictedProjection :
    (total U P).Elements ⥤ P.FullSubcategoryᵒᵖ :=
  CategoryOfElements.π (total U P) ⋙ CategoryTheory.Prod.fst _ _

private theorem restrictedProjection_weak :
    WeakEquivalence (nerveMap (restrictedProjection U P)) := by
  let D := time U P
  let e := GrothendieckTotalElements.equivalence D
  letI : WeakEquivalence (nerveMap e.functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  letI : WeakEquivalence (nerveMap (Grothendieck.forget (GrothendieckTotalElements.elementDiagram D))) :=
    GrothendieckContractibleFibers.projection_weak _ (fun A ↦ timeElements_point U A.unop.obj)
  apply (weakEquivalence_precomp_iff (nerveMap e.functor) _).mp
  change WeakEquivalence (nerveMap (GrothendieckTotalElements.toTotal D ⋙ restrictedProjection U P))
  rw [GrothendieckTotalElements.forget_square D]
  infer_instance

private theorem forgetNative_weak : WeakEquivalence (nerveMap (forgetNative U P)) := by
  let e := indexLiftEquivalence U P
  letI : WeakEquivalence (nerveMap e.functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  letI : WeakEquivalence (nerveMap (restrictedProjection U P).op) :=
    (TotalElementsWeakComparison.nerveMap_op_iff _).mpr (restrictedProjection_weak U P)
  letI : WeakEquivalence (nerveMap (unopUnop P.FullSubcategory)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  apply (weakEquivalence_precomp_iff (nerveMap e.functor) _).mp
  change WeakEquivalence (nerveMap (indexLift U P ⋙ forgetNative U P))
  have h : indexLift U P ⋙ forgetNative U P =
      (restrictedProjection U P).op ⋙ unopUnop P.FullSubcategory := by
    refine CategoryTheory.Functor.ext (fun A ↦ ObjectProperty.FullSubcategory.ext rfl) ?_
    intro A B f
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  rw [h]
  change WeakEquivalence (nerveMap (restrictedProjection U P).op ≫
    nerveMap (unopUnop P.FullSubcategory))
  infer_instance

/-- The actual cylinders over the retained native sources. -/
abbrev restrictedFibers :=
  (indexProperty U P).ι ⋙ joint U ⋙ JTGraphCylinderFiberDiagram.diagram

abbrev RestrictedResolution := Grothendieck (restrictedFibers U P)

/-- The canonical inclusion keeps the time and internal necklace data unchanged. -/
abbrev includeResolution : RestrictedResolution U P ⥤ Resolution U :=
  Grothendieck.pre (joint U ⋙ JTGraphCylinderFiberDiagram.diagram) (indexProperty U P).ι

/-- The restricted cylinder projects weakly to the retained native slice. -/
theorem restrictedToNative_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (restrictedFibers U P) ⋙ forgetNative U P)) := by
  letI : WeakEquivalence (nerveMap (Grothendieck.forget (restrictedFibers U P))) :=
    GrothendieckContractibleFibers.projection_weak _ (fun A ↦
      JTHomotopyTargetComma.fiber_point_GW_at ((joint U).obj A.obj).1 ((joint U).obj A.obj).2)
  letI := forgetNative_weak U P
  change WeakEquivalence (nerveMap (Grothendieck.forget (restrictedFibers U P)) ≫
    nerveMap (forgetNative U P))
  infer_instance

/-- A weakly contractible retained native slice supplies a weakly
contractible resolution using the original cylinders. -/
theorem restrictedResolution_point_GW (hP : GW (pointMap (nerve P.FullSubcategory))) :
    GW (pointMap (nerve (RestrictedResolution U P))) := by
  let f := nerveMap (Grothendieck.forget (restrictedFibers U P) ⋙ forgetNative U P)
  letI : WeakEquivalence f := restrictedToNative_weak U P
  letI : WeakEquivalence (pointMap (nerve P.FullSubcategory)) :=
    (weakEquivalence_iff_GW _).mpr hP
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (f ≫ pointMap (nerve P.FullSubcategory)) (pointMap _)]
  infer_instance

end
end DaggerModels.PartII.FiniteSourceSlice

namespace DaggerModels.PartII.FiniteSourceSlice

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex
open JTGraphVariableTimeTransport (resolutionDiagram transportResolution)

noncomputable section

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q) (P : ObjectProperty (NativeSlice U))

private abbrev resolutionProperty : ObjectProperty (Resolution U) :=
  fun A ↦ indexProperty U P A.base

private def fullResolutionLift :
    RestrictedResolution U P ⥤ (resolutionProperty U P).FullSubcategory :=
  (resolutionProperty U P).lift (includeResolution U P) (fun A ↦ A.base.property)

private def fullResolutionInverse :
    (resolutionProperty U P).FullSubcategory ⥤ RestrictedResolution U P where
  obj A := ⟨⟨A.obj.base, A.property⟩, A.obj.fiber⟩
  map f := ⟨ObjectProperty.homMk f.hom.base, f.hom.fiber⟩
  map_id A := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  map_comp f g := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    rfl

private def fullResolutionEquivalence :
    RestrictedResolution U P ≌ (resolutionProperty U P).FullSubcategory where
  functor := fullResolutionLift U P
  inverse := fullResolutionInverse U P
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
  functor_unitIso_comp _ := by simp

private theorem fullResolution_point_GW (hP : GW (pointMap (nerve P.FullSubcategory))) :
    GW (pointMap (nerve (resolutionProperty U P).FullSubcategory)) := by
  let f := nerveMap (fullResolutionEquivalence U P).functor
  let p := pointMap (nerve (resolutionProperty U P).FullSubcategory)
  letI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff f p).mp
  rw [pointIsTerminal.hom_ext (f ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr (restrictedResolution_point_GW U P hP)

private theorem inclusion_cancel {C D : Type} [SmallCategory C] [SmallCategory D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory} (h : F ⋙ P.ι = G ⋙ P.ι) :
    F = G := by
  have ho (c : C) : (F.obj c).obj = (G.obj c).obj :=
    congrArg (fun H : C ⥤ D ↦ H.obj c) h
  let e (c : C) : F.obj c = G.obj c := ObjectProperty.FullSubcategory.ext (ho c)
  refine CategoryTheory.Functor.ext e ?_
  intro a b f
  apply P.ι.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

variable {B : Type} [SmallCategory B]
variable (L : B ⥤ TargetComma Q)

private abbrev sourceDiagram :=
  L ⋙ CostructuredArrow.proj _ Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

private abbrev keep (b : B) := resolutionProperty (L.obj b) (sources (sourceDiagram L) b)

/-- Each fiber uses finitely many native collapses when the original diagram
has finitely many objects and arrows. -/
theorem finite_native_sources [Finite B] (h : ∀ a b : B, Finite (a ⟶ b)) (b : B) :
    Finite (slice (sourceDiagram L) b) :=
  finite_sources (sourceDiagram L) h b

private def changeSource {b c : B} (f : b ⟶ c) :
    (keep L b).FullSubcategory ⥤ (keep L c).FullSubcategory :=
  (keep L c).lift ((keep L b).ι ⋙ transportResolution (L.map f)) (fun A ↦
    transport_source L f A.obj.base A.property)

private theorem changeSource_id (b : B) : changeSource L (𝟙 b) = 𝟭 _ := by
  apply inclusion_cancel (keep L b)
  change (keep L b).ι ⋙ transportResolution (L.map (𝟙 b)) = (keep L b).ι
  rw [L.map_id, JTGraphVariableTimeTransport.transportResolution_id]
  rfl

private theorem changeSource_comp {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    changeSource L (f ≫ g) = changeSource L f ⋙ changeSource L g := by
  apply inclusion_cancel (keep L d)
  change (keep L b).ι ⋙ transportResolution (L.map (f ≫ g)) =
    (keep L b).ι ⋙ transportResolution (L.map f) ⋙ transportResolution (L.map g)
  rw [L.map_comp, JTGraphVariableTimeTransport.transportResolution_comp]

/-- Retain only collapses occurring in the diagram while allowing all exact
time families and internal cylinder necklaces over those collapses. -/
def diagram : B ⥤ Cat.{0, 0} where
  obj b := Cat.of (keep L b).FullSubcategory
  map f := (changeSource L f).toCatHom
  map_id b := Cat.Hom.ext (changeSource_id L b)
  map_comp f g := Cat.Hom.ext (changeSource_comp L f g)

private def diagramInclusion : diagram L ⟶ L ⋙ resolutionDiagram Q where
  app b := (keep L b).ι.toCatHom
  naturality _ _ _ := rfl

/-- The inclusion acts by the literal original operators. -/
abbrev inclusion : Grothendieck (diagram L) ⥤ Grothendieck (L ⋙ resolutionDiagram Q) :=
  Grothendieck.map (diagramInclusion L)

/-- The restriction is still a Kan weak cover of the diagram. -/
theorem projection_weak : WeakEquivalence (nerveMap (Grothendieck.forget (diagram L))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun b ↦
    fullResolution_point_GW (L.obj b) (sources (sourceDiagram L) b) (slice_point_GW _ b))

/-- The restricted cover includes in the full cover by a Kan weak equivalence. -/
theorem inclusion_weak : WeakEquivalence (nerveMap (inclusion L)) := by
  letI : WeakEquivalence (nerveMap (Grothendieck.forget (diagram L))) := projection_weak L
  let p := nerveMap (Grothendieck.forget (L ⋙ resolutionDiagram Q))
  letI : WeakEquivalence p := JTGraphVariableResolutionCategory.projection_weak_of L
  apply (weakEquivalence_postcomp_iff (nerveMap (inclusion L)) p).mp
  change WeakEquivalence (nerveMap (inclusion L ⋙ Grothendieck.forget (L ⋙ resolutionDiagram Q)))
  exact projection_weak L

end
end DaggerModels.PartII.FiniteSourceSlice

