import DaggerModelsPartII.JTGraphParameterTimeResolution
import DaggerModelsPartII.JTGraphTransportRestriction
import DaggerModelsPartII.JTGraphCylinderSpanProjection
import DaggerModelsPartII.TotalElementsWeakComparison
import Mathlib.CategoryTheory.Functor.Hom

/-! Graph parameter families over all exact original arrow factorizations.

The restriction and transport use the original graph lifts. Their commutation
is `JTGraphTransportRestriction.transport_restrict`; composition uses
`JTGraphLiftRestriction.restrict_comp` and `GraphLift.transport_comp`.
The Grothendieck projection uses the existing simplex resolution and
`GrothendieckContractibleFibers.projection_weak`.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphArrowParameterDiagram

open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphParameterTimeResolution JTHomotopyTargetTimeResolution
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- The literal arrow and both original factorization operators. -/
abbrev ArrowIndex := (Functor.hom (TargetComma Q)).Elements

private abbrev native : TargetComma Q ⥤ NecklaceCode :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

private abbrev collapse (a : ArrowIndex Q) := (native Q).map a.snd

variable {Q}

private theorem factor {a b : ArrowIndex Q} (f : a ⟶ b) :
    (native Q).map f.val.1.unop ≫ collapse Q a ≫ (native Q).map f.val.2 =
      collapse Q b := by
  rw [← (native Q).map_comp, ← (native Q).map_comp]
  exact congrArg (native Q).map f.property

private def mapLift {a b : ArrowIndex Q} (f : a ⟶ b)
    (D : Lifts a.fst.2 (collapse Q a)) : Lifts b.fst.2 (collapse Q b) :=
  ⟨restrict (D.val.transport f.val.2.left) ((native Q).map f.val.1.unop), by
    change (native Q).map f.val.1.unop ≫ D.val.collapse ≫ (native Q).map f.val.2 =
      collapse Q b
    rw [D.property]
    exact factor f⟩

private theorem mapLift_id (a : ArrowIndex Q) (D : Lifts a.fst.2 (collapse Q a)) :
    mapLift (𝟙 a) D = D := by
  apply Subtype.ext
  change restrict (D.val.transport (𝟙 _)) ((native Q).map (𝟙 _)) = D.val
  rw [GraphLift.transport_id, (native Q).map_id, restrict_id]

private theorem mapLift_comp {a b d : ArrowIndex Q} (f : a ⟶ b) (g : b ⟶ d)
    (D : Lifts a.fst.2 (collapse Q a)) :
    mapLift (f ≫ g) D = mapLift g (mapLift f D) := by
  apply Subtype.ext
  change restrict (D.val.transport (f.val.2.left ≫ g.val.2.left))
      ((native Q).map (g.val.1.unop ≫ f.val.1.unop)) =
    restrict ((restrict (D.val.transport f.val.2.left)
      ((native Q).map f.val.1.unop)).transport g.val.2.left) ((native Q).map g.val.1.unop)
  rw [JTGraphTransportRestriction.transport_restrict (D.val.transport f.val.2.left)
    ((native Q).map f.val.1.unop) g.val.2, restrict_comp, GraphLift.transport_comp, Functor.map_comp]

variable (Q)

private def timeMap {a b : ArrowIndex Q} (f : a ⟶ b) :
    timeSpace a.fst.2 (collapse Q a) ⟶ timeSpace b.fst.2 (collapse Q b) where
  app _ D i := mapLift f (D i)
  naturality := by intros; rfl

/-- Native precomposition and original target transport act simultaneously
on every time simplex of exact parameters. -/
def diagram : ArrowIndex Q ⥤ SSet.{0} where
  obj a := timeSpace a.fst.2 (collapse Q a)
  map f := timeMap Q f
  map_id a := by
    apply NatTrans.ext
    funext n D i
    exact mapLift_id a (D i)
  map_comp f g := by
    apply NatTrans.ext
    funext n D i
    exact mapLift_comp f g (D i)

/-- Every original arrow has an exact graph lift, obtained by restricting an
identity-collapse lift at its target to its actual native source. -/
theorem lifts_nonempty (a : ArrowIndex Q) : Nonempty (Lifts a.fst.2 (collapse Q a)) := by
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift a.fst.2.left
  refine ⟨⟨restrict E (collapse Q a), ?_⟩⟩
  change collapse Q a ≫ E.collapse = collapse Q a
  rw [hE]
  exact Category.comp_id _

/-- The space of exact time families over each original arrow is weakly contractible. -/
theorem time_point_GW (a : ArrowIndex Q) : GW (pointMap ((diagram Q).obj a)) :=
  (point_GW_iff _ _).mp
    (resolution_point_GW a.fst.2 (collapse Q a) (lifts_nonempty Q a).some)


/-- All time simplices of exact graph parameters over the original arrows. -/
abbrev timeSimplices := diagram Q ⋙ SimplicialResolutionFunctor.elementsOpposite

/-- The full time-simplex category over each original arrow has weakly contractible nerve. -/
theorem timeSimplices_point_GW (a : ArrowIndex Q) :
    GW (pointMap (nerve ((timeSimplices Q).obj a))) := by
  let X := (diagram Q).obj a
  let T := (native Q).obj a.fst.1.unop
  let F := BoundaryNecklaceComma.fiberDiagram (degree X ⋙ JTNecklaceEndpointCylinder.under T)
  let p := nerveMap (Grothendieck.forget F)
  have : WeakEquivalence p := forget_weak T X
  let t := pointMap (nerve X.Elementsᵒᵖ)
  have h : p ≫ t = pointMap (nerve (TimeResolution T X)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence t
  apply (weakEquivalence_precomp_iff p t).mp
  rw [h]
  exact (weakEquivalence_iff_GW _).mpr
    (resolution_point_GW a.fst.2 (collapse Q a) (lifts_nonempty Q a).some)

/-- The assembled category of exact parameter simplices has the weak homotopy
type of the original arrow-factorization index. -/
theorem projection_weak : WeakEquivalence (nerveMap (Grothendieck.forget (timeSimplices Q))) :=
  GrothendieckContractibleFibers.projection_weak _ (timeSimplices_point_GW Q)


private abbrev sourceProjection : ArrowIndex Q ⥤ (TargetComma Q)ᵒᵖ :=
  CategoryOfElements.π (Functor.hom (TargetComma Q)) ⋙
    CategoryTheory.Prod.fst (TargetComma Q)ᵒᵖ (TargetComma Q)

private abbrev forgetToSource :=
  Grothendieck.forget (timeSimplices Q) ⋙ sourceProjection Q

/-- On reversing the factorization directions, each exact parameter family
has the original source object and all its original source arrows. -/
def toOriginal : (Grothendieck (timeSimplices Q))ᵒᵖ ⥤ TargetComma Q :=
  (forgetToSource Q).op ⋙ unopUnop (TargetComma Q)

/-- The total category with every exact parameter family compares weakly to
the original fixed-target comma. -/
theorem toOriginal_weak : WeakEquivalence (nerveMap (toOriginal Q)) := by
  have : WeakEquivalence (nerveMap (Grothendieck.forget (timeSimplices Q))) :=
    projection_weak Q
  have : WeakEquivalence (nerveMap (sourceProjection Q)) :=
    JTGraphCylinderSpanProjection.homElements_source_weak (TargetComma Q)
  have h : WeakEquivalence (nerveMap (forgetToSource Q)) := by
    change WeakEquivalence (nerveMap (Grothendieck.forget (timeSimplices Q)) ≫
      nerveMap (sourceProjection Q))
    infer_instance
  have : WeakEquivalence (nerveMap (forgetToSource Q).op) :=
    (TotalElementsWeakComparison.nerveMap_op_iff _).mpr h
  have : WeakEquivalence (nerveMap (unopUnop (TargetComma Q))) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (nerveMap (forgetToSource Q).op ≫
    nerveMap (unopUnop (TargetComma Q)))
  infer_instance

/-- Weak contractibility can be proved on all compatible original
factorizations with their exact higher parameter data. -/
theorem targetComma_point_iff :
    GW (pointMap (nerve (Grothendieck (timeSimplices Q))ᵒᵖ)) ↔
      GW (pointMap (nerve (TargetComma Q))) := by
  let f := nerveMap (toOriginal Q)
  have : WeakEquivalence f := toOriginal_weak Q
  have h : f ≫ pointMap (nerve (TargetComma Q)) =
      pointMap (nerve (Grothendieck (timeSimplices Q))ᵒᵖ) := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← h]
  exact weakEquivalence_precomp_iff f _

end

end DaggerModels.PartII.JTGraphArrowParameterDiagram
