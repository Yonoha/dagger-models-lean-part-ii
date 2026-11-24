import DaggerModelsPartII.JTEndpointGraphCoefficientSlice
import DaggerModelsPartII.JTEndpointRowGraphNormalization
import DaggerModelsPartII.JTCommonCoefficientExtensionDiagram
import DaggerModelsPartII.SemiSimplexPairedBoundary
import DaggerModelsPartII.SemiSimplexBoundaryComparison
import DaggerModelsPartII.TotalElementsWeakComparison

/-! Exact common-coefficient endpoint extensions over all mixed arrows to one graph. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen Prod

namespace DaggerModels.PartII.JTEndpointGraphCoefficientChoices

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointRowGraphOperators JTEndpointRowGraphNormalization JTEndpointGraphCoefficientSlice
open JTEndpointNormalizationLifts SemiSimplexBoundaryLifting

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (m : SimplexCategory) := std.obj m
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev leftVertex (A : Over P) := vertexAt A.left.unop 0
private abbrev rightVertex (A : Over P) := vertexAt A.left.unop
  (Fin.last (horizontalDegree A.left.unop).len)

private theorem leftVertex_naturality {A B : Over P} (f : A ⟶ B) :
    leftVertex P A ≫ std.map ((coefficients P).map f).left = leftVertex P B :=
  leftVertex_map f.left.unop

private theorem rightVertex_naturality {A B : Over P} (f : A ⟶ B) :
    rightVertex P A ≫ std.map ((coefficients P).map f).left = rightVertex P B :=
  rightVertex_map f.left.unop

/-- The original left endpoint base on a mixed graph. -/
abbrev leftBase (A : MixedGraphs q) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (term (Δ (coefficientDegree.obj A)) ≫ vertexPoint W x)
    (graphCoefficient A.unop ≫ rowVertex W (horizontalDegree A.unop) 0)

/-- The original right endpoint base on a mixed graph. -/
abbrev rightBase (A : MixedGraphs q) (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (graphCoefficient A.unop ≫ rowVertex W (horizontalDegree A.unop)
    (Fin.last (horizontalDegree A.unop).len))
    (term (Δ (coefficientDegree.obj A)) ≫ vertexPoint W y)

private theorem leftBase_factor (A : Over P) :
    std.map ((coefficients P).obj A).hom ≫ leftBase P x = leftBase A.left x :=
  leftBase_map (x := x) A.hom.unop

private theorem rightBase_factor (A : Over P) :
    std.map ((coefficients P).obj A).hom ≫ rightBase P y = rightBase A.left y :=
  rightBase_map (y := y) A.hom.unop

/-- The left square of each child uses the same parent endpoint base. -/
def leftSquare (A : Over P) :
    CommSq (vertexPoint W x ≫ identityFamily W) (leftVertex P A) (endpointArrow W)
      (std.map ((coefficients P).obj A).hom ≫ leftBase P x) := by
  rw [leftBase_factor]
  exact leftAt hx A.left.unop

/-- The right square of each child uses the same parent endpoint base. -/
def rightSquare (A : Over P) :
    CommSq (vertexPoint W y ≫ identityFamily W) (rightVertex P A) (endpointArrow W)
      (std.map ((coefficients P).obj A).hom ≫ rightBase P y) := by
  rw [rightBase_factor]
  exact rightAt hy A.left.unop

private abbrev leftDegree :=
  JTCommonCoefficientExtensionDiagram.degreeDiagram (coefficients P)
    (leftVertex P) (leftVertex_naturality P) (leftSquare P hx)

private abbrev rightDegree :=
  JTCommonCoefficientExtensionDiagram.degreeDiagram (coefficients P)
    (rightVertex P) (rightVertex_naturality P) (rightSquare P hy)

/-- All pairs of enlarged endpoint maps, with the original exact arrows to the parent. -/
abbrev choices :=
  ((leftDegree P hx).prod' (rightDegree P hy)) ⋙ pairedChoiceFunctor

private abbrev leftOriginal :=
  JTCommonCoefficientExtensionDiagram.originalSpaces (coefficients P)
    (leftVertex P) (leftVertex_naturality P) (leftSquare P hx)

private abbrev rightOriginal :=
  JTCommonCoefficientExtensionDiagram.originalSpaces (coefficients P)
    (rightVertex P) (rightVertex_naturality P) (rightSquare P hy)

private abbrev original := ((leftOriginal P hx).prod' (rightOriginal P hy)) ⋙ simplicialProduct

private abbrev leftForget :=
  JTCommonCoefficientExtensionDiagram.degreeForget (coefficients P)
    (leftVertex P) (leftVertex_naturality P) (leftSquare P hx)

private abbrev rightForget :=
  JTCommonCoefficientExtensionDiagram.degreeForget (coefficients P)
    (rightVertex P) (rightVertex_naturality P) (rightSquare P hy)

private abbrev time := SemiSimplexCategory.toSimplexCategory

/-- Forget the enlarged maps by restricting to the actual coefficient-time prisms. -/
def forget : choices P hx hy ⟶
    original P hx hy ⋙ (Functor.whiskeringLeft _ _ _).obj time.op where
  app A := pairedForget ((leftForget P hx).app A) ((rightForget P hy).app A)
  naturality {A B} f := by
    change pairedChoiceFunctor.map ((leftDegree P hx).map f ×ₘ (rightDegree P hy).map f) ≫
        pairedForget ((leftForget P hx).app B) ((rightForget P hy).app B) =
      pairedForget ((leftForget P hx).app A) ((rightForget P hy).app A) ≫
        Functor.whiskerLeft time.op
          (simplicialProduct.map ((leftOriginal P hx).map f ×ₘ (rightOriginal P hy).map f))
    rw [simplicialProduct_map]
    exact pairedForget_natural _ _ _ _ _ _
      ((leftForget P hx).naturality f) ((rightForget P hy).naturality f)

/-- Restriction admits a lift with any prescribed compatible time boundary. -/
theorem forget_boundaryLifting
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (A : Over P) : HasBoundaryLifting ((forget P hx hy).app (op A)) := by
  letI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  apply hasBoundaryLifting_paired
  · change HasBoundaryLifting ((leftForget P hx).app (op A))
    rw [JTCommonCoefficientExtensionDiagram.degreeForget_fixed]
    exact (JTCommonCoefficientNormalization.hasBoundaryLifting (leftSquare P hx A)).precompIso _
  · change HasBoundaryLifting ((rightForget P hy).app (op A))
    rw [JTCommonCoefficientExtensionDiagram.degreeForget_fixed]
    exact (JTCommonCoefficientNormalization.hasBoundaryLifting (rightSquare P hy A)).precompIso _

private theorem fiber_eq {A B X Y : SSet.{0}} {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}
    {b c : B ⟶ Y} (h : b = c) (sq : CommSq t i p b) (sq' : CommSq t i p c) :
    (SSet.ihomToPullbackFiber sq : SSet.{0}) = SSet.ihomToPullbackFiber sq' := by
  subst c
  rfl

/-- The original target of the forgetful map is the child's literal normalization space. -/
theorem original_obj (A : Over P) :
    (original P hx hy).obj (op A) = (spaces hx hy).obj A.left.unop :=
  congrArg₂ (fun X Y : SSet.{0} ↦ X ⨯ Y)
    (fiber_eq (leftBase_factor P (x := x) A) (leftSquare P hx A) (leftAt hx A.left.unop))
    (fiber_eq (rightBase_factor P (y := y) A) (rightSquare P hy A) (rightAt hy A.left.unop))

/-- The labeled coefficient maps and all injective times. -/
abbrev Index := (GrothendieckTotalElements.totalDiagram (choices P hx hy)).Elementsᵒᵖ

/-- Retain the actual mixed over-category arrow. -/
abbrev base : Index P hx hy ⥤ Over P :=
  (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (choices P hx hy)) ⋙
    CategoryTheory.Prod.fst _ _).leftOp

/-- Retain the actual injective time arrow. -/
abbrev semiTime : Index P hx hy ⥤ SemiSimplexCategory :=
  (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (choices P hx hy)) ⋙
    CategoryTheory.Prod.snd _ _).leftOp

/-- The full ordered parameter of the chosen enlarged endpoint families. -/
abbrev enlarged : Index P hx hy ⥤ SimplexCategory :=
  ((base P hx hy ⋙ coefficients P).prod' (semiTime P hx hy)) ⋙
    JTCommonCoefficientParameter.parameter (coefficientDegree.obj P)

abbrev leftChoice (U : Index P hx hy) :
    JTCommonCoefficientLiftChoices.Extension (leftSquare P hx ((base P hx hy).obj U))
      (time.obj ((semiTime P hx hy).obj U)) :=
  U.unop.snd.1

abbrev rightChoice (U : Index P hx hy) :
    JTCommonCoefficientLiftChoices.Extension (rightSquare P hy ((base P hx hy).obj U))
      (time.obj ((semiTime P hx hy).obj U)) :=
  U.unop.snd.2

/-- Both entire families reindex along the actual enlarged parameter map. -/
theorem choice_maps {U V : Index P hx hy} (f : U ⟶ V) :
    (leftChoice P hx hy U).map = std.map ((enlarged P hx hy).map f) ≫
      (leftChoice P hx hy V).map ∧
    (rightChoice P hx hy U).map = std.map ((enlarged P hx hy).map f) ≫
      (rightChoice P hx hy V).map := by
  let u : ((base P hx hy).obj U, (semiTime P hx hy).obj U) ⟶
      ((base P hx hy).obj V, (semiTime P hx hy).obj V) :=
    ((base P hx hy).map f, (semiTime P hx hy).map f)
  have hL := JTCommonCoefficientExtensionDiagram.degreeDiagram_uncurry_map (coefficients P)
    (leftVertex P) (leftVertex_naturality P) (leftSquare P hx) u (leftChoice P hx hy V)
  have hR := JTCommonCoefficientExtensionDiagram.degreeDiagram_uncurry_map (coefficients P)
    (rightVertex P) (rightVertex_naturality P) (rightSquare P hy) u (rightChoice P hx hy V)
  constructor
  · exact (congrArg (fun E ↦ (JTCommonCoefficientLiftChoices.Extension.map E.1))
      f.unop.property).symm.trans hL
  · exact (congrArg (fun E ↦ (JTCommonCoefficientLiftChoices.Extension.map E.2))
      f.unop.property).symm.trans hR

/-- Lift an actual graph and time operator from the two full endpoint equations. -/
def homOfChoiceMaps {U V : Index P hx hy}
    (u : ((base P hx hy).obj U, (semiTime P hx hy).obj U) ⟶
      ((base P hx hy).obj V, (semiTime P hx hy).obj V))
    (hL : (leftChoice P hx hy U).map = std.map
      (JTCommonCoefficientParameter.map ((coefficients P).map u.1).left
        (Over.w ((coefficients P).map u.1)) (time.map u.2)
          (SemiSimplexCategory.homEquiv u.2).injective) ≫ (leftChoice P hx hy V).map)
    (hR : (rightChoice P hx hy U).map = std.map
      (JTCommonCoefficientParameter.map ((coefficients P).map u.1).left
        (Over.w ((coefficients P).map u.1)) (time.map u.2)
          (SemiSimplexCategory.homEquiv u.2).injective) ≫ (rightChoice P hx hy V).map) :
    U ⟶ V :=
  Quiver.Hom.op ⟨(prodOpEquiv (C := Over P) (D := SemiSimplexCategory)).functor.map u.op, by
    apply Prod.ext <;> apply JTCommonCoefficientLiftChoices.Extension.ext
    · exact (JTCommonCoefficientExtensionDiagram.degreeDiagram_uncurry_map (coefficients P)
        (leftVertex P) (leftVertex_naturality P) (leftSquare P hx) u
        (leftChoice P hx hy V)).trans hL.symm
    · exact (JTCommonCoefficientExtensionDiagram.degreeDiagram_uncurry_map (coefficients P)
        (rightVertex P) (rightVertex_naturality P) (rightSquare P hy) u
        (rightChoice P hx hy V)).trans hR.symm⟩

private abbrev choiceElements := GrothendieckTotalElements.elementDiagram (choices P hx hy)
private abbrev originalElements := original P hx hy ⋙ Functor.elementsFunctor

private def forgetElements : choiceElements P hx hy ⟶ originalElements P hx hy :=
  Functor.whiskerRight (forget P hx hy) Functor.elementsFunctor ≫
    Functor.whiskerLeft (original P hx hy) JTSemiSimplexElementsWeak.elementForgetUnopNat

/-- The full enlargement over the slice has weakly contractible nerve. -/
theorem index_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (Index P hx hy))) := by
  let A := choices P hx hy
  let B := original P hx hy
  let β := forgetElements P hx hy
  have hb : GW (pointMap (nerve (Over P)ᵒᵖ)) :=
    (SynchronizedSimplicialParameters.point_op_iff _).2
      (DaggerNativeOverNerveWeakContractibility.point_GW P)
  have hB (X : (Over P)ᵒᵖ) : GW (pointMap (B.obj X)) := by
    change GW (pointMap ((original P hx hy).obj (op X.unop)))
    rw [original_obj]
    exact spaces_point_GW hx hy hW X.unop.left.unop
  let E := (GrothendieckTotalElements.equivalence B).functor.op
  letI : WeakEquivalence (nerveMap E) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence E
  letI : WeakEquivalence (pointMap (nerve (GrothendieckTotalElements.totalDiagram B).Elementsᵒᵖ)) :=
    (weakEquivalence_iff_GW _).mpr (SynchronizedSimplicialParameters.index_point_GW_of B hb hB)
  have hG : GW (pointMap (nerve (Grothendieck (originalElements P hx hy))ᵒᵖ)) := by
    change GW (pointMap (nerve (Grothendieck (GrothendieckTotalElements.elementDiagram B))ᵒᵖ))
    rw [← pointIsTerminal.hom_ext (nerveMap E ≫ pointMap _) (pointMap _)]
    exact (weakEquivalence_iff_GW _).mp inferInstance
  letI : WeakEquivalence (pointMap (nerve (Grothendieck (originalElements P hx hy)))) :=
    (weakEquivalence_iff_GW _).mpr ((SynchronizedSimplicialParameters.point_op_iff _).mp hG)
  have hβ (X : (Over P)ᵒᵖ) : WeakEquivalence (nerveMap (β.app X).toFunctor) := by
    apply (TotalElementsWeakComparison.nerveMap_op_iff ((β.app X).toFunctor)).mp
    change WeakEquivalence (nerveMap (toFullElements ((forget P hx hy).app (op X.unop))))
    exact (weakEquivalence_iff_GW _).mpr
      (toFullElements_weak (forget_boundaryLifting P hx hy hW X.unop))
  letI : WeakEquivalence (nerveMap (Grothendieck.map β)) :=
    GrothendieckNerveMapWeak.map_weak β hβ
  have hA : GW (pointMap (nerve (Grothendieck (choiceElements P hx hy)))) := by
    rw [← pointIsTerminal.hom_ext (nerveMap (Grothendieck.map β) ≫ pointMap _) (pointMap _)]
    exact (weakEquivalence_iff_GW _).mp inferInstance
  let e := (GrothendieckTotalElements.equivalence A).inverse.op
  letI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  letI : WeakEquivalence (pointMap (nerve (Grothendieck (choiceElements P hx hy))ᵒᵖ)) :=
    (weakEquivalence_iff_GW _).mpr ((SynchronizedSimplicialParameters.point_op_iff _).2 hA)
  rw [← pointIsTerminal.hom_ext (nerveMap e ≫ pointMap _) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTEndpointGraphCoefficientChoices
