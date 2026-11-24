import DaggerModelsPartII.JTCommonCoefficientExtensionDiagram
import DaggerModelsPartII.JTRowGraphCommonCenter
import DaggerModelsPartII.JTRowGraphNormalizationDiagram
import DaggerModelsPartII.JTCommonCoefficientNormalization
import DaggerModelsPartII.SemiSimplexPairedBoundary
import DaggerModelsPartII.JTHigherCommonMixedGraphFamilies
import DaggerModelsPartII.OrderedLabelElements
import DaggerModelsPartII.DecoratedCylinderNecklacePresentation
import DaggerModelsPartII.JTNormalizedGraphTargetArrow
import DaggerModelsPartII.JTCommonCoefficientBeadLift

/-! Both original endpoint extension diagrams over the one canonical graph
coefficient base of a fixed raw simplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphFiber JTRowGraphNormalizationDiagram JTMixedGraphEndpointLifts
open JTOrdinaryGraphNormalizationSpace JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev simplex (k : SimplexCategory) := std.obj k
private abbrev one := (Δ[0] : SSet.{0})
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable (q : simplex ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W))
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev C := center q
private abbrev S (G : Fiber q) := (supportAt q).obj G
private abbrev c (G : Fiber q) := ((JTRowGraphCommonCenter.diagram q).obj G).hom

private theorem coefficient_along {G H : Fiber q} (u : G ⟶ H) :
    SSet.stdSimplex.map u.hom.operator ≫ coefficient H = coefficient G := by
  rw [← SSet.yonedaEquiv_symm_map]
  exact congrArg SSet.yonedaEquiv.symm u.hom.coefficient

private theorem restrict_coefficient (G : Fiber q) :
    std.map (c q G) ≫ coefficient (C q) = coefficient (S q G) :=
  coefficient_along q ((reductionAt q).app G)

private abbrev corner (j : Fin (d + 1)) (G : Fiber q) : one ⟶ simplex (S q G).obj.degree :=
  vertex (S q G).obj.degree (graphIndex ⦋d⦌ (S q G).obj.degree (S q G).obj.parameter j)

private theorem corner_natural (j : Fin (d + 1)) {G H : Fiber q} (u : G ⟶ H) :
    corner q j G ≫ std.map ((JTRowGraphCommonCenter.diagram q).map u).left = corner q j H := by
  let f := ((supportAt q).map u).hom
  have h : graphIndex ⦋d⦌ (S q H).obj.degree (S q H).obj.parameter j =
      f.operator.toOrderHom (graphIndex ⦋d⦌ (S q G).obj.degree (S q G).obj.parameter j) :=
    (congrArg (fun s ↦ graphIndex ⦋d⦌ (S q H).obj.degree s j) f.parameter).symm.trans
      (JTMixedGraphEdgeFamilyReindex.graphIndex_reindex f.operator (S q G).obj.parameter j)
  change vertex _ _ ≫ std.map f.operator = vertex _ _
  unfold vertex
  rw [← std.map_comp, SimplexCategory.const_comp, h]

private abbrev leftBase (q : simplex ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W))
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (term (simplex (C q).obj.degree) ≫ vertexPoint W x)
    (coefficient (C q) ≫ rowVertex W ⦋d⦌ 0)

private abbrev rightBase (q : simplex ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W))
    (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (coefficient (C q) ≫ rowVertex W ⦋d⦌ (Fin.last d))
    (term (simplex (C q).obj.degree) ≫ vertexPoint W y)

private theorem left_base_eq (G : Fiber q) :
    std.map (c q G) ≫ leftBase q x =
      prod.lift (term (simplex (S q G).obj.degree) ≫ vertexPoint W x)
        (coefficient (S q G) ≫ rowVertex W ⦋d⦌ 0) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ vertexPoint W x) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  · simp only [Category.assoc, prod.lift_snd]
    rw [← Category.assoc, restrict_coefficient]

private theorem right_base_eq (G : Fiber q) :
    std.map (c q G) ≫ rightBase q y =
      prod.lift (coefficient (S q G) ≫ rowVertex W ⦋d⦌ (Fin.last d))
        (term (simplex (S q G).obj.degree) ≫ vertexPoint W y) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    rw [← Category.assoc, restrict_coefficient]
  · simp only [Category.assoc, prod.lift_snd]
    rw [← Category.assoc]
    exact congrArg (· ≫ vertexPoint W y) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private def leftSq (G : Fiber q) :
    CommSq (vertexPoint W x ≫ identityFamily W) (corner q 0 G)
      (endpointArrow W) (std.map (c q G) ≫ leftBase q x) := by
  rw [left_base_eq]
  exact leftSquare W ⦋d⦌ (S q G).obj.degree (coefficient (S q G)) (S q G).obj.parameter x
    (leftEndpoint hx (S q G))

private def rightSq (G : Fiber q) :
    CommSq (vertexPoint W y ≫ identityFamily W) (corner q (Fin.last d) G)
      (endpointArrow W) (std.map (c q G) ≫ rightBase q y) := by
  rw [right_base_eq]
  exact rightSquare W ⦋d⦌ (S q G).obj.degree (coefficient (S q G)) (S q G).obj.parameter y
    (rightEndpoint hy (S q G))

/-- The exact left endpoint choices along all supported coefficient arrows and time faces. -/
def leftChoices : (Fiber q × SemiSimplexCategory)ᵒᵖ ⥤ Type :=
  JTCommonCoefficientExtensionDiagram.diagram (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

/-- The exact right endpoint choices along all supported coefficient arrows and time faces. -/
def rightChoices : (Fiber q × SemiSimplexCategory)ᵒᵖ ⥤ Type :=
  JTCommonCoefficientExtensionDiagram.diagram (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

/-- The original left normalization spaces in each supported coefficient and time degree. -/
def leftOriginal : (Fiber q × SemiSimplexCategory)ᵒᵖ ⥤ Type :=
  JTCommonCoefficientExtensionDiagram.original (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

/-- The original right normalization spaces in each supported coefficient and time degree. -/
def rightOriginal : (Fiber q × SemiSimplexCategory)ᵒᵖ ⥤ Type :=
  JTCommonCoefficientExtensionDiagram.original (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

/-- Forget the left enlargement along all original coefficient and injective time arrows. -/
def leftForget : leftChoices q hx ⟶ leftOriginal q hx :=
  JTCommonCoefficientExtensionDiagram.forget (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

/-- Forget the right enlargement along all original coefficient and injective time arrows. -/
def rightForget : rightChoices q hy ⟶ rightOriginal q hy :=
  JTCommonCoefficientExtensionDiagram.forget (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

section Paired

open SemiSimplexBoundaryLifting
open JTCommonCoefficientNormalization

variable (G : Fiber q)

private abbrev leftFiber := (SSet.ihomToPullbackFiber (leftSq q hx G) : SSet.{0})
private abbrev rightFiber := (SSet.ihomToPullbackFiber (rightSq q hy G) : SSet.{0})

private theorem fiber_eq {A B X Y : SSet.{0}} {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}
    {b b' : B ⟶ Y} (h : b = b') (sq : CommSq t i p b) (sq' : CommSq t i p b') :
    (SSet.ihomToPullbackFiber sq : SSet.{0}) = SSet.ihomToPullbackFiber sq' := by
  subst b'
  rfl

private theorem pairedSpace_eq :
    Limits.prod (C := SSet.{0}) (leftFiber q hx G) (rightFiber q hy G) =
      (JTRowGraphNormalizationDiagram.diagram hx hy).obj (op (S q G)) := by
  change _ = space W ⦋d⦌ (S q G).obj.degree (coefficient (S q G)) (S q G).obj.parameter
    x y (leftEndpoint hx (S q G)) (rightEndpoint hy (S q G))
  unfold space leftSpace rightSpace
  exact congrArg₂ (fun A B : SSet.{0} ↦ A ⨯ B)
    (fiber_eq (left_base_eq q (x := x) G) _ _)
    (fiber_eq (right_base_eq q (y := y) G) _ _)

/-- The paired enlarged choices at one supported graph, with the two original boundaries. -/
def pairedNormalizationChoices : SemiSimplexCategoryᵒᵖ ⥤ Type :=
  pairedChoices (choices (leftSq q hx G)) (choices (rightSq q hy G))

/-- At a supported graph both enlarged choices forget to its original
ordered product of normalization spaces. -/
def pairedNormalizationForget :
    pairedNormalizationChoices q hx hy G ⟶
      SemiSimplexCategory.toSimplexCategory.op ⋙
        (JTRowGraphNormalizationDiagram.diagram hx hy).obj (op (S q G)) :=
  pairedForget (JTCommonCoefficientNormalization.forget (leftSq q hx G))
    (JTCommonCoefficientNormalization.forget (rightSq q hy G)) ≫
      Functor.whiskerLeft _ (eqToHom (pairedSpace_eq q hx hy G))

private theorem boundaryLifting_post_eq {E : SemiSimplexCategoryᵒᵖ ⥤ Type} {X Y : SSet.{0}}
    (h : X = Y) (α : E ⟶ SemiSimplexCategory.toSimplexCategory.op ⋙ X)
    (hα : HasBoundaryLifting α) :
    HasBoundaryLifting (α ≫ Functor.whiskerLeft _ (eqToHom h)) := by
  subst Y
  simpa using hα

/-- Any compatible family of both prescribed endpoint faces lifts over
the exact original product normalization simplex at this supported graph. -/
theorem pairedNormalization_boundaryLifting
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    HasBoundaryLifting (pairedNormalizationForget q hx hy G) := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  apply boundaryLifting_post_eq
  exact hasBoundaryLifting_paired _ _ (hasBoundaryLifting _) (hasBoundaryLifting _)

private abbrev leftSpaces :=
  JTCommonCoefficientExtensionDiagram.originalSpaces (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

private abbrev rightSpaces :=
  JTCommonCoefficientExtensionDiagram.originalSpaces (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

private abbrev supportedLeftSq (G : Fiber q) :=
  leftSquare W ⦋d⦌ (S q G).obj.degree (coefficient (S q G)) (S q G).obj.parameter x
    (leftEndpoint hx (S q G))

private abbrev supportedRightSq (G : Fiber q) :=
  rightSquare W ⦋d⦌ (S q G).obj.degree (coefficient (S q G)) (S q G).obj.parameter y
    (rightEndpoint hy (S q G))

private theorem fiber_eq_natural {A B B' X Y : SSet.{0}} {t : A ⟶ X}
    {i : A ⟶ B} {i' : A ⟶ B'} {p : X ⟶ Y}
    {b c : B ⟶ Y} {b' c' : B' ⟶ Y} (h : b = c) (h' : b' = c')
    (sq : CommSq t i p b) (sq' : CommSq t i' p b')
    (s : CommSq t i p c) (s' : CommSq t i' p c')
    (f : B ⟶ B') (hi : i ≫ f = i') (hb : f ≫ b' = b) (hc : f ≫ c' = c) :
    JTFixedLiftSpacePrecomp.precomp sq sq' f hi hb ≫ eqToHom (fiber_eq h sq s) =
      eqToHom (fiber_eq h' sq' s') ≫ JTFixedLiftSpacePrecomp.precomp s s' f hi hc := by
  subst c
  subst c'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem product_eqToHom {A B C D : SSet.{0}} (h : A = B) (h' : C = D) :
    eqToHom (congrArg₂ (fun P Q : SSet.{0} ↦ P ⨯ Q) h h') =
      prod.map (eqToHom h) (eqToHom h') := by
  subst B
  subst D
  simp only [eqToHom_refl, prod.map_id_id]

/-- The exact product of the supported coefficient normalization spaces. -/
def pairedOriginalSpaces : (Fiber q)ᵒᵖ ⥤ SSet.{0} :=
  (leftSpaces q hx).prod' (rightSpaces q hy) ⋙ simplicialProduct

/-- Comparing the common-base endpoint squares with the original graph
squares is natural in the original supported coefficient arrow. -/
def pairedOriginalIso : pairedOriginalSpaces q hx hy ≅
    (supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy :=
  NatIso.ofComponents (fun D ↦ eqToIso (pairedSpace_eq q hx hy D.unop)) (by
    intro D E u
    let v := (supportAt q).map u.unop
    have eL := fiber_eq_natural (left_base_eq q (x := x) E.unop)
      (left_base_eq q (x := x) D.unop)
      (leftSq q hx E.unop) (leftSq q hx D.unop)
      (supportedLeftSq q hx E.unop) (supportedLeftSq q hx D.unop)
      (std.map v.hom.operator) (corner_natural q 0 u.unop)
    have eR := fiber_eq_natural (right_base_eq q (y := y) E.unop)
      (right_base_eq q (y := y) D.unop)
      (rightSq q hy E.unop) (rightSq q hy D.unop)
      (supportedRightSq q hy E.unop) (supportedRightSq q hy D.unop)
      (std.map v.hom.operator) (corner_natural q (Fin.last d) u.unop)
    have hm : (pairedOriginalSpaces q hx hy).map u =
        prod.map ((leftSpaces q hx).map u) ((rightSpaces q hy).map u) :=
      simplicialProduct_map (show ((leftSpaces q hx).obj D, (rightSpaces q hy).obj D) ⟶
        ((leftSpaces q hx).obj E, (rightSpaces q hy).obj E) from
          ((leftSpaces q hx).map u, (rightSpaces q hy).map u))
    have hma : ((supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy).map u =
        prod.map (JTRowGraphNormalizationDiagram.leftMap hx v)
          (JTRowGraphNormalizationDiagram.rightMap hy v) := rfl
    have hest (P : Fiber q) : eqToHom (pairedSpace_eq q hx hy P) =
        prod.map (eqToHom (fiber_eq (left_base_eq q (x := x) P)
          (leftSq q hx P) (supportedLeftSq q hx P)))
          (eqToHom (fiber_eq (right_base_eq q (y := y) P)
            (rightSq q hy P) (supportedRightSq q hy P))) :=
      product_eqToHom _ _
    change (pairedOriginalSpaces q hx hy).map u ≫ eqToHom (pairedSpace_eq q hx hy E.unop) =
      eqToHom (pairedSpace_eq q hx hy D.unop) ≫
        ((supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy).map u
    rw [hm, hma, hest, hest, prod.map_map, prod.map_map]
    congr 1
    · have h := JTCommonCoefficientLiftChoices.base_precomp (g := leftBase q x)
        v.hom.operator (Over.w ((JTRowGraphCommonCenter.diagram q).map u.unop))
      exact eL h _
    · have h := JTCommonCoefficientLiftChoices.base_precomp (g := rightBase q y)
        v.hom.operator (Over.w ((JTRowGraphCommonCenter.diagram q).map u.unop))
      exact eR h _)

open JTCommonCoefficientExtensionDiagram

private abbrev leftDegrees :=
  degreeDiagram (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

private abbrev rightDegrees :=
  degreeDiagram (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

private abbrev leftDegreeForget :=
  degreeForget (JTRowGraphCommonCenter.diagram q)
    (corner q 0) (corner_natural q 0) (leftSq q hx)

private abbrev rightDegreeForget :=
  degreeForget (JTRowGraphCommonCenter.diagram q)
    (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy)

private abbrev restrictionFunctor : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory.op

/-- The paired enlarged choices retain both original directions of restriction. -/
def pairedDegreeDiagram : (Fiber q)ᵒᵖ ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (leftDegrees q hx).prod' (rightDegrees q hy) ⋙ pairedChoiceFunctor

private def pairedDegreeForgetPre :
    pairedDegreeDiagram q hx hy ⟶ pairedOriginalSpaces q hx hy ⋙ restrictionFunctor where
  app H := pairedForget ((leftDegreeForget q hx).app H) ((rightDegreeForget q hy).app H)
  naturality {D E} u := by
    have hm : (pairedOriginalSpaces q hx hy).map u =
        prod.map ((leftSpaces q hx).map u) ((rightSpaces q hy).map u) :=
      simplicialProduct_map (show ((leftSpaces q hx).obj D, (rightSpaces q hy).obj D) ⟶
        ((leftSpaces q hx).obj E, (rightSpaces q hy).obj E) from
          ((leftSpaces q hx).map u, (rightSpaces q hy).map u))
    have h := pairedForget_natural ((leftDegreeForget q hx).app D)
      ((rightDegreeForget q hy).app D) ((leftDegrees q hx).map u) ((rightDegrees q hy).map u)
      ((leftSpaces q hx).map u) ((rightSpaces q hy).map u)
      ((leftDegreeForget q hx).naturality u) ((rightDegreeForget q hy).naturality u)
    simpa only [← hm] using h

/-- Both endpoint enlargements forget naturally to the actual old
normalization diagram, keeping every original coefficient arrow. -/
def pairedDegreeForget :
    pairedDegreeDiagram q hx hy ⟶
      (supportAt q).op ⋙ JTRowGraphNormalizationDiagram.diagram hx hy ⋙ restrictionFunctor :=
  pairedDegreeForgetPre q hx hy ≫ Functor.whiskerRight (pairedOriginalIso q hx hy).hom _

/-- The paired mixed source restricts to the precise fixed-graph choices. -/
def pairedFixedIso :
    (pairedDegreeDiagram q hx hy).obj (op G) ≅ pairedNormalizationChoices q hx hy G :=
  pairedChoiceFunctor.mapIso
    ((fixedIso (JTRowGraphCommonCenter.diagram q) (corner q 0) (corner_natural q 0)
      (leftSq q hx) G).prod
     (fixedIso (JTRowGraphCommonCenter.diagram q) (corner q (Fin.last d))
      (corner_natural q (Fin.last d)) (rightSq q hy) G))

private theorem pairedDegreeForgetPre_app :
    (pairedDegreeForgetPre q hx hy).app (op G) =
      (pairedFixedIso q hx hy G).hom ≫
        pairedForget (JTCommonCoefficientNormalization.forget (leftSq q hx G))
          (JTCommonCoefficientNormalization.forget (rightSq q hy G)) := by
  let eL := fixedIso (JTRowGraphCommonCenter.diagram q) (corner q 0)
    (corner_natural q 0) (leftSq q hx) G
  let eR := fixedIso (JTRowGraphCommonCenter.diagram q) (corner q (Fin.last d))
    (corner_natural q (Fin.last d)) (rightSq q hy) G
  let αL := (leftDegreeForget q hx).app (op G)
  let αR := (rightDegreeForget q hy).app (op G)
  let βL := JTCommonCoefficientNormalization.forget (leftSq q hx G)
  let βR := JTCommonCoefficientNormalization.forget (rightSq q hy G)
  let inc := SemiSimplexCategory.toSimplexCategory.op
  have hL : eL.hom ≫ βL = αL ≫ Functor.whiskerLeft inc (𝟙 (leftFiber q hx G)) := by
    have he : Functor.whiskerLeft inc (𝟙 (leftFiber q hx G)) = 𝟙 _ :=
      restrictionFunctor.map_id _
    rw [he]
    exact (degreeForget_fixed (JTRowGraphCommonCenter.diagram q) (corner q 0)
      (corner_natural q 0) (leftSq q hx) G).symm.trans (Category.comp_id αL).symm
  have hR : eR.hom ≫ βR = αR ≫ Functor.whiskerLeft inc (𝟙 (rightFiber q hy G)) := by
    have he : Functor.whiskerLeft inc (𝟙 (rightFiber q hy G)) = 𝟙 _ :=
      restrictionFunctor.map_id _
    rw [he]
    exact (degreeForget_fixed (JTRowGraphCommonCenter.diagram q) (corner q (Fin.last d))
      (corner_natural q (Fin.last d)) (rightSq q hy) G).symm.trans (Category.comp_id αR).symm
  have h := pairedForget_natural αL αR eL.hom eR.hom
    (𝟙 (leftFiber q hx G)) (𝟙 (rightFiber q hy G)) hL hR
  let L := leftFiber q hx G
  let R := rightFiber q hy G
  have hp : prod.map (𝟙 L) (𝟙 R) = 𝟙 (L ⨯ R) :=
    prod.map_id_id (X := L) (Y := R)
  have he : Functor.whiskerLeft inc (prod.map (𝟙 L) (𝟙 R)) = 𝟙 _ :=
    (congrArg (fun f : L ⨯ R ⟶ L ⨯ R ↦ restrictionFunctor.map f) hp).trans
      (restrictionFunctor.map_id _)
  rw [he] at h
  exact (h.trans (Category.comp_id (pairedForget αL αR))).symm

/-- The mixed map on a coefficient fiber is the verified relative
boundary-lifting map with only the canonical source reindexing. -/
theorem pairedDegreeForget_app :
    (pairedDegreeForget q hx hy).app (op G) =
      (pairedFixedIso q hx hy G).hom ≫ pairedNormalizationForget q hx hy G := by
  rw [pairedDegreeForget, NatTrans.comp_app, pairedDegreeForgetPre_app, Category.assoc]
  rfl

end Paired

section Labels

open JTHigherCommonMixedGraphFamilies (commonChoiceFamilies
  commonChoiceFamilies_orderedPoint_reindex)
open JTHigherInterleavedParameter (common)
open JTCommonCoefficientLiftChoices (Extension)
open JTCommonCoefficientExtensionDiagram (degreeDiagram_uncurry_map)
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints

private abbrev ord := SemiSimplexCategory.toSimplexCategory
private abbrev labelRow :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (TripleBeadEndpointLabel.code d))

/-- The exact choices indexed simultaneously by a supported coefficient and
an injective time degree. -/
def mixedChoiceDiagram : (Fiber q)ᵒᵖ × SemiSimplexCategoryᵒᵖ ⥤ Type :=
  Functor.uncurry.obj (pairedDegreeDiagram q hx hy)

private abbrev parameterOp :=
  (prodOpEquiv (C := Fiber q) (D := SemiSimplexCategory)).inverse ⋙ (semisimplexParameter q).op

/-- The original three-bead ordered label of the two enlargement choices. -/
def choiceLabel (G : Fiber q) (N : SemiSimplexCategory)
    (E : (mixedChoiceDiagram q hx hy).obj (op G, op N)) :
    (labelRow (W := W) (x := x) (y := y) (d := d)).obj
      (op ((semisimplexParameter q).obj (G, N))) := by
  let L : Extension (leftSq q hx G) (ord.obj N) := E.1
  let R : Extension (rightSq q hy G) (ord.obj N) := E.2
  exact JTMixedGraphOrderedLabel.orderedPoint
    (commonChoiceFamilies (c q G) (ord.obj N) (coefficient (C q))
      (S q G).obj.parameter x y L R 0)

/-- The actual ordered labels preserve the entire coefficient and time map,
including time injections which move the initial vertex. -/
def choiceLabels :
    mixedChoiceDiagram q hx hy ⟶
      parameterOp q ⋙ labelRow (W := W) (x := x) (y := y) (d := d) where
  app P := choiceLabel q hx hy P.1.unop P.2.unop
  naturality {P P'} u := by
    funext E
    let G := P'.1.unop
    let H := P.1.unop
    let N := P'.2.unop
    let M := P.2.unop
    let v : (G, N) ⟶ (H, M) := ⟨u.1.unop, u.2.unop⟩
    let a := ((JTRowGraphCommonCenter.diagram q).map v.1).left
    let ha := Over.w ((JTRowGraphCommonCenter.diagram q).map v.1)
    let j := ord.map v.2
    let hj := (SemiSimplexCategory.homEquiv v.2).injective
    let E' := (mixedChoiceDiagram q hx hy).map u E
    have hL := degreeDiagram_uncurry_map (JTRowGraphCommonCenter.diagram q)
      (corner q 0) (corner_natural q 0) (leftSq q hx) v E.1
    have hR := degreeDiagram_uncurry_map (JTRowGraphCommonCenter.diagram q)
      (corner q (Fin.last d)) (corner_natural q (Fin.last d)) (rightSq q hy) v E.2
    exact commonChoiceFamilies_orderedPoint_reindex
      (c q G) (ord.obj N) (coefficient (C q)) (S q G).obj.parameter x y E'.1 E'.2
      (c q H) (S q H).obj.parameter E.1 E.2 a ha j hj 0 0 hL hR

private abbrev labelCode := TripleBeadEndpointLabel.code d

private def taggedParameter :
    (Fiber q)ᵒᵖ × SemiSimplexCategoryᵒᵖ ⥤
      (DaggerChosenRigidificationNecklace.NecklaceCode × SimplexCategory)ᵒᵖ :=
  parameterOp q ⋙ (((Functor.const SimplexCategory).obj (labelCode (d := d))).prod'
    (𝟭 SimplexCategory)).op

/-- The joint category of exact normalization choices evaluates to the
original decorated label index with both actual operator components. -/
def choiceLabelIndex :
    (mixedChoiceDiagram q hx hy).Elementsᵒᵖ ⥤
      OrderedLabelElements.Index W (boundaryPoint W x y) where
  obj P := op ⟨(taggedParameter q).obj P.unop.fst, (choiceLabels q hx hy).app _ P.unop.snd⟩
  map {P P'} u := Quiver.Hom.op ⟨(taggedParameter q).map u.unop.val, by
    let E := orderedNecklaceLabels W (boundaryPoint W x y)
    have h := ((NatTrans.mapElements (choiceLabels q hx hy)).map u.unop).property
    change (E.obj (op (labelCode (d := d)))).map ((parameterOp q).map u.unop.val)
      ((E.map (𝟙 (op (labelCode (d := d))))).app _
        ((choiceLabels q hx hy).app _ P'.unop.snd)) =
      (choiceLabels q hx hy).app _ P.unop.snd
    rw [E.map_id, NatTrans.id_app]
    exact h⟩
  map_id P := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact (taggedParameter q).map_id _
  map_comp u v := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact (taggedParameter q).map_comp v.unop.val u.unop.val

/-- The evaluation retains the literal common-coefficient parameter. -/
theorem choiceLabelIndex_degree (P : (mixedChoiceDiagram q hx hy).Elementsᵒᵖ) :
    OrderedLabelElements.degree W (boundaryPoint W x y) ((choiceLabelIndex q hx hy).obj P) =
      ((parameterOp q).obj P.unop.fst).unop := rfl


open JTNecklaceEndpointCylinder

/-- On the reduced cylinder of a label, the original operator is exactly
the common-coefficient operator, with the same native three-bead code. -/
theorem choiceLabelIndex_under_map {P P' : (mixedChoiceDiagram q hx hy).Elementsᵒᵖ}
    (u : P ⟶ P') :
    (DecoratedCylinderNecklacePresentation.underDiagram W x y).map
        ((choiceLabelIndex q hx hy).map u) =
      (under (labelCode (d := d))).map (((parameterOp q).map u.unop.val).unop) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 (labelCode (d := d))) (((parameterOp q).obj P.unop.fst).unop) ≫
      (value (labelCode (d := d))).map (((parameterOp q).map u.unop.val).unop) = _
  rw [nativeMap_id, Category.id_comp]
  rfl


open MonoidalCategory CartesianMonoidalCategory
open JTHigherMixedGraphTargetLift (common_whole_raw commonLift commonLift_decorated
  commonLift_native commonToDecorated commonToDecorated_natural toNativeTarget toNativeTarget_natural)
open DaggerChosenRigidificationNecklace.NecklaceCode (singleIso)
open JTMixedGraphRawRefinement (nativeRawGraph)

private abbrev choicesIndex := (mixedChoiceDiagram q hx hy).Elementsᵒᵖ
private abbrev graphAt (P : choicesIndex q hx hy) := P.unop.fst.1.unop
private abbrev coefficientAt (P : choicesIndex q hx hy) := c q (graphAt q hx hy P)
private abbrev timeAt (P : choicesIndex q hx hy) := ord.obj P.unop.fst.2.unop

open JTHigherCommonMixedGraphFamilies (common_vertical_stationary)

private abbrev targetAt := JTNormalizedGraphTargetArrow.target hx hy
private abbrev pullbackAt := JTTargetCommaPullback.diagram W x y (targetAt q hx hy)

/-- Every actual joint choice supplies the original raw-bead pullback map
on its entire native time cylinder. -/
def choiceBeadLift (P : choicesIndex q hx hy) :
    (under (labelCode (d := d))).obj (timeAt q hx hy P) ⟶
      (pullbackAt q hx hy).obj ((choiceLabelIndex q hx hy).obj P) := by
  let G := graphAt q hx hy P
  let n := timeAt q hx hy P
  let r := coefficientAt q hx hy P
  let s := (S q G).obj.parameter
  let L : Extension (leftSq q hx G) n := P.unop.snd.1
  let R : Extension (rightSq q hy G) n := P.unop.snd.2
  let E := commonChoiceFamilies r n (coefficient (C q)) s x y L R 0
  have hq : nativeRawGraph W d (C q).obj.degree (coefficient (C q))
      (s ≫ GroupoidSimplex.parameter.map r) = (targetAt q hx hy).map := by
    change (singleIso d).hom ≫ rawGraph W ⦋d⦌ (C q).obj.degree
      (coefficient (C q)) (s ≫ GroupoidSimplex.parameter.map r) = _
    rw [supported_parameter q G, raw_eq (C q)]
    rfl
  have hL := common_vertical_stationary r _ (leftSq q hx G) L
  have hR := common_vertical_stationary r _ (rightSq q hy G) R
  exact commonLift r (coefficient (C q)) s (targetAt q hx hy).first (targetAt q hx hy).last E
    (common_whole_raw r (coefficient (C q)) s hq (targetAt q hx hy).first
      (targetAt q hx hy).last E hL hR)


/-- The time projection of the joint choice retains the actual injective operator. -/
def choiceTime : choicesIndex q hx hy ⥤ SimplexCategory :=
  (CategoryOfElements.π (mixedChoiceDiagram q hx hy) ⋙
    CategoryTheory.Prod.snd _ _).leftOp ⋙ ord

private abbrev rawChoiceLabel (P : choicesIndex q hx hy) :=
  (choiceLabelIndex q hx hy).obj P

private abbrev parameterAt (P : choicesIndex q hx hy) :=
  (S q (graphAt q hx hy P)).obj.parameter

/-- The decorated leg is the entire common-coefficient cylinder. -/
@[reassoc]
theorem choiceBeadLift_fst (P : choicesIndex q hx hy) :
    choiceBeadLift q hx hy P ≫ JTTargetCommaPullback.fst W x y (targetAt q hx hy)
        (rawChoiceLabel q hx hy P) =
      commonToDecorated (n := timeAt q hx hy P) (coefficientAt q hx hy P)
        (parameterAt q hx hy P) := by
  unfold choiceBeadLift
  apply commonLift_decorated

/-- The native leg is the original endpoint-preserving outer collapse. -/
@[reassoc]
theorem choiceBeadLift_snd (P : choicesIndex q hx hy) :
    choiceBeadLift q hx hy P ≫ JTTargetCommaPullback.snd W x y (targetAt q hx hy)
        (rawChoiceLabel q hx hy P) =
      toNativeTarget d (timeAt q hx hy P) := by
  unfold choiceBeadLift
  apply commonLift_native

set_option maxHeartbeats 450000 in
private theorem choiceCylinder_natural {P P' : choicesIndex q hx hy} (u : P ⟶ P') :
    commonToDecorated (n := timeAt q hx hy P) (coefficientAt q hx hy P)
        (parameterAt q hx hy P) ≫
      (under (labelCode (d := d))).map (((parameterOp q).map u.unop.val).unop) =
      (under (labelCode (d := d))).map ((choiceTime q hx hy).map u) ≫
        commonToDecorated (n := timeAt q hx hy P') (coefficientAt q hx hy P')
          (parameterAt q hx hy P') := by
  let a := u.unop.val.1.unop
  let j := u.unop.val.2.unop
  let f := (JTRowGraphCommonCenter.diagram q).map a
  have hf := Over.w f
  let hj := (SemiSimplexCategory.homEquiv j).injective
  have hs : parameterAt q hx hy P ≫ GroupoidSimplex.parameter.map f.left =
      parameterAt q hx hy P' := ((supportAt q).map a).hom.parameter
  exact commonToDecorated_natural (coefficientAt q hx hy P) (parameterAt q hx hy P)
    f.left hf (ord.map j) hj (parameterAt q hx hy P') hs

/-- The actual lifts of the full cylinders form a natural transformation
over the same ordered native target and the original varying decorated labels. -/
def choiceBeadLiftNatural :
    choiceTime q hx hy ⋙ under (labelCode (d := d)) ⟶
      choiceLabelIndex q hx hy ⋙ pullbackAt q hx hy where
  app := choiceBeadLift q hx hy
  naturality {P P'} u := by
    let Q := targetAt q hx hy
    let i := rawChoiceLabel q hx hy P'
    apply pullback.hom_ext
      (f := (DecoratedCylinderNecklacePresentation.underCocone W x y).app i)
      (g := JTTargetCommaPullback.targetMap W x y Q)
    · change ((under (labelCode (d := d))).map ((choiceTime q hx hy).map u) ≫
          choiceBeadLift q hx hy P') ≫ JTTargetCommaPullback.fst W x y Q i =
        (choiceBeadLift q hx hy P ≫
          (pullbackAt q hx hy).map ((choiceLabelIndex q hx hy).map u)) ≫
          JTTargetCommaPullback.fst W x y Q i
      rw [Category.assoc, choiceBeadLift_fst, Category.assoc, JTTargetCommaPullback.map_fst,
        choiceBeadLift_fst_assoc, choiceLabelIndex_under_map]
      exact (choiceCylinder_natural q hx hy u).symm
    · change ((under (labelCode (d := d))).map ((choiceTime q hx hy).map u) ≫
          choiceBeadLift q hx hy P') ≫ JTTargetCommaPullback.snd W x y Q i =
        (choiceBeadLift q hx hy P ≫
          (pullbackAt q hx hy).map ((choiceLabelIndex q hx hy).map u)) ≫
          JTTargetCommaPullback.snd W x y Q i
      rw [Category.assoc, choiceBeadLift_snd, Category.assoc, JTTargetCommaPullback.map_snd,
        choiceBeadLift_snd]
      exact toNativeTarget_natural d ((choiceTime q hx hy).map u)

end Labels

end
end DaggerModels.PartII.JTRowGraphCommonCenter
