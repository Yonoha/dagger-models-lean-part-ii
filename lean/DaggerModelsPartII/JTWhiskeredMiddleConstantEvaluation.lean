import DaggerModelsPartII.JTSupportedPathWhiskeredRaw
import DaggerModelsPartII.JTSupportedPathWhiskeredEndpointLabels
import DaggerModelsPartII.JTVariableMiddleNativeProjection
import DaggerModelsPartII.JTNativeTimeProductTransport

/-!
The literal constant-middle endpoint retains the original whole graph,
native necklace, and time. The two outer equations restrict the supplied old
whole raw equation by `JTWhiskeredGraphRaw.piece_restrict`. For the middle,
`JTSupportedPathWhiskeredRaw.old_middle_target` derives the old target's
joint value from that same whole raw equation and the original support
factor; `old_middle_constant_raw` evaluates the new constant coefficient.
No native-target or new piece raw premise is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWhiskeredMiddleConstantEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {S T : SSet.{0}} (i : S ⟶ T) :=
  diagramMappingPrecomp (discreteFree.map i) W

private theorem eqToHom_comp_map_raw_heq {A B U : NecklaceCode}
    (h : A = B) (f : B ⟶ U) {X : SSet.{0}}
    (q : U.toSSet ⟶ X) :
    HEq ((eqToHom h ≫ f).map ≫ q) (f.map ≫ q) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]
  exact HEq.rfl

private theorem eqToHom_product_heq {A B : NecklaceCode}
    (h : A = B) {X Z : SSet.{0}} (p : X ⟶ A.toSSet ⊗ Z) :
    HEq (p ≫ ((eqToHom h).map ⊗ₘ 𝟙 Z)) p := by
  cases h
  simp only [eqToHom_refl]
  change HEq (p ≫ (NecklaceCode.simplicialFunctor.map (𝟙 _) ⊗ₘ 𝟙 Z)) p
  rw [NecklaceCode.simplicialFunctor.map_id]
  have htensor := MonoidalCategory.id_tensorHom_id
    (NecklaceCode.simplicialFunctor.obj A) Z
  rw [htensor]
  exact heq_of_eq (Category.comp_id p)

private theorem native_raw_app {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (F G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (a : I) {U : NecklaceCode} (c :
      (JTParametrizedTargetFamilies.codes F.labels).obj a ⟶ U)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) :
    HEq (((JTVariableMiddleNativeProjection.nativeIso F G).inv.app a ≫ c).map ≫ q)
      (c.map ≫ q) := by
  rw [JTVariableMiddleNativeProjection.nativeIso_inv_app_transport]
  exact eqToHom_comp_map_raw_heq _ c q

private theorem native_product_app {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (F G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (a : I) (t : SimplexCategory) {X : SSet.{0}}
    (p : X ⟶ ((JTParametrizedTargetFamilies.codes F.labels).obj a).toSSet ⊗
      J.obj t) :
    HEq (p ≫ (((JTVariableMiddleNativeProjection.nativeIso F G).hom.app a).map ⊗ₘ
      𝟙 (J.obj t))) p := by
  rw [JTVariableMiddleNativeProjection.nativeIso_hom_app_transport]
  exact eqToHom_product_heq _ p

private theorem native_raw_eq {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (F G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (a : I) {U : NecklaceCode}
    (c : wedge (P.obj a) (wedge (M.obj a) (R.obj a)) ⟶ U)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) :
    (show (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⟶ X from
      ((JTVariableMiddleNativeProjection.nativeIso F G).inv.app a ≫ c).map ≫ q) =
      c.map ≫ q :=
  eq_of_heq (native_raw_app F G a c q)

private theorem native_product_eq {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (F G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (a : I) (t : SimplexCategory) {X : SSet.{0}}
    (p : X ⟶ (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⊗ J.obj t) :
    (show X ⟶ (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⊗ J.obj t from
      p ≫ (((JTVariableMiddleNativeProjection.nativeIso F G).hom.app a).map ⊗ₘ
        𝟙 (J.obj t))) = p :=
  eq_of_heq (native_product_app F G a t p)


private theorem native_product_eq_with_id {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (F G : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (a : I) (t : SimplexCategory) {X : SSet.{0}}
    (p : X ⟶ (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⊗ J.obj t) :
    (show X ⟶ (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⊗ J.obj t from
      p ≫ (((JTVariableMiddleNativeProjection.nativeIso F G).hom.app a).map ⊗ₘ
        𝟙 (J.obj t)) ≫ 𝟙 _) = p := by
  exact (congrArg (fun f ↦ p ≫ f)
    (Category.comp_id
      (((JTVariableMiddleNativeProjection.nativeIso F G).hom.app a).map ⊗ₘ
        𝟙 (J.obj t)))).trans (native_product_eq F G a t p)

private def familyEvaluation {I : Type} [SmallCategory I]
    {W : Source} {x y : Vertex W} {P M R : I ⥤ NecklaceCode}
    {K : I ⥤ SimplexCategory}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (F : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y)
      P M R K) (time : I ⥤ SimplexCategory)
    (c : JTParametrizedTargetFamilies.codes F.labels ⟶ (Functor.const I).obj Q.code)
    {Y : I ⥤ SSet.{0}}
    (π : Y ⟶ JTVariableMiddleGraphEvaluation.productDiagram Q F time c)
    (θ : Y ⟶ K ⋙ J)
    (H : ∀ a : I, JTWhiskeredGraphRaw.PieceEquations W (F.data a)
      (JTVariableMiddleGraphEvaluation.nativeCoordinate Q F time c π a)
      (θ.app a) (JTVariableMiddleGraphEvaluation.rawTarget Q F c a)) :
    BoundaryNecklaceComma.Presentation
        (JTVariableMiddleGraphEvaluation.reduced Q F time c π) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTVariableMiddleGraphEvaluation.evaluation Q F time c π θ H


variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (P R : I ⥤ NecklaceCode)
variable (A : JTSupportedPathWhiskeredDiagram.Surroundings W x z y L P R)
variable (time : I ⥤ SimplexCategory)
variable {Y : I ⥤ SSet.{0}}
variable (oldπ : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct
  W x z y L P R A time)
variable (oldθ : Y ⟶ K W z L ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : JTParametrizedTargetFamilies.codes
  (JTSupportedPathWhiskeredGraph.oldLabels W x z y L P R A) ⟶
    (Functor.const I).obj Q.code)

private abbrev M := JTParametrizedTargetFamilies.codes L
private abbrev T (a : I) := wedge (P.obj a) (wedge ((M W z L).obj a) (R.obj a))
private abbrev C₀ (a : I) := JTSupportedPathWhiskeredGraph.oldData
  W x z y L P R A a
private abbrev C₁ (a : I) := JTSupportedPathWhiskeredEndpointLabels.constantData
  W x z y L P R A a
private abbrev oldH (a : I) : Y.obj a ⟶ (T W z L P R a).toSSet :=
  oldπ.app a ≫ fst (T W z L P R a).toSSet (J.obj (time.obj a))
private abbrev oldG (a : I) : (T W z L P R a).toSSet ⟶ Raw W :=
  (c.app a).map ≫ Q.map

variable (oldRaw : ∀ a : I,
  lift (oldH W x z y L P R A time oldπ a) (oldθ.app a) ≫
    realizedLabel (T W z L P R a).toSSet W ((K W z L).obj a)
      (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients (C₀ W x z y L P R A a)))) =
      oldH W x z y L P R A time oldπ a ≫ oldG W x z y L P R A Q c a)
variable (oldMiddleQ : ∀ a : I,
  pullback (oldH W x z y L P R A time oldπ a)
    (tripleRightU (P.obj a) ((M W z L).obj a) (R.obj a)) ⟶ J.obj (S.obj a))
variable (oldMiddleFactor : ∀ a : I,
  pullback.fst (oldH W x z y L P R A time oldπ a)
      (tripleRightU (P.obj a) ((M W z L).obj a) (R.obj a)) ≫ oldθ.app a =
    oldMiddleQ a ≫ J.map (u.app a))

include oldRaw in
private theorem outer_raw {V : NecklaceCode} (a : I)
    (i : V.toSSet ⟶ (T W z L P R a).toSSet)
    (d : std.obj ((K W z L).obj a) ⟶ TripleBeadEndpointLabel.labels W V)
    (hd : JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients (C₀ W x z y L P R A a)) ≫
          pre W i = d) :
    lift (pullback.snd (oldH W x z y L P R A time oldπ a) i)
      (pullback.fst (oldH W x z y L P R A time oldπ a) i ≫ oldθ.app a) ≫
        realizedLabel V.toSSet W ((K W z L).obj a) (SSet.yonedaEquiv d) =
      pullback.snd (oldH W x z y L P R A time oldπ a) i ≫ i ≫
        oldG W x z y L P R A Q c a := by
  let h := oldH W x z y L P R A time oldπ a
  have hr := JTWhiskeredGraphRaw.piece_restrict W h (oldθ.app a) i
    (JTComposedPrismLabels.coefficient
      (JTThreePieceLabelOperators.coefficients (C₀ W x z y L P R A a))) d hd
  calc
    _ = pullback.fst h i ≫
        (lift h (oldθ.app a) ≫
          realizedLabel (T W z L P R a).toSSet W ((K W z L).obj a)
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
              (JTThreePieceLabelOperators.coefficients
                (C₀ W x z y L P R A a))))) := hr.symm
    _ = pullback.fst h i ≫ h ≫ oldG W x z y L P R A Q c a := by
          rw [oldRaw a]
    _ = _ := by rw [← Category.assoc, pullback.condition, Category.assoc]

include hs oldRaw oldMiddleQ oldMiddleFactor in
/-- Exact raw equations on all three complete native inverse images of the
constant-middle family, over the same original old graph and target `Q`. -/
theorem pieceEquations (a : I) :
    JTWhiskeredGraphRaw.PieceEquations W (C₁ W x z y L P R A a)
      (oldH W x z y L P R A time oldπ a) (oldθ.app a)
      (oldG W x z y L P R A Q c a) := by
  let h := oldH W x z y L P R A time oldπ a
  let T₀ := (M W z L).obj a
  let C₀a := C₀ W x z y L P R A a
  let C₁a := C₁ W x z y L P R A a
  refine ⟨?_, ?_, ?_⟩
  · have hd : JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients C₀a) ≫
          pre W (tripleRightT (P.obj a) T₀ (R.obj a)) = C₁a.left := by
      rw [JTWhiskeredGraphRaw.coefficient_left W C₀a]
      rfl
    exact outer_raw W x z y L P R A time oldπ oldθ Q c
      oldRaw a (tripleRightT (P.obj a) T₀ (R.obj a)) C₁a.left hd
  · have hconst : lift (pullback.snd h (tripleRightU (P.obj a) T₀ (R.obj a)))
        (pullback.fst h (tripleRightU (P.obj a) T₀ (R.obj a)) ≫ oldθ.app a) ≫
          realizedLabel T₀.toSSet W ((K W z L).obj a)
            (SSet.yonedaEquiv C₁a.middle) =
        pullback.snd h (tripleRightU (P.obj a) T₀ (R.obj a)) ≫
          term T₀.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
      have hsConst : std.map (𝟙 ((K W z L).obj a)) ≫ C₁a.middle =
          JTConstantOrderedLabel.constantCoefficient W z T₀ ((K W z L).obj a) := by
        change C₁a.middle = _
        rfl
      have hc := JTSupportedPathWhiskeredRaw.old_middle_constant_raw W z
        (𝟙 ((K W z L).obj a)) C₁a.middle hsConst
        (pullback.snd h (tripleRightU (P.obj a) T₀ (R.obj a)))
        (pullback.fst h (tripleRightU (P.obj a) T₀ (R.obj a)) ≫ oldθ.app a)
      have hJ : J.map (𝟙 ((K W z L).obj a)) =
          𝟙 (J.obj ((K W z L).obj a)) := J.map_id _
      rw [hJ, Category.comp_id] at hc
      exact hc
    have htarget := JTSupportedPathWhiskeredRaw.old_middle_target W z
      C₀a (u.app a) (hs a) h (oldθ.app a)
      (oldG W x z y L P R A Q c a) (oldRaw a)
      (oldMiddleQ a) (oldMiddleFactor a)
    exact hconst.trans htarget.symm
  · have hd : JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients C₀a) ≫
          pre W (tripleRightV (P.obj a) T₀ (R.obj a)) = C₁a.right := by
      rw [JTWhiskeredGraphRaw.coefficient_right W C₀a]
      rfl
    exact outer_raw W x z y L P R A time oldπ oldθ Q c
      oldRaw a (tripleRightV (P.obj a) T₀ (R.obj a)) C₁a.right hd

private abbrev oldF := JTSupportedPathWhiskeredGraph.oldFamily W x z y L P R A
private abbrev F := JTSupportedPathWhiskeredEndpointLabels.constantFamily
  W x z y L P R A

/-- The constant-middle endpoint retains the same collapse into `Q`. -/
def collapse : JTParametrizedTargetFamilies.codes
    (JTSupportedPathWhiskeredEndpointLabels.constantLabels W x z y L P R A) ⟶
      (Functor.const I).obj Q.code :=
  (JTVariableMiddleNativeProjection.nativeIso
    (oldF W x z y L P R A) (F W x z y L P R A)).inv ≫ c

theorem rawTarget_app (a : I) :
    (((collapse W x z y L P R A Q c).app a).map ≫ Q.map :
      (T W z L P R a).toSSet ⟶ Raw W) =
      oldG W x z y L P R A Q c a := by
  exact native_raw_eq (oldF W x z y L P R A) (F W x z y L P R A)
    a (c.app a) Q.map

/-- The original native/time product and the constant-middle evaluation
product are canonically isomorphic with identity components. -/
def productIso : JTSupportedPathWhiskeredGraph.oldProduct
    W x z y L P R A time ≅
      JTVariableMiddleGraphEvaluation.productDiagram Q
        (F W x z y L P R A) time
        (collapse W x z y L P R A Q c) :=
  (JTNativeTimeProductTransport.iso
    (JTVariableMiddleNativeProjection.nativeIso
      (oldF W x z y L P R A) (F W x z y L P R A)) time).trans
    (JTGraphCoveredProductInterface.iso
      (JTParametrizedTargetFamilies.codes (F W x z y L P R A).labels)
      time Q.code Q.map (collapse W x z y L P R A Q c))

/-- Project the unchanged old graph through that explicit native/time iso. -/
def projection : Y ⟶
    JTVariableMiddleGraphEvaluation.productDiagram Q
      (F W x z y L P R A) time
      (collapse W x z y L P R A Q c) :=
  oldπ ≫ (productIso W x z y L P R A time Q c).hom

theorem projection_app (a : I) :
    ((projection W x z y L P R A time oldπ Q c).app a :
      Y.obj a ⟶ (T W z L P R a).toSSet ⊗ J.obj (time.obj a)) =
    (oldπ.app a : Y.obj a ⟶ (T W z L P R a).toSSet ⊗ J.obj (time.obj a)) := by
  exact native_product_eq_with_id (oldF W x z y L P R A) (F W x z y L P R A)
    a (time.obj a) (oldπ.app a)


/-- The full native graph and independent original time are retained. -/
abbrev reduced : I ⥤ Under JTXiEndpointCollapse.boundary :=
  JTVariableMiddleGraphEvaluation.reduced Q (F W x z y L P R A) time
    (collapse W x z y L P R A Q c)
    (projection W x z y L P R A time oldπ Q c)

include hs oldRaw oldMiddleQ oldMiddleFactor in
theorem piecesForEvaluation (a : I) :
    JTWhiskeredGraphRaw.PieceEquations W ((F W x z y L P R A).data a)
      (JTVariableMiddleGraphEvaluation.nativeCoordinate Q
        (F W x z y L P R A) time
        (collapse W x z y L P R A Q c)
        (projection W x z y L P R A time oldπ Q c) a)
      (oldθ.app a)
      (JTVariableMiddleGraphEvaluation.rawTarget Q
        (F W x z y L P R A)
        (collapse W x z y L P R A Q c) a) := by
  change JTWhiskeredGraphRaw.PieceEquations W
    (C₁ W x z y L P R A a)
    ((projection W x z y L P R A time oldπ Q c).app a ≫
      fst (T W z L P R a).toSSet (J.obj (time.obj a)))
    (oldθ.app a) (((collapse W x z y L P R A Q c).app a).map ≫ Q.map)
  rw [projection_app W x z y L P R A time oldπ Q c a,
    rawTarget_app W x z y L P R A Q c a]
  exact pieceEquations W x z y L S u hs P R A time oldπ oldθ Q c
    oldRaw oldMiddleQ oldMiddleFactor a

include hs oldRaw oldMiddleQ oldMiddleFactor in
/-- Complete evaluation of every internal necklace at the literal
constant-middle endpoint in the unchanged target comma category `Q`. -/
def evaluation : BoundaryNecklaceComma.Presentation
    (reduced W x z y L P R A time oldπ Q c) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  familyEvaluation Q (F W x z y L P R A) time
    (collapse W x z y L P R A Q c)
    (projection W x z y L P R A time oldπ Q c) oldθ
    (piecesForEvaluation W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor)

/-- Forget the complete presentation to the original supplied index. -/
abbrev toOriginal : BoundaryNecklaceComma.Presentation
    (reduced W x z y L P R A time oldπ Q c) ⥤ I :=
  JTVariableMiddleGraphEvaluation.toOriginal Q (F W x z y L P R A) time
    (collapse W x z y L P R A Q c)
    (projection W x z y L P R A time oldπ Q c)

/-- A componentwise trivial-fibration old graph gives the weak cover for
the constant-middle endpoint without any new graph assumption. -/
theorem toOriginal_weak
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (toOriginal W x z y L P R A time oldπ Q c)) :=
  JTVariableMiddleGraphEvaluation.toOriginal_weak Q
    (F W x z y L P R A) time
    (collapse W x z y L P R A Q c)
    (projection W x z y L P R A time oldπ Q c) (fun a ↦ by
      change trivialFibrations SSet.{0}
        (oldπ.app a ≫ (productIso W x z y L P R A time Q c).hom.app a)
      exact (trivialFibrations SSet.{0}).comp_mem _ _ (hπ a)
        ((trivialFibrations SSet.{0}).of_isIso _))

end
end DaggerModels.PartII.JTWhiskeredMiddleConstantEvaluation
