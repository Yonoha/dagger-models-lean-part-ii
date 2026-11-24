import DaggerModelsPartII.JTSupportedPathWhiskeredGraph
import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTVariableMiddleGraphEvaluation

/-!
The complete supported path with changing outer necklaces inherits the old
graph raw equations. We reuse `JTWhiskeredGraphRawTransport.raw` for the two
unchanged outer coefficients, `JTWhiskeredGraphRaw.piece_restrict` for the old
middle inverse image, and `JTSupportedPathChainLabels.coefficientMap_raw` for
the new middle. All parameters remain on their complete graph domains.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open HomotopicalAlgebra
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathWhiskeredRaw

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

/-- Any old coefficient constant on an ordinal support has literal joint raw
value on every graph whose full parameter factors through that support. -/
theorem old_middle_constant_raw (W : Source) (z : Vertex W)
    {T : NecklaceCode} {k d : SimplexCategory} {X : SSet.{0}}
    (u : d ⟶ k) (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W T)
    (hs : std.map u ≫ c = JTConstantOrderedLabel.constantCoefficient W z T d)
    (h : X ⟶ T.toSSet) (q : X ⟶ J.obj d) :
    lift h (q ≫ J.map u) ≫ realizedLabel T.toSSet W k (SSet.yonedaEquiv c) =
      h ≫ term T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [JTWhiskerEdgeGraphRaw.coefficient_reindex W u h q c, hs]
  have hr := JTComposedPrismLabels.rawProduct_constant W z T
    (snd T.toSSet (J.obj d))
  dsimp only [JTComposedPrismLabels.rawProduct,
    JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr]
  simp only [← Category.assoc, lift_fst]

/-- The old whole raw equation determines its middle native target value on
the complete inverse image. A supported constant old middle coefficient
identifies that value with the joint; no native target equation is assumed. -/
theorem old_middle_target (W : Source) (z : Vertex W)
    {x y : Vertex W} {P M R : NecklaceCode}
    {k d : SimplexCategory} {Y : SSet.{0}}
    (C : JTThreePieceLabelOperators.Data W P M R k x y)
    (u : d ⟶ k)
    (hs : std.map u ≫ C.middle =
      JTConstantOrderedLabel.constantCoefficient W z M d)
    (h : Y ⟶ (wedge P (wedge M R)).toSSet)
    (θ : Y ⟶ J.obj k)
    (g : (wedge P (wedge M R)).toSSet ⟶ Raw W)
    (oldraw : lift h θ ≫
      realizedLabel (wedge P (wedge M R)).toSSet W k
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients C))) = h ≫ g)
    (q : pullback h (tripleRightU P M R) ⟶ J.obj d)
    (hq : (pullback.fst h (tripleRightU P M R) ≫ θ) = q ≫ J.map u) :
    pullback.snd h (tripleRightU P M R) ≫ tripleRightU P M R ≫ g =
      pullback.snd h (tripleRightU P M R) ≫ term M.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W z) := by
  have hc := JTWhiskeredGraphRaw.coefficient_middle W C
  have hp := JTWhiskeredGraphRaw.piece_restrict W h θ
    (tripleRightU P M R)
    (JTComposedPrismLabels.coefficient
      (JTThreePieceLabelOperators.coefficients C)) C.middle hc
  have hm : lift (pullback.snd h (tripleRightU P M R))
      (pullback.fst h (tripleRightU P M R) ≫ θ) ≫
        realizedLabel M.toSSet W k (SSet.yonedaEquiv C.middle) =
      pullback.snd h (tripleRightU P M R) ≫ tripleRightU P M R ≫ g := by
    calc
      _ = pullback.fst h (tripleRightU P M R) ≫
          (lift h θ ≫ realizedLabel (wedge P (wedge M R)).toSSet W k
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
              (JTThreePieceLabelOperators.coefficients C)))) := hp.symm
      _ = pullback.fst h (tripleRightU P M R) ≫ h ≫ g := by rw [oldraw]
      _ = _ := by
        rw [← Category.assoc, pullback.condition, Category.assoc]
  rw [hq] at hm
  exact hm.symm.trans
    (old_middle_constant_raw W z u C.middle hs
      (pullback.snd h (tripleRightU P M R)) q)

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

private abbrev B := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev base := JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev deg := JTSupportedPathChainLabels.ordinals W z L S u hs
private abbrev α := JTSupportedPathChainLabels.toOldCoefficient W z L S u hs
private abbrev M := JTParametrizedTargetFamilies.codes L
private abbrev T (a : I) := wedge (P.obj a) (wedge ((M W z L).obj a) (R.obj a))
private abbrev C (a : I) :=
  JTSupportedPathWhiskeredGraph.oldData W x z y L P R A a
private abbrev D (p : B W z L S u hs) :=
  JTSupportedPathWhiskeredDiagram.data W x z y L S u hs P R A p
private abbrev oldH (a : I) : Y.obj a ⟶ (T W z L P R a).toSSet :=
  oldπ.app a ≫ fst (T W z L P R a).toSSet (J.obj (time.obj a))
private abbrev oldG (a : I) : (T W z L P R a).toSSet ⟶ Raw W :=
  (c.app a).map ≫ Q.map
private abbrev graph := JTSupportedPathWhiskeredGraph.graph W z L S u hs oldθ
private abbrev toOld := JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ
private abbrev π := JTSupportedPathWhiskeredGraph.projectionNew
  W x z y L S u hs P R A time oldπ oldθ
private abbrev θ := JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ
private abbrev newH (p : B W z L S u hs) :
    (graph W z L S u hs oldθ).obj p ⟶
      (T W z L P R ((base W z L S u hs).obj p)).toSSet :=
  (π W x z y L S u hs P R A time oldπ oldθ).app p ≫
    fst (T W z L P R ((base W z L S u hs).obj p)).toSSet
      (J.obj (time.obj ((base W z L S u hs).obj p)))

variable (oldRaw : ∀ a : I,
  lift (oldH W x z y L P R A time oldπ a) (oldθ.app a) ≫
    realizedLabel (T W z L P R a).toSSet W ((K W z L).obj a)
      (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients (C W x z y L P R A a)))) =
      oldH W x z y L P R A time oldπ a ≫ oldG W x z y L P R A Q c a)

variable (oldMiddleQ : ∀ a : I,
  pullback (oldH W x z y L P R A time oldπ a)
    (tripleRightU (P.obj a) ((M W z L).obj a) (R.obj a)) ⟶ J.obj (S.obj a))
variable (oldMiddleFactor : ∀ a : I,
  pullback.fst (oldH W x z y L P R A time oldπ a)
      (tripleRightU (P.obj a) ((M W z L).obj a) (R.obj a)) ≫ oldθ.app a =
    oldMiddleQ a ≫ J.map (u.app a))

private theorem newH_old (p : B W z L S u hs) :
    newH W x z y L S u hs P R A time oldπ oldθ p =
      (toOld W z L S u hs oldθ).app p ≫
        oldH W x z y L P R A time oldπ
          ((base W z L S u hs).obj p) := by
  unfold newH oldH π
  rw [JTSupportedPathWhiskeredGraph.projectionNew_app]
  simp only [JTSupportedPathWhiskeredGraph.projection, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]

private theorem θ_old (p : B W z L S u hs) :
    (θ W z L S u hs oldθ).app p ≫ J.map ((α W z L S u hs).app p) =
      (toOld W z L S u hs oldθ).app p ≫
        oldθ.app ((base W z L S u hs).obj p) :=
  NatTrans.congr_app (JTSupportedPathWhiskeredGraph.parameter_old
    W z L S u hs oldθ) p

include oldRaw in
/-- An outer native piece is transported directly from the old whole graph,
without replacing that graph by the full native-time product. -/
private theorem outer_raw {V : NecklaceCode}
    (p : B W z L S u hs)
    (i : V.toSSet ⟶ (T W z L P R ((base W z L S u hs).obj p)).toSSet)
    (d : std.obj ((deg W z L S u hs).obj p) ⟶
      TripleBeadEndpointLabel.labels W V)
    (hd : d = std.map ((α W z L S u hs).app p) ≫
      JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (C W x z y L P R A ((base W z L S u hs).obj p))) ≫ pre W i) :
    lift (pullback.snd
        (newH W x z y L S u hs P R A time oldπ oldθ p) i)
      (pullback.fst
        (newH W x z y L S u hs P R A time oldπ oldθ p) i ≫
          (θ W z L S u hs oldθ).app p) ≫
        realizedLabel V.toSSet W ((deg W z L S u hs).obj p)
          (SSet.yonedaEquiv d) =
      pullback.snd
        (newH W x z y L S u hs P R A time oldπ oldθ p) i ≫ i ≫
          oldG W x z y L P R A Q c ((base W z L S u hs).obj p) := by
  let b := (base W z L S u hs).obj p
  let h := newH W x z y L S u hs P R A time oldπ oldθ p
  let η := pullback.fst h i ≫ (toOld W z L S u hs oldθ).app p
  have hn : η ≫ oldH W x z y L P R A time oldπ b =
      pullback.snd h i ≫ i := by
    calc
      _ = pullback.fst h i ≫ h := by
        change (pullback.fst h i ≫
          (toOld W z L S u hs oldθ).app p) ≫
            oldH W x z y L P R A time oldπ b = _
        rw [Category.assoc, ← newH_old W x z y L S u hs P R A time oldπ oldθ p]
      _ = _ := pullback.condition
  have hq : (pullback.fst h i ≫ (θ W z L S u hs oldθ).app p) ≫
      J.map ((α W z L S u hs).app p) = η ≫ oldθ.app b := by
    calc
      _ = pullback.fst h i ≫ ((θ W z L S u hs oldθ).app p ≫
          J.map ((α W z L S u hs).app p)) := Category.assoc _ _ _
      _ = pullback.fst h i ≫
          ((toOld W z L S u hs oldθ).app p ≫ oldθ.app b) := by
            rw [θ_old W z L S u hs oldθ p]
      _ = η ≫ oldθ.app b := (Category.assoc _ _ _).symm
  exact JTWhiskeredGraphRawTransport.raw W
    (oldH W x z y L P R A time oldπ b) (oldθ.app b)
    (JTComposedPrismLabels.coefficient
      (JTThreePieceLabelOperators.coefficients (C W x z y L P R A b)))
    (oldG W x z y L P R A Q c b) (oldRaw b)
    (pullback.snd h i)
    (pullback.fst h i ≫ (θ W z L S u hs oldθ).app p)
    η i ((α W z L S u hs).app p) d hd hn hq

include oldRaw oldMiddleQ oldMiddleFactor in
/-- The middle full inverse image has the same literal joint raw value as
the old whole target, after transport of the old support parameter. -/
private theorem middle_raw
    (hu : ∀ a : I, Mono (u.app a))
    (p : B W z L S u hs) :
    lift (pullback.snd
        (newH W x z y L S u hs P R A time oldπ oldθ p)
        (tripleRightU (P.obj ((base W z L S u hs).obj p))
          ((M W z L).obj ((base W z L S u hs).obj p))
          (R.obj ((base W z L S u hs).obj p))))
      (pullback.fst
        (newH W x z y L S u hs P R A time oldπ oldθ p)
        (tripleRightU (P.obj ((base W z L S u hs).obj p))
          ((M W z L).obj ((base W z L S u hs).obj p))
          (R.obj ((base W z L S u hs).obj p))) ≫
            (θ W z L S u hs oldθ).app p) ≫
      realizedLabel ((M W z L).obj ((base W z L S u hs).obj p)).toSSet W
        ((deg W z L S u hs).obj p)
        (SSet.yonedaEquiv (D W x z y L S u hs P R A p).middle) =
    pullback.snd
        (newH W x z y L S u hs P R A time oldπ oldθ p)
        (tripleRightU (P.obj ((base W z L S u hs).obj p))
          ((M W z L).obj ((base W z L S u hs).obj p))
          (R.obj ((base W z L S u hs).obj p))) ≫
      tripleRightU (P.obj ((base W z L S u hs).obj p))
        ((M W z L).obj ((base W z L S u hs).obj p))
        (R.obj ((base W z L S u hs).obj p)) ≫
          oldG W x z y L P R A Q c ((base W z L S u hs).obj p) := by
  let b := (base W z L S u hs).obj p
  let h := newH W x z y L S u hs P R A time oldπ oldθ p
  let i := tripleRightU (P.obj b) ((M W z L).obj b) (R.obj b)
  let h₀ := oldH W x z y L P R A time oldπ b
  let η := (toOld W z L S u hs oldθ).app p
  have hnative : (pullback.fst h i ≫ η) ≫ h₀ = pullback.snd h i ≫ i := by
    rw [Category.assoc, ← newH_old W x z y L S u hs P R A time oldπ oldθ p]
    exact pullback.condition
  let m := pullback.lift (pullback.fst h i ≫ η) (pullback.snd h i) hnative
  have hm₁ : m ≫ pullback.fst h₀ i = pullback.fst h i ≫ η :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd h₀ i = pullback.snd h i :=
    pullback.lift_snd _ _ _
  have hfactor : (pullback.fst h i ≫ (θ W z L S u hs oldθ).app p) ≫
      J.map ((α W z L S u hs).app p) =
        (m ≫ oldMiddleQ b) ≫ J.map (u.app b) := by
    calc
      _ = pullback.fst h i ≫
          ((θ W z L S u hs oldθ).app p ≫
            J.map ((α W z L S u hs).app p)) := Category.assoc _ _ _
      _ = pullback.fst h i ≫ (η ≫ oldθ.app b) := by
            rw [θ_old W z L S u hs oldθ p]
      _ = (pullback.fst h i ≫ η) ≫ oldθ.app b :=
            (Category.assoc _ _ _).symm
      _ = (m ≫ pullback.fst h₀ i) ≫ oldθ.app b := by rw [hm₁]
      _ = m ≫ (pullback.fst h₀ i ≫ oldθ.app b) := Category.assoc _ _ _
      _ = m ≫ (oldMiddleQ b ≫ J.map (u.app b)) := by
            rw [oldMiddleFactor b]
      _ = _ := by rw [Category.assoc]
  letI : Mono (u.app b) := hu b
  have hnew := JTSupportedPathChainLabels.coefficientMap_raw W z L S u hs p
    (pullback.snd h i) (pullback.fst h i ≫ (θ W z L S u hs oldθ).app p)
    (m ≫ oldMiddleQ b) hfactor
  have hold := old_middle_target W z (C W x z y L P R A b)
    (u.app b) (hs b) h₀ (oldθ.app b)
    (oldG W x z y L P R A Q c b) (oldRaw b)
    (oldMiddleQ b) (oldMiddleFactor b)
  have htarget : pullback.snd h i ≫ i ≫
      oldG W x z y L P R A Q c b =
    pullback.snd h i ≫ term ((M W z L).obj b).toSSet ≫
      SSet.yonedaEquiv.symm (rawVertex W z) := by
    calc
      _ = (m ≫ pullback.snd h₀ i) ≫ i ≫
          oldG W x z y L P R A Q c b := by rw [hm₂]
      _ = m ≫ (pullback.snd h₀ i ≫ i ≫
          oldG W x z y L P R A Q c b) := by simp only [Category.assoc]
      _ = m ≫ (pullback.snd h₀ i ≫ term ((M W z L).obj b).toSSet ≫
          SSet.yonedaEquiv.symm (rawVertex W z)) := congrArg (m ≫ ·) hold
      _ = (m ≫ pullback.snd h₀ i) ≫ term ((M W z L).obj b).toSSet ≫
          SSet.yonedaEquiv.symm (rawVertex W z) := by simp only [Category.assoc]
      _ = _ := by rw [hm₂]
  exact hnew.trans htarget.symm

include oldRaw oldMiddleQ oldMiddleFactor in
/-- The actual globally whiskered supported path has all three exact raw
equations on the full native inverse images of its new graph. -/
theorem pieceEquations (hu : ∀ a : I, Mono (u.app a))
    (p : B W z L S u hs) :
    JTWhiskeredGraphRaw.PieceEquations W (D W x z y L S u hs P R A p)
      (newH W x z y L S u hs P R A time oldπ oldθ p)
      ((θ W z L S u hs oldθ).app p)
      (oldG W x z y L P R A Q c ((base W z L S u hs).obj p)) := by
  let b := (base W z L S u hs).obj p
  let C₀ := C W x z y L P R A b
  let D₀ := D W x z y L S u hs P R A p
  let β := (α W z L S u hs).app p
  refine ⟨?_, ?_, ?_⟩
  · have hd : D₀.left = std.map β ≫
        JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients C₀) ≫
            pre W (tripleRightT (P.obj b) ((M W z L).obj b) (R.obj b)) := by
      rw [JTWhiskeredGraphRaw.coefficient_left W C₀]
      rfl
    exact outer_raw W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw p (tripleRightT (P.obj b) ((M W z L).obj b) (R.obj b))
      D₀.left hd
  · exact middle_raw W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu p
  · have hd : D₀.right = std.map β ≫
        JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients C₀) ≫
            pre W (tripleRightV (P.obj b) ((M W z L).obj b) (R.obj b)) := by
      rw [JTWhiskeredGraphRaw.coefficient_right W C₀]
      rfl
    exact outer_raw W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw p (tripleRightV (P.obj b) ((M W z L).obj b) (R.obj b))
      D₀.right hd

/-- The unchanged old target collapse on the literal new path labels. -/
def collapse : JTParametrizedTargetFamilies.codes
    (JTSupportedPathWhiskeredGraph.pathLabels W x z y L S u hs P R A) ⟶
      (Functor.const (B W z L S u hs)).obj Q.code :=
  eqToHom (JTSupportedPathWhiskeredGraph.code_reindex
      W x z y L S u hs P R A) ≫
    Functor.whiskerLeft (base W z L S u hs) c

private abbrev F := JTSupportedPathWhiskeredDiagram.variableMiddleFamily
  W x z y L S u hs P R A
private abbrev pathTime := base W z L S u hs ⋙ time

/-- The exact full inverse image of both endpoint lines for the path graph. -/
abbrev reduced : B W z L S u hs ⥤ Under JTXiEndpointCollapse.boundary :=
  JTVariableMiddleGraphEvaluation.reduced Q
    (F W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (collapse W x z y L S u hs P R A Q c)
    (JTSupportedPathWhiskeredGraph.projectionNew
      W x z y L S u hs P R A time oldπ oldθ)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- The complete supported path evaluates every internal necklace in the
unchanged original target comma category `Q`. -/
def evaluation (hu : ∀ a : I, Mono (u.app a)) :
    BoundaryNecklaceComma.Presentation
      (reduced W x z y L S u hs P R A time oldπ oldθ Q c) ⥤
        JTGraphFactoredPresentation.TargetComma Q :=
  JTVariableMiddleGraphEvaluation.evaluation Q
    (F W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (collapse W x z y L S u hs P R A Q c)
    (JTSupportedPathWhiskeredGraph.projectionNew
      W x z y L S u hs P R A time oldπ oldθ)
    (θ W z L S u hs oldθ)
    (pieceEquations W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)

/-- Forget the complete internal-necklace presentation to its path chain. -/
abbrev toChain : BoundaryNecklaceComma.Presentation
    (reduced W x z y L S u hs P R A time oldπ oldθ Q c) ⥤
      B W z L S u hs :=
  JTVariableMiddleGraphEvaluation.toOriginal Q
    (F W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (collapse W x z y L S u hs P R A Q c)
    (JTSupportedPathWhiskeredGraph.projectionNew
      W x z y L S u hs P R A time oldπ oldθ)

/-- The complete graph presentation weakly covers its path-chain index. -/
theorem toChain_weak
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (toChain W x z y L S u hs P R A time oldπ oldθ Q c)) := by
  apply JTVariableMiddleGraphEvaluation.toOriginal_weak Q
    (F W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (collapse W x z y L S u hs P R A Q c)
    (JTSupportedPathWhiskeredGraph.projectionNew
      W x z y L S u hs P R A time oldπ oldθ)
  intro p
  change trivialFibrations SSet.{0}
    ((JTSupportedPathWhiskeredGraph.projection
      W x z y L S u hs P R A time oldπ oldθ).app p)
  exact JTSupportedPathWhiskeredGraph.projection_trivialFibration
    W x z y L S u hs P R A time oldπ oldθ hπ p

/-- The whole graph presentation returns to the unchanged supplied index. -/
abbrev toOriginal : BoundaryNecklaceComma.Presentation
    (reduced W x z y L S u hs P R A time oldπ oldθ Q c) ⥤ I :=
  toChain W x z y L S u hs P R A time oldπ oldθ Q c ⋙
    base W z L S u hs

/-- The complete fixed-target evaluation has a weak presentation cover of
the original index when the path choice spaces are weakly contractible. -/
theorem toOriginal_weak
    (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((M W z L).obj a).len)
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (toOriginal W x z y L S u hs P R A time oldπ oldθ Q c)) := by
  haveI : WeakEquivalence (nerveMap
      (toChain W x z y L S u hs P R A time oldπ oldθ Q c)) :=
    toChain_weak W x z y L S u hs P R A time oldπ oldθ Q c hπ
  haveI : WeakEquivalence (nerveMap (base W z L S u hs)) :=
    JTSupportedPathChainLabels.toOriginal_weak W z L S u hs hu hW hp
  change WeakEquivalence
    (nerveMap (toChain W x z y L S u hs P R A time oldπ oldθ Q c) ≫
      nerveMap (base W z L S u hs))
  infer_instance

end
end DaggerModels.PartII.JTSupportedPathWhiskeredRaw
