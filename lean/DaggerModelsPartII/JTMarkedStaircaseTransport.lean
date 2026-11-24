import DaggerModelsPartII.JTBinaryPrismSideTransport
import DaggerModelsPartII.JTMarkedStaircaseGraphs
import DaggerModelsPartII.JTSharedCoefficientGraphPair
import DaggerModelsPartII.JTSharedCoefficientNativeParameter
import DaggerModelsPartII.JTSharedCoefficientEvaluation
import DaggerModelsPartII.JTHomotopyTargetComma
import DaggerModelsPartII.FiniteLastVertexFactor
import DaggerModelsPartII.JTFiniteGraphWedgeEvaluation

/-! Transport of actual staircase comparisons along native, time and coefficient arrows. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode DaggerNerveHomotopy

namespace DaggerModels.PartII.JTMarkedStaircaseTransport

open JTParameterBlocks (common leftIn rightIn)
open JTMarkedStaircaseGraphs (stepOperator stepParameter stepInputs leftPath rightPath)
open JTOrderedLabelBinaryGlue (Inputs code reindex)
open JTBinaryPrismParameter (sideMap parameter_left parameter_right)
open JTBinaryPrismRealization (realizeInputs realizeProduct collapse
  realizeOrderedProduct_reindex realizeProduct_reindexTime)
open JTSharedCoefficientNativeParameter (pull pull_left pull_right)
open JTSharedCoefficientEvaluation (evaluate evaluate_congr restrict_raw compare compareNative)
open JTDoubledGraphTime (degree operator fold)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTCodiscreteParameterPairing (coord coord_map)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {T U T' U' : NecklaceCode} {k l k' l' n n' : SimplexCategory}
variable (f : T ⟶ T') (g : U ⟶ U') (a : n ⟶ n') (α : k ⟶ k') (β : l ⟶ l')
variable (d : Fin ((common k l).len + 1))

private abbrev block := JTParameterBlockOperators.map α β
private abbrev cut := (block α β).toOrderHom d
private abbrev joined := @JTBinaryPrismTargetLift.parameter T U k l n

variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
variable (s' : T'.toSSet ⊗ J.obj n' ⟶ J.obj k') (t' : U'.toSSet ⊗ J.obj n' ⟶ J.obj l')
variable (hs : (f.map ⊗ₘ J.map a) ≫ s' = s ≫ J.map α)
variable (ht : (g.map ⊗ₘ J.map a) ≫ t' = t ≫ J.map β)

include hs ht in
/-- If the block operator reflects both strict inequalities at the cut,
the entire doubled staircase graph transports strictly. -/
theorem stepParameter_square
    (hleft : ∀ u, u < d → (block α β).toOrderHom u < cut α β d)
    (hright : ∀ u, d < u → cut α β d < (block α β).toOrderHom u) :
    pull f g (operator a) (stepParameter (joined s' t') (cut α β d)) =
      stepParameter (joined s t) d ≫ J.map (stepOperator d α β) := by
  exact JTDoubledGraphTime.extend_square _ _ _ (sideMap f g).map a (block α β) _ _ _ _
    (JTBinaryPrismSideTransport.mixedParameterSquare f g a α β hs ht)
    (JTOrdinalStaircaseNaturality.map_before_of_strict_right _ _ (block α β) d hright)
    (JTOrdinalStaircaseNaturality.map_after_of_strict_left _ _ (block α β) d hleft)

private theorem restriction_postcomp {A X : SSet.{0}} {m m' B B' N : SimplexCategory}
    (ι : A ⟶ X) (p : X ⊗ J.obj N ⟶ J.obj m) (r : m ⟶ B) (r' : m' ⟶ B')
    (c : m ⟶ m') (b : B ⟶ B') (q : A ⊗ J.obj N ⟶ J.obj B)
    (h : c ≫ r' = r ≫ b) (hq : (ι ▷ J.obj N) ≫ p ≫ J.map r = q) :
    (ι ▷ J.obj N) ≫ (p ≫ J.map c) ≫ J.map r' = q ≫ J.map b := by
  simp only [Category.assoc]
  rw [← J.map_comp, h, J.map_comp]
  simpa only [Category.assoc] using congrArg (fun u ↦ u ≫ J.map b) hq

/-- With the coefficient and cut fixed, the whole staircase graph commutes
with native and time pullback. -/
theorem pull_step {K L : SimplexCategory} (t : Fin ((common K L).len + 1))
    (p : (code T' U').toSSet ⊗ J.obj n' ⟶ J.obj (common K L)) :
    pull f g (operator a) (stepParameter p t) = stepParameter (pull f g a p) t := by
  let B := common K L
  let e₀ := JTOrdinalStaircaseComparison.before B t
  let e₁ := JTOrdinalStaircaseComparison.after B t
  have h : ((sideMap f g).map ⊗ₘ J.map a) ≫ p = pull f g a p ≫ J.map (𝟙 B) := by
    rw [J.map_id, Category.comp_id]
    rfl
  have h₀ : e₀ ≫ 𝟙 _ = 𝟙 B ≫ e₀ := (Category.comp_id _).trans (Category.id_comp _).symm
  have h₁ : e₁ ≫ 𝟙 _ = 𝟙 B ≫ e₁ := (Category.comp_id _).trans (Category.id_comp _).symm
  simpa only [J.map_id, Category.comp_id] using
    JTDoubledGraphTime.extend_square (pull f g a p) e₀ e₁ (sideMap f g).map a (𝟙 B) (𝟙 _)
      p e₀ e₁ h h₀ h₁

variable {i₀ i₁ : Fin (k.len + 1)} {j₀ j₁ : Fin (l.len + 1)}
variable (hi : i₀ ≤ i₁) (hj : j₀ ≤ j₁)
variable (hsl : ∀ q p v, coord k q (s.app q p) v ≤ i₀)
variable (htr : ∀ q p v, j₁ ≤ coord l q (t.app q p) v)

private abbrev leftTarget := leftPath (α.toOrderHom.monotone hi) (cut α β d)
private abbrev rightTarget := rightPath (β.toOrderHom.monotone hj) (cut α β d)
private abbrev pushed := stepParameter (joined s t) d ≫ J.map (stepOperator d α β)
private abbrev pulled := pull f g (operator a) (stepParameter (joined s' t') (cut α β d))

include hsl in
private theorem pushed_left :
    (tripleRightT T (single 1) U ▷ J.obj (degree n)) ≫ pushed α β d s t ≫
      J.map (leftTarget α β d hi) = (T.toSSet ◁ fold n) ≫ s ≫ J.map α := by
  rw [← Category.assoc (T.toSSet ◁ fold n)]
  exact restriction_postcomp _ _ _ _ _ _ _ (JTMarkedStaircaseGraphs.stepOperator_left hi d α β)
    (JTMarkedStaircaseGraphs.left_restriction hi d (joined s t) s (parameter_left _ _ _ _ _ _) hsl)

include htr in
private theorem pushed_right :
    (tripleRightV T (single 1) U ▷ J.obj (degree n)) ≫ pushed α β d s t ≫
      J.map (rightTarget α β d hj) = (U.toSSet ◁ fold n) ≫ t ≫ J.map β := by
  rw [← Category.assoc (U.toSSet ◁ fold n)]
  exact restriction_postcomp _ _ _ _ _ _ _ (JTMarkedStaircaseGraphs.stepOperator_right hj d α β)
    (JTMarkedStaircaseGraphs.right_restriction hj d (joined s t) t (parameter_right _ _ _ _ _ _) htr)

include hs hsl in
private theorem pulled_left :
    (tripleRightT T (single 1) U ▷ J.obj (degree n)) ≫ pulled f g a α β d s' t' ≫
      J.map (leftTarget α β d hi) = (T.toSSet ◁ fold n) ≫ s ≫ J.map α := by
  have he : (tripleRightT T (single 1) U ▷ J.obj n) ≫ pull f g a (joined s' t') =
      (s ≫ J.map α) ≫ J.map (leftIn k' l') := by
    have h : (tripleRightT T' (single 1) U' ⊗ₘ 𝟙 (J.obj n')) ≫ joined s' t' =
        s' ≫ J.map (leftIn k' l') := parameter_left _ _ _ _ _ _
    rw [← tensorHom_id, pull_left, h, ← Category.assoc, hs]
  have hb (q p v) : coord k' q ((s ≫ J.map α).app q p) v ≤ α.toOrderHom i₀ := by
    change coord k' q ((J.map α).app q (s.app q p)) v ≤ _
    rw [coord_map]
    exact α.toOrderHom.monotone (hsl q p v)
  unfold pulled
  rw [pull_step, JTMarkedStaircaseGraphs.left_restriction (α.toOrderHom.monotone hi) (cut α β d)
    (pull f g a (joined s' t')) (s ≫ J.map α) he hb]

include ht htr in
private theorem pulled_right :
    (tripleRightV T (single 1) U ▷ J.obj (degree n)) ≫ pulled f g a α β d s' t' ≫
      J.map (rightTarget α β d hj) = (U.toSSet ◁ fold n) ≫ t ≫ J.map β := by
  have he : (tripleRightV T (single 1) U ▷ J.obj n) ≫ pull f g a (joined s' t') =
      (t ≫ J.map β) ≫ J.map (rightIn k' l') := by
    have h : (tripleRightV T' (single 1) U' ⊗ₘ 𝟙 (J.obj n')) ≫ joined s' t' =
        t' ≫ J.map (rightIn k' l') := parameter_right _ _ _ _ _ _
    rw [← tensorHom_id, pull_right, h, ← Category.assoc, ht]
  have hb (q p v) : β.toOrderHom j₁ ≤ coord l' q ((t ≫ J.map β).app q p) v := by
    change _ ≤ coord l' q ((J.map β).app q (t.app q p)) v
    rw [coord_map]
    exact β.toOrderHom.monotone (htr q p v)
  unfold pulled
  rw [pull_step, JTMarkedStaircaseGraphs.right_restriction (β.toOrderHom.monotone hj) (cut α β d)
    (pull f g a (joined s' t')) (t ≫ J.map β) he hb]

variable {W : Source} {x z y : Vertex W}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)
variable (u : (L W x z T').obj (op k')) (v : (L W z y U').obj (op l'))

private abbrev uNative := ((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).app (op k') u
private abbrev vNative := ((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).app (op l') v
private abbrev targetInputs :=
  stepInputs (α.toOrderHom.monotone hi) (β.toOrderHom.monotone hj) (cut α β d) u v
private abbrev sharedInputs := JTBinaryPrismNativeLabels.restrictInputs f g (targetInputs α β d hi hj u v)

variable (hSu : realizeProduct W k s (orderedLabel W x z T k ((L W x z T).map α.op (uNative f u))) =
  fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
variable (hTv : realizeProduct W l t (orderedLabel W z y U l ((L W z y U).map β.op (vNative g v))) =
  fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map)

include hs ht hsl htr hSu hTv in
/-- Pushing the source graph and pulling the target graph agree after both
side restrictions. Their full interpolation is therefore over the original
raw wedge, even if the coefficient operators identify vertices at the cut. -/
theorem interpolation_over_wedge :
    realizeInputs (sharedInputs f g α β d hi hj u v)
      (JTDoubledGraphTime.extendPair (pushed α β d s t) (pulled f g a α β d s' t')) =
      fst (code T U).toSSet (J.obj (degree (degree n))) ≫ (collapse c e).map ≫
        (NecklacesOver.wedge P Q).map := by
  unfold sharedInputs targetInputs
  rw [JTMarkedStaircaseGraphs.stepInputs_native]
  apply JTSharedCoefficientGraphPair.pair_over_wedge (leftTarget α β d hi) (rightTarget α β d hj)
    (uNative f u) (vNative g v) c e _ _
    ((T.toSSet ◁ fold n) ≫ s ≫ J.map α) ((U.toSSet ◁ fold n) ≫ t ≫ J.map β)
  · exact pushed_left α β d s t hi hsl
  · exact pulled_left f g a α β d s s' t' hs hi hsl
  · exact pushed_right α β d s t hj htr
  · exact pulled_right f g a α β d t s' t' ht hj htr
  · rw [← realizeProduct_reindexTime, realizeOrderedProduct_reindex, hSu, whiskerLeft_fst_assoc]
  · rw [← realizeProduct_reindexTime, realizeOrderedProduct_reindex, hTv, whiskerLeft_fst_assoc]

section Evaluation

variable (c' : T' ⟶ P.code) (e' : U' ⟶ Q.code)

private abbrev sourceInputs := stepInputs hi hj d ((L W x z T).map α.op (uNative f u))
  ((L W z y U).map β.op (vNative g v))

private abbrev sourceParameter := stepParameter (joined s t) d
private abbrev targetParameter := stepParameter (joined s' t') (cut α β d)

private abbrev cylinderOperator :=
  NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (code T U, degree n) ⟶ (code T' U', degree n') from (sideMap f g, operator a))

variable (hf : f ≫ c' = c) (hg : g ≫ e' = e)
variable (h₀ : realizeInputs (sourceInputs f g α β d hi hj u v) (sourceParameter d s t) =
  fst (code T U).toSSet (J.obj (degree n)) ≫ (collapse c e).map ≫ (NecklacesOver.wedge P Q).map)
variable (h₁ : realizeInputs (targetInputs α β d hi hj u v) (targetParameter α β d s' t') =
  fst (code T' U').toSSet (J.obj (degree n')) ≫ (collapse c' e').map ≫ (NecklacesOver.wedge P Q).map)

include hf hg hs ht hsl htr hSu hTv in
/-- Over one native/time arrow, the two actual fixed-target evaluations
are homotopic after singular realization, including when a cut collapses.
The target evaluation is precomposed with the full reduced cylinder operator. -/
def evaluationHomotopy : SSet.Homotopy
    (R.map (nerveMap (evaluate (NecklacesOver.wedge P Q) (collapse c e)
      (sourceInputs f g α β d hi hj u v) (sourceParameter d s t) h₀)))
    (R.map (nerveMap (CostructuredArrow.map (cylinderOperator f g a) ⋙
      evaluate (NecklacesOver.wedge P Q) (collapse c' e') (targetInputs α β d hi hj u v)
        (targetParameter α β d s' t') h₁))) := by
  let A := NecklacesOver.wedge P Q
  let D := sharedInputs f g α β d hi hj u v
  let p₀ := sourceParameter d s t
  let p₁ := pulled f g a α β d s' t'
  let p := JTDoubledGraphTime.extendPair (pushed α β d s t) p₁
  let r := stepOperator d α β
  let h := interpolation_over_wedge f g a α β d s t s' t' hs ht hi hj hsl htr
    c e u v hSu hTv
  have hL : ((code T U).toSSet ◁ J.map (leftIn (degree n) (degree n))) ≫ p = p₀ ≫ J.map r :=
    JTDoubledGraphTime.extendPair_left _ _
  have hR : ((code T U).toSSet ◁ J.map (rightIn (degree n) (degree n))) ≫ p = p₁ ≫ J.map (𝟙 _) := by
    rw [J.map_id, Category.comp_id]
    exact JTDoubledGraphTime.extendPair_right _ _
  let hRight := restrict_raw A (collapse c e) D (𝟙 _) (rightIn (degree n) (degree n)) p p₁ h hR
  have hp : ((sideMap f g).map ⊗ₘ J.map (operator a)) ≫ targetParameter α β d s' t' =
      p₁ ≫ J.map (𝟙 _) := by
    rw [J.map_id, Category.comp_id]
    rfl
  let comparison := compareNative A f g (𝟙 _) (targetInputs α β d hi hj u v) (operator a)
    (collapse c e) (collapse c' e') p₁ (targetParameter α β d s' t')
    (JTBinaryPrismSideTransport.collapse_sideMap f g hf hg) hp hRight h₁
  let H := FiniteLastVertexFactor.homotopy_of_roof
    (compare A (collapse c e) D r (leftIn (degree n) (degree n)) p p₀ h hL)
    (compare A (collapse c e) D (𝟙 _) (rightIn (degree n) (degree n)) p p₁ h hR)
    (JTHomotopyTargetComma.fiber_point_GW_at (code T U) (degree (degree n)))
  have hInputs : reindex r D = sourceInputs f g α β d hi hj u v :=
    JTMarkedStaircaseGraphs.stepInputs_transport hi hj d α β f g u v
  exact (H.congr (congrArg (fun F ↦ R.map (nerveMap F))
    (evaluate_congr A (collapse c e) (reindex r D) p₀ hInputs)) rfl).trans
      (natTransHomotopyR comparison)

end Evaluation

section Factorizations

variable {k'' l'' : SimplexCategory}
variable (α' : k' ⟶ k'') (β' : l' ⟶ l'')

private abbrev throughStage := pulled f g a α β d s' t' ≫
  J.map (stepOperator (cut α β d) α' β')

private theorem cut_comp : cut α' β' (cut α β d) = cut (α ≫ α') (β ≫ β') d :=
  SimplexCategory.congr_toOrderHom_apply (JTParameterBlockOperators.map_comp α α' β β') d

/-- Changing both ends of an intermediate comparison is exact when the
native/time maps and coefficient factorizations are composed. -/
theorem throughStage_change_endpoints {T₀ U₀ : NecklaceCode} {n₀ k₀ l₀ k₃ l₃ : SimplexCategory}
    (f₀ : T₀ ⟶ T) (g₀ : U₀ ⟶ U) (a₀ : n₀ ⟶ n) (A₀ : k₀ ⟶ k) (B₀ : l₀ ⟶ l)
    (d₀ : Fin ((common k₀ l₀).len + 1)) (A₃ : k'' ⟶ k₃) (B₃ : l'' ⟶ l₃) :
    pull f₀ g₀ (operator a₀) (throughStage f g a α β (cut A₀ B₀ d₀) s' t' α' β') ≫
      J.map (stepOperator (cut α' β' (cut α β (cut A₀ B₀ d₀))) A₃ B₃) =
    throughStage (f₀ ≫ f) (g₀ ≫ g) (a₀ ≫ a) (A₀ ≫ α) (B₀ ≫ β) d₀ s' t'
      (α' ≫ A₃) (β' ≫ B₃) := by
  unfold throughStage pulled
  rw [JTSharedCoefficientNativeParameter.pull_postcomp, Category.assoc, ← J.map_comp,
    JTMarkedStaircaseGraphs.stepOperator_comp, JTSharedCoefficientNativeParameter.pull_comp,
    cut_comp A₀ B₀ d₀ α β]
  have ha : operator a₀ ≫ operator a = operator (a₀ ≫ a) :=
    JTParameterBlockOperators.map_comp a₀ a a₀ a
  rw [ha]

include hs hsl in
private theorem throughStage_left :
    (tripleRightT T (single 1) U ▷ J.obj (degree n)) ≫
      throughStage f g a α β d s' t' α' β' ≫ J.map (leftTarget (α ≫ α') (β ≫ β') d hi) =
      (T.toSSet ◁ fold n) ≫ s ≫ J.map (α ≫ α') := by
  have hh : stepOperator (cut α β d) α' β' ≫ leftTarget (α ≫ α') (β ≫ β') d hi =
      leftTarget α β d hi ≫ α' := by
    unfold leftTarget
    rw [← cut_comp α β d α' β']
    exact JTMarkedStaircaseGraphs.stepOperator_left (α.toOrderHom.monotone hi) (cut α β d) α' β'
  have hp := restriction_postcomp _ _ _ _ _ _ _ hh (pulled_left f g a α β d s s' t' hs hi hsl)
  simpa only [Category.assoc, J.map_comp] using hp

include ht htr in
private theorem throughStage_right :
    (tripleRightV T (single 1) U ▷ J.obj (degree n)) ≫
      throughStage f g a α β d s' t' α' β' ≫ J.map (rightTarget (α ≫ α') (β ≫ β') d hj) =
      (U.toSSet ◁ fold n) ≫ t ≫ J.map (β ≫ β') := by
  have hh : stepOperator (cut α β d) α' β' ≫ rightTarget (α ≫ α') (β ≫ β') d hj =
      rightTarget α β d hj ≫ β' := by
    unfold rightTarget
    rw [← cut_comp α β d α' β']
    exact JTMarkedStaircaseGraphs.stepOperator_right (β.toOrderHom.monotone hj) (cut α β d) α' β'
  have hp := restriction_postcomp _ _ _ _ _ _ _ hh (pulled_right f g a α β d t s' t' ht hj htr)
  simpa only [Category.assoc, J.map_comp] using hp

variable (A : k ⟶ k'') (B : l ⟶ l'')

/-- One intermediate stage, with its full native and time maps from the
source and its two coefficient factorizations through to the final stage. -/
structure Stage where
  leftCode : NecklaceCode
  rightCode : NecklaceCode
  timeDegree : SimplexCategory
  leftDegree : SimplexCategory
  rightDegree : SimplexCategory
  leftMap : T ⟶ leftCode
  rightMap : U ⟶ rightCode
  timeMap : n ⟶ timeDegree
  leftOperator : k ⟶ leftDegree
  rightOperator : l ⟶ rightDegree
  leftFinal : leftDegree ⟶ k''
  rightFinal : rightDegree ⟶ l''
  left_comp : leftOperator ≫ leftFinal = A
  right_comp : rightOperator ≫ rightFinal = B
  leftGraph : leftCode.toSSet ⊗ J.obj timeDegree ⟶ J.obj leftDegree
  rightGraph : rightCode.toSSet ⊗ J.obj timeDegree ⟶ J.obj rightDegree
  left_square : (leftMap.map ⊗ₘ J.map timeMap) ≫ leftGraph = s ≫ J.map leftOperator
  right_square : (rightMap.map ⊗ₘ J.map timeMap) ≫ rightGraph = t ≫ J.map rightOperator

include hsl htr in
/-- Pull any intermediate staircase back to the source code and time,
then push it to the final coefficient. Both final restrictions are fixed. -/
def stageGraph (D : Stage s t A B) : JTFiniteGraphWedgeEvaluation.Graph
    (leftTarget A B d hi) (rightTarget A B d hj)
    ((T.toSSet ◁ fold n) ≫ s ≫ J.map A) ((U.toSSet ◁ fold n) ≫ t ≫ J.map B) := by
  let p := throughStage D.leftMap D.rightMap D.timeMap D.leftOperator D.rightOperator d
    D.leftGraph D.rightGraph D.leftFinal D.rightFinal
  refine ⟨p, ?_, ?_⟩
  · have h := throughStage_left D.leftMap D.rightMap D.timeMap D.leftOperator D.rightOperator d
      s D.leftGraph D.rightGraph D.left_square hi hsl D.leftFinal D.rightFinal
    rw [D.left_comp, D.right_comp] at h
    exact h
  · have h := throughStage_right D.leftMap D.rightMap D.timeMap D.leftOperator D.rightOperator d
      t D.leftGraph D.rightGraph D.right_square hj htr D.leftFinal D.rightFinal
    rw [D.left_comp, D.right_comp] at h
    exact h

include hsl htr in
/-- All stages of one finite factorization diagram give one object of the
exact graph-choice index over the common source and final coefficient. -/
def stageFamily {q : ℕ} (D : Fin (q + 1) → Stage s t A B) :=
  JTGraphChoiceIndex.ofFamily (fun i ↦ stageGraph d s t hi hj hsl htr A B (D i))

include hsl htr in
theorem stageFamily_vertex {q : ℕ} (D : Fin (q + 1) → Stage s t A B) (i : Fin (q + 1)) :
    JTGraphChoiceIndex.vertex (stageFamily d s t hi hj hsl htr A B D) i =
      stageGraph d s t hi hj hsl htr A B (D i) := rfl

end Factorizations

end

end DaggerModels.PartII.JTMarkedStaircaseTransport
