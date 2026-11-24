import DaggerModelsPartII.JTMarkedBinaryLabels
import DaggerModelsPartII.JTOrdinalStaircaseNaturality
import DaggerModelsPartII.JTDoubledGraphTime
import DaggerModelsPartII.JTBinaryPrismNativeLabels

/-! Full graph comparisons along the staircase between two admissible pairs of marks. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTMarkedStaircaseGraphs

open JTParameterBlocks (common leftIn rightIn)
open JTMarkedParameterBlocks (leftMarked rightMarked leftIn_leftMarked rightIn_rightMarked)
open JTMarkedBinaryLabels (leftClip_parameter rightClip_parameter)
open JTOrdinalStaircaseComparison (before after path before_path after_path adjacent first_endpoint last_endpoint)
open JTOrderedLabelBinaryGlue (Inputs code reindex)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTBinaryPrismRealization (realizeProduct realizeInputs realizeInputs_over_wedge
  realizeOrderedProduct_reindex realizeProduct_reindexTime)
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

private theorem path_over {X : SSet.{0}} {K B : SimplexCategory}
    (f₀ f₁ : K ⟶ B) (h : ∀ u, f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t : Fin (K.len + 1)) (p : X ⟶ J.obj K) (s : X ⟶ J.obj B)
    (h₀ : p ≫ J.map f₀ = s) (h₁ : p ≫ J.map f₁ = s) :
    p ≫ J.map (before K t ≫ path K B f₀ f₁ h t) = s ∧
      p ≫ J.map (after K t ≫ path K B f₀ f₁ h t) = s := by
  have hc (q : SimplexCategoryᵒᵖ) (x : X.obj q) (v : Fin (q.unop.len + 1))
      (f : K ⟶ B) (hf : p ≫ J.map f = s) :
      f.toOrderHom (coord K q (p.app q x) v) = coord B q (s.app q x) v := by
    have e := congrArg (fun u ↦ coord B q u v) (congrFun (NatTrans.congr_app hf q) x)
    change coord B q ((J.map f).app q (p.app q x)) v = _ at e
    rw [coord_map] at e
    exact e
  constructor
  · apply JTCodiscreteParameterPairing.hom_ext
    intro q x v
    change coord B q ((J.map (before K t ≫ path K B f₀ f₁ h t)).app q (p.app q x)) v = _
    rw [coord_map, before_path]
    split_ifs
    · exact hc q x v f₀ h₀
    · exact hc q x v f₁ h₁
  · apply JTCodiscreteParameterPairing.hom_ext
    intro q x v
    change coord B q ((J.map (after K t ≫ path K B f₀ f₁ h t)).app q (p.app q x)) v = _
    rw [coord_map, after_path]
    split_ifs
    · exact hc q x v f₀ h₀
    · exact hc q x v f₁ h₁

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode} {k l n : SimplexCategory}

private abbrev K (k l : SimplexCategory) := common k l
private abbrev H (k l : SimplexCategory) := ⦋(K k l).len + 1⦌
private abbrev N (n : SimplexCategory) := JTDoubledGraphTime.degree n
private abbrev SL (T U : NecklaceCode) := tripleRightT T (single 1) U
private abbrev SR (T U : NecklaceCode) := tripleRightV T (single 1) U

variable {i₀ i₁ : Fin (k.len + 1)} {j₀ j₁ : Fin (l.len + 1)}
variable (hi : i₀ ≤ i₁) (hj : j₀ ≤ j₁) (d : Fin ((K k l).len + 1))

/-- The left coefficient restriction along an actual staircase step. -/
def leftPath : H k l ⟶ k :=
  path (K k l) k (leftMarked k l i₀) (leftMarked k l i₁)
    (fun u ↦ min_le_min_left ((JTParameterBlocks.leftRet k l).toOrderHom u) hi) d

/-- The right coefficient restriction along an actual staircase step. -/
def rightPath : H k l ⟶ l :=
  path (K k l) l (rightMarked k l j₀) (rightMarked k l j₁)
    (fun u ↦ max_le_max_left ((JTParameterBlocks.rightRet k l).toOrderHom u) hj) d

private def inputsOf {m : SimplexCategory} (a : m ⟶ k) (b : m ⟶ l)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) : Inputs W T U m x z y where
  left := (L W x z T).map a.op u
  right := (L W z y U).map b.op v

/-- Use the two actual ordered labels over the shared staircase simplex. -/
def stepInputs (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) :
    Inputs W T U (H k l) x z y :=
  inputsOf (leftPath hi d) (rightPath hj d) u v

section Transport

variable {k' l' : SimplexCategory} (a : k ⟶ k') (b : l ⟶ l')

private abbrev block := JTParameterBlockOperators.map a b
private abbrev cut : Fin ((K k' l').len + 1) := (block a b).toOrderHom d

/-- The phase-preserving staircase operator induced by two coefficient maps. -/
def stepOperator : H k l ⟶ H k' l' :=
  JTOrdinalStaircaseNaturality.map _ _ (block a b) d

theorem stepOperator_id : stepOperator d (𝟙 k) (𝟙 l) = 𝟙 (H k l) := by
  unfold stepOperator block
  rw [JTParameterBlockOperators.map_id, JTOrdinalStaircaseNaturality.map_id]

theorem stepOperator_comp {k'' l'' : SimplexCategory} (a' : k' ⟶ k'') (b' : l' ⟶ l'') :
    stepOperator d a b ≫ stepOperator (cut d a b) a' b' = stepOperator d (a ≫ a') (b ≫ b') := by
  unfold stepOperator
  rw [JTOrdinalStaircaseNaturality.map_comp, JTParameterBlockOperators.map_comp]

/-- The left coefficient restriction transports even when vertices coalesce. -/
theorem stepOperator_left :
    stepOperator d a b ≫ leftPath (a.toOrderHom.monotone hi) (cut d a b) = leftPath hi d ≫ a := by
  exact JTOrdinalStaircaseNaturality.path_map _ _ _ _ (block a b) a _ _ _ _ _ _
    (JTMarkedParameterBlocks.leftMarked_map a b i₀)
    (JTMarkedParameterBlocks.leftMarked_map a b i₁) d

/-- The right coefficient restriction transports even when vertices coalesce. -/
theorem stepOperator_right :
    stepOperator d a b ≫ rightPath (b.toOrderHom.monotone hj) (cut d a b) = rightPath hj d ≫ b := by
  exact JTOrdinalStaircaseNaturality.path_map _ _ _ _ (block a b) b _ _ _ _ _ _
    (JTMarkedParameterBlocks.rightMarked_map a b j₀)
    (JTMarkedParameterBlocks.rightMarked_map a b j₁) d

private theorem transportLabel {S S' : NecklaceCode} {v₀ v₁ : Vertex W}
    {m m' B B' : SimplexCategory} (f : S ⟶ S') (c : m ⟶ m')
    (p : m ⟶ B) (p' : m' ⟶ B') (r : B ⟶ B') (h : c ≫ p' = p ≫ r)
    (u : (L W v₀ v₁ S').obj (op B')) :
    (L W v₀ v₁ S).map c.op
      (((orderedNecklaceLabels W (boundaryPoint W v₀ v₁)).map f.op).app (op m')
        ((L W v₀ v₁ S').map p'.op u)) =
    (L W v₀ v₁ S).map p.op ((L W v₀ v₁ S).map r.op
      (((orderedNecklaceLabels W (boundaryPoint W v₀ v₁)).map f.op).app (op B') u)) := by
  have hn := congrFun (((orderedNecklaceLabels W (boundaryPoint W v₀ v₁)).map f.op).naturality
    p'.op) u
  change ((orderedNecklaceLabels W (boundaryPoint W v₀ v₁)).map f.op).app (op m')
      ((L W v₀ v₁ S').map p'.op u) =
    (L W v₀ v₁ S).map p'.op
      (((orderedNecklaceLabels W (boundaryPoint W v₀ v₁)).map f.op).app (op B') u) at hn
  rw [hn, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, h]

/-- Restricting the staircase labels along the two native sides applies
the same native restrictions to the two original inputs. -/
theorem stepInputs_native {T' U' : NecklaceCode} (f : T ⟶ T') (g : U ⟶ U')
    (u : (L W x z T').obj (op k)) (v : (L W z y U').obj (op l)) :
    JTBinaryPrismNativeLabels.restrictInputs f g (stepInputs hi hj d u v) =
      stepInputs hi hj d
        (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).app (op k) u)
        (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).app (op l) v) := by
  exact congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := H k l)
      (x := x) (z := z) (y := y))
    (congrFun (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).naturality
      (leftPath hi d).op) u)
    (congrFun (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).naturality
      (rightPath hj d).op) v)

/-- Native side maps and arbitrary coefficient maps transport the whole
ordered input of the staircase step. -/
theorem stepInputs_transport {T' U' : NecklaceCode} (f : T ⟶ T') (g : U ⟶ U')
    (u' : (L W x z T').obj (op k')) (v' : (L W z y U').obj (op l')) :
    reindex (stepOperator d a b) (JTBinaryPrismNativeLabels.restrictInputs f g
      (stepInputs (a.toOrderHom.monotone hi) (b.toOrderHom.monotone hj) (cut d a b) u' v')) =
    stepInputs hi hj d
      ((L W x z T).map a.op
        (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).app (op k') u'))
      ((L W z y U).map b.op
        (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).app (op l') v')) := by
  exact congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := H k l)
      (x := x) (z := z) (y := y))
    (transportLabel f _ _ _ a (stepOperator_left hi d a b) u')
    (transportLabel g _ _ _ b (stepOperator_right hj d a b) v')

end Transport

private theorem reindex_inputsOf {m m' : SimplexCategory} (f : m' ⟶ m) (a : m ⟶ k) (b : m ⟶ l)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) :
    reindex f (inputsOf a b u v) = inputsOf (f ≫ a) (f ≫ b) u v := by
  exact congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := m')
    (x := x) (z := z) (y := y))
    (FunctorToTypes.map_comp_apply (L W x z T) a.op f.op u).symm
    (FunctorToTypes.map_comp_apply (L W z y U) b.op f.op v).symm

/-- Consecutive staircase pieces restrict to the same actual ordered inputs. -/
theorem stepInputs_adjacent (d' : Fin ((K k l).len + 1)) (hdd' : d.val + 1 = d'.val)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) :
    reindex (before (K k l) d) (stepInputs hi hj d u v) =
      reindex (after (K k l) d') (stepInputs hi hj d' u v) := by
  simp only [stepInputs, reindex_inputsOf, leftPath, rightPath]
  rw [adjacent (K k l) k _ _ _ d d' hdd', adjacent (K k l) l _ _ _ d d' hdd']

/-- Starting at the last cut has the first pair of marks. -/
theorem stepInputs_last (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) :
    reindex (before (K k l) (Fin.last (K k l).len))
        (stepInputs hi hj (Fin.last (K k l).len) u v) =
      JTMarkedBinaryLabels.inputs u v i₀ j₀ := by
  simp only [stepInputs, reindex_inputsOf, leftPath, rightPath]
  rw [last_endpoint, last_endpoint]
  rfl

/-- Ending at the first cut has the second pair of marks. -/
theorem stepInputs_first (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) :
    reindex (after (K k l) 0) (stepInputs hi hj 0 u v) =
      JTMarkedBinaryLabels.inputs u v i₁ j₁ := by
  simp only [stepInputs, reindex_inputsOf, leftPath, rightPath]
  rw [first_endpoint, first_endpoint]
  rfl

/-- The whole graph with the two coordinate placements of the staircase. -/
def stepParameter (p : (code T U).toSSet ⊗ J.obj n ⟶ J.obj (K k l))
    (d : Fin ((K k l).len + 1)) : (code T U).toSSet ⊗ J.obj (N n) ⟶ J.obj (H k l) :=
  JTDoubledGraphTime.extend p (before (K k l) d) (after (K k l) d)

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (p : (code T U).toSSet ⊗ J.obj n ⟶ J.obj (K k l))
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
variable (hpL : (SL T U ▷ J.obj n) ≫ p = s ≫ J.map (leftIn k l))
variable (hpR : (SR T U ▷ J.obj n) ≫ p = t ≫ J.map (rightIn k l))
variable (hs : ∀ q a v, coord k q (s.app q a) v ≤ i₀)
variable (ht : ∀ q a v, j₁ ≤ coord l q (t.app q a) v)

include hpL hs in
/-- The staircase graph restricts to the original left graph after folding time. -/
theorem left_restriction :
    (SL T U ▷ J.obj (N n)) ≫ stepParameter p d ≫ J.map (leftPath hi d) =
      (T.toSSet ◁ JTDoubledGraphTime.fold n) ≫ s := by
  have h (i : Fin (k.len + 1)) (hi' : i₀ ≤ i) :
      ((SL T U ▷ J.obj n) ≫ p) ≫ J.map (leftMarked k l i) = s := by
    rw [hpL, Category.assoc, ← J.map_comp, leftIn_leftMarked]
    exact leftClip_parameter s i (fun q a v ↦ (hs q a v).trans hi')
  have hov := path_over (leftMarked k l i₀) (leftMarked k l i₁)
    (fun u ↦ min_le_min_left ((JTParameterBlocks.leftRet k l).toOrderHom u) hi) d
    ((SL T U ▷ J.obj n) ≫ p) s (h i₀ le_rfl) (h i₁ hi)
  exact JTDoubledGraphTime.extend_over p _ _ (SL T U) (leftPath hi d) s
    (by simpa only [Category.assoc, leftPath] using hov.1)
    (by simpa only [Category.assoc, leftPath] using hov.2)

include hpR ht in
/-- The staircase graph restricts to the original right graph after folding time. -/
theorem right_restriction :
    (SR T U ▷ J.obj (N n)) ≫ stepParameter p d ≫ J.map (rightPath hj d) =
      (U.toSSet ◁ JTDoubledGraphTime.fold n) ≫ t := by
  have h (j : Fin (l.len + 1)) (hj' : j ≤ j₁) :
      ((SR T U ▷ J.obj n) ≫ p) ≫ J.map (rightMarked k l j) = t := by
    rw [hpR, Category.assoc, ← J.map_comp, rightIn_rightMarked]
    exact rightClip_parameter t j (fun q a v ↦ hj'.trans (ht q a v))
  have hov := path_over (rightMarked k l j₀) (rightMarked k l j₁)
    (fun u ↦ max_le_max_left ((JTParameterBlocks.rightRet k l).toOrderHom u) hj) d
    ((SR T U ▷ J.obj n) ≫ p) t (h j₀ hj) (h j₁ le_rfl)
  exact JTDoubledGraphTime.extend_over p _ _ (SR T U) (rightPath hj d) t
    (by simpa only [Category.assoc, rightPath] using hov.1)
    (by simpa only [Category.assoc, rightPath] using hov.2)

include hpL hpR hs ht in
/-- Every mixed time simplex at a staircase step realizes to the fixed
raw target, including the whole connector and both original side maps. -/
theorem step_over_wedge (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
    (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (hs' : realizeProduct W k s (orderedLabel W x z T k u) = fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
    (ht' : realizeProduct W l t (orderedLabel W z y U l v) = fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map) :
    realizeInputs (stepInputs hi hj d u v) (stepParameter p d) =
      fst (code T U).toSSet (J.obj (N n)) ≫ (JTBinaryPrismRealization.collapse c e).map ≫
        (NecklacesOver.wedge P Q).map := by
  apply realizeInputs_over_wedge
  · change realizeProduct W (H k l) ((SL T U ▷ J.obj (N n)) ≫ stepParameter p d)
        (orderedLabel W x z T (H k l) ((L W x z T).map (leftPath hi d).op u)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc, left_restriction hi d p s hpL hs,
      ← realizeProduct_reindexTime, hs', whiskerLeft_fst_assoc]
  · change realizeProduct W (H k l) ((SR T U ▷ J.obj (N n)) ≫ stepParameter p d)
        (orderedLabel W z y U (H k l) ((L W z y U).map (rightPath hj d).op v)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc, right_restriction hj d p t hpR ht,
      ← realizeProduct_reindexTime, ht', whiskerLeft_fst_assoc]

end

end DaggerModels.PartII.JTMarkedStaircaseGraphs
