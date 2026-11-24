import DaggerModelsPartII.JTMarkedParameterBlocks
import DaggerModelsPartII.JTBinaryPrismLabelOperators
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-! Ordered binary labels using seam vertices transported by arbitrary coefficient maps. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTMarkedBinaryLabels

open JTParameterBlocks (common)
open JTMarkedParameterBlocks (leftMarked rightMarked leftMarked_map rightMarked_map leftClip rightClip)
open JTOrderedLabelBinaryGlue (Inputs orderedTriplePoint orderedTriplePoint_map reindex)
open OrderedNecklaceVertexPoints (boundaryPoint)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open JTBinaryPrismRealization (realizeProduct realizeOrderedProduct_reindex)
open JTRealizedLabelEndpoints (orderedLabel)
open DaggerChosenRigidificationNecklace.NecklaceCode (single tripleRightT tripleRightV)
open JTCodiscreteParameterPairing (coord coord_map)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {k l k' l' : SimplexCategory}

/-- Pull back the two ordered labels to the common ordinal with marked clamps. -/
def inputs (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) : Inputs W T U (common k l) x z y where
  left := (L W x z T).map (leftMarked k l i).op u
  right := (L W z y U).map (rightMarked k l j).op v

variable (u : (L W x z T).obj (op k')) (v : (L W z y U).obj (op l'))
variable (a : k ⟶ k') (b : l ⟶ l') (i : Fin (k.len + 1)) (j : Fin (l.len + 1))

private theorem inputs_map :
    reindex (JTParameterBlockOperators.map a b)
      (inputs u v (a.toOrderHom i) (b.toOrderHom j)) =
      inputs ((L W x z T).map a.op u) ((L W z y U).map b.op v) i j := by
  refine congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := common k l)
    (x := x) (z := z) (y := y)) ?_ ?_
  · change (L W x z T).map (JTParameterBlockOperators.map a b).op
        ((L W x z T).map (leftMarked k' l' (a.toOrderHom i)).op u) =
        (L W x z T).map (leftMarked k l i).op ((L W x z T).map a.op u)
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, leftMarked_map a b i]
  · change (L W z y U).map (JTParameterBlockOperators.map a b).op
        ((L W z y U).map (rightMarked k' l' (b.toOrderHom j)).op v) =
        (L W z y U).map (rightMarked k l j).op ((L W z y U).map b.op v)
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, rightMarked_map a b j]

/-- The whole joined label is natural for arbitrary coefficient maps when
the seam vertices are transported by those maps. -/
theorem label_map :
    (L W x y (JTOrderedLabelBinaryGlue.code T U)).map (JTParameterBlockOperators.map a b).op
        (orderedTriplePoint (inputs u v (a.toOrderHom i) (b.toOrderHom j))) =
      orderedTriplePoint (inputs ((L W x z T).map a.op u) ((L W z y U).map b.op v) i j) := by
  rw [orderedTriplePoint_map, inputs_map]

/-- Clipping a coefficient on the left leaves every parameter already bounded by that mark intact. -/
theorem leftClip_parameter {X : SSet.{0}} (p : X ⟶ J.obj k) (i : Fin (k.len + 1))
    (h : ∀ q s v, coord k q (p.app q s) v ≤ i) : p ≫ J.map (leftClip k i) = p := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q s v
  change coord k q ((J.map (leftClip k i)).app q (p.app q s)) v = _
  rw [coord_map]
  exact min_eq_left (h q s v)

/-- Clipping a coefficient on the right leaves every parameter already bounded by that mark intact. -/
theorem rightClip_parameter {X : SSet.{0}} (p : X ⟶ J.obj l) (j : Fin (l.len + 1))
    (h : ∀ q s v, j ≤ coord l q (p.app q s) v) : p ≫ J.map (rightClip l j) = p := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q s v
  change coord l q ((J.map (rightClip l j)).app q (p.app q s)) v = _
  rw [coord_map]
  exact max_eq_left (h q s v)

/-- The original coefficient map carries an upper mark to an upper mark of the transported
full parameter. -/
theorem upperBound_map {X : SSet.{0}} (p : X ⟶ J.obj k) (a : k ⟶ k')
    (i : Fin (k.len + 1)) (hi : ∀ q s v, coord k q (p.app q s) v ≤ i) :
    ∀ q s v, coord k' q ((p ≫ J.map a).app q s) v ≤ a.toOrderHom i := by
  intro q s v
  change coord k' q ((J.map a).app q (p.app q s)) v ≤ _
  rw [coord_map]
  exact a.toOrderHom.monotone (hi q s v)

/-- The original coefficient map carries a lower mark to a lower mark of the transported
full parameter. -/
theorem lowerBound_map {X : SSet.{0}} (p : X ⟶ J.obj l) (b : l ⟶ l')
    (j : Fin (l.len + 1)) (hj : ∀ q s v, j ≤ coord l q (p.app q s) v) :
    ∀ q s v, b.toOrderHom j ≤ coord l' q ((p ≫ J.map b).app q s) v := by
  intro q s v
  change _ ≤ coord l' q ((J.map b).app q (p.app q s)) v
  rw [coord_map]
  exact b.toOrderHom.monotone (hj q s v)

/-- When the full parameter lies below the mark, clipping the original
left coefficient leaves its realized map into the raw input unchanged. -/
theorem leftClip_realize {X : SSet.{0}} (p : T.toSSet ⊗ X ⟶ J.obj k)
    (u : (L W x y T).obj (op k)) (i : Fin (k.len + 1))
    (hi : ∀ q s v, coord k q (p.app q s) v ≤ i) :
    realizeProduct W k p (orderedLabel W x y T k ((L W x y T).map (leftClip k i).op u)) =
      realizeProduct W k p (orderedLabel W x y T k u) := by
  rw [← realizeOrderedProduct_reindex (leftClip k i) p u, leftClip_parameter p i hi]

/-- When the full parameter lies above the mark, clipping the original
right coefficient leaves its realized map into the raw input unchanged. -/
theorem rightClip_realize {X : SSet.{0}} (p : T.toSSet ⊗ X ⟶ J.obj l)
    (u : (L W x y T).obj (op l)) (j : Fin (l.len + 1))
    (hj : ∀ q s v, j ≤ coord l q (p.app q s) v) :
    realizeProduct W l p (orderedLabel W x y T l ((L W x y T).map (rightClip l j).op u)) =
      realizeProduct W l p (orderedLabel W x y T l u) := by
  rw [← realizeOrderedProduct_reindex (rightClip l j) p u, rightClip_parameter p j hj]

private theorem inputs_eq_blockInputs (u : (L W x z T).obj (op k))
    (v : (L W z y U).obj (op l)) (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    inputs u v i j = JTBinaryPrismRealization.blockInputs
      ((L W x z T).map (leftClip k i).op u) ((L W z y U).map (rightClip l j).op v) := by
  refine congrArg₂ (Inputs.mk (W := W) (T := T) (U := U) (k := common k l)
    (x := x) (z := z) (y := y)) ?_ ?_
  · exact FunctorToTypes.map_comp_apply (L W x z T)
      (leftClip k i).op (JTParameterBlocks.leftRet k l).op u
  · exact FunctorToTypes.map_comp_apply (L W z y U)
      (rightClip l j).op (JTParameterBlocks.rightRet k l).op v

section RawWedge

open JTOrderedLabelBinaryGlue (code)
open JTParameterBlocks (leftIn rightIn)

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {X : SSet.{0}}

/-- Marked gluing retains the full original raw equation whenever the two
marks bound the corresponding original parameters on all simplices. -/
theorem raw_over_wedge (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1))
    (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (s : T.toSSet ⊗ X ⟶ J.obj k) (t : U.toSSet ⊗ X ⟶ J.obj l)
    (p : (code T U).toSSet ⊗ X ⟶ J.obj (common k l))
    (hpL : (tripleRightT T (single 1) U ⊗ₘ 𝟙 X) ≫ p = s ≫ J.map (leftIn k l))
    (hpR : (tripleRightV T (single 1) U ⊗ₘ 𝟙 X) ≫ p = t ≫ J.map (rightIn k l))
    (hi : ∀ q a w, coord k q (s.app q a) w ≤ i)
    (hj : ∀ q a w, j ≤ coord l q (t.app q a) w)
    (hs : realizeProduct W k s (orderedLabel W x z T k u) = fst T.toSSet X ≫ c.map ≫ P.map)
    (ht : realizeProduct W l t (orderedLabel W z y U l v) = fst U.toSSet X ≫ e.map ≫ Q.map) :
    realizeProduct W (common k l) p
      (orderedLabel W x y (code T U) (common k l) (orderedTriplePoint (inputs u v i j))) =
      fst (code T U).toSSet X ≫ (JTBinaryPrismRealization.collapse c e).map ≫
        (NecklacesOver.wedge P Q).map := by
  rw [inputs_eq_blockInputs]
  exact JTBinaryPrismRealization.raw_over_wedge _ _ p c e s t hpL hpR
    ((leftClip_realize s u i hi).trans hs) ((rightClip_realize t v j hj).trans ht)

end RawWedge

end

end DaggerModels.PartII.JTMarkedBinaryLabels
