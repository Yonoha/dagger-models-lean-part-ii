import DaggerModelsPartII.JTParametrizedTargetFamilyJoin
import DaggerModelsPartII.JTMarkedBinaryLabels
import DaggerModelsPartII.JTSharedCoefficientEvaluation

/-! Gluing whole parametrized families at transported coefficient marks. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTMarkedParametrizedTargetFamilyJoin

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedLabelElements (label projection)
open JTBinaryPrismNativeLabels (orderedTriplePoint_native restrictInputs)
open JTOrderedLabelBinaryGlue (orderedTriplePoint)
open JTParameterBlocks (common leftIn rightIn)
open JTBinaryPrismParameter (sideMap)
open JTMarkedBinaryLabels (inputs)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y

variable {A : Type} [SmallCategory A]
variable {W : Source} {x z y : Vertex W}

private abbrev proj (a b : Vertex W) := projection W (boundaryPoint W a b)

abbrev degree {a b : Vertex W} (L : A ⥤ Index W a b) :=
  L ⋙ proj a b ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

/-- Choose one coefficient vertex at each object, carried by every original arrow. -/
structure Mark {a b : Vertex W} (L : A ⥤ Index W a b) where
  vertex : ∀ p, Fin (((degree L).obj p).len + 1)
  naturality : ∀ {p q} (f : p ⟶ q), ((degree L).map f).toOrderHom (vertex p) = vertex q

private theorem inputs_native {T U T' U' : NecklaceCode} {k l : SimplexCategory}
    (f : T ⟶ T') (g : U ⟶ U')
    (u : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T')).obj (op k))
    (v : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U')).obj (op l))
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    restrictInputs f g (inputs u v i j) =
      inputs (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).app (op k) u)
        (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).app (op l) v) i j := by
  refine congrArg₂ (JTOrderedLabelBinaryGlue.Inputs.mk (W := W) (T := T) (U := U)
    (k := common k l) (x := x) (z := z) (y := y)) ?_ ?_
  · exact congrFun (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).naturality
      (JTMarkedParameterBlocks.leftMarked k l i).op) u
  · exact congrFun (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).naturality
      (JTMarkedParameterBlocks.rightMarked k l j).op) v

variable (L : A ⥤ Index W x z) (R : A ⥤ Index W z y)
variable (i : Mark L) (j : Mark R)

private abbrev projected :=
  ((L ⋙ proj x z).prod' (R ⋙ proj z y)) ⋙ JTParametrizedTargetFamilyJoin.joinOperators

private abbrev joinedInputs (p : A) :=
  inputs (label W (boundaryPoint W x z) (L.obj p)) (label W (boundaryPoint W z y) (R.obj p))
    (i.vertex p) (j.vertex p)

private abbrev joinedPoint (p : A) := orderedTriplePoint (joinedInputs L R i j p)

set_option maxHeartbeats 400000 in
private theorem joinedPoint_map {p q : A} (f : p ⟶ q) :
    (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)).map
      (((projected L R).map f).op) (joinedPoint L R i j q) = joinedPoint L R i j p := by
  let a := (proj x z).map (L.map f)
  let b := (proj z y).map (R.map f)
  let k := (degree L).obj q
  let l := (degree R).obj q
  let u := label W (boundaryPoint W x z) (L.obj q)
  let v := label W (boundaryPoint W z y) (R.obj q)
  let O := orderedNecklaceLabels W (boundaryPoint W x y)
  let c := JTOrderedLabelBinaryGlue.code ((proj x z).obj (L.obj p)).1 ((proj z y).obj (R.obj p)).1
  let c' := JTOrderedLabelBinaryGlue.code ((proj x z).obj (L.obj q)).1 ((proj z y).obj (R.obj q)).1
  let uCode : c ⟶ c' := sideMap a.1 b.1
  let α := a.2
  let β := b.2
  change (O.obj (op c)).map (JTParameterBlockOperators.map α β).op
      ((O.map uCode.op).app (op (common k l))
        (orderedTriplePoint (inputs u v (i.vertex q) (j.vertex q)))) =
    joinedPoint L R i j p
  have hn := orderedTriplePoint_native a.1 b.1 (inputs u v (i.vertex q) (j.vertex q))
  change (O.map uCode.op).app (op (common k l))
      (orderedTriplePoint (inputs u v (i.vertex q) (j.vertex q))) = _ at hn
  rw [hn, inputs_native]
  have hi : α.toOrderHom (i.vertex p) = i.vertex q := i.naturality f
  have hj : β.toOrderHom (j.vertex p) = j.vertex q := j.naturality f
  rw [← hi, ← hj, JTMarkedBinaryLabels.label_map]
  have hL := OrderedLabelElements.label_map W (boundaryPoint W x z) (L.map f)
  have hR := OrderedLabelElements.label_map W (boundaryPoint W z y) (R.map f)
  let Oₗ := orderedNecklaceLabels W (boundaryPoint W x z)
  let Oᵣ := orderedNecklaceLabels W (boundaryPoint W z y)
  change (Oₗ.obj (op ((proj x z).obj (L.obj p)).1)).map α.op
      ((Oₗ.map a.1.op).app (op k) u) = _ at hL
  change (Oᵣ.obj (op ((proj z y).obj (R.obj p)).1)).map β.op
      ((Oᵣ.map b.1.op).app (op l) v) = _ at hR
  exact congrArg₂ (fun a b ↦ orderedTriplePoint (inputs a b (i.vertex p) (j.vertex p))) hL hR

/-- Glue the original labels, using transported marks in place of the ordinal endpoints. -/
def joinedLabels : A ⥤ Index W x y where
  obj p := op ⟨op ((projected L R).obj p), joinedPoint L R i j p⟩
  map f := Quiver.Hom.op ⟨((projected L R).map f).op, joinedPoint_map L R i j f⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((projected L R).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((projected L R).map_comp f g)

theorem joinedLabels_map {p q : A} (f : p ⟶ q) :
    (proj x y).map ((joinedLabels L R i j).map f) =
      (sideMap ((proj x z).map (L.map f)).1 ((proj z y).map (R.map f)).1,
        JTParameterBlockOperators.map ((degree L).map f) ((degree R).map f)) := rfl

/-- The left block transports any mark from the original left diagram. -/
def leftMark (a : Mark L) : Mark (joinedLabels L R i j) where
  vertex p := (leftIn ((degree L).obj p) ((degree R).obj p)).toOrderHom (a.vertex p)
  naturality {p q} f := by
    have h := SimplexCategory.congr_toOrderHom_apply
      (JTParameterBlockOperators.leftIn_map ((degree L).map f) ((degree R).map f)) (a.vertex p)
    change ((degree (joinedLabels L R i j)).map f).toOrderHom
        ((leftIn _ _).toOrderHom (a.vertex p)) =
      (leftIn _ _).toOrderHom (a.vertex q)
    change (JTParameterBlockOperators.map ((degree L).map f) ((degree R).map f)).toOrderHom
        ((leftIn _ _).toOrderHom (a.vertex p)) =
      (leftIn _ _).toOrderHom (a.vertex q)
    exact h.trans (congrArg (leftIn _ _).toOrderHom (a.naturality f))

/-- The right block transports any mark from the original right diagram. -/
def rightMark (b : Mark R) : Mark (joinedLabels L R i j) where
  vertex p := (rightIn ((degree L).obj p) ((degree R).obj p)).toOrderHom (b.vertex p)
  naturality {p q} f := by
    have h := SimplexCategory.congr_toOrderHom_apply
      (JTParameterBlockOperators.rightIn_map ((degree L).map f) ((degree R).map f)) (b.vertex p)
    change (JTParameterBlockOperators.map ((degree L).map f) ((degree R).map f)).toOrderHom
        ((rightIn _ _).toOrderHom (b.vertex p)) =
      (rightIn _ _).toOrderHom (b.vertex q)
    exact h.trans (congrArg (rightIn _ _).toOrderHom (b.naturality f))

section Families

open JTBinaryPrismRealization (collapse)
open JTBinaryPrismSideTransport (collapse_sideMap mixedParameterSquare)
open JTBinaryPrismTargetLift (parameter)

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {time : A ⥤ SimplexCategory}
variable (F : Family P L time) (G : Family Q R time)

/-- A mark is an upper bound for the full parametrized family, on every simplex. -/
def UpperBound {a b : Vertex W} {K : A ⥤ Index W a b}
    {T : NecklacesOver (Raw W) (rawVertex W a) (rawVertex W b)}
    (M : Family T K time) (u : Mark K) : Prop :=
  ∀ p q s v, coord ((degree K).obj p) q ((M.parameter p).app q s) v ≤ u.vertex p

/-- A mark is a lower bound for the full parametrized family, on every simplex. -/
def LowerBound {a b : Vertex W} {K : A ⥤ Index W a b}
    {T : NecklacesOver (Raw W) (rawVertex W a) (rawVertex W b)}
    (M : Family T K time) (u : Mark K) : Prop :=
  ∀ p q s v, u.vertex p ≤ coord ((degree K).obj p) q ((M.parameter p).app q s) v

variable (hi : UpperBound F i) (hj : LowerBound G j)

private theorem collapse_natural {a b : Vertex W} {K : A ⥤ Index W a b}
    {T : NecklacesOver (Raw W) (rawVertex W a) (rawVertex W b)}
    (M : Family T K time) {p q : A} (f : p ⟶ q) :
    ((proj a b).map (K.map f)).1 ≫ M.collapse.app q = M.collapse.app p := by
  have h := M.collapse.naturality f
  change ((proj a b).map (K.map f)).1 ≫ M.collapse.app q = M.collapse.app p ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

include hi hj in
set_option maxHeartbeats 500000 in
private theorem joined_raw (p : A) :
    (JTParametrizedTargetLiftTransport.graph (i := (joinedLabels L R i j).obj p)
      (parameter (F.parameter p) (G.parameter p))).right ≫
        ((DecoratedCylinderNecklacePresentation.underCocone W x y).app
          ((joinedLabels L R i j).obj p)).right =
      NecklaceCylinderAugmentation.augmentation
        (JTOrderedLabelBinaryGlue.code ((codes L).obj p) ((codes R).obj p)) (time.obj p) ≫
        (collapse (F.collapse.app p) (G.collapse.app p)).map ≫ (NecklacesOver.wedge P Q).map := by
  let l := label W (boundaryPoint W x z) (L.obj p)
  let r := label W (boundaryPoint W z y) (R.obj p)
  let k := (degree L).obj p
  let m := (degree R).obj p
  let T := (codes L).obj p
  let U := (codes R).obj p
  let S := J.obj (time.obj p)
  let s := F.parameter p
  let t := G.parameter p
  let c := F.collapse.app p
  let e := G.collapse.app p
  let b := parameter s t
  have hs := JTBinaryPrismParameter.parameter_left T U (common k m) S
    (s ≫ J.map (leftIn k m)) (t ≫ J.map (rightIn k m))
  have ht := JTBinaryPrismParameter.parameter_right T U (common k m) S
    (s ≫ J.map (leftIn k m)) (t ≫ J.map (rightIn k m))
  have h := JTMarkedBinaryLabels.raw_over_wedge l r (i.vertex p) (j.vertex p)
    c e s t b hs ht (hi p) (hj p) (JTParametrizedTargetFamilies.rawProduct F p)
    (JTParametrizedTargetFamilies.rawProduct G p)
  exact JTSharedCoefficientEvaluation.graph_raw (NecklacesOver.wedge P Q) (collapse c e)
    (joinedInputs L R i j p) b h

set_option maxHeartbeats 500000 in
/-- Glue the entire families over the original native wedge, including all
native, time and coefficient operators and both raw-value equations. -/
def join : Family (NecklacesOver.wedge P Q) (joinedLabels L R i j) time where
  collapse :=
    { app p := collapse (F.collapse.app p) (G.collapse.app p)
      naturality {p q} f := by
        change ((proj x y).map ((joinedLabels L R i j).map f)).1 ≫
            collapse (F.collapse.app q) (G.collapse.app q) =
          collapse (F.collapse.app p) (G.collapse.app p) ≫ 𝟙 _
        rw [joinedLabels_map, Category.comp_id]
        exact collapse_sideMap ((proj x z).map (L.map f)).1 ((proj z y).map (R.map f)).1
          (collapse_natural F f) (collapse_natural G f) }
  parameter p := parameter (F.parameter p) (G.parameter p)
  parameter_map {p q} f := by
    rw [joinedLabels_map]
    exact mixedParameterSquare ((proj x z).map (L.map f)).1 ((proj z y).map (R.map f)).1
      (time.map f) ((degree L).map f) ((degree R).map f) (F.parameter_map f) (G.parameter_map f)
  raw p := joined_raw L R i j F G hi hj p

end Families

end
end DaggerModels.PartII.JTMarkedParametrizedTargetFamilyJoin
