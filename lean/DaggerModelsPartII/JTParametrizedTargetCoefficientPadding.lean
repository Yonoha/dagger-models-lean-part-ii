import DaggerModelsPartII.JTOrderedLabelCoefficientPadding
import DaggerModelsPartII.JTCylinderOverTargetBaseChange

/-! Retain the whole raw evaluation over compatible padded coefficient labels. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetCoefficientPadding

open JTOrderedLabelCoefficientPadding
open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph graph_square)
open JTMarkedParametrizedTargetFamilyJoin (degree)
open JTMarkedFiniteParametrizedTargetFamilies (Synchronized)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time)

private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev a (p : Extensions L) := (base L).obj p
private abbrev ins (p : Extensions L) := embedding ((degree L).obj (a p))

private abbrev param (p : Extensions L) := F.parameter (a p) ≫ J.map (ins p)

private theorem param_map {p q : Extensions L} (f : p ⟶ q) :
    (((pr.map ((labels L).map f)).1).map ⊗ₘ J.map ((base L ⋙ time).map f)) ≫ param F q =
      param F p ≫ J.map (pr.map ((labels L).map f)).2 := by
  let r := (base L).map f
  let u := ((pr.map (L.map r)).1).map
  let v := (degree L).map r
  change (u ⊗ₘ J.map (time.map r)) ≫ F.parameter (a q) ≫ J.map (ins q) =
    (F.parameter (a p) ≫ J.map (ins p)) ≫ J.map (JTPaddedTimeOperators.map v)
  rw [← Category.assoc, F.parameter_map r]
  change (F.parameter (a p) ≫ J.map v) ≫ J.map (ins q) =
    (F.parameter (a p) ≫ J.map (ins p)) ≫ J.map (JTPaddedTimeOperators.map v)
  have h : v ≫ ins q = ins p ≫ JTPaddedTimeOperators.map v := embedding_natural v
  rw [Category.assoc, ← J.map_comp, h, J.map_comp, ← Category.assoc]

private theorem comparison_graph (p : Extensions L) :
    graph (i := L.obj (a p)) (F.parameter (a p)) ≫
      (underDiagram W x y).map ((comparison L).app p) =
    graph (i := (labels L).obj p) (param F p) := by
  let b := (comparison L).app p
  let T := (codes L).obj (a p)
  let n := time.obj (a p)
  have hb : pr.map b = (𝟙 T, ins p) := rfl
  have hp : (((pr.map b).1).map ⊗ₘ J.map (𝟙 n)) ≫ param F p =
      F.parameter (a p) ≫ J.map (pr.map b).2 := by
    rw [hb, J.map_id]
    change (𝟙 T.toSSet ⊗ₘ 𝟙 (J.obj n)) ≫ param F p = param F p
    rw [tensorHom_id, id_whiskerRight, Category.id_comp]
  have h := graph_square b (𝟙 n) (F.parameter (a p)) (param F p) hp
  change graph (i := L.obj (a p)) (F.parameter (a p)) ≫ (underDiagram W x y).map b =
    NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (T, n) ⟶ (T, n) from ((pr.map b).1, 𝟙 n)) ≫
      graph (i := (labels L).obj p) (param F p) at h
  rw [hb] at h
  have hId : NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (T, n) ⟶ (T, n) from (𝟙 T, 𝟙 n)) = 𝟙 _ :=
    NecklaceCylinderJointDiagram.cylinderUnder.map_id (T, n)
  rw [hId, Category.id_comp] at h
  exact h

private theorem padded_raw (p : Extensions L) :
    (graph (i := (labels L).obj p) (param F p)).right ≫
      ((underCocone W x y).app ((labels L).obj p)).right =
      augmentation ((codes L).obj (a p)) (time.obj (a p)) ≫
        (F.collapse.app (a p)).map ≫ Q.map := by
  let b := (comparison L).app p
  let g := graph (i := L.obj (a p)) (F.parameter (a p))
  let z := graph (i := (labels L).obj p) (param F p)
  have h := congrArg (fun f ↦ f.right) (comparison_graph F p)
  change g.right ≫ ((underDiagram W x y).map b).right = z.right at h
  have ht := (underCocone W x y).naturality b
  change (underDiagram W x y).map b ≫ (underCocone W x y).app ((labels L).obj p) =
      (underCocone W x y).app (L.obj (a p)) ≫ 𝟙 _ at ht
  rw [Category.comp_id] at ht
  have hr := congrArg (fun f ↦ f.right) ht
  change ((underDiagram W x y).map b).right ≫
      ((underCocone W x y).app ((labels L).obj p)).right =
    ((underCocone W x y).app (L.obj (a p))).right at hr
  change z.right ≫ ((underCocone W x y).app ((labels L).obj p)).right = _
  rw [← h, Category.assoc, hr]
  exact F.raw (a p)

/-- On the full index of compatible padded choices the raw value and the native code are unchanged. -/
def paddedFamily : Family Q (labels L) (base L ⋙ time) where
  collapse := Functor.whiskerLeft (base L) F.collapse
  parameter := param F
  parameter_map f := param_map F f
  raw p := padded_raw F p

/-- The two added outside coefficients bound the entire graph, and every operator retains them. -/
def synchronized : Synchronized (base L ⋙ time) Q where
  labels := labels L
  family := paddedFamily F
  lower := lower L
  upper := upper L
  lower_bound _ _ _ _ := Fin.zero_le _
  upper_bound _ _ _ _ := Fin.le_last _

private abbrev originalFamily := F.precomp (base L)
private abbrev targetDiagram := JTTargetCommaPullback.diagram W x y Q

set_option maxHeartbeats 400000 in
/-- The actual pullback lifts compare along the middle face with no change
of time or native traversal. -/
theorem comparison_lifts (p : Extensions L) :
    (JTParametrizedTargetFamilies.liftNatural (originalFamily F)).app p ≫
      targetDiagram.map ((comparison L).app p) =
    (JTParametrizedTargetFamilies.liftNatural (paddedFamily F)).app p := by
  let i := L.obj (a p)
  let i' := (labels L).obj p
  let T := (codes L).obj (a p)
  let n := time.obj (a p)
  let r := (comparison L).app p
  let g := graph (i := i) (F.parameter (a p))
  let h := graph (i := i') (param F p)
  let c := F.collapse.app (a p)
  let k : (JTNecklaceEndpointCylinder.under T).obj n ⟶
      (JTNecklaceEndpointCylinder.under T).obj n := 𝟙 _
  have hd : g ≫ (underDiagram W x y).map r = k ≫ h :=
    (comparison_graph F p).trans (Category.id_comp _).symm
  have hn : JTCylinderOverTarget.native W x y Q T n c =
      k ≫ JTCylinderOverTarget.native W x y Q T n c := (Category.id_comp _).symm
  have sq := JTCylinderOverTargetBaseChange.lift_compare W x y Q i i' T T n n
    g h c c (F.raw (a p)) (padded_raw F p) k r hd hn
  change _ = k ≫ (JTParametrizedTargetFamilies.liftNatural (paddedFamily F)).app p at sq
  exact sq.trans (Category.id_comp _)

end
end DaggerModels.PartII.JTParametrizedTargetCoefficientPadding
