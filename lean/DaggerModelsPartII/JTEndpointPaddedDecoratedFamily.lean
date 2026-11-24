import DaggerModelsPartII.JTOrderedLabelEndpointPadding
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! Pull the entire original graph family back to the endpoint-padded labels. -/

set_option autoImplicit false
set_option maxHeartbeats 90000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTEndpointPaddedDecoratedFamily

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph graph_square)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private theorem transportParameter
    {X X' Y Y' S T U V : SSet.{0}}
    (u : X' ⟶ X) (v : Y' ⟶ Y) (f : X ⟶ Y) (g : X' ⟶ Y')
    (j : S ⟶ T) (p : X ⊗ S ⟶ U) (q : Y ⊗ T ⟶ V) (c : U ⟶ V)
    (h : g ≫ v = u ≫ f) (hp : (f ⊗ₘ j) ≫ q = p ≫ c) :
    (g ⊗ₘ j) ≫ ((v ⊗ₘ 𝟙 T) ≫ q) = ((u ⊗ₘ 𝟙 S) ≫ p) ≫ c := by
  calc
    _ = ((g ≫ v) ⊗ₘ j) ≫ q := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
    _ = ((u ⊗ₘ 𝟙 S) ≫ (f ⊗ₘ j)) ≫ q := by
      rw [tensorHom_comp_tensorHom, Category.id_comp, h]
    _ = _ := by rw [Category.assoc, hp, Category.assoc]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev oldCode (a : A) := (codes L).obj a
private abbrev oldDegree (a : A) := ((pr.obj (L.obj a))).2

/-- Change the original decorated labels by pulling them back along the full endpoint collapse. -/
abbrev labels (L : A ⥤ Index W x y) := L ⋙ JTOrderedLabelEndpointPadding.pad W x y

private abbrev rcode (a : A) := JTNativeEndpointPadding.collapse.app (oldCode (L := L) a)

private def collapseCodes (L : A ⥤ Index W x y) : codes (labels L) ⟶ codes L where
  app a := rcode (L := L) a
  naturality {_ _} f := JTNativeEndpointPadding.collapse.naturality ((codes L).map f)

/-- The decorated map remembers exactly which two beads were collapsed. -/
def collapseLabels (L : A ⥤ Index W x y) : labels L ⟶ L where
  app a := (JTOrderedLabelEndpointPadding.collapse W x y).app (L.obj a)
  naturality {_ _} f := (JTOrderedLabelEndpointPadding.collapse W x y).naturality (L.map f)

private abbrev parameter (a : A) :
    (JTNativeEndpointPadding.pad.obj (oldCode (L := L) a)).toSSet ⊗ J.obj (time.obj a) ⟶
      J.obj (oldDegree (L := L) a) :=
  ((rcode (L := L) a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ F.parameter a

private theorem parameterMap {a b : A} (f : a ⟶ b) :
    ((((pr.map ((labels L).map f)).1).map) ⊗ₘ J.map (time.map f)) ≫ parameter F b =
      parameter F a ≫ J.map (pr.map ((labels L).map f)).2 := by
  let c := (codes L).map f
  have h := JTNativeEndpointPadding.collapse.naturality c
  have hm := congrArg (fun m : JTNativeEndpointPadding.pad.obj (oldCode (L := L) a) ⟶
    oldCode (L := L) b ↦ m.map) h
  exact transportParameter _ _ _ _ _ _ _ _ hm (F.parameter_map f)

/-- The decorated collapse keeps the graph parameter after the native collapse. -/
theorem collapseParameter (a : A) :
    (((pr.map ((collapseLabels L).app a)).1).map ⊗ₘ J.map (𝟙 (time.obj a))) ≫ F.parameter a =
      parameter F a ≫ J.map (pr.map ((collapseLabels L).app a)).2 := by
  change ((rcode (L := L) a).map ⊗ₘ J.map (𝟙 (time.obj a))) ≫ F.parameter a =
    parameter F a ≫ J.map (𝟙 (oldDegree (L := L) a))
  rw [J.map_id, J.map_id, Category.comp_id]

private theorem pasteRaw
    {X Y V Z T U R K : SSet.{0}}
    (p : X ⟶ Y) (r : Y ⟶ V) (s : X ⟶ Z) (q : Z ⟶ V)
    (v : V ⟶ K) (w : Y ⟶ K) (a : Z ⟶ T) (a' : X ⟶ U)
    (b : T ⟶ R) (c : U ⟶ T) (d : R ⟶ K)
    (h₁ : p ≫ r = s ≫ q) (h₂ : r ≫ v = w)
    (h₃ : q ≫ v = a ≫ b ≫ d) (h₄ : s ≫ a = a' ≫ c) :
    p ≫ w = a' ≫ (c ≫ b) ≫ d := by
  rw [← h₂, ← Category.assoc, h₁, Category.assoc, h₃,
    ← Category.assoc s, h₄]
  simp only [Category.assoc]

private theorem paddedRaw (a : A) :
    (graph (i := (labels L).obj a) (m := time.obj a) (parameter F a)).right ≫
        ((underCocone W x y).app ((labels L).obj a)).right =
      augmentation (JTNativeEndpointPadding.pad.obj (oldCode (L := L) a)) (time.obj a) ≫
        (rcode (L := L) a ≫ F.collapse.app a).map ≫ Q.map := by
  let r := (collapseLabels L).app a
  let n := time.obj a
  let p := graph (i := (labels L).obj a) (m := n) (parameter F a)
  let q := graph (i := L.obj a) (m := n) (F.parameter a)
  let d := ((underCocone W x y).app (L.obj a)).right
  let d' := ((underCocone W x y).app ((labels L).obj a)).right
  let h := rcode (L := L) a
  let s := JTNecklaceEndpointCylinder.nativeMap h n
  have hGraph := congrArg (fun f ↦ f.right)
    (graph_square r (𝟙 n) (parameter F a) (F.parameter a) (collapseParameter F a))
  have hGraph₀ : p.right ≫ ((underDiagram W x y).map r).right =
      (s ≫ (JTNecklaceEndpointCylinder.value (oldCode (L := L) a)).map (𝟙 n)) ≫ q.right :=
    hGraph
  have hGraph' : p.right ≫ ((underDiagram W x y).map r).right = s ≫ q.right :=
    hGraph₀.trans (congrArg (· ≫ q.right)
      ((congrArg (s ≫ ·) ((JTNecklaceEndpointCylinder.value (oldCode (L := L) a)).map_id n)).trans
        (Category.comp_id s)))
  have hLabel := congrArg (fun f ↦ f.right) ((underCocone W x y).naturality r)
  have hLabel' : ((underDiagram W x y).map r).right ≫ d = d' :=
    hLabel.trans (Category.comp_id d')
  exact pasteRaw p.right ((underDiagram W x y).map r).right s q.right d d'
    (augmentation (oldCode (L := L) a) n)
    (augmentation (JTNativeEndpointPadding.pad.obj (oldCode (L := L) a)) n)
    (F.collapse.app a).map h.map Q.map hGraph' hLabel' (F.raw a)
    (augmentation_native_natural h n)

/-- The padded graph retains the whole fixed-target comparison, with the same time. -/
def family : Family Q (labels L) time where
  collapse := collapseCodes L ≫ F.collapse
  parameter := parameter F
  parameter_map f := parameterMap F f
  raw a := paddedRaw F a

end
end DaggerModels.PartII.JTEndpointPaddedDecoratedFamily
