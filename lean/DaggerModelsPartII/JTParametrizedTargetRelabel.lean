import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! Transport a fixed-target family across a decorated relabeling with invertible native code. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetRelabel

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph graph_square)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)
open JTNecklaceEndpointCylinder (nativeMap)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev c (i : I W x y) := (pr.obj i).1
private abbrev d (i : I W x y) := (pr.obj i).2

variable {L M : A ⥤ I W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (r : L ⟶ M)
variable (ρ : codes L ≅ codes M)
variable (hρ : ∀ a, (pr.map (r.app a)).1 = ρ.hom.app a)

private abbrev parameter (a : A) :
    (c (M.obj a)).toSSet ⊗ J.obj (time.obj a) ⟶ J.obj (d (M.obj a)) :=
  ((ρ.inv.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
    F.parameter a ≫ J.map (pr.map (r.app a)).2

private theorem parameter_map {a b : A} (f : a ⟶ b) :
    (((pr.map (M.map f)).1).map ⊗ₘ J.map (time.map f)) ≫
        parameter F r ρ b =
      parameter F r ρ a ≫ J.map (pr.map (M.map f)).2 := by
  have hc := ρ.inv.naturality f
  have hr := congrArg (fun t ↦ (pr.map t).2) (r.naturality f)
  change (pr.map (M.map f)).1 ≫ ρ.inv.app b =
      ρ.inv.app a ≫ (pr.map (L.map f)).1 at hc
  change (pr.map (L.map f)).2 ≫ (pr.map (r.app b)).2 =
      (pr.map (r.app a)).2 ≫ (pr.map (M.map f)).2 at hr
  change _ ≫ (((ρ.inv.app b).map ⊗ₘ 𝟙 _) ≫
      F.parameter b ≫ J.map (pr.map (r.app b)).2) =
    (((ρ.inv.app a).map ⊗ₘ 𝟙 _) ≫ F.parameter a ≫
      J.map (pr.map (r.app a)).2) ≫ J.map (pr.map (M.map f)).2
  have hcm := congrArg (fun t ↦ t.map) hc
  change (pr.map (M.map f)).1.map ≫ (ρ.inv.app b).map =
      (ρ.inv.app a).map ≫ (pr.map (L.map f)).1.map at hcm
  simp only [← Category.assoc, tensorHom_comp_tensorHom, hcm]
  simp only [Category.comp_id]
  have ht : (((ρ.inv.app a).map ≫ (pr.map (L.map f)).1.map) ⊗ₘ
      J.map (time.map f)) =
      ((ρ.inv.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
        ((pr.map (L.map f)).1.map ⊗ₘ J.map (time.map f)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht, Category.assoc ((ρ.inv.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a)))
    ((pr.map (L.map f)).1.map ⊗ₘ J.map (time.map f)) (F.parameter b),
    F.parameter_map f]
  simp only [Category.assoc, ← J.map_comp, hr]

include hρ in
private theorem raw (a : A) :
    (graph (parameter F r ρ a)).right ≫
        ((underCocone W x y).app (M.obj a)).right =
      augmentation (c (M.obj a)) (time.obj a) ≫
        ((ρ.inv.app a ≫ F.collapse.app a).map) ≫ Q.map := by
  let h := (pr.map (r.app a)).1
  let k := (pr.map (r.app a)).2
  let n := time.obj a
  let g := graph (F.parameter a)
  let z := graph (parameter F r ρ a)
  have hid : h ≫ ρ.inv.app a = 𝟙 (c (L.obj a)) := by
    dsimp only [h]
    rw [hρ a]
    exact congrArg (fun t ↦ t.app a) ρ.hom_inv_id
  have hpid : h.map ≫ (ρ.inv.app a).map = 𝟙 (c (L.obj a)).toSSet := by
    have hh := congrArg (fun t ↦ t.map) hid
    simpa only [NecklaceCode.simplicialFunctor.map_id] using hh
  have hp : (h.map ⊗ₘ J.map (𝟙 n)) ≫ parameter F r ρ a =
      F.parameter a ≫ J.map k := by
    rw [J.map_id]
    change (h.map ⊗ₘ 𝟙 (J.obj n)) ≫
        (((ρ.inv.app a).map ⊗ₘ 𝟙 (J.obj n)) ≫ F.parameter a ≫ J.map k) = _
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hpid,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  have hs := graph_square (r.app a) (𝟙 n) (F.parameter a)
    (parameter F r ρ a) hp
  change g ≫ (underDiagram W x y).map (r.app a) =
    NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (h, 𝟙 n)) ≫ z at hs
  have hmap : (NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (h, 𝟙 n))).right =
        nativeMap h n := by
    change nativeMap h n ≫ (JTNecklaceEndpointCylinder.value (c (M.obj a))).map (𝟙 n) = _
    rw [(JTNecklaceEndpointCylinder.value (c (M.obj a))).map_id, Category.comp_id]
  have hgraph := congrArg (fun t ↦ t.right) hs
  change g.right ≫ ((underDiagram W x y).map (r.app a)).right =
      (NecklaceCylinderJointDiagram.cylinderUnder.map
        (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (h, 𝟙 n))).right ≫ z.right
    at hgraph
  rw [hmap] at hgraph
  have hcone := congrArg (fun t ↦ t.right) ((underCocone W x y).naturality (r.app a))
  change ((underDiagram W x y).map (r.app a)).right ≫
      ((underCocone W x y).app (M.obj a)).right =
      ((underCocone W x y).app (L.obj a)).right at hcone
  have hraw : nativeMap h n ≫
      (z.right ≫ ((underCocone W x y).app (M.obj a)).right) =
      augmentation (c (L.obj a)) n ≫ (F.collapse.app a).map ≫ Q.map := by
    rw [← Category.assoc, ← hgraph, Category.assoc, hcone]
    exact F.raw a
  have hinv : ρ.inv.app a ≫ h = 𝟙 (c (M.obj a)) := by
    dsimp only [h]
    rw [hρ a]
    exact congrArg (fun t ↦ t.app a) ρ.inv_hom_id
  have hcancel : nativeMap (ρ.inv.app a) n ≫ nativeMap h n = 𝟙 _ := by
    rw [← JTNecklaceEndpointCylinder.nativeMap_comp, hinv]
    exact JTNecklaceEndpointCylinder.nativeMap_id _ _
  have htransport := congrArg (fun t ↦ nativeMap (ρ.inv.app a) n ≫ t) hraw
  change nativeMap (ρ.inv.app a) n ≫
      ((nativeMap h n ≫ z.right) ≫ ((underCocone W x y).app (M.obj a)).right) =
    nativeMap (ρ.inv.app a) n ≫
      (augmentation (c (L.obj a)) n ≫ (F.collapse.app a).map ≫ Q.map) at htransport
  simp only [← Category.assoc, hcancel, Category.id_comp] at htransport
  have haug := augmentation_native_natural (ρ.inv.app a) n
  change nativeMap (ρ.inv.app a) n ≫ augmentation (c (L.obj a)) n =
      augmentation (c (M.obj a)) n ≫ (ρ.inv.app a).map at haug
  rw [haug] at htransport
  simpa only [← Category.assoc] using htransport

/-- Relabel a family through an isomorphism of its native necklace projection. -/
def relabel : Family Q M time where
  collapse := ρ.inv ≫ F.collapse
  parameter := parameter F r ρ
  parameter_map f := parameter_map F r ρ f
  raw a := by
    simpa only [NatTrans.comp_app] using raw F r ρ hρ a


/-- The native collapse is transported through the inverse code comparison. -/
theorem relabel_collapse_app (a : A) :
    (relabel F r ρ hρ).collapse.app a = ρ.inv.app a ≫ F.collapse.app a := rfl

/-- The parameter keeps the original time and changes the decorated coefficient. -/
theorem relabel_parameter (a : A) :
    (relabel F r ρ hρ).parameter a =
      ((ρ.inv.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
        F.parameter a ≫ J.map (pr.map (r.app a)).2 := rfl


/-- The actual map of cylinders induced by a native isomorphism at fixed time. -/
def nativeCylinder :
    JTParametrizedTargetFamilies.cylinders (L := L) (time := time) ⟶
      JTParametrizedTargetFamilies.cylinders (L := M) (time := time) :=
  Functor.whiskerRight (NatTrans.prod' ρ.hom (𝟙 time))
    NecklaceCylinderJointDiagram.cylinderUnder

private abbrev targetDiagram := JTTargetCommaPullback.diagram W x y Q


/-- The two original projections commute with the relabeling on the entire cylinder. -/
theorem lift_component (a : A) :
    (JTParametrizedTargetFamilies.liftNatural F).app a ≫
        targetDiagram.map (r.app a) =
      (nativeCylinder ρ).app a ≫
        (JTParametrizedTargetFamilies.liftNatural (relabel F r ρ hρ)).app a := by
  let h := (pr.map (r.app a)).1
  let n := time.obj a
  have hc : h ≫ (relabel F r ρ hρ).collapse.app a = F.collapse.app a := by
    change h ≫ (ρ.inv.app a ≫ F.collapse.app a) = F.collapse.app a
    have hi : h ≫ ρ.inv.app a = 𝟙 _ := by
      dsimp only [h]
      rw [hρ a]
      exact congrArg (fun t ↦ t.app a) ρ.hom_inv_id
    rw [← Category.assoc, hi, Category.id_comp]
  have hp : (h.map ⊗ₘ J.map (𝟙 n)) ≫
      (relabel F r ρ hρ).parameter a =
        F.parameter a ≫ J.map (pr.map (r.app a)).2 := by
    rw [relabel_parameter]
    have hi : h.map ≫ (ρ.inv.app a).map = 𝟙 _ := by
      have ht : h ≫ ρ.inv.app a = 𝟙 _ := by
        dsimp only [h]
        rw [hρ a]
        exact congrArg (fun t ↦ t.app a) ρ.hom_inv_id
      have hh := congrArg (fun t ↦ t.map) ht
      simpa only [NecklaceCode.simplicialFunctor.map_id] using hh
    rw [J.map_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hi,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  have sq := JTParametrizedTargetLiftTransport.lift_square Q (r.app a) (𝟙 n)
    (F.parameter a) ((relabel F r ρ hρ).parameter a)
    (F.collapse.app a) ((relabel F r ρ hρ).collapse.app a)
    hc hp (F.raw a) ((relabel F r ρ hρ).raw a)
  change _ = NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (h, 𝟙 n)) ≫ _ at sq
  have hn : (nativeCylinder ρ).app a =
      NecklaceCylinderJointDiagram.cylinderUnder.map
        (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (h, 𝟙 n)) := by
    change NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (c (L.obj a), n) ⟶ (c (M.obj a), n) from (ρ.hom.app a, 𝟙 n)) = _
    rw [← hρ a]
  rw [hn]
  simpa only [JTParametrizedTargetFamilies.liftNatural] using sq

end
end DaggerModels.PartII.JTParametrizedTargetRelabel
