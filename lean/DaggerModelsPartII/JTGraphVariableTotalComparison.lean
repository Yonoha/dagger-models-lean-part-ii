import DaggerModelsPartII.JTGraphVariableTotalCylinder
import DaggerModelsPartII.JTGraphVariableComparisonTransport
import DaggerModelsPartII.JTGraphVariableComparisonConesOperators

/-! The full comparison of the total cylinder resolution to the original comma projection. -/

set_option autoImplicit false
set_option maxHeartbeats 45000

open CategoryTheory Limits Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableResolutionCategory

open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeTraversal (cylinders labels)
open JTGraphVariableTimeTransport (resolutionDiagram transport)
open JTGraphVariableTimeComparison (liftNatural decoratedCollapse nativeCollapse collapse_square)
open JTGraphVariableComparisonTransport (lift_square)
open JTGraphVariableComparisonConesOperators (label_triangle native_triangle)
open JTGraphVariableLabelTransport (labelTransport)
open BoundaryNecklaceComma (necklaceUnder sourceCode)
open JTTargetCommaPullback (toPullback equivalence operator_ext)

noncomputable section

section Naturality

universe u v w z
variable {I : Type u} {C : Type v} [Category.{w} I] [Category.{z} C] (F : I ⥤ C)

private theorem liftNaturality {i j k : I} {X Y : C}
    (a : i ⟶ j) (d : j ⟶ k) (g : X ⟶ Y)
    (u : X ⟶ F.obj i) (v : X ⟶ F.obj j) (w : Y ⟶ F.obj k)
    (ha : u ≫ F.map a = v) (hd : g ≫ w = v ≫ F.map d) :
    g ≫ w = u ≫ F.map (a ≫ d) := by
  rw [hd, F.map_comp, ← Category.assoc, ha]

private theorem collapseNaturality {X Y Z A B : C}
    (a : X ⟶ Y) (d : Y ⟶ Z) (g : A ⟶ B)
    (u : X ⟶ A) (v : Y ⟶ B) (w : Z ⟶ B)
    (ha : a ≫ v = u ≫ g) (hd : d ≫ w = v) :
    (a ≫ d) ≫ w = u ≫ g := by
  rw [Category.assoc, hd, ha]

private theorem liftCollapse {X Y U V Z : C}
    (e : X ⟶ Y) (l : Y ⟶ U) (a : U ⟶ Z) (c : Y ⟶ V) (m : V ⟶ Z)
    (h : l ≫ a = c ≫ m) : (e ≫ l) ≫ a = (e ≫ c) ≫ m := by
  rw [Category.assoc, h, Category.assoc]

end Naturality

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev outer := Grothendieck.forget (resolutionDiagram Q)
private abbrev cylinder := totalJoint Q ⋙ NecklaceCylinderJointDiagram.cylinderUnder

private theorem total_lift_right {P P' : Total Q} (f : P ⟶ P') :
    ((cylinder Q).map f).right ≫ ((liftNatural P'.base).app P'.fiber.base).right =
      ((liftNatural P.base).app P.fiber.base).right ≫ ((E Q).map ((totalLabels Q).map f)).right := by
  let L := Under.forget JTXiEndpointCollapse.boundary
  let d := (labels P'.base).map f.fiber.base
  let a := (labelTransport f.base).app P.fiber.base
  let u := ((liftNatural P.base).app P.fiber.base).right
  let v := ((liftNatural P'.base).app ((transport f.base).obj P.fiber.base)).right
  let w := ((liftNatural P'.base).app P'.fiber.base).right
  let g := ((cylinders P'.base).map f.fiber.base).right
  have ha : u ≫ (E Q ⋙ L).map a = v :=
    congrArg (fun k ↦ k.right) (lift_square f.base P.fiber.base)
  have hd : g ≫ w = v ≫ (E Q ⋙ L).map d :=
    congrArg (fun k ↦ k.right) ((liftNatural P'.base).naturality f.fiber.base)
  have hm : ((cylinder Q).map f).right = g :=
    congrArg (fun k ↦ (NecklaceCylinderJointDiagram.cylinderUnder.map k).right) (totalJoint_map Q f)
  have hl : (totalLabels Q).map f = a ≫ d := totalLabels_map Q f
  have h : g ≫ w = u ≫ (E Q ⋙ L).map (a ≫ d) :=
    liftNaturality (E Q ⋙ L) a d g u v w ha hd
  exact (congrArg (· ≫ w) hm).trans
    (h.trans (congrArg (fun k ↦ u ≫ (E Q ⋙ L).map k) hl.symm))

private def underNatTrans {I : Type} [SmallCategory I]
    {F G : I ⥤ Under JTXiEndpointCollapse.boundary}
    (a : ∀ i, F.obj i ⟶ G.obj i)
    (h : ∀ {i j} (f : i ⟶ j), (F.map f).right ≫ (a j).right =
      (a i).right ≫ (G.map f).right) : F ⟶ G where
  app := a
  naturality {_ _} f := Under.UnderMorphism.ext (h f)

/-- The original pullback lift is natural on the entire total resolution. -/
def totalLift : cylinder Q ⟶ totalLabels Q ⋙ E Q :=
  underNatTrans (F := cylinder Q) (G := totalLabels Q ⋙ E Q)
    (fun P ↦ (liftNatural P.base).app P.fiber.base) (fun f ↦ total_lift_right Q f)

private abbrev originalLabel := outer Q ⋙
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    DecoratedCylinderNecklacePresentation.projection W x y
private abbrev originalCode :=
  outer Q ⋙ CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

private def labelCollapse : totalLabels Q ⟶ originalLabel Q where
  app P := (decoratedCollapse P.base).app P.fiber.base
  naturality {P P'} f := by
    let a := (labelTransport f.base).app P.fiber.base
    let d := (labels P'.base).map f.fiber.base
    let u := (decoratedCollapse P.base).app P.fiber.base
    let v := (decoratedCollapse P'.base).app ((transport f.base).obj P.fiber.base)
    let w := (decoratedCollapse P'.base).app P'.fiber.base
    let g := f.base.left.base
    have h₁ : (totalLabels Q).map f = a ≫ d := totalLabels_map Q f
    have h₂ : a ≫ v = u ≫ g := label_triangle f.base P.fiber.base
    have h₃ : d ≫ w = v ≫ 𝟙 _ := (decoratedCollapse P'.base).naturality f.fiber.base
    exact (congrArg (· ≫ w) h₁).trans
      (collapseNaturality a d g u v w h₂ (h₃.trans (Category.comp_id v)))

private def codeCollapse : cylinder Q ⟶ originalCode Q ⋙ necklaceUnder where
  app P := (nativeCollapse P.base).app P.fiber.base
  naturality {P P'} f := by
    let g := (cylinders P'.base).map f.fiber.base
    let u := (nativeCollapse P.base).app P.fiber.base
    let v := (nativeCollapse P'.base).app ((transport f.base).obj P.fiber.base)
    let w := (nativeCollapse P'.base).app P'.fiber.base
    have hm : (cylinder Q).map f = g :=
      congrArg NecklaceCylinderJointDiagram.cylinderUnder.map (totalJoint_map Q f)
    have hd : g ≫ w = v ≫ 𝟙 _ := (nativeCollapse P'.base).naturality f.fiber.base
    have hn : v = u ≫ necklaceUnder.map f.base.left.fiber.left :=
      eq_of_heq (native_triangle f.base P.fiber.base)
    exact (congrArg (· ≫ w) hm).trans (hd.trans ((Category.comp_id v).trans hn))

/-- Send every internal necklace to its actual presentation in the fixed-target pullback. -/
def toPresentation :
    Total Q ⥤ JTTargetCommaPullback.Presentation W x y Q :=
  JTTargetCommaPullback.assemble (E Q) (totalLabels Q) (totalCode Q)
    (totalEvaluation Q ≫ totalLift Q)


section AssembledCone

variable {I K : Type} [SmallCategory I] [SmallCategory K]
variable (F : I ⥤ Under JTXiEndpointCollapse.boundary)
variable {b : K ⥤ I} {c : K ⥤ NecklaceCode}
variable (m : c ⋙ necklaceUnder ⟶ b ⋙ F)
variable (D : K ⥤ BoundaryNecklaceComma.Presentation F)
variable (a : b ⟶ D ⋙ Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram F))
variable (g : c ⟶ D ⋙ sourceCode F)
variable (h : ∀ P, (m.app P) ≫ F.map (a.app P) =
  necklaceUnder.map (g.app P) ≫ (D.obj P).fiber.hom)

/-- Two natural operators with compatible evaluations give a natural
transformation to the specified boundary presentations. -/
private def assembledCone : JTTargetCommaPullback.assemble F b c m ⟶ D where
  app P := ⟨a.app P, CostructuredArrow.homMk (g.app P) (h P).symm⟩
  naturality {P P'} f := by
    apply operator_ext
    · exact a.naturality f
    · let C := sourceCode F
      change C.map (_ ≫ _) = C.map (_ ≫ _)
      rw [C.map_comp, C.map_comp]
      exact g.naturality f

end AssembledCone

set_option maxHeartbeats 120000 in
private def collapseCode : totalCode Q ⟶ originalCode Q where
  app P := JTTargetCommaPullback.nativeArrow ((totalEvaluation Q ≫ codeCollapse Q).app P)
  naturality {_ _} f := NecklaceCode.Hom.ext (congrArg (fun k ↦ k.right)
    ((totalEvaluation Q ≫ codeCollapse Q).naturality f))

private theorem cone_comm_right (P : Total Q) :
    ((totalEvaluation Q ≫ totalLift Q).app P).right ≫
        ((E Q).map ((labelCollapse Q).app P)).right =
      (necklaceUnder.map ((collapseCode Q).app P)).right ≫
        ((toPullback W x y Q).obj P.base).fiber.hom.right := by
  let e := ((totalEvaluation Q).app P).right
  let l := ((liftNatural P.base).app P.fiber.base).right
  let a := ((E Q).map ((labelCollapse Q).app P)).right
  let c := ((codeCollapse Q).app P).right
  let m := ((toPullback W x y Q).obj P.base).fiber.hom.right
  have hc : (necklaceUnder.map ((collapseCode Q).app P)).right = e ≫ c := rfl
  have h : l ≫ a = c ≫ m := congrArg (fun k ↦ k.right) (collapse_square P.base P.fiber.base)
  exact (liftCollapse e l a c m h).trans (congrArg (· ≫ m) hc.symm)

private theorem cone_comm (P : Total Q) :
    ((totalEvaluation Q ≫ totalLift Q).app P) ≫ (E Q).map ((labelCollapse Q).app P) =
      necklaceUnder.map ((collapseCode Q).app P) ≫
        ((toPullback W x y Q).obj P.base).fiber.hom :=
  Under.UnderMorphism.ext (cone_comm_right Q P)

set_option maxHeartbeats 120000 in
/-- The total resolution compares naturally to its original comma object,
with all inner operators retained by the pullback construction. -/
def totalComparison : toPresentation Q ⋙ (equivalence W x y Q).inverse ⟶ outer Q :=
  Functor.whiskerRight (assembledCone (E Q) (totalEvaluation Q ≫ totalLift Q)
    (outer Q ⋙ toPullback W x y Q) (labelCollapse Q) (collapseCode Q) (cone_comm Q))
      (equivalence W x y Q).inverse ≫
    Functor.whiskerLeft (outer Q) (equivalence W x y Q).unitIso.inv


end
end DaggerModels.PartII.JTGraphVariableResolutionCategory
