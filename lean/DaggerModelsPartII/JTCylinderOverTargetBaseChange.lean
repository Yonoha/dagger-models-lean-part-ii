import DaggerModelsPartII.JTCylinderOverTargetReindex

/-!
# Base change of the actual endpoint-cylinder comma functor
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCylinderOverTargetBaseChange

open JTCylinderOverTarget JTTargetCommaPullback JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev B := JTXiEndpointCollapse.boundary

/-- The Grothendieck comparison induced by any commuting square over `Under B`. -/
def comparisonOfSquare {I : Type} [SmallCategory I] (E : I ⥤ Under B)
    {i' i : I} {A' A : Under B}
    (p' : A' ⟶ E.obj i') (p : A ⟶ E.obj i) (g : A' ⟶ A) (a : i' ⟶ i)
    (h : p' ≫ E.map a = g ≫ p) :
    CostructuredArrow.map p' ⋙ Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i' ⟶
      CostructuredArrow.map g ⋙ CostructuredArrow.map p ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i := by
  let F := BoundaryNecklaceComma.fiberDiagram E
  let G := BoundaryNecklaceComma.diagram
  have hm : (G.map p').toFunctor ⋙ (F.map a).toFunctor =
      (G.map g).toFunctor ⋙ (G.map p).toFunctor := by
    change (G.map p').toFunctor ⋙ (G.map (E.map a)).toFunctor = _
    calc
      _ = (G.map (p' ≫ E.map a)).toFunctor :=
        (congrArg Cat.Hom.toFunctor (G.map_comp p' (E.map a))).symm
      _ = (G.map (g ≫ p)).toFunctor := congrArg (fun k ↦ (G.map k).toFunctor) h
      _ = _ := congrArg Cat.Hom.toFunctor (G.map_comp g p)
  refine Functor.whiskerLeft (CostructuredArrow.map p')
      (Grothendieck.ιNatTrans (F := F) a) ≫ eqToHom ?_
  change ((G.map p').toFunctor ⋙ (F.map a).toFunctor) ⋙ Grothendieck.ι F i =
    (G.map g).toFunctor ⋙ (G.map p).toFunctor ⋙ Grothendieck.ι F i
  rw [hm, Functor.assoc]

section Operators

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {i' i : I} {A' A : Under B}
variable (p' : A' ⟶ E.obj i') (p : A ⟶ E.obj i) (g : A' ⟶ A) (a : i' ⟶ i)
variable (h : p' ≫ E.map a = g ≫ p)

/-- The comparison component has the specified decorated base operator. -/
theorem comparisonOfSquare_base (P : CostructuredArrow necklaceUnder A') :
    ((comparisonOfSquare E p' p g a h).app P).base = a := by
  simp only [comparisonOfSquare, NatTrans.comp_app, Functor.whiskerLeft_app,
    Grothendieck.comp_base, Grothendieck.ιNatTrans_app_base, eqToHom_app,
    Grothendieck.base_eqToHom]
  exact Category.comp_id a

/-- The comparison component keeps the entire internal necklace map. -/
theorem comparisonOfSquare_code (P : CostructuredArrow necklaceUnder A') :
    (BoundaryNecklaceComma.sourceCode E).map ((comparisonOfSquare E p' p g a h).app P) =
      𝟙 P.left := by
  simp only [comparisonOfSquare, NatTrans.comp_app, Functor.whiskerLeft_app,
    eqToHom_app, Functor.map_comp, eqToHom_map]
  change 𝟙 P.left ≫ eqToHom _ = 𝟙 P.left
  exact Category.comp_id _

end Operators

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (i' i : DecoratedNecklaceHomDiagram.Index W x y)
variable (S' S : NecklaceCode) (m n : SimplexCategory)
variable (h' : (under S').obj m ⟶ (underDiagram W x y).obj i')
variable (h : (under S).obj n ⟶ (underDiagram W x y).obj i)
variable (d' : S' ⟶ Q.code) (d : S ⟶ Q.code)
variable (hr' : h'.right ≫ ((underCocone W x y).app i').right =
  augmentation S' m ≫ d'.map ≫ Q.map)
variable (hr : h.right ≫ ((underCocone W x y).app i).right =
  augmentation S n ≫ d.map ≫ Q.map)
variable (g : (under S').obj m ⟶ (under S).obj n) (a : i' ⟶ i)
variable (hDecorated : h' ≫ (underDiagram W x y).map a = g ≫ h)
variable (hNative : JTCylinderOverTarget.native W x y Q S' m d' =
  g ≫ JTCylinderOverTarget.native W x y Q S n d)

include hDecorated hNative in
/-- Equality of the two actual pullback lifts over a decorated base arrow. -/
theorem lift_compare :
    JTCylinderOverTarget.lift W x y Q i' S' m h' d' hr' ≫
        (diagram W x y Q).map a =
      g ≫ JTCylinderOverTarget.lift W x y Q i S n h d hr := by
  apply pullback.hom_ext (f := (underCocone W x y).app i)
    (g := targetMap W x y Q)
  · change (_ ≫ _) ≫ fst W x y Q i = (_ ≫ _) ≫ fst W x y Q i
    calc
      _ = (JTCylinderOverTarget.lift W x y Q i' S' m h' d' hr' ≫
          fst W x y Q i') ≫ (underDiagram W x y).map a := by
        rw [Category.assoc, map_fst, ← Category.assoc]
      _ = h' ≫ (underDiagram W x y).map a := by
        rw [JTCylinderOverTarget.lift_decorated]
      _ = g ≫ h := hDecorated
      _ = (g ≫ JTCylinderOverTarget.lift W x y Q i S n h d hr) ≫
          fst W x y Q i := by
        rw [Category.assoc, JTCylinderOverTarget.lift_decorated]
  · change (_ ≫ _) ≫ snd W x y Q i = (_ ≫ _) ≫ snd W x y Q i
    simp only [Category.assoc, map_snd, JTCylinderOverTarget.lift_native, hNative]

include hDecorated hNative in
/-- The Grothendieck comparison before transport through the target equivalence. -/
def comparePresentation :
    CostructuredArrow.map (JTCylinderOverTarget.lift W x y Q i' S' m h' d' hr') ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i' ⟶
      CostructuredArrow.map g ⋙
        CostructuredArrow.map (JTCylinderOverTarget.lift W x y Q i S n h d hr) ⋙
          Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i :=
  comparisonOfSquare (diagram W x y Q)
    (JTCylinderOverTarget.lift W x y Q i' S' m h' d' hr')
    (JTCylinderOverTarget.lift W x y Q i S n h d hr) g a
    (lift_compare W x y Q i' i S' S m n h' h d' d hr' hr g a hDecorated hNative)

include hDecorated hNative in
/-- Base change as a natural transformation of the actual comma functors. -/
def compare :
    JTCylinderOverTarget.functor W x y Q i' S' m h' d' hr' ⟶
      CostructuredArrow.map g ⋙
        JTCylinderOverTarget.functor W x y Q i S n h d hr := by
  exact Functor.whiskerRight
      (comparePresentation W x y Q i' i S' S m n h' h d' d hr' hr g a
        hDecorated hNative)
      (equivalence W x y Q).inverse

end

end DaggerModels.PartII.JTCylinderOverTargetBaseChange
