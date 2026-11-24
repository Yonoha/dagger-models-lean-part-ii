import DaggerModelsPartII.JTTargetCommaPullbackDiagram

/-!
# Change of the fixed target in the actual pullback diagrams

Every native arrow of targets acts on the whole pullback diagram, keeping
the cylinder component and postcomposing the native target component.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaPullbackNaturality

open JTTargetCommaPullback (diagram targetMap fst snd condition map_fst map_snd map_snd_assoc
  lift lift_fst lift_snd lift_snd_assoc)
open DecoratedCylinderNecklacePresentation (toTarget underCocone)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)

local notation "I" => DecoratedNecklaceHomDiagram.Index W x y
local notation "N" => NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

private theorem targetMap_comp {Q Q' : N} (f : Q ⟶ Q') :
    necklaceUnder.map f.hom ≫ targetMap W x y Q' = targetMap W x y Q :=
  Under.UnderMorphism.ext f.w

private def changeAt {Q Q' : N} (f : Q ⟶ Q') (i : I) :
    (diagram W x y Q).obj i ⟶ (diagram W x y Q').obj i :=
  pullback.lift (fst W x y Q i) (snd W x y Q i ≫ necklaceUnder.map f.hom) (by
    rw [Category.assoc, targetMap_comp W x y f]
    exact condition W x y Q i)

@[reassoc]
private theorem changeAt_fst {Q Q' : N} (f : Q ⟶ Q') (i : I) :
    changeAt W x y f i ≫ fst W x y Q' i = fst W x y Q i :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem changeAt_snd {Q Q' : N} (f : Q ⟶ Q') (i : I) :
    changeAt W x y f i ≫ snd W x y Q' i = snd W x y Q i ≫ necklaceUnder.map f.hom :=
  pullback.lift_snd _ _ _

/-- Map all cylinders over a native target arrow, with the same decorated labels. -/
def diagramMap {Q Q' : N} (f : Q ⟶ Q') : diagram W x y Q ⟶ diagram W x y Q' where
  app := changeAt W x y f
  naturality {_ j} g := by
    apply pullback.hom_ext (f := (underCocone W x y).app j) (g := targetMap W x y Q')
    · change (_ ≫ _) ≫ fst W x y Q' j = (_ ≫ _) ≫ fst W x y Q' j
      simp only [Category.assoc, changeAt_fst, map_fst, changeAt_fst_assoc]
    · change (_ ≫ _) ≫ snd W x y Q' j = (_ ≫ _) ≫ snd W x y Q' j
      simp only [Category.assoc, changeAt_snd, map_snd, map_snd_assoc]

@[reassoc]
theorem diagramMap_fst {Q Q' : N} (f : Q ⟶ Q') (i : I) :
    (diagramMap W x y f).app i ≫ fst W x y Q' i = fst W x y Q i :=
  changeAt_fst W x y f i

@[reassoc]
theorem diagramMap_snd {Q Q' : N} (f : Q ⟶ Q') (i : I) :
    (diagramMap W x y f).app i ≫ snd W x y Q' i =
      snd W x y Q i ≫ necklaceUnder.map f.hom :=
  changeAt_snd W x y f i

/-- The original pullback diagrams vary functorially with the target necklace. -/
def diagrams : N ⥤ I ⥤ Under JTXiEndpointCollapse.boundary where
  obj := diagram W x y
  map := diagramMap W x y
  map_id Q := by
    apply NatTrans.ext
    funext i
    apply pullback.hom_ext (f := (underCocone W x y).app i) (g := targetMap W x y Q)
    · change _ ≫ fst W x y Q i = _ ≫ fst W x y Q i
      simp only [diagramMap_fst, NatTrans.id_app, Category.id_comp]
    · change _ ≫ snd W x y Q i = _ ≫ snd W x y Q i
      simp only [diagramMap_snd, NatTrans.id_app, Category.id_comp]
      change snd W x y Q i ≫ necklaceUnder.map (𝟙 Q.code) = snd W x y Q i
      rw [necklaceUnder.map_id, Category.comp_id]
  map_comp {_ _ Q''} f g := by
    apply NatTrans.ext
    funext i
    apply pullback.hom_ext (f := (underCocone W x y).app i) (g := targetMap W x y Q'')
    · change _ ≫ fst W x y Q'' i = _ ≫ fst W x y Q'' i
      simp only [diagramMap_fst, NatTrans.comp_app, Category.assoc]
    · change _ ≫ snd W x y Q'' i = _ ≫ snd W x y Q'' i
      simp only [diagramMap_snd, diagramMap_snd_assoc, NatTrans.comp_app, Category.assoc]
      exact congrArg (fun k ↦ snd W x y _ i ≫ k) (necklaceUnder.map_comp f.hom g.hom)

/-- The strict pair of original maps commutes with actual change of target. -/
theorem lift_changeTarget {Q Q' : N} (f : Q ⟶ Q')
    (P : CostructuredArrow (toTarget W x y) Q) :
    lift W x y Q' ((CostructuredArrow.map f).obj P) =
      lift W x y Q P ≫ (diagramMap W x y f).app P.left.base := by
  let P' := (CostructuredArrow.map f).obj P
  apply pullback.hom_ext (f := (underCocone W x y).app P.left.base) (g := targetMap W x y Q')
  · change lift W x y Q' P' ≫ fst W x y Q' P.left.base = _ ≫ fst W x y Q' P.left.base
    calc
      _ = P.left.fiber.hom := lift_fst W x y Q' P'
      _ = _ := by rw [Category.assoc, diagramMap_fst, lift_fst]
  · change lift W x y Q' P' ≫ snd W x y Q' P.left.base = _ ≫ snd W x y Q' P.left.base
    calc
      _ = necklaceUnder.map (P.hom.hom ≫ f.hom) := lift_snd W x y Q' P'
      _ = necklaceUnder.map P.hom.hom ≫ necklaceUnder.map f.hom :=
        necklaceUnder.map_comp P.hom.hom f.hom
      _ = _ := by rw [Category.assoc, diagramMap_snd, lift_snd_assoc]

end

end DaggerModels.PartII.JTTargetCommaPullbackNaturality
