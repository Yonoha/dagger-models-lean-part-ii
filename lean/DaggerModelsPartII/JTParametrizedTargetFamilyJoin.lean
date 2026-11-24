import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTBinaryPrismNativeLabels

/-! Binary gluing with independently varying native side codes. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTParametrizedTargetFamilyJoin

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open OrderedLabelElements (label projection)
open JTBinaryPrismNativeLabels (labelArrow labelArrow_projection)
open JTBinaryPrismParameter (sideMap)
open JTBinaryPrismRealization (collapse raw_over_wedge)
open JTBinaryPrismSideTransport (collapse_sideMap mixedParameterSquare)
open JTBinaryPrismTargetLift (index)
open JTParameterBlockOperators (map_first map_last)

noncomputable section

private abbrev A₁ := single 1
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A]
variable {W : Source} {x z y : Vertex W}

private abbrev I (W : Source) (x y : Vertex W) := DecoratedNecklaceHomDiagram.Index W x y
private abbrev proj (x y : Vertex W) := projection W (boundaryPoint W x y)
private abbrev atLabel (x y : Vertex W) := label W (boundaryPoint W x y)
private abbrev outputDegree {x y : Vertex W} (i : I W x y) := ((proj x y).obj i).2

/-- Arrows of an ordered labelling diagram retain the first or last
coefficient vertex when used for gluing at that vertex. -/
def PreservesFirst (L : A ⥤ I W x y) : Prop :=
  ∀ {a b : A} (f : a ⟶ b), ((proj x y).map (L.map f)).2.toOrderHom 0 = 0

def PreservesLast (L : A ⥤ I W x y) : Prop :=
  ∀ {a b : A} (f : a ⟶ b),
    ((proj x y).map (L.map f)).2.toOrderHom (Fin.last (outputDegree (L.obj a)).len) =
      Fin.last (outputDegree (L.obj b)).len

variable (L : A ⥤ I W x z) (R : A ⥤ I W z y)
variable (hL : PreservesLast L) (hR : PreservesFirst R)

private abbrev joinedObj (a : A) := index (atLabel x z (L.obj a)) (atLabel z y (R.obj a))
private abbrev u {a b : A} (f : a ⟶ b) := (proj x z).map (L.map f)
private abbrev v {a b : A} (f : a ⟶ b) := (proj z y).map (R.map f)

private abbrev joinLabel (i : I W x z) (j : I W z y) :=
  index (atLabel x z i) (atLabel z y j)

set_option maxHeartbeats 450000 in
private def joinLabelArrow {i i' : I W x z} {j j' : I W z y} (a : i ⟶ i') (b : j ⟶ j')
    (ha : ((proj x z).map a).2.toOrderHom (Fin.last (outputDegree i).len) =
      Fin.last (outputDegree i').len)
    (hb : ((proj z y).map b).2.toOrderHom 0 = 0) :
    joinLabel i j ⟶ joinLabel i' j' := by
  let h₁ := OrderedLabelElements.label_map W (boundaryPoint W x z) a
  let h₂ := OrderedLabelElements.label_map W (boundaryPoint W z y) b
  let g := labelArrow ((proj x z).map a).1 ((proj z y).map b).1
    (atLabel x z i') (atLabel z y j') ((proj x z).map a).2 ((proj z y).map b).2 ha hb
  let e := congrArg₂ (fun l r ↦ index l r) h₁.symm h₂.symm
  exact eqToHom e ≫ g

private def joinedMap {a b : A} (f : a ⟶ b) : joinedObj L R a ⟶ joinedObj L R b :=
  joinLabelArrow (L.map f) (R.map f) (hL f) (hR f)

private instance : (proj x y).Faithful := by
  change ((CategoryOfElements.π (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y))).leftOp).Faithful
  infer_instance

set_option maxHeartbeats 500000 in
private theorem joinLabelArrow_projection {i i' : I W x z} {j j' : I W z y}
    (a : i ⟶ i') (b : j ⟶ j')
    (ha : ((proj x z).map a).2.toOrderHom (Fin.last (outputDegree i).len) =
      Fin.last (outputDegree i').len)
    (hb : ((proj z y).map b).2.toOrderHom 0 = 0) :
    (proj x y).map (joinLabelArrow a b ha hb) =
      (sideMap ((proj x z).map a).1 ((proj z y).map b).1,
        JTParameterBlockOperators.map ((proj x z).map a).2 ((proj z y).map b).2) := by
  unfold joinLabelArrow
  rw [Functor.map_comp, eqToHom_map, labelArrow_projection]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private theorem joinedMap_projection {a b : A} (f : a ⟶ b) :
    (proj x y).map (joinedMap L R hL hR f) =
      (sideMap (u L f).1 (v R f).1, JTParameterBlockOperators.map (u L f).2 (v R f).2) :=
  joinLabelArrow_projection (L.map f) (R.map f) (hL f) (hR f)

private theorem sideMap_comp {L₀ L₁ L₂ R₀ R₁ R₂ : NecklaceCode}
    (f : L₀ ⟶ L₁) (g : R₀ ⟶ R₁) (f' : L₁ ⟶ L₂) (g' : R₁ ⟶ R₂) :
    sideMap (f ≫ f') (g ≫ g') = Hom.comp.{0} (sideMap f g) (sideMap f' g') := by
  unfold sideMap
  rw [← wedgeMap_comp, ← wedgeMap_comp]
  rfl

private abbrev Operator := NecklaceCode × SimplexCategory

/-- The original native and ordinal-sum operators of two binary inputs. -/
def joinOperators : Operator × Operator ⥤ Operator where
  obj p := (JTOrderedLabelBinaryGlue.code p.1.1 p.2.1,
    JTParameterBlocks.common p.1.2 p.2.2)
  map f := (sideMap f.1.1 f.2.1, JTParameterBlockOperators.map f.1.2 f.2.2)
  map_id a := Prod.ext
    (show sideMap (Hom.id.{0} a.1.1) (Hom.id.{0} a.2.1) = Hom.id.{0} _ by
      change wedgeMap (Hom.id.{0} a.1.1) (wedgeMap (Hom.id.{0} A₁) (Hom.id.{0} a.2.1)) =
        Hom.id.{0} _
      rw [wedgeMap_id, wedgeMap_id])
    (JTParameterBlockOperators.map_id _ _)
  map_comp f g := Prod.ext
    (sideMap_comp f.1.1 f.2.1 g.1.1 g.2.1)
    (JTParameterBlockOperators.map_comp f.1.2 g.1.2 f.2.2 g.2.2).symm

private abbrev projected := ((L ⋙ proj x z).prod' (R ⋙ proj z y)) ⋙ joinOperators

private theorem projected_map {a b : A} (f : a ⟶ b) :
    (proj x y).map (joinedMap L R hL hR f) = (projected L R).map f :=
  joinedMap_projection L R hL hR f

set_option maxHeartbeats 500000 in
/-- The actual joined label diagram. Its code may change along both sides,
and its coefficient arrows retain the original connector conditions. -/
def joinedLabels : A ⥤ I W x y where
  obj := joinedObj L R
  map := joinedMap L R hL hR
  map_id a := (proj x y).map_injective <|
    (projected_map L R hL hR (𝟙 a)).trans <|
      ((projected L R).map_id a).trans ((proj x y).map_id (joinedObj L R a)).symm
  map_comp f g := (proj x y).map_injective <| calc
    _ = (projected L R).map (f ≫ g) := projected_map L R hL hR (f ≫ g)
    _ = (projected L R).map f ≫ (projected L R).map g := (projected L R).map_comp f g
    _ = (proj x y).map (joinedMap L R hL hR f) ≫
      (proj x y).map (joinedMap L R hL hR g) :=
        congrArg₂ (· ≫ ·) (projected_map L R hL hR f).symm (projected_map L R hL hR g).symm
    _ = _ := ((proj x y).map_comp (joinedMap L R hL hR f) (joinedMap L R hL hR g)).symm

set_option maxHeartbeats 450000 in
/-- The joined diagram has the specified source and coefficient operators. -/
theorem joinedLabels_map {a b : A} (f : a ⟶ b) :
    (proj x y).map ((joinedLabels L R hL hR).map f) =
      (sideMap (u L f).1 (v R f).1, JTParameterBlockOperators.map (u L f).2 (v R f).2) :=
  joinedMap_projection L R hL hR f

/-- Reindexing both sides keeps the literal joined label functor. -/
theorem joinedLabels_precomp {B : Type} [SmallCategory B] (G : B ⥤ A) :
    joinedLabels (G ⋙ L) (G ⋙ R) (fun f ↦ hL (G.map f)) (fun f ↦ hR (G.map f)) =
      G ⋙ joinedLabels L R hL hR := rfl

section Comparison

variable {L R hL hR}
variable {L' : A ⥤ I W x z} {R' : A ⥤ I W z y}
variable {hL' : PreservesLast L'} {hR' : PreservesFirst R'}
variable (α : L ⟶ L') (β : R ⟶ R')
variable (hα : ∀ a, ((proj x z).map (α.app a)).2.toOrderHom
    (Fin.last (outputDegree (L.obj a)).len) = Fin.last (outputDegree (L'.obj a)).len)
variable (hβ : ∀ a, ((proj z y).map (β.app a)).2.toOrderHom 0 = 0)

private def joinedOperatorComparison : projected L R ⟶ projected L' R' :=
  Functor.whiskerRight
    (NatTrans.prod' (Functor.whiskerRight α (proj x z)) (Functor.whiskerRight β (proj z y)))
    joinOperators

set_option maxHeartbeats 500000 in
/-- Join natural changes of the two labels which retain the coefficient vertices at the seam. -/
def compareLabels : joinedLabels L R hL hR ⟶ joinedLabels L' R' hL' hR' where
  app a := joinLabelArrow (α.app a) (β.app a) (hα a) (hβ a)
  naturality {a b} f := by
    apply (proj x y).map_injective
    rw [Functor.map_comp, Functor.map_comp, joinedLabels_map, joinedLabels_map,
      joinLabelArrow_projection, joinLabelArrow_projection]
    exact (joinedOperatorComparison α β).naturality f

/-- The comparison has the exact joined native and coefficient operators. -/
theorem compareLabels_map (a : A) :
    (proj x y).map ((compareLabels (hL := hL) (hR := hR) (hL' := hL') (hR' := hR')
      α β hα hβ).app a) =
      (sideMap ((proj x z).map (α.app a)).1 ((proj z y).map (β.app a)).1,
        JTParameterBlockOperators.map ((proj x z).map (α.app a)).2 ((proj z y).map (β.app a)).2) :=
  joinLabelArrow_projection (α.app a) (β.app a) (hα a) (hβ a)

end Comparison

/-- The actual joined diagram inherits its outer first coefficient vertex. -/
theorem joinedPreservesFirst (hL₀ : PreservesFirst L) :
    PreservesFirst (joinedLabels L R hL hR) := by
  intro a b f
  change ((proj x y).map ((joinedLabels L R hL hR).map f)).2.toOrderHom 0 = 0
  rw [joinedLabels_map]
  exact map_first (u L f).2 (v R f).2 (hL₀ f)

/-- The actual joined diagram inherits its outer last coefficient vertex. -/
theorem joinedPreservesLast (hR₁ : PreservesLast R) :
    PreservesLast (joinedLabels L R hL hR) := by
  intro a b f
  change ((proj x y).map ((joinedLabels L R hL hR).map f)).2.toOrderHom
      (Fin.last (JTParameterBlocks.common (outputDegree (L.obj a)) (outputDegree (R.obj a))).len) =
    Fin.last (JTParameterBlocks.common (outputDegree (L.obj b)) (outputDegree (R.obj b))).len
  rw [joinedLabels_map]
  exact map_last (u L f).2 (v R f).2 (hR₁ f)

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {time : A ⥤ SimplexCategory}
variable (F : Family P L time) (G : Family Q R time)

private theorem leftCollapse {a b : A} (f : a ⟶ b) :
    (u L f).1 ≫ F.collapse.app b = F.collapse.app a := by
  have h := F.collapse.naturality f
  change (u L f).1 ≫ F.collapse.app b = F.collapse.app a ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem rightCollapse {a b : A} (f : a ⟶ b) :
    (v R f).1 ≫ G.collapse.app b = G.collapse.app a := by
  have h := G.collapse.naturality f
  change (v R f).1 ≫ G.collapse.app b = G.collapse.app a ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

set_option maxHeartbeats 600000 in
/-- Join two whole parameter diagrams along the literal ordered endpoint,
retaining their changing native codes and their actual collapse maps. -/
def join : Family (NecklacesOver.wedge P Q) (joinedLabels L R hL hR) time where
  collapse :=
    { app a := collapse (F.collapse.app a) (G.collapse.app a)
      naturality {a b} f := by
        change ((proj x y).map ((joinedLabels L R hL hR).map f)).1 ≫
            collapse (F.collapse.app b) (G.collapse.app b) =
          collapse (F.collapse.app a) (G.collapse.app a) ≫ 𝟙 _
        rw [joinedLabels_map, Category.comp_id]
        exact collapse_sideMap (u L f).1 (v R f).1 (leftCollapse L F f) (rightCollapse R G f) }
  parameter a := JTBinaryPrismTargetLift.parameter (F.parameter a) (G.parameter a)
  parameter_map {a b} f := by
    rw [joinedLabels_map]
    exact mixedParameterSquare (u L f).1 (v R f).1 (time.map f) (u L f).2 (v R f).2
      (F.parameter_map f) (G.parameter_map f)
  raw a := by
    let l := atLabel x z (L.obj a)
    let r := atLabel z y (R.obj a)
    let s := F.parameter a
    let t := G.parameter a
    change JTInterpolatedReducedCylinder.cylinderMap _ (JTBinaryPrismTargetLift.parameter s t) ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app (index l r)).right = _
    rw [← JTBinaryPrismSideTransport.binaryCylinder_eq_interpolated]
    exact JTBinaryPrismTargetLift.cylinderMap_raw l r s t (F.collapse.app a) (G.collapse.app a)
      (JTParametrizedTargetFamilies.rawProduct F a) (JTParametrizedTargetFamilies.rawProduct G a)

end

end DaggerModels.PartII.JTParametrizedTargetFamilyJoin
