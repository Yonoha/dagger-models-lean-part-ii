import DaggerModelsPartII.JTNativePulledCutCoherence
import DaggerModelsPartII.JTCylinderOverTargetBaseChangeComp

/-!
Composition of the complete fixed-target comparisons for native restrictions.
The coherence is proved on the full internal-necklace presentation before
transport through the fixed-target equivalence. No normalized or mixed-base
comparison is asserted.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativePulledComparisonComposition

open BoundaryNecklaceComma (necklaceUnder)
open JTCylinderOverTargetBaseChange (comparisonOfSquare)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {i₀ i₁ i₂ : I} {A₀ A₁ A₂ : Under B}
variable (p₀ : A₀ ⟶ E.obj i₀) (p₁ : A₁ ⟶ E.obj i₁)
  (p₂ : A₂ ⟶ E.obj i₂)
variable (u : A₀ ⟶ A₁) (v : A₁ ⟶ A₂)
  (a : i₀ ⟶ i₁) (b : i₁ ⟶ i₂)
variable (ha : p₀ ≫ E.map a = u ≫ p₁)
  (hb : p₁ ≫ E.map b = v ≫ p₂)

/-- The two paths from the original internal-necklace fiber to the final
presentation have exactly the same domain functor, including associators. -/
private theorem target_comp :
    CostructuredArrow.map u ⋙ CostructuredArrow.map v ⋙
        CostructuredArrow.map p₂ ⋙
          Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i₂ =
      CostructuredArrow.map (u ≫ v) ⋙ CostructuredArrow.map p₂ ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i₂ := by
  have h := congrArg Cat.Hom.toFunctor
    (BoundaryNecklaceComma.diagram.map_comp u v)
  change CostructuredArrow.map (u ≫ v) =
    CostructuredArrow.map u ⋙ CostructuredArrow.map v at h
  rw [h, Functor.assoc]

/-- Composition holds after any fixed-target evaluation functor, and hence
retains every internal necklace of the original source. -/
theorem comparison_comp_evaluated
    {X : Type} [Category X]
    (H : BoundaryNecklaceComma.Presentation E ⥤ X) :
    Functor.whiskerRight
      (comparisonOfSquare E p₀ p₂ (u ≫ v) (a ≫ b)
        (JTCylinderOverTargetBaseChangeComp.square_comp E p₀ p₁ p₂
          u v a b ha hb)) H =
      Functor.whiskerRight (comparisonOfSquare E p₀ p₁ u a ha) H ≫
        Functor.whiskerLeft (CostructuredArrow.map u)
          (Functor.whiskerRight (comparisonOfSquare E p₁ p₂ v b hb) H) ≫
        eqToHom (congrArg (fun F ↦ F ⋙ H)
          (target_comp E p₂ u v)) := by
  rw [JTCylinderOverTargetBaseChangeComp.comparisonOfSquare_comp
    E p₀ p₁ p₂ u v a b ha hb]
  ext P
  simp only [Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, eqToHom_app, eqToHom_map]

/-- The exact data of two composable native restriction squares. -/
structure ComparisonData {I : Type} [SmallCategory I] (E : I ⥤ Under B) where
  i₀ : I
  i₁ : I
  i₂ : I
  A₀ : Under B
  A₁ : Under B
  A₂ : Under B
  p₀ : A₀ ⟶ E.obj i₀
  p₁ : A₁ ⟶ E.obj i₁
  p₂ : A₂ ⟶ E.obj i₂
  u : A₀ ⟶ A₁
  v : A₁ ⟶ A₂
  a : i₀ ⟶ i₁
  b : i₁ ⟶ i₂
  ha : p₀ ≫ E.map a = u ≫ p₁
  hb : p₁ ≫ E.map b = v ≫ p₂

/-- The full typed equality, including the internal-necklace domain
associator. -/
def ComparisonData.Property {I : Type} [SmallCategory I]
    {E : I ⥤ Under B} (d : ComparisonData E)
    {X : Type} [Category X]
    (H : BoundaryNecklaceComma.Presentation E ⥤ X) : Prop :=
  Functor.whiskerRight
      (comparisonOfSquare E d.p₀ d.p₂ (d.u ≫ d.v) (d.a ≫ d.b)
        (JTCylinderOverTargetBaseChangeComp.square_comp E
          d.p₀ d.p₁ d.p₂ d.u d.v d.a d.b d.ha d.hb)) H =
    Functor.whiskerRight
        (comparisonOfSquare E d.p₀ d.p₁ d.u d.a d.ha) H ≫
      Functor.whiskerLeft (CostructuredArrow.map d.u)
        (Functor.whiskerRight
          (comparisonOfSquare E d.p₁ d.p₂ d.v d.b d.hb) H) ≫
      eqToHom (congrArg (fun G ↦ G ⋙ H)
        (target_comp E d.p₂ d.u d.v))

/-- Every pair of actual squares has the composed comparison, for an
arbitrary fixed-target evaluator on the whole original presentation. -/
theorem ComparisonData.property {I : Type} [SmallCategory I]
    {E : I ⥤ Under B} (d : ComparisonData E)
    {X : Type} [Category X]
    (H : BoundaryNecklaceComma.Presentation E ⥤ X) : d.Property H :=
  comparison_comp_evaluated E d.p₀ d.p₁ d.p₂ d.u d.v
    d.a d.b d.ha d.hb H

/-- A natural family of original pullback lifts supplies the two exact
restriction squares without any objectwise choices. -/
def ComparisonData.ofNatTrans
    {I A : Type} [SmallCategory I] [SmallCategory A]
    (E : I ⥤ Under B) (C : A ⥤ Under B) (L : A ⥤ I)
    (ρ : C ⟶ L ⋙ E) {r₀ r₁ r₂ : A}
    (u : r₀ ⟶ r₁) (v : r₁ ⟶ r₂) : ComparisonData E where
  i₀ := L.obj r₀
  i₁ := L.obj r₁
  i₂ := L.obj r₂
  A₀ := C.obj r₀
  A₁ := C.obj r₁
  A₂ := C.obj r₂
  p₀ := ρ.app r₀
  p₁ := ρ.app r₁
  p₂ := ρ.app r₂
  u := C.map u
  v := C.map v
  a := L.map u
  b := L.map v
  ha := (ρ.naturality u).symm
  hb := (ρ.naturality v).symm

/-- Naturality of the family gives strict composition of its full evaluated
restriction comparisons, including the source functors and associator. -/
theorem comparison_comp_ofNatTrans
    {I A : Type} [SmallCategory I] [SmallCategory A]
    (E : I ⥤ Under B) (C : A ⥤ Under B) (L : A ⥤ I)
    (ρ : C ⟶ L ⋙ E) {r₀ r₁ r₂ : A}
    (u : r₀ ⟶ r₁) (v : r₁ ⟶ r₂)
    {X : Type} [Category X]
    (H : BoundaryNecklaceComma.Presentation E ⥤ X) :
    (ComparisonData.ofNatTrans E C L ρ u v).Property H :=
  (ComparisonData.ofNatTrans E C L ρ u v).property H

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
private abbrev T (W : Source) (x y : Vertex W) (i : Index W x y) :=
  ((pr W x y).obj i).1
private abbrev k (W : Source) (x y : Vertex W) (i : Index W x y) :=
  ((pr W x y).obj i).2
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : Vertex W} (i : Index W x y)
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (n : SimplexCategory) (c : T W x y i ⟶ Q.code)
variable (p : (T W x y i).toSSet ⊗ J.obj n ⟶ J.obj (k W x y i))
variable (hr :
  (JTParametrizedTargetLiftTransport.graph (i := i) p).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i).right =
    NecklaceCylinderAugmentation.augmentation (T W x y i) n ≫ c.map ≫ Q.map)

include hr in
/-- Two successive native restrictions of the one fixed ambient family have
the same complete fixed-target comparison as their composite. -/
theorem native_family_comparison_comp
    {r₀ r₁ r₂ : Over (T W x y i)}
    (u : r₀ ⟶ r₁) (v : r₁ ⟶ r₂) :
    (ComparisonData.ofNatTrans
      (JTTargetCommaPullback.diagram W x y Q)
      (JTParametrizedTargetFamilies.cylinders
        (L := JTNativePulledFamilyDiagram.labels i)
        (time := JTNativePulledFamilyDiagram.time i n))
      (JTNativePulledFamilyDiagram.labels i)
      (JTParametrizedTargetFamilies.liftNatural
        (JTNativePulledFamilyDiagram.family i n c p hr)) u v).Property
      (JTTargetCommaExactEvaluation.fromPresentation W x y Q) :=
  comparison_comp_ofNatTrans
    (JTTargetCommaPullback.diagram W x y Q)
    (JTParametrizedTargetFamilies.cylinders
      (L := JTNativePulledFamilyDiagram.labels i)
      (time := JTNativePulledFamilyDiagram.time i n))
    (JTNativePulledFamilyDiagram.labels i)
    (JTParametrizedTargetFamilies.liftNatural
      (JTNativePulledFamilyDiagram.family i n c p hr)) u v
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

end
end DaggerModels.PartII.JTNativePulledComparisonComposition
