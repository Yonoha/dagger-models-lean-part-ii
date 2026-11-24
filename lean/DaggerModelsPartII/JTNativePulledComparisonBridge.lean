import DaggerModelsPartII.JTNativePulledEvaluationBridge

/-!
Compatibility of the complete native restriction comparison with the exact
target evaluator. The comparison between the legacy inverse evaluator and
its exact copy is the existing `JTTargetCommaExactEvaluation.inverseIso`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativePulledComparisonBridge

noncomputable section

section Generic

variable {C D X : Type} [Category C] [Category D] [Category X]
variable {B₀ B₂ : C ⥤ D} (β : B₀ ⟶ B₂)
variable {Hinv Hexact : D ⥤ X} (e : Hinv ≅ Hexact)

/-- Postcomposition of a comparison commutes with an isomorphism of target
evaluators, on every object of the complete source category. -/
theorem whiskerRight_iso_square :
    Functor.whiskerRight β Hinv ≫ Functor.whiskerLeft B₂ e.hom =
      Functor.whiskerLeft B₀ e.hom ≫ Functor.whiskerRight β Hexact := by
  apply NatTrans.ext
  funext P
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] using e.hom.naturality (β.app P)

/-- Naturality at a morphism is unchanged when that morphism is identified
by a componentwise comparison before evaluation. -/
theorem iso_component_square {P Q : D} (f g : P ⟶ Q) (h : f = g) :
    Hinv.map f ≫ e.hom.app Q = e.hom.app P ≫ Hexact.map g := by
  rw [h]
  exact e.hom.naturality g

private abbrev B := JTXiEndpointCollapse.boundary

/-- The exact one-arrow compatibility equation attached to a pair of
restriction squares. It uses the first square; the second is retained for
the subsequent composition theorem. -/
def comparisonIsoSquare
    {I : Type} [SmallCategory I] {E : I ⥤ Under B}
    (d : JTNativePulledComparisonComposition.ComparisonData E)
    {X : Type} [Category X]
    {Hinv Hexact : BoundaryNecklaceComma.Presentation E ⥤ X}
    (e : Hinv ≅ Hexact) : Prop :=
  Functor.whiskerRight
      (JTCylinderOverTargetBaseChange.comparisonOfSquare E
        d.p₀ d.p₁ d.u d.a d.ha) Hinv ≫
      Functor.whiskerLeft
        (CostructuredArrow.map d.u ⋙ CostructuredArrow.map d.p₁ ⋙
          Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) d.i₁) e.hom =
    Functor.whiskerLeft
        (CostructuredArrow.map d.p₀ ⋙
          Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) d.i₀) e.hom ≫
      Functor.whiskerRight
        (JTCylinderOverTargetBaseChange.comparisonOfSquare E
          d.p₀ d.p₁ d.u d.a d.ha) Hexact

/-- The compatibility square is precisely naturality of the existing
isomorphism of fixed-target evaluators at the comparison component. -/
theorem comparison_iso_square
    {I : Type} [SmallCategory I] {E : I ⥤ Under B}
    (d : JTNativePulledComparisonComposition.ComparisonData E)
    {X : Type} [Category X]
    {Hinv Hexact : BoundaryNecklaceComma.Presentation E ⥤ X}
    (e : Hinv ≅ Hexact) : comparisonIsoSquare d e :=
  whiskerRight_iso_square
    (JTCylinderOverTargetBaseChange.comparisonOfSquare E
      d.p₀ d.p₁ d.u d.a d.ha) e

end Generic

section Cast

variable {C₀ C₁ D X : Type}
variable [Category C₀] [Category C₁] [Category D] [Category X]
variable (g : C₀ ⥤ C₁) (B₀ : C₀ ⥤ D) (B₁ : C₁ ⥤ D)
variable (β : B₀ ⟶ g ⋙ B₁)
variable {Hinv Hexact : D ⥤ X} (e : Hinv ≅ Hexact)
variable {K₀ : C₀ ⥤ X} {K₁ : C₁ ⥤ X}

/-- A commuting exact-evaluator square gives the square with the specified
isomorphism of evaluators and the original endpoint equality proofs. -/
theorem evaluator_cast_square (h₀ : B₀ ⋙ Hexact = K₀) (h₁ : B₁ ⋙ Hexact = K₁)
    (γ : K₀ ⟶ g ⋙ K₁)
    (hγ : Functor.whiskerRight β Hexact ≫ Functor.whiskerLeft g (eqToHom h₁) =
      eqToHom h₀ ≫ γ) :
    Functor.whiskerRight β Hinv ≫
        Functor.whiskerLeft g
          ((Functor.isoWhiskerLeft B₁ e ≪≫ eqToIso h₁).hom) =
      (Functor.isoWhiskerLeft B₀ e ≪≫ eqToIso h₀).hom ≫ γ := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom,
    Functor.whiskerLeft_comp]
  have he : Functor.whiskerRight β Hinv ≫
      Functor.whiskerLeft g (Functor.whiskerLeft B₁ e.hom) =
      Functor.whiskerLeft B₀ e.hom ≫ Functor.whiskerRight β Hexact := by
    apply NatTrans.ext
    funext P
    exact e.hom.naturality (β.app P)
  calc
    _ = (Functor.whiskerRight β Hinv ≫
        Functor.whiskerLeft g (Functor.whiskerLeft B₁ e.hom)) ≫
        Functor.whiskerLeft g (eqToHom h₁) := (Category.assoc _ _ _).symm
    _ = (Functor.whiskerLeft B₀ e.hom ≫ Functor.whiskerRight β Hexact) ≫
        Functor.whiskerLeft g (eqToHom h₁) := by rw [he]
    _ = Functor.whiskerLeft B₀ e.hom ≫ (eqToHom h₀ ≫ γ) := by
      rw [Category.assoc, hγ]
    _ = _ := (Category.assoc _ _ _).symm

end Cast

section Presentation

variable {A I : Type} [SmallCategory A] [SmallCategory I]
variable (E : I ⥤ Under B) (C : A ⥤ Under B)
variable (L : A ⥤ I) (ρ : C ⟶ L ⋙ E)
private theorem comparison_fiber {i₀ i₁ : I} {A₀ A₁ : Under B}
    (p₀ : A₀ ⟶ E.obj i₀) (p₁ : A₁ ⟶ E.obj i₁)
    (g : A₀ ⟶ A₁) (a : i₀ ⟶ i₁) (h : p₀ ≫ E.map a = g ≫ p₁)
    (P : CostructuredArrow BoundaryNecklaceComma.necklaceUnder A₀) :
    ((JTCylinderOverTargetBaseChange.comparisonOfSquare E p₀ p₁ g a h).app P).fiber.left =
      𝟙 P.left :=
  JTCylinderOverTargetBaseChange.comparisonOfSquare_code E p₀ p₁ g a h P

/-- The full family cross arrow is exactly the comparison of its naturality square,
on every internal-necklace object. -/
theorem mapPresentation_cross {r s : A} (u : r ⟶ s)
    (P : (BoundaryNecklaceComma.fiberDiagram C).obj r) :
    (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ).map
        ((Grothendieck.ιNatTrans (F := BoundaryNecklaceComma.fiberDiagram C) u).app P) =
      (JTCylinderOverTargetBaseChange.comparisonOfSquare E
        (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm).app P := by
  apply JTTargetCommaPullback.operator_ext
  · rw [JTCylinderOverTargetBaseChange.comparisonOfSquare_base]
    rfl
  · exact (JTBoundaryNecklacePresentationCone.mapPresentation_code E C L ρ
        ((Grothendieck.ιNatTrans (F := BoundaryNecklaceComma.fiberDiagram C) u).app P)).trans
      (JTCylinderOverTargetBaseChange.comparisonOfSquare_code E
        (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm P).symm

variable {X : Type} [Category X]
variable {Hinv Hexact : BoundaryNecklaceComma.Presentation E ⥤ X}

/-- Evaluation of one full fiber after an isomorphism of target evaluators. -/
def presentationFiberIso (e : Hinv ≅ Hexact) (a : A) :
    (CostructuredArrow.map (ρ.app a) ⋙
      Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) (L.obj a)) ⋙ Hinv ≅
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram C) a ⋙
      (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ Hexact) :=
  Functor.isoWhiskerLeft
    (CostructuredArrow.map (ρ.app a) ⋙
      Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) (L.obj a)) e ≪≫
    eqToIso (by
      rw [← JTNativePulledEvaluationBridge.mapPresentation_fiber E C L ρ a]
      rfl)

/-- The evaluated full cross arrow commutes with arbitrary evaluator isomorphisms. -/
theorem presentation_comparison_square (e : Hinv ≅ Hexact)
    {r s : A} (u : r ⟶ s) :
    Functor.whiskerRight
        (JTCylinderOverTargetBaseChange.comparisonOfSquare E
          (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm) Hinv ≫
      Functor.whiskerLeft (CostructuredArrow.map (C.map u))
        (presentationFiberIso E C L ρ e s).hom =
    (presentationFiberIso E C L ρ e r).hom ≫
      Functor.whiskerRight
        (Grothendieck.ιNatTrans (F := BoundaryNecklaceComma.fiberDiagram C) u)
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ Hexact) ≫
      (Functor.associator (CostructuredArrow.map (C.map u))
        (Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram C) s)
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ Hexact)).hom := by
  apply NatTrans.ext
  funext P
  simp only [presentationFiberIso, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Functor.associator_hom_app,
    Category.comp_id, Functor.comp_map]
  have h := mapPresentation_cross E C L ρ u P
  simp only [JTBoundaryNecklacePresentationCone.mapPresentation, Functor.comp_map] at h
  rw [h]
  let f := (JTCylinderOverTargetBaseChange.comparisonOfSquare E
    (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm).app P
  exact (e.hom.naturality f).trans
    ((Category.comp_id
      (e.hom.app ((CostructuredArrow.map (ρ.app r) ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) (L.obj r)).obj P) ≫
        Hexact.map f)).symm.trans (Category.assoc _ _ _))

/-- The presentation cross arrow commutes with arbitrary endpoint equalities
after any exact evaluator, with those equality proofs retained symbolically. -/
theorem exact_evaluator_cast_square
    (H : BoundaryNecklaceComma.Presentation E ⥤ X)
    (h : ∀ a, (CostructuredArrow.map (ρ.app a) ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) (L.obj a)) ⋙ H =
      Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram C) a ⋙
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H))
    {r s : A} (u : r ⟶ s) :
    Functor.whiskerRight
        (JTCylinderOverTargetBaseChange.comparisonOfSquare E
          (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm) H ≫
      Functor.whiskerLeft (CostructuredArrow.map (C.map u)) (eqToHom (h s)) =
    eqToHom (h r) ≫
      Functor.whiskerRight
        (Grothendieck.ιNatTrans (F := BoundaryNecklaceComma.fiberDiagram C) u)
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H) ≫
      (Functor.associator (CostructuredArrow.map (C.map u))
        (Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram C) s)
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H)).hom := by
  apply NatTrans.ext
  funext P
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    eqToHom_app, eqToHom_refl, Functor.associator_hom_app, Functor.comp_map]
  have hp := mapPresentation_cross E C L ρ u P
  simp only [JTBoundaryNecklacePresentationCone.mapPresentation, Functor.comp_map] at hp
  rw [hp]
  exact (Category.id_comp
    (H.map ((JTCylinderOverTargetBaseChange.comparisonOfSquare E
      (ρ.app r) (ρ.app s) (C.map u) (L.map u) (ρ.naturality u).symm).app P) ≫
      𝟙 (H.obj
        ((CostructuredArrow.map (C.map u) ⋙ CostructuredArrow.map (ρ.app s) ⋙
          Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) (L.obj s)).obj P)))).symm

end Presentation

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W
    (OrderedNecklaceVertexPoints.boundaryPoint W x y)
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

private abbrev F := JTNativePulledFamilyDiagram.family i n c p hr
private abbrev L := JTNativePulledFamilyDiagram.labels i
private abbrev C := JTParametrizedTargetFamilies.cylinders
  (L := L i) (time := JTNativePulledFamilyDiagram.time i n)
private abbrev D := JTTargetCommaPullback.diagram W x y Q

private theorem cylinders_map_explicit
    {A : Type} [SmallCategory A]
    (labels : A ⥤ Index W x y) (time : A ⥤ SimplexCategory)
    {r s : A} (u : r ⟶ s) :
    (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u =
      NecklaceCylinderJointDiagram.cylinderUnder.map
        (show (((pr W x y).obj (labels.obj r)).1, time.obj r) ⟶
            (((pr W x y).obj (labels.obj s)).1, time.obj s) from
          (((pr W x y).map (labels.map u)).1, time.map u)) := rfl

private theorem transportNativeSquare
    {i₀ i₁ : Index W x y} {m₀ m₁ : SimplexCategory}
    (a : i₀ ⟶ i₁) (j : m₀ ⟶ m₁)
    (d₀ : ((pr W x y).obj i₀).1 ⟶ Q.code)
    (d₁ : ((pr W x y).obj i₁).1 ⟶ Q.code)
    (hc : ((pr W x y).map a).1 ≫ d₁ = d₀) :
    JTCylinderOverTarget.native W x y Q ((pr W x y).obj i₀).1 m₀ d₀ =
      NecklaceCylinderJointDiagram.cylinderUnder.map
          (show (((pr W x y).obj i₀).1, m₀) ⟶
              (((pr W x y).obj i₁).1, m₁) from
            (((pr W x y).map a).1, j)) ≫
        JTCylinderOverTarget.native W x y Q ((pr W x y).obj i₁).1 m₁ d₁ := by
  apply Under.UnderMorphism.ext
  change NecklaceCylinderAugmentation.augmentation _ _ ≫ d₀.map =
    (JTNecklaceEndpointCylinder.nativeMap ((pr W x y).map a).1 m₀ ≫
      (JTNecklaceEndpointCylinder.value ((pr W x y).obj i₁).1).map j) ≫
        NecklaceCylinderAugmentation.augmentation _ _ ≫ d₁.map
  have hh : (((pr W x y).map a).1).map ≫ d₁.map = d₀.map :=
    congrArg (fun f : ((pr W x y).obj i₀).1 ⟶ Q.code ↦ f.map) hc
  rw [Category.assoc,
    ← Category.assoc ((JTNecklaceEndpointCylinder.value ((pr W x y).obj i₁).1).map j),
    NecklaceCylinderAugmentation.augmentation_parameter_natural,
    ← Category.assoc (JTNecklaceEndpointCylinder.nativeMap ((pr W x y).map a).1 m₀),
    NecklaceCylinderAugmentation.augmentation_native_natural, Category.assoc, hh]

private def transportPresentation
    {i₀ i₁ : Index W x y} {m₀ m₁ : SimplexCategory}
    (a : i₀ ⟶ i₁) (j : m₀ ⟶ m₁)
    (p₀ : ((pr W x y).obj i₀).1.toSSet ⊗ J.obj m₀ ⟶
      J.obj ((pr W x y).obj i₀).2)
    (p₁ : ((pr W x y).obj i₁).1.toSSet ⊗ J.obj m₁ ⟶
      J.obj ((pr W x y).obj i₁).2)
    (d₀ : ((pr W x y).obj i₀).1 ⟶ Q.code)
    (d₁ : ((pr W x y).obj i₁).1 ⟶ Q.code)
    (hc : ((pr W x y).map a).1 ≫ d₁ = d₀)
    (hp : ((((pr W x y).map a).1).map ⊗ₘ J.map j) ≫ p₁ =
      p₀ ≫ J.map ((pr W x y).map a).2)
    (h₀ : (JTParametrizedTargetLiftTransport.graph p₀).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i₀).right =
        NecklaceCylinderAugmentation.augmentation _ _ ≫ d₀.map ≫ Q.map)
    (h₁ : (JTParametrizedTargetLiftTransport.graph p₁).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i₁).right =
        NecklaceCylinderAugmentation.augmentation _ _ ≫ d₁.map ≫ Q.map) :=
  JTCylinderOverTargetBaseChange.comparePresentation W x y Q i₀ i₁
    ((pr W x y).obj i₀).1 ((pr W x y).obj i₁).1 m₀ m₁
    (JTParametrizedTargetLiftTransport.graph p₀)
    (JTParametrizedTargetLiftTransport.graph p₁) d₀ d₁ h₀ h₁
    (NecklaceCylinderJointDiagram.cylinderUnder.map
      (show (((pr W x y).obj i₀).1, m₀) ⟶
          (((pr W x y).obj i₁).1, m₁) from
        (((pr W x y).map a).1, j))) a
    (JTParametrizedTargetLiftTransport.graph_square a j p₀ p₁ hp)
    (transportNativeSquare a j d₀ d₁ hc)

private theorem transport_compare_eq
    {i₀ i₁ : Index W x y} {m₀ m₁ : SimplexCategory}
    (a : i₀ ⟶ i₁) (j : m₀ ⟶ m₁)
    (p₀ : ((pr W x y).obj i₀).1.toSSet ⊗ J.obj m₀ ⟶
      J.obj ((pr W x y).obj i₀).2)
    (p₁ : ((pr W x y).obj i₁).1.toSSet ⊗ J.obj m₁ ⟶
      J.obj ((pr W x y).obj i₁).2)
    (d₀ : ((pr W x y).obj i₀).1 ⟶ Q.code)
    (d₁ : ((pr W x y).obj i₁).1 ⟶ Q.code)
    (hc : ((pr W x y).map a).1 ≫ d₁ = d₀)
    (hp : ((((pr W x y).map a).1).map ⊗ₘ J.map j) ≫ p₁ =
      p₀ ≫ J.map ((pr W x y).map a).2)
    (h₀ : (JTParametrizedTargetLiftTransport.graph p₀).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i₀).right =
        NecklaceCylinderAugmentation.augmentation _ _ ≫ d₀.map ≫ Q.map)
    (h₁ : (JTParametrizedTargetLiftTransport.graph p₁).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i₁).right =
        NecklaceCylinderAugmentation.augmentation _ _ ≫ d₁.map ≫ Q.map) :
    JTParametrizedTargetLiftTransport.compare Q a j p₀ p₁ d₀ d₁ hc hp h₀ h₁ =
      Functor.whiskerRight (transportPresentation a j p₀ p₁ d₀ d₁ hc hp h₀ h₁)
        (JTTargetCommaPullback.equivalence W x y Q).inverse := by
  dsimp only [JTParametrizedTargetLiftTransport.compare,
    JTCylinderOverTargetBaseChange.compare, transportPresentation]

private theorem family_presentation_eq
    {A : Type} [SmallCategory A]
    {labels : A ⥤ Index W x y} {time : A ⥤ SimplexCategory}
    (G : JTParametrizedTargetFamilies.Family Q labels time)
    {r s : A} (u : r ⟶ s)
    (hc : ((pr W x y).map (labels.map u)).1 ≫ G.collapse.app s = G.collapse.app r)
    (hp : ((((pr W x y).map (labels.map u)).1).map ⊗ₘ J.map (time.map u)) ≫
      G.parameter s = G.parameter r ≫ J.map ((pr W x y).map (labels.map u)).2) :
    transportPresentation (labels.map u) (time.map u)
        (G.parameter r) (G.parameter s) (G.collapse.app r) (G.collapse.app s)
        hc hp (G.raw r) (G.raw s) =
      JTCylinderOverTargetBaseChange.comparisonOfSquare
        (JTTargetCommaPullback.diagram W x y Q)
        ((JTParametrizedTargetFamilies.liftNatural G).app r)
        ((JTParametrizedTargetFamilies.liftNatural G).app s)
        ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u)
        (labels.map u) ((JTParametrizedTargetFamilies.liftNatural G).naturality u).symm := by
  simp only [cylinders_map_explicit]
  dsimp only [transportPresentation, JTCylinderOverTargetBaseChange.comparePresentation,
    JTParametrizedTargetFamilies.liftNatural]
  all_goals rfl

/-- The full family comparison commutes with the existing evaluator isomorphisms. -/
theorem family_comparison_square
    {A : Type} [SmallCategory A]
    {labels : A ⥤ Index W x y} {time : A ⥤ SimplexCategory}
    (G : JTParametrizedTargetFamilies.Family Q labels time)
    {r s : A} (u : r ⟶ s) :
    Functor.whiskerRight
        (JTCylinderOverTargetBaseChange.comparisonOfSquare
          (JTTargetCommaPullback.diagram W x y Q)
          ((JTParametrizedTargetFamilies.liftNatural G).app r)
          ((JTParametrizedTargetFamilies.liftNatural G).app s)
          ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u)
          (labels.map u) ((JTParametrizedTargetFamilies.liftNatural G).naturality u).symm)
        (JTTargetCommaPullback.equivalence W x y Q).inverse ≫
      Functor.whiskerLeft
        (CostructuredArrow.map
          ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u))
        (JTNativePulledEvaluationBridge.fiberEvaluationIso G s).hom =
    (JTNativePulledEvaluationBridge.fiberEvaluationIso G r).hom ≫
      Functor.whiskerRight
        (Grothendieck.ιNatTrans
          (F := BoundaryNecklaceComma.fiberDiagram
            (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time))) u)
        (JTParametrizedTargetFamilies.evaluate G) ≫
      (Functor.associator
        (CostructuredArrow.map
          ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u))
        (Grothendieck.ι
          (BoundaryNecklaceComma.fiberDiagram
            (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time))) s)
        (JTParametrizedTargetFamilies.evaluate G)).hom := by
  unfold JTNativePulledEvaluationBridge.fiberEvaluationIso
  refine evaluator_cast_square
    (CostructuredArrow.map
      ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u))
    (CostructuredArrow.map ((JTParametrizedTargetFamilies.liftNatural G).app r) ⋙
      Grothendieck.ι
        (BoundaryNecklaceComma.fiberDiagram (JTTargetCommaPullback.diagram W x y Q))
        (labels.obj r))
    (CostructuredArrow.map ((JTParametrizedTargetFamilies.liftNatural G).app s) ⋙
      Grothendieck.ι
        (BoundaryNecklaceComma.fiberDiagram (JTTargetCommaPullback.diagram W x y Q))
        (labels.obj s))
    (JTCylinderOverTargetBaseChange.comparisonOfSquare
      (JTTargetCommaPullback.diagram W x y Q)
      ((JTParametrizedTargetFamilies.liftNatural G).app r)
      ((JTParametrizedTargetFamilies.liftNatural G).app s)
      ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u)
      (labels.map u) ((JTParametrizedTargetFamilies.liftNatural G).naturality u).symm)
    (JTTargetCommaExactEvaluation.inverseIso W x y Q)
    (JTNativePulledEvaluationBridge.exactFiber_eq_total G r)
    (JTNativePulledEvaluationBridge.exactFiber_eq_total G s)
    (Functor.whiskerRight
        (Grothendieck.ιNatTrans
          (F := BoundaryNecklaceComma.fiberDiagram
            (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time))) u)
        (JTParametrizedTargetFamilies.evaluate G) ≫
      (Functor.associator
        (CostructuredArrow.map
          ((JTParametrizedTargetFamilies.cylinders (L := labels) (time := time)).map u))
        (Grothendieck.ι
          (BoundaryNecklaceComma.fiberDiagram
            (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time))) s)
        (JTParametrizedTargetFamilies.evaluate G)).hom) ?_
  exact exact_evaluator_cast_square
    (JTTargetCommaPullback.diagram W x y Q)
    (JTParametrizedTargetFamilies.cylinders (L := labels) (time := time))
    labels (JTParametrizedTargetFamilies.liftNatural G)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)
    (JTNativePulledEvaluationBridge.exactFiber_eq_total G) u

include hr in
/-- The evaluator-copy square holds on an actual native restriction arrow
in the one strict family over the fixed ambient internal source. -/
theorem native_inverse_square {r s : Over (T W x y i)} (u : r ⟶ s) :
    comparisonIsoSquare
      (JTNativePulledComparisonComposition.ComparisonData.ofNatTrans
        (D (W := W) (x := x) (y := y) (Q := Q))
        (C i n) (L i)
        (JTParametrizedTargetFamilies.liftNatural (F i n c p hr))
        u (𝟙 s))
      (JTTargetCommaExactEvaluation.inverseIso W x y Q) :=
  comparison_iso_square _ (JTTargetCommaExactEvaluation.inverseIso W x y Q)

private def nativeLift (r : Over (T W x y i)) :=
  JTCylinderOverTarget.lift W x y Q (JTNativePulledCutComparison.label i r.hom)
    (((pr W x y).obj (JTNativePulledCutComparison.label i r.hom)).1) n
    (JTParametrizedTargetLiftTransport.graph
      (i := JTNativePulledCutComparison.label i r.hom) (m := n)
      (JTNativePulledCutComparison.parameter i n p r.hom))
    (r.hom ≫ c) (JTNativePulledCutComparison.raw (Q := Q) i n c p hr r.hom)

private def nativeCylinderMap {r s : Over (T W x y i)} (u : r ⟶ s) :=
  NecklaceCylinderJointDiagram.cylinderUnder.map
    (show (((pr W x y).obj (JTNativePulledCutComparison.label i r.hom)).1, n) ⟶
        (((pr W x y).obj (JTNativePulledCutComparison.label i s.hom)).1, n) from
      (((pr W x y).map
        (JTNativePulledCutComparison.labelMap i r.hom s.hom u.left (Over.w u))).1,
        𝟙 n))

private theorem nativeCylinderMap_eq {r s : Over (T W x y i)} (u : r ⟶ s) :
    nativeCylinderMap i n u = (C i n).map u :=
  (cylinders_map_explicit (L i) (JTNativePulledFamilyDiagram.time i n) u).symm

private def native_lift_square {r s : Over (T W x y i)} (u : r ⟶ s) :=
  JTParametrizedTargetLiftTransport.lift_square
    (W := W) (x := x) (y := y)
    (i := JTNativePulledCutComparison.label i r.hom)
    (i' := JTNativePulledCutComparison.label i s.hom) (m := n) (n := n)
    Q (JTNativePulledCutComparison.labelMap i r.hom s.hom u.left (Over.w u)) (𝟙 n)
    (JTNativePulledCutComparison.parameter i n p r.hom)
    (JTNativePulledCutComparison.parameter i n p s.hom)
    (r.hom ≫ c) (s.hom ≫ c)
    (by
      change u.left ≫ (s.hom ≫ c) = r.hom ≫ c
      rw [← Category.assoc, Over.w u])
    (by
      change (u.left.map ⊗ₘ J.map (𝟙 n)) ≫
          ((s.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
        ((r.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (k W x y i))
      rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
        tensorHom_comp_tensorHom, Category.id_comp]
      exact congrArg
        (fun v : r.left.toSSet ⟶ (T W x y i).toSSet ↦
          (v ⊗ₘ 𝟙 (J.obj n)) ≫ p)
        (congrArg (fun q : r.left ⟶ T W x y i ↦ q.map) (Over.w u)))
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr r.hom)
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr s.hom)

private def nativePresentationComparison {r s : Over (T W x y i)} (u : r ⟶ s) :=
  transportPresentation
    (JTNativePulledCutComparison.labelMap i r.hom s.hom u.left (Over.w u)) (𝟙 n)
    (JTNativePulledCutComparison.parameter i n p r.hom)
    (JTNativePulledCutComparison.parameter i n p s.hom)
    (r.hom ≫ c) (s.hom ≫ c)
    (by
      change u.left ≫ (s.hom ≫ c) = r.hom ≫ c
      rw [← Category.assoc, Over.w u])
    (by
      change (u.left.map ⊗ₘ J.map (𝟙 n)) ≫
          ((s.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
        ((r.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (k W x y i))
      rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
        tensorHom_comp_tensorHom, Category.id_comp]
      exact congrArg
        (fun v : r.left.toSSet ⟶ (T W x y i).toSSet ↦
          (v ⊗ₘ 𝟙 (J.obj n)) ≫ p)
        (congrArg (fun q : r.left ⟶ T W x y i ↦ q.map) (Over.w u)))
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr r.hom)
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr s.hom)

private theorem native_legacy_presentation {r s : Over (T W x y i)} (u : r ⟶ s) :
    JTNativePulledCutComparison.compare i n c p hr
        r.hom s.hom u.left (Over.w u) =
      Functor.whiskerRight (nativePresentationComparison i n c p hr u)
        (JTTargetCommaPullback.equivalence W x y Q).inverse :=
  transport_compare_eq
    (JTNativePulledCutComparison.labelMap i r.hom s.hom u.left (Over.w u)) (𝟙 n)
    (JTNativePulledCutComparison.parameter i n p r.hom)
    (JTNativePulledCutComparison.parameter i n p s.hom)
    (r.hom ≫ c) (s.hom ≫ c)
    (by
      change u.left ≫ (s.hom ≫ c) = r.hom ≫ c
      rw [← Category.assoc, Over.w u])
    (by
      change (u.left.map ⊗ₘ J.map (𝟙 n)) ≫
          ((s.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
        ((r.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (k W x y i))
      rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
        tensorHom_comp_tensorHom, Category.id_comp]
      exact congrArg
        (fun v : r.left.toSSet ⟶ (T W x y i).toSSet ↦
          (v ⊗ₘ 𝟙 (J.obj n)) ≫ p)
        (congrArg (fun q : r.left ⟶ T W x y i ↦ q.map) (Over.w u)))
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr r.hom)
    (JTNativePulledCutComparison.raw (Q := Q) i n c p hr s.hom)

private theorem native_presentation_family {r s : Over (T W x y i)} (u : r ⟶ s) :
    nativePresentationComparison i n c p hr u =
      JTCylinderOverTargetBaseChange.comparisonOfSquare
        (D (W := W) (x := x) (y := y) (Q := Q))
        ((JTParametrizedTargetFamilies.liftNatural (F i n c p hr)).app r)
        ((JTParametrizedTargetFamilies.liftNatural (F i n c p hr)).app s)
        ((C i n).map u) ((L i).map u)
        ((JTParametrizedTargetFamilies.liftNatural (F i n c p hr)).naturality u).symm :=
  family_presentation_eq (F i n c p hr) u
    (by
      change u.left ≫ (s.hom ≫ c) = r.hom ≫ c
      rw [← Category.assoc, Over.w u])
    (by
      change (u.left.map ⊗ₘ J.map (𝟙 n)) ≫
          ((s.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
        ((r.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (k W x y i))
      rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
        tensorHom_comp_tensorHom, Category.id_comp]
      exact congrArg
        (fun v : r.left.toSSet ⟶ (T W x y i).toSSet ↦
          (v ⊗ₘ 𝟙 (J.obj n)) ≫ p)
        (congrArg (fun q : r.left ⟶ T W x y i ↦ q.map) (Over.w u)))

include hr in
/-- The legacy native comparison and the complete Family comparison agree
through the specified evaluator isomorphisms, with the domain associator explicit. -/
theorem native_comparison_square {r s : Over (T W x y i)} (u : r ⟶ s) :
    JTNativePulledCutComparison.compare i n c p hr
        r.hom s.hom u.left (Over.w u) ≫
      Functor.whiskerLeft (CostructuredArrow.map ((C i n).map u))
        (JTNativePulledEvaluationBridge.nativeEvaluationIso i n c p hr s).hom =
    (JTNativePulledEvaluationBridge.nativeEvaluationIso i n c p hr r).hom ≫
      Functor.whiskerRight
        (Grothendieck.ιNatTrans (F := BoundaryNecklaceComma.fiberDiagram (C i n)) u)
        (JTParametrizedTargetFamilies.evaluate (F i n c p hr)) ≫
      (Functor.associator (CostructuredArrow.map ((C i n).map u))
        (Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (C i n)) s)
        (JTParametrizedTargetFamilies.evaluate (F i n c p hr))).hom := by
  rw [native_legacy_presentation i n c p hr u, native_presentation_family i n c p hr u]
  exact family_comparison_square (F i n c p hr) u

end
end DaggerModels.PartII.JTNativePulledComparisonBridge
