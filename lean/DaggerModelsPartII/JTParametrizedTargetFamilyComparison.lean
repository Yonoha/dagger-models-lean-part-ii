import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange
import DaggerModelsPartII.JTParametrizedTargetPullback

/-! Exact comparison of full parametrized families over the same fixed target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTParametrizedTargetFamilyComparison

open JTParametrizedTargetFamilies (Family codes cylinders liftNatural evaluate Presentation)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTBoundaryNecklacePresentationTransport (comparisonWithSourceChange)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L M : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {t u : A ⥤ SimplexCategory}

private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)

/-- The actual coefficient-ordinal functor of a decorated label diagram. -/
abbrev degrees (L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y) :=
  L ⋙ pr ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

variable (r : L ⟶ M) (v : t ⟶ u)

/-- The original native operators, with the original boundaries. -/
abbrev native := Functor.whiskerRight r
  (pr ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory)

/-- The original coefficient operators of the decorated map. -/
abbrev coefficient := Functor.whiskerRight r
  (pr ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory)

/-- Apply both original native and time operators to the reduced cylinders. -/
abbrev cylinderMap : cylinders (L := L) (time := t) ⟶ cylinders (L := M) (time := u) :=
  Functor.whiskerRight (NatTrans.prod' (native r) v) NecklaceCylinderJointDiagram.cylinderUnder

variable (F : Family Q L t) (G : Family Q M u)

/-- Require the exact native triangle and the original whole parameter square. -/
structure Compatible : Prop where
  collapse : native r ≫ G.collapse = F.collapse
  parameter : ∀ a,
    (((native r).app a).map ⊗ₘ J.map (v.app a)) ≫ G.parameter a =
      F.parameter a ≫ J.map ((coefficient r).app a)

variable (h : Compatible r v F G)

include h in
set_option maxHeartbeats 700000 in
/-- The original fixed-target lift square on the entire reduced cylinders. -/
theorem lift_component (a : A) :
    (liftNatural F).app a ≫ (JTTargetCommaPullback.diagram W x y Q).map (r.app a) =
      (cylinderMap r v).app a ≫ (liftNatural G).app a :=
  JTParametrizedTargetLiftTransport.lift_square Q (r.app a) (v.app a)
    (F.parameter a) (G.parameter a) (F.collapse.app a) (G.collapse.app a)
    (congrArg (fun p : codes L ⟶ (Functor.const A).obj Q.code ↦ p.app a) h.collapse)
    (h.parameter a) (F.raw a) (G.raw a)

/-- Send every original internal necklace through the actual reduced-cylinder maps. -/
abbrev presentation : Presentation (L := L) (time := t) ⥤ Presentation (L := M) (time := u) :=
  Grothendieck.map (Functor.whiskerRight (cylinderMap r v) BoundaryNecklaceComma.diagram)

set_option maxHeartbeats 900000 in
/-- The square induces a comparison of the complete evaluations in the same target comma. -/
def compare : evaluate F ⟶ presentation r v ⋙ evaluate G := by
  exact comparisonWithSourceChange (JTTargetCommaPullback.diagram W x y Q)
    (liftNatural F) (liftNatural G) (cylinderMap r v) r (lift_component r v F G h)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

/-- Arbitrary native and time changes over the same base still induce a
nerve weak equivalence on the full internal-necklace presentations. -/
theorem presentation_weak : WeakEquivalence (nerveMap (presentation r v)) := by
  let p₀ := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (cylinders (L := L) (time := t)))
  let p₁ := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (cylinders (L := M) (time := u)))
  haveI : WeakEquivalence (nerveMap p₀) :=
    JTParametrizedTargetFamilies.projection_weak (L := L) (time := t)
  haveI : WeakEquivalence (nerveMap p₁) :=
    JTParametrizedTargetFamilies.projection_weak (L := M) (time := u)
  have he : nerveMap (presentation r v) ≫ nerveMap p₁ = nerveMap p₀ :=
    (nerveFunctor.map_comp (presentation r v).toCatHom p₁.toCatHom).symm.trans
      (congrArg nerveMap (Grothendieck.functor_comp_forget
        (α := Functor.whiskerRight (cylinderMap r v) BoundaryNecklaceComma.diagram)))
  exact weakEquivalence_of_postcomp_of_fac he

section Pullback

open JTParametrizedTargetLiftTransport (graph)
open NecklaceCylinderAugmentation (augmentation)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

variable (s : degrees M ⟶ degrees L) (hs : s ≫ coefficient r = 𝟙 (degrees M))

private abbrev pulledParameter (a : A) :
    ((codes L).obj a).toSSet ⊗ J.obj (u.obj a) ⟶ J.obj ((degrees L).obj a) :=
  JTParametrizedTargetPullback.parameter (r.app a) (u.obj a) (s.app a) (G.parameter a)

set_option maxHeartbeats 700000 in
private theorem pulledParameter_map {a b : A} (f : a ⟶ b) :
    (((codes L).map f).map ⊗ₘ J.map (u.map f)) ≫ pulledParameter r G s b =
      pulledParameter r G s a ≫ J.map ((degrees L).map f) := by
  let fL := ((codes L).map f).map
  let fM := ((codes M).map f).map
  let v := J.map (u.map f)
  let r₀ := ((native r).app a).map
  let r₁ := ((native r).app b).map
  have hN : fL ≫ r₁ = r₀ ≫ fM := congrArg (fun q ↦ q.map) ((native r).naturality f)
  have hC := s.naturality f
  have hP : (fM ⊗ₘ v) ≫ G.parameter b = G.parameter a ≫ J.map ((degrees M).map f) :=
    G.parameter_map f
  have hT : (fL ⊗ₘ v) ≫ (r₁ ⊗ₘ 𝟙 _) = (r₀ ⊗ₘ 𝟙 _) ≫ (fM ⊗ₘ v) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id, hN]
  change (fL ⊗ₘ v) ≫ (r₁ ⊗ₘ 𝟙 _) ≫ G.parameter b ≫ J.map (s.app b) =
    ((r₀ ⊗ₘ 𝟙 _) ≫ G.parameter a ≫ J.map (s.app a)) ≫ J.map ((degrees L).map f)
  rw [← Category.assoc (fL ⊗ₘ v), hT]
  simp only [Category.assoc]
  rw [← Category.assoc (fM ⊗ₘ v), hP, Category.assoc, ← J.map_comp, hC, J.map_comp]

include hs in
set_option maxHeartbeats 500000 in
private theorem pulledParameter_square (a : A) :
    (((native r).app a).map ⊗ₘ J.map (𝟙 (u.obj a))) ≫ G.parameter a =
      pulledParameter r G s a ≫ J.map ((coefficient r).app a) := by
  have h : s.app a ≫ (pr.map (r.app a)).2 = 𝟙 ((degrees M).obj a) :=
    NatTrans.congr_app hs a
  exact JTParametrizedTargetPullback.parameter_square (r.app a) (u.obj a) (s.app a) h
    (G.parameter a)

include hs in
set_option maxHeartbeats 400000 in
private theorem pulled_raw (a : A) :
    (graph (i := L.obj a) (pulledParameter r G s a)).right ≫
        ((underCocone W x y).app (L.obj a)).right =
      augmentation ((codes L).obj a) (u.obj a) ≫
        ((native r).app a ≫ G.collapse.app a).map ≫ Q.map := by
  have h : s.app a ≫ (pr.map (r.app a)).2 = 𝟙 ((degrees M).obj a) :=
    NatTrans.congr_app hs a
  exact JTParametrizedTargetPullback.pulled_raw (r.app a) (u.obj a) (s.app a) h
    (G.parameter a) Q (G.collapse.app a) (G.raw a)

/-- Pull the full parameter back along a decorated native collapse with a
section on coefficients. The lifted family retains the same fixed target. -/
def pullback : Family Q L u where
  collapse := native r ≫ G.collapse
  parameter := pulledParameter r G s
  parameter_map f := pulledParameter_map r G s f
  raw a := pulled_raw r G s hs a

/-- The pullback projection satisfies the exact native and parameter laws. -/
theorem pullback_compatible : Compatible r (𝟙 u) (pullback r G s hs) G where
  collapse := rfl
  parameter := pulledParameter_square r G s hs

/-- The projection compares the two whole evaluations in the same fixed target. -/
def pullback_compare : evaluate (pullback r G s hs) ⟶ presentation r (𝟙 u) ⋙ evaluate G :=
  compare r (𝟙 u) (pullback r G s hs) G (pullback_compatible r G s hs)

end Pullback

end

end DaggerModels.PartII.JTParametrizedTargetFamilyComparison
