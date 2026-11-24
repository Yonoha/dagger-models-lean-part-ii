import DaggerModelsPartII.JTTargetCommaPullbackDiagram
import DaggerModelsPartII.JTOverParametrizedMapping

/-!
# Parametrized maps to the actual decorated cylinders

Over-target maps to each decorated pullback correspond to the full
parametrized maps into its original cylinder with the specified equality
over the raw realization. This identification commutes with source
restriction and with every decorated label operator.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedCylinderOverMapping

open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTTargetCommaPullback (diagram targetMap fst snd map_fst map_snd)

noncomputable section

private def sliceEquiv {Q Z A E : SSet.{0}} {a : A ⟶ Z} {q : Q ⟶ Z}
    {l : E ⟶ A} {r : E ⟶ Q} (sq : IsPullback l r a q) (P : Over Q) :
    (P ⟶ Over.mk r) ≃ ((Over.map q).obj P ⟶ Over.mk a) where
  toFun m := Over.homMk (m.left ≫ l) (by
    change (m.left ≫ l) ≫ a = P.hom ≫ q
    have hm : m.left ≫ r = P.hom := Over.w m
    rw [Category.assoc, sq.w, ← Category.assoc, hm])
  invFun m := Over.homMk (sq.lift m.left P.hom (Over.w m)) (sq.lift_snd _ _ _)
  left_inv m := by
    apply Over.OverMorphism.ext
    apply sq.hom_ext
    · exact sq.lift_fst _ _ _
    · exact (sq.lift_snd _ _ _).trans (Over.w m).symm
  right_inv m := by
    apply Over.OverMorphism.ext
    exact sq.lift_fst _ _ _

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev B := JTXiEndpointCollapse.boundary

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

local notation "I" => DecoratedNecklaceHomDiagram.Index W x y
local notation "D" => underDiagram W x y
local notation "ρ" => underCocone W x y
local notation "E" => diagram W x y Q

private abbrev forgetBoundary := Under.forget B

/-- The actual decorated pullback, viewed over the entire native target. -/
def decoratedTarget : I ⥤ Over Q.code.toSSet :=
  Over.lift (E ⋙ forgetBoundary) {
    app i := (snd W x y Q i).right
    naturality := by
      intro i j u
      change ((E).map u).right ≫ (snd W x y Q j).right =
        (snd W x y Q i).right ≫ 𝟙 Q.code.toSSet
      exact (congrArg (fun h ↦ h.right) (map_snd W x y Q u)).trans
        (Category.comp_id _).symm }

/-- The actual decorated cylinder, viewed over the raw realization. -/
def rawTarget : I ⥤ Over (Raw W) :=
  Over.lift (D ⋙ forgetBoundary) {
    app i := ((ρ).app i).right
    naturality := by
      intro i j u
      exact congrArg (fun h ↦ h.right) ((ρ).naturality u) }

private theorem pullback_at (i : I) :
    IsPullback (fst W x y Q i).right (snd W x y Q i).right ((ρ).app i).right Q.map :=
  (IsPullback.of_hasPullback ((ρ).app i) (targetMap W x y Q)).map forgetBoundary

/-- The full map over the native target is equivalent to a map into the
same original cylinder satisfying the original equation over the raw realization. -/
def homEquiv (P : Over Q.code.toSSet) (i : I) :
    (P ⟶ (decoratedTarget W x y Q).obj i) ≃
      ((Over.map Q.map).obj P ⟶ (rawTarget W x y).obj i) :=
  sliceEquiv (pullback_at W x y Q i) P

theorem homEquiv_precomp {P P' : Over Q.code.toSSet} (g : P ⟶ P') (i : I)
    (m : P' ⟶ (decoratedTarget W x y Q).obj i) :
    homEquiv W x y Q P i (g ≫ m) =
      (Over.map Q.map).map g ≫ homEquiv W x y Q P' i m := by
  apply Over.OverMorphism.ext
  change (g.left ≫ m.left) ≫ (fst W x y Q i).right =
    g.left ≫ (m.left ≫ (fst W x y Q i).right)
  exact Category.assoc _ _ _

theorem homEquiv_postcomp (P : Over Q.code.toSSet) {i j : I} (u : i ⟶ j)
    (m : P ⟶ (decoratedTarget W x y Q).obj i) :
    homEquiv W x y Q P j (m ≫ (decoratedTarget W x y Q).map u) =
      homEquiv W x y Q P i m ≫ (rawTarget W x y).map u := by
  apply Over.OverMorphism.ext
  change (m.left ≫ ((E).map u).right) ≫ (fst W x y Q j).right =
    (m.left ≫ (fst W x y Q i).right) ≫ ((D).map u).right
  have h : ((E).map u).right ≫ (fst W x y Q j).right =
      (fst W x y Q i).right ≫ ((D).map u).right :=
    congrArg (fun k ↦ k.right) (map_fst W x y Q u)
  simp only [Category.assoc, h]

variable (K : SimplexCategory ⥤ SSet.{0})

private def rawFrame (P : Over Q.code.toSSet) : SimplexCategory ⥤ Over (Raw W) :=
  (JTOverParametrizedMapping.frame K Q.code.toSSet).obj P ⋙ Over.map Q.map

/-- Parametrized strict lifts into the original cylinder over the raw realization. -/
def rawMapping (P : Over Q.code.toSSet) (i : I) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := (rawTarget W x y).obj i) (rawFrame W x y Q K P)

def rawPrecomp {P P' : Over Q.code.toSSet} (g : P ⟶ P') (i : I) :
    rawMapping W x y Q K P' i ⟶ rawMapping W x y Q K P i :=
  EndpointMappingFiber.precomp (Z := (rawTarget W x y).obj i)
    (Functor.whiskerRight ((JTOverParametrizedMapping.frame K Q.code.toSSet).map g)
      (Over.map Q.map))

def rawPostcomp (P : Over Q.code.toSSet) {i j : I} (u : i ⟶ j) :
    rawMapping W x y Q K P i ⟶ rawMapping W x y Q K P j :=
  Functor.whiskerLeft (rawFrame W x y Q K P).op (yoneda.map ((rawTarget W x y).map u))

/-- The two descriptions agree in every parameter degree and on all its operators. -/
def mappingIso (P : Over Q.code.toSSet) (i : I) :
    JTOverParametrizedMapping.mapping K Q.code.toSSet P ((decoratedTarget W x y Q).obj i) ≅
      rawMapping W x y Q K P i :=
  NatIso.ofComponents (fun k ↦ (homEquiv W x y Q
    (((JTOverParametrizedMapping.frame K Q.code.toSSet).obj P).obj k.unop) i).toIso) (by
      intro k l g
      funext m
      exact homEquiv_precomp W x y Q
        (((JTOverParametrizedMapping.frame K Q.code.toSSet).obj P).map g.unop) i m)

theorem mappingIso_precomp {P P' : Over Q.code.toSSet} (g : P ⟶ P') (i : I) :
    JTOverParametrizedMapping.precomp K Q.code.toSSet g ((decoratedTarget W x y Q).obj i) ≫
        (mappingIso W x y Q K P i).hom =
      (mappingIso W x y Q K P' i).hom ≫ rawPrecomp W x y Q K g i := by
  apply NatTrans.ext
  funext k m
  exact homEquiv_precomp W x y Q
    (((JTOverParametrizedMapping.frame K Q.code.toSSet).map g).app k.unop) i m

theorem mappingIso_postcomp (P : Over Q.code.toSSet) {i j : I} (u : i ⟶ j) :
    JTOverParametrizedMapping.postcomp K Q.code.toSSet P ((decoratedTarget W x y Q).map u) ≫
        (mappingIso W x y Q K P j).hom =
      (mappingIso W x y Q K P i).hom ≫ rawPostcomp W x y Q K P u := by
  apply NatTrans.ext
  funext k m
  exact homEquiv_postcomp W x y Q
    (((JTOverParametrizedMapping.frame K Q.code.toSSet).obj P).obj k.unop) u m

end

end DaggerModels.PartII.JTDecoratedCylinderOverMapping
