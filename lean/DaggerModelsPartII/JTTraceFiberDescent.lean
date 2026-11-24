import DaggerModelsPartII.JTJointRelativeParameters

/-!
# Descent of groupoid parameters along vertex-surjective diagram maps

A natural parameter descends exactly when its vertex coordinates are constant
on the fibers of the map. The codiscrete parameter is determined by vertices,
so the descended natural transformation is unique.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTraceFiberDescent

open JTJointRelativeParameters (parameterOfNaturalVertices parameterOfNaturalVertices_coord
  parameter_ext)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] {M N : I ⥤ SSet.{0}}
variable (a : M ⟶ N) (k : I ⥤ SimplexCategory)
variable (s : M ⟶ k ⋙ J)

/-- The parameter takes equal vertex coordinates on each vertex fiber. -/
def FiberConstant : Prop :=
  ∀ p (u v : (M.obj p).obj zero),
    (a.app p).app zero u = (a.app p).app zero v →
      coord (k.obj p) zero ((s.app p).app zero u) 0 =
        coord (k.obj p) zero ((s.app p).app zero v) 0

variable (h : ∀ p, Function.Surjective ((a.app p).app zero))

private def lift (p : I) (v : (N.obj p).obj zero) : (M.obj p).obj zero :=
  Classical.choose (h p v)

private theorem lift_fac (p : I) (v : (N.obj p).obj zero) :
    (a.app p).app zero (lift a h p v) = v :=
  Classical.choose_spec (h p v)

private def assignment (p : I) (v : (N.obj p).obj zero) :
    Fin ((k.obj p).len + 1) :=
  coord (k.obj p) zero ((s.app p).app zero (lift a h p v)) 0

private theorem assignment_natural (hFiber : FiberConstant a k s)
    {p p' : I} (f : p ⟶ p') (v : (N.obj p).obj zero) :
    assignment a k s h p' ((N.map f).app zero v) =
      (k.map f).toOrderHom (assignment a k s h p v) := by
  let x := lift a h p v
  let y := lift a h p' ((N.map f).app zero v)
  have ha := congrFun (NatTrans.congr_app (a.naturality f) zero) x
  change ((a.app p').app zero) ((M.map f).app zero x) =
    (N.map f).app zero ((a.app p).app zero x) at ha
  have hxy : (a.app p').app zero y =
      (a.app p').app zero ((M.map f).app zero x) := by
    rw [show (a.app p').app zero y = (N.map f).app zero v from lift_fac a h p' _,
      ha, lift_fac a h p v]
  have hs := congrFun (NatTrans.congr_app (s.naturality f) zero) x
  change (s.app p').app zero ((M.map f).app zero x) =
    (J.map (k.map f)).app zero ((s.app p).app zero x) at hs
  unfold assignment
  change coord (k.obj p') zero ((s.app p').app zero y) 0 =
    (k.map f).toOrderHom (coord (k.obj p) zero ((s.app p).app zero x) 0)
  rw [hFiber p' y ((M.map f).app zero x) hxy, hs,
    JTCodiscreteParameterPairing.coord_map]

/-- A fiber-constant parameter descends to the quotient diagram. -/
def descend (hFiber : FiberConstant a k s) : N ⟶ k ⋙ J :=
  parameterOfNaturalVertices N k (assignment a k s h)
    (assignment_natural a k s h hFiber)

@[reassoc]
theorem precomp_descend (hFiber : FiberConstant a k s) :
    a ≫ descend a k s h hFiber = s := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro u
  change coord (k.obj p) zero
      (((descend a k s h hFiber).app p).app zero ((a.app p).app zero u)) 0 =
    coord (k.obj p) zero ((s.app p).app zero u) 0
  rw [descend, parameterOfNaturalVertices_coord]
  exact hFiber p (lift a h p ((a.app p).app zero u)) u
    (lift_fac a h p _)

/-- The descended parameter is unique among parameters with the given pullback. -/
theorem precomp_injective (h : ∀ p, Function.Surjective ((a.app p).app zero))
    (t₁ t₂ : N ⟶ k ⋙ J)
    (ht : a ≫ t₁ = a ≫ t₂) : t₁ = t₂ := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro v
  obtain ⟨u, rfl⟩ := h p v
  exact congrArg (fun z ↦ coord (k.obj p) zero z 0)
    (congrFun (NatTrans.congr_app (NatTrans.congr_app ht p) zero) u)

/-- Existence of a descended parameter forces constancy on vertex fibers. -/
theorem fiberConstant_of_precomp (t : N ⟶ k ⋙ J)
    (ht : a ≫ t = s) : FiberConstant a k s := by
  intro p u v huv
  have hu := congrFun (NatTrans.congr_app (NatTrans.congr_app ht p) zero) u
  have hv := congrFun (NatTrans.congr_app (NatTrans.congr_app ht p) zero) v
  change (t.app p).app zero ((a.app p).app zero u) = (s.app p).app zero u at hu
  change (t.app p).app zero ((a.app p).app zero v) = (s.app p).app zero v at hv
  rw [← hu, huv, hv]

/-- Exact criterion for a unique natural descended groupoid parameter. -/
theorem existsUnique_iff_fiberConstant
    (h : ∀ p, Function.Surjective ((a.app p).app zero)) :
    (∃! t : N ⟶ k ⋙ J, a ≫ t = s) ↔ FiberConstant a k s := by
  constructor
  · rintro ⟨t, ht, -⟩
    exact fiberConstant_of_precomp a k s t ht
  · intro hFiber
    refine ⟨descend a k s h hFiber, precomp_descend a k s h hFiber, ?_⟩
    intro t ht
    exact precomp_injective a k h t (descend a k s h hFiber)
      (ht.trans (precomp_descend a k s h hFiber).symm)

end

end DaggerModels.PartII.JTTraceFiberDescent
