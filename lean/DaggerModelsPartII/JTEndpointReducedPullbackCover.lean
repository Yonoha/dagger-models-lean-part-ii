import DaggerModelsPartII.JTEndpointReducedCover

/-!
# The reduced endpoint cylinder over the full inverse-image boundary

The covered boundary is the pullback of the original boundary inclusion
along a cylinder projection. Its collapse uses the entire inverse image.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen
open DaggerSSetGluing

namespace DaggerModels.PartII.JTEndpointReducedPullbackCover

noncomputable section

variable {I : Type} [SmallCategory I] {B : SSet.{0}}
variable {A X X' : I ⥤ SSet.{0}} (π : X' ⟶ X) (d : A ⟶ X)

/-- The complete inverse image of the old boundary. -/
abbrev covered : I ⥤ SSet.{0} := pullback π d

abbrev u : covered π d ⟶ X' := pullback.fst π d
abbrev v : covered π d ⟶ A := pullback.snd π d

/-- Inclusion of the covered boundary into the new cylinder. -/
abbrev boundaryInclusion : covered π d ⟶ X' := u π d

/-- Projection of the covered boundary onto the old boundary. -/
abbrev boundaryProjection : covered π d ⟶ A := v π d

/-- The defining pullback square of the covered boundary. -/
theorem boundary_square : boundaryInclusion π d ≫ π = boundaryProjection π d ≫ d :=
  pullback.condition

private theorem uv : u π d ≫ π = v π d ≫ d := boundary_square π d

private theorem pointwise_pullback (p : I) :
    IsPullback ((u π d).app p) ((v π d).app p) (π.app p) (d.app p) :=
  (IsPullback.of_hasPullback π d).map ((evaluation I SSet.{0}).obj p)
/-- The boundary projection is a trivial fibration whenever the cylinder
projection is a trivial fibration in this degree. -/
theorem boundaryProjection_trivial (p : I) (hπ : trivialFibrations SSet.{0} (π.app p)) :
    trivialFibrations SSet.{0} ((v π d).app p) :=
  (trivialFibrations SSet.{0}).of_isPullback (pointwise_pullback π d p) hπ

/-- The inverse image of a monic old boundary is monic in each degree. -/
theorem boundaryInclusion_mono (p : I) [Mono (d.app p)] : Mono ((u π d).app p) := by
  exact (monomorphisms.iff _).mp ((monomorphisms SSet.{0}).of_isPullback
    (pointwise_pullback π d p).flip ((monomorphisms.iff _).mpr inferInstance))

variable (e : A ⟶ (Functor.const I).obj B)
variable (Y : I ⥤ Under B) (i : X ⟶ Y ⋙ Under.forget B)
variable (hi : d ≫ i = e ≫ JTEndpointReducedCover.boundary Y)

/-- Collapse the entire covered boundary onto the old endpoint boundary. -/
abbrev collapse : covered π d ⟶ (Functor.const I).obj B := v π d ≫ e

/-- The reduced cylinder built from the full inverse image. -/
abbrev reduced : I ⥤ Under B := JTEndpointReducedCover.reduced (u π d) (collapse π d e)

include hi in
private theorem covered_hi :
    v π d ≫ d ≫ i = collapse π d e ≫ JTEndpointReducedCover.boundary Y := by
  rw [Category.assoc, hi, ← Category.assoc]

include hi in
private theorem covered_square :
    u π d ≫ (π ≫ i) = collapse π d e ≫ JTEndpointReducedCover.boundary Y := by
  rw [← Category.assoc, uv π d, Category.assoc]
  exact covered_hi π d e Y i hi

/-- Projection of the reduced covered cylinder to the old pushout diagram. -/
def projection : reduced π d e ⟶ Y :=
  JTEndpointReducedCover.descend (u π d) (collapse π d e) Y (π ≫ i)
    (covered_square π d e Y i hi)

/-- The projection agrees exactly with the old cylinder map on its cylinder summand. -/
theorem projection_cylinder (p : I) :
    (pushout.inl (u π d) (collapse π d e)).app p ≫
      ((projection π d e Y i hi).app p).right = π.app p ≫ i.app p :=
  JTEndpointReducedCover.descend_cylinder (u π d) (collapse π d e) Y (π ≫ i)
    (covered_square π d e Y i hi) p

/-- The projection agrees exactly with the old boundary map on the collapsed summand. -/
theorem projection_boundary (p : I) :
    (pushout.inr (u π d) (collapse π d e)).app p ≫
      ((projection π d e Y i hi).app p).right =
      (JTEndpointReducedCover.boundary Y).app p :=
  Under.w ((projection π d e Y i hi).app p)

/-- Pointwise weak equivalence of the reduced projection. The three vertical
maps of the pushout cube are the boundary projection, the cylinder projection,
and the identity on the endpoint boundary. -/
theorem projection_weak (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    [Mono (d.app p)] (hπ : trivialFibrations SSet.{0} (π.app p)) :
    WeakEquivalence ((projection π d e Y i hi).app p).right := by
  letI : Mono ((u π d).app p) := boundaryInclusion_mono π d p
  let lower : IsPushout ((u π d).app p) ((collapse π d e).app p)
      ((pushout.inl (u π d) (collapse π d e)).app p)
      ((pushout.inr (u π d) (collapse π d e)).app p) :=
    (IsPushout.of_hasPushout (u π d) (collapse π d e)).map ((evaluation I _).obj p)
  let m := ((projection π d e Y i hi).app p).right
  have hk : (u π d).app p ≫ π.app p = (v π d).app p ≫ d.app p :=
    NatTrans.congr_app (uv π d) p
  have he : (collapse π d e).app p ≫ 𝟙 B = (v π d).app p ≫ e.app p := by
    simp [collapse]
  have hr : (pushout.inl (u π d) (collapse π d e)).app p ≫ m =
      π.app p ≫ i.app p := projection_cylinder π d e Y i hi p
  have hs : (pushout.inr (u π d) (collapse π d e)).app p ≫ m =
      𝟙 B ≫ (JTEndpointReducedCover.boundary Y).app p := by
    exact (Under.w ((projection π d e Y i hi).app p)).trans
      (Category.id_comp _).symm
  apply (weakEquivalence_iff_GW _).mpr
  exact DaggerSSetGluing.geometric_of_pushout_cube _ _ _ _ _ _ _ _ lower sq
    ((v π d).app p) (π.app p) (𝟙 B) m hk he hr hs
    ((weakEquivalence_iff_GW _).mp
      ((mem_trivialFibrations_iff _).mp (boundaryProjection_trivial π d p hπ)).2)
    ((weakEquivalence_iff_GW _).mp
      ((mem_trivialFibrations_iff _).mp hπ).2)
    ((weakEquivalence_iff_GW (𝟙 B)).mp (inferInstance : WeakEquivalence (𝟙 B)))

/-- Typeclass form of the pointwise weak-equivalence result. -/
theorem projection_weak_of_trivialFibration (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p)
      ((JTEndpointReducedCover.boundary Y).app p))
    [Mono (d.app p)] [Fibration (π.app p)] [WeakEquivalence (π.app p)] :
    WeakEquivalence ((projection π d e Y i hi).app p).right := by
  apply projection_weak π d e Y i hi p sq
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

end

end DaggerModels.PartII.JTEndpointReducedPullbackCover
