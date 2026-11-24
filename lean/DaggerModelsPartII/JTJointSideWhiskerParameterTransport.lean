import DaggerModelsPartII.JTJointSideWhisker

/-!
# Mixed native, coefficient and time transport of a relative endpoint edge
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointSideWhiskerParameterTransport

open JTComposedPrismLabels (parameter parameter_left parameter_right)
open JTJointSideWhisker (edgeParameter appendParameter prependParameter)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1
private abbrev pt : SSet.{0} := Δ[0]
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev firstAt (T : NecklaceCode) := pointAt.{0} T (ULift.up 0)
private abbrev lastAt (T : NecklaceCode) := pointAt.{0} T (ULift.up (Fin.last T.len))

section Restrict

variable {X Y X' Y' I I' : SSet.{0}} {k k' : SimplexCategory}
variable (u : I ⟶ I') (r : k ⟶ k')

/-- Restriction to a commuting horizontal square preserves the mixed parameter equation. -/
theorem restrict_square (p : Y ⊗ I ⟶ J.obj k) (q : Y' ⊗ I' ⟶ J.obj k')
    (g : Y ⟶ Y') (f : X ⟶ X') (i : X ⟶ Y) (j : X' ⟶ Y')
    (h : i ≫ g = f ≫ j)
    (hp : (g ⊗ₘ u) ≫ q = p ≫ J.map r) :
    (f ⊗ₘ u) ≫ ((j ⊗ₘ 𝟙 I') ≫ q) = ((i ⊗ₘ 𝟙 I) ≫ p) ≫ J.map r := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ← h,
    ← Category.id_comp u, ← tensorHom_comp_tensorHom, Category.assoc, hp, Category.assoc]

/-- Pulling a timed endpoint across the extra edge is natural in both other coordinates. -/
theorem edge_map (p : pt ⊗ I ⟶ J.obj k) (q : pt ⊗ I' ⟶ J.obj k')
    (h : (𝟙 pt ⊗ₘ u) ≫ q = p ≫ J.map r) :
    (𝟙 E.toSSet ⊗ₘ u) ≫ edgeParameter q = edgeParameter p ≫ J.map r :=
  restrict_square u r p q (𝟙 pt) (𝟙 E.toSSet) (term E.toSSet) (term E.toSSet)
    (by simp only [Category.id_comp, Category.comp_id]) h

end Restrict

section Wedge

variable {T U T' U' : NecklaceCode} {k k' : SimplexCategory} {I I' : SSet.{0}}
variable (f : T ⟶ T') (g : U ⟶ U') (u : I ⟶ I') (r : k ⟶ k')
variable (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
variable (p' : T'.toSSet ⊗ I' ⟶ J.obj k') (q' : U'.toSSet ⊗ I' ⟶ J.obj k')
variable (h : (lastAt T ⊗ₘ 𝟙 I) ≫ p = (firstAt U ⊗ₘ 𝟙 I) ≫ q)
variable (h' : (lastAt T' ⊗ₘ 𝟙 I') ≫ p' = (firstAt U' ⊗ₘ 𝟙 I') ≫ q')

/-- The wedge parameter respects the exact simultaneous change on both pieces. -/
theorem parameter_map (hp : (f.map ⊗ₘ u) ≫ p' = p ≫ J.map r)
    (hq : (g.map ⊗ₘ u) ≫ q' = q ≫ J.map r) :
    ((wedgeMap f g).map ⊗ₘ u) ≫ parameter p' q' h' = parameter p q h ≫ J.map r := by
  apply ((wedgeIsPushout T U).map (tensorRight I)).hom_ext
  · change (wedgeιLeft T U ⊗ₘ 𝟙 I) ≫ (((wedgeMap f g).map ⊗ₘ u) ≫ _) = _
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, wedgeMap_left,
      ← Category.comp_id u, ← tensorHom_comp_tensorHom, Category.assoc, parameter_left,
      ← Category.assoc]
    change (f.map ⊗ₘ u) ≫ p' =
      ((wedgeιLeft T U ⊗ₘ 𝟙 I) ≫ parameter p q h) ≫ J.map r
    rw [parameter_left]
    exact hp
  · change (wedgeιRight T U ⊗ₘ 𝟙 I) ≫ (((wedgeMap f g).map ⊗ₘ u) ≫ _) = _
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, wedgeMap_right,
      ← Category.comp_id u, ← tensorHom_comp_tensorHom, Category.assoc, parameter_right,
      ← Category.assoc]
    change (g.map ⊗ₘ u) ≫ q' =
      ((wedgeιRight T U ⊗ₘ 𝟙 I) ≫ parameter p q h) ≫ J.map r
    rw [parameter_right]
    exact hq

end Wedge

section Edges

variable {T T' : NecklaceCode} {k k' : SimplexCategory} {I I' : SSet.{0}}
variable (g : T ⟶ T') (u : I ⟶ I') (r : k ⟶ k')
variable (p : T.toSSet ⊗ I ⟶ J.obj k) (q : T'.toSSet ⊗ I' ⟶ J.obj k')
variable (h : (g.map ⊗ₘ u) ≫ q = p ≫ J.map r)

include h in
/-- The completed left cut respects a cut-preserving mixed operator. -/
theorem append_map :
    ((wedgeMap g (𝟙 E)).map ⊗ₘ u) ≫ appendParameter q = appendParameter p ≫ J.map r := by
  apply parameter_map g (𝟙 E) u r _ _ _ _ _ _ h
  change (𝟙 E.toSSet ⊗ₘ u) ≫ edgeParameter ((lastAt T' ⊗ₘ 𝟙 I') ≫ q) =
    edgeParameter ((lastAt T ⊗ₘ 𝟙 I) ≫ p) ≫ J.map r
  apply edge_map u r
  apply restrict_square u r p q g.map (𝟙 pt) (lastAt T) (lastAt T') _ h
  rw [Category.id_comp]
  exact pointAt_last_comp g

include h in
/-- The completed right cut respects a cut-preserving mixed operator. -/
theorem prepend_map :
    ((wedgeMap (𝟙 E) g).map ⊗ₘ u) ≫ prependParameter q =
      prependParameter p ≫ J.map r := by
  refine parameter_map (𝟙 E) g u r _ _ _ _ _ _ ?_ h
  change (𝟙 E.toSSet ⊗ₘ u) ≫ edgeParameter ((firstAt T' ⊗ₘ 𝟙 I') ≫ q) =
    edgeParameter ((firstAt T ⊗ₘ 𝟙 I) ≫ p) ≫ J.map r
  apply edge_map u r
  apply restrict_square u r p q g.map (𝟙 pt) (firstAt T) (firstAt T') _ h
  rw [Category.id_comp]
  exact pointAt_first_comp g

end Edges

end
end DaggerModels.PartII.JTJointSideWhiskerParameterTransport
