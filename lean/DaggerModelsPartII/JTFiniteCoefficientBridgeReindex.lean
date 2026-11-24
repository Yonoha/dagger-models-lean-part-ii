import DaggerModelsPartII.JTFiniteCoefficientBridgeCylinder

/-!
# Restricting a finite bridge to an ordered subcollection of copies
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeReindex

open JTFiniteCoefficientBridgeOrder (bridge vertexEquiv mapCopies_vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv mapCopies_vertex)
open JTFiniteCoefficientBridgePrism
open JTFiniteCoefficientBridgeGroupoid (paired)
open JTFiniteCoefficientBridgeCylinder
open JTCodiscreteParameterPairing (coord coord_map pairBy coord_pairBy)
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a
private abbrev J := GroupoidSimplex.parameter

variable {m m' : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory} {b₂ : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (d : ∀ e, k ⟶ b₂ e) (u : k ⟶ b') (n : SimplexCategory)
variable (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
variable (hr : ∀ (e : Fin (m + 1)) (x : Fin (k.len + 1) × Fin (n.len + 1)),
  JTCommonCoefficientParameter.vertexEquiv (c e) n x =
    JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x)

private abbrev coefficientOperator := JTFiniteCoefficientBridgeOrder.mapCopies c d u n j hj hr
private abbrev timeOperator := JTFiniteCoefficientBridgeTime.mapCopies j hj n

theorem rankVertex_mapCopies (a : Fin (k.len + 1)) (t : Fin ((time m n).len + 1)) :
    (coefficientOperator c d u n j hj hr).toOrderHom (rankVertex c u n (a, t)) =
      rankVertex d u n (a, (timeOperator n j hj).toOrderHom t) := by
  obtain ⟨⟨e, s⟩, rfl⟩ := (timeVertexEquiv m n).surjective t
  rw [rankVertex_apply, mapCopies_vertexEquiv, mapCopies_vertex, rankVertex_apply]

/-- The entire ordinary prism restricts along the specified subcollection. -/
theorem prism_mapCopies :
    prism.{v} c u n ≫ SSet.stdSimplex.map (coefficientOperator c d u n j hj hr) =
      (simplex k ◁ SSet.stdSimplex.map (timeOperator n j hj)) ≫ prism d u n := by
  apply NatTrans.ext
  funext q z
  apply SSet.stdSimplex.objEquiv.injective
  ext a : 3
  change (coefficientOperator c d u n j hj hr).toOrderHom
      ((SSet.stdSimplex.objEquiv ((prism c u n).app q z)).toOrderHom a) =
    (SSet.stdSimplex.objEquiv ((prism d u n).app q
      (z.1, (SSet.stdSimplex.map (timeOperator n j hj)).app q z.2))).toOrderHom a
  rw [prism_app, prism_app]
  exact rankVertex_mapCopies c d u n j hj hr _ _

/-- The same restriction holds on the original groupoid parameters. -/
theorem paired_mapCopies :
    paired c u n ≫ J.map (coefficientOperator c d u n j hj hr) =
      (J.obj k ◁ J.map (timeOperator n j hj)) ≫ paired d u n := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z a
  change coord _ q ((J.map (coefficientOperator c d u n j hj hr)).app q
      ((pairBy (rankVertex c u n)).app q z)) a =
    coord _ q ((pairBy (rankVertex d u n)).app q
      (z.1, (J.map (timeOperator n j hj)).app q z.2)) a
  rw [coord_map, coord_pairBy, coord_pairBy, coord_map]
  exact rankVertex_mapCopies c d u n j hj hr _ _

private theorem graphPrism_mapCopies {X : SSet.{0}} (s : X ⟶ J.obj k) :
    graphPrism c u n s ≫ (X ◁ J.map (coefficientOperator c d u n j hj hr)) =
      (X ◁ J.map (timeOperator n j hj)) ≫ graphPrism d u n s := by
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_mapCopies c d u n j hj hr, ← MonoidalCategory.id_tensorHom,
      ← Category.assoc (s ⊗ₘ 𝟙 (J.obj (time m n))),
      ← Category.assoc (𝟙 X ⊗ₘ J.map (timeOperator n j hj)),
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rfl

/-- The actual reduced cylinder and both ordered endpoints restrict
along the same map of whole copy subcollections. -/
theorem cylinderMap_mapCopies (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    cylinderMap c u n T s ≫ (value T).map (coefficientOperator c d u n j hj hr) =
      (value T).map (timeOperator n j hj) ≫ cylinderMap d u n T s := by
  have hC {a a' : SimplexCategory} (g : a ⟶ a') :
      (T.toSSet ◁ J.map g) ≫ (cylinder T).app a' =
        (cylinder T).app a ≫ (value T).map g :=
    (cylinder T).naturality g
  have hB {a a' : SimplexCategory} (g : a ⟶ a') :
      (boundary T).app a ≫ (value T).map g = (boundary T).app a' := by
    rw [← (boundary T).naturality g]
    exact Category.id_comp _
  apply (isPushout T (time m n)).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, ← hC,
      ← Category.assoc, graphPrism_mapCopies c d u n j hj hr s, Category.assoc, ←
      Category.assoc ((cylinder T).app (time m n)), ← hC, Category.assoc, cylinderMap_cylinder]
  · rw [← Category.assoc, cylinderMap_boundary, hB, ← Category.assoc, hB, cylinderMap_boundary]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeReindex
