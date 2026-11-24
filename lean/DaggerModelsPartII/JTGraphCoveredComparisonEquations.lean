import DaggerModelsPartII.JTGraphCoveredCylinderEquations
import DaggerModelsPartII.JTNecklacePrismQuotientWeak

/-!
Coordinate equations for comparisons in the original fixed target.

Reuse the public covered projection cylinder equation, the original native
augmentation, prism quotient naturality, and the two projections of the
literal fixed-target pullback. No terminal-target identification is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredComparisonEquations

open JTParametrizedTargetFamilies (codes)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceEndpointCylinder (cylinder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)

private abbrev productDiagram := JTJointRelativeParameters.withTime Q.map J time
  (Over.lift (codes L) c) (JTTargetIntervalOverMapping.whole Q.code)

variable {Y : I ⥤ SSet.{0}} (π : Y ⟶ productDiagram Q L time c)

/-- The native leg on the whole cylinder is the actual map to Q, including
its original native collapse. The fixed target need not be a point. -/
theorem native_cylinder (a : I) :
    (JTGraphCoveredCylinderEquations.inc Q L time c π).app a ≫
        ((JTGraphCoveredLabelEvaluation.nativeLeg Q L time c π).app a).right =
      π.app a ≫ fst ((codes L).obj a).toSSet (J.obj (time.obj a)) ≫ (c.app a).map := by
  change (JTGraphCoveredCylinderEquations.inc Q L time c π).app a ≫
    (((JTGraphCoveredLabelEvaluation.projection Q L time c π).app a).right ≫
      ((JTDecoratedIntervalCylinder.native Q (Over.lift (codes L) c) time).app a).right) = _
  rw [← Category.assoc, JTGraphCoveredCylinderEquations.projection_cylinder]
  change (π.app a ≫ (cylinder ((codes L).obj a)).app (time.obj a)) ≫
    (NecklaceCylinderAugmentation.augmentation ((codes L).obj a) (time.obj a) ≫
      (c.app a).map) = _
  calc
    _ = π.app a ≫ (((cylinder ((codes L).obj a)).app (time.obj a) ≫
        NecklaceCylinderAugmentation.augmentation ((codes L).obj a) (time.obj a)) ≫
          (c.app a).map) := by simp only [Category.assoc]
    _ = _ := by rw [NecklaceCylinderAugmentation.augmentation_cylinder]

/-- A full graph map commutes with both native and coefficient changes
before taking the endpoint quotient. -/
theorem graph_cylinder_map {X Y : SSet.{0}} {T U : NecklaceCode}
    {k l : SimplexCategory} (f : T ⟶ U) (α : k ⟶ l)
    (h : X ⟶ T.toSSet) (θ : X ⟶ J.obj k)
    (h' : Y ⟶ U.toSSet) (θ' : Y ⟶ J.obj l) (η : X ⟶ Y)
    (hn : h ≫ f.map = η ≫ h') (hθ : θ ≫ J.map α = η ≫ θ') :
    (lift h θ ≫ (cylinder T).app k) ≫
        (NecklaceCylinderJointDiagram.cylinderUnder.map
          (show (T, k) ⟶ (U, l) from (f, α))).right =
      η ≫ lift h' θ' ≫ (cylinder U).app l := by
  have hp : lift h θ ≫ (f.map ⊗ₘ J.map α) = η ≫ lift h' θ' := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst] using hn
    · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd] using hθ
  have hc := JTNecklacePrismQuotientWeak.quotient.naturality
    (show (T, k) ⟶ (U, l) from (f, α))
  change (f.map ⊗ₘ J.map α) ≫ (cylinder U).app l =
    (cylinder T).app k ≫
      (NecklaceCylinderJointDiagram.cylinderUnder.map
        (show (T, k) ⟶ (U, l) from (f, α))).right at hc
  rw [Category.assoc, ← hc, ← Category.assoc, hp]
  exact Category.assoc _ _ _

/-- Equality of both complete legs gives the literal fixed-Q pullback
square. Both labels keep the original global endpoints. -/
theorem fixedTarget_square
    {a b : DecoratedNecklaceHomDiagram.Index W x y}
    {U V : Under B} (f : a ⟶ b) (r : U ⟶ V)
    (u₀ : U ⟶ (JTTargetCommaPullback.diagram W x y Q).obj a)
    (v₀ : V ⟶ (JTTargetCommaPullback.diagram W x y Q).obj b)
    {u₁ : U ⟶ (underDiagram W x y).obj a}
    {v₁ : V ⟶ (underDiagram W x y).obj b}
    {u₂ : U ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    {v₂ : V ⟶ BoundaryNecklaceComma.necklaceUnder.obj Q.code}
    (hu₁ : u₀ ≫ JTTargetCommaPullback.fst W x y Q a = u₁)
    (hv₁ : v₀ ≫ JTTargetCommaPullback.fst W x y Q b = v₁)
    (hu₂ : u₀ ≫ JTTargetCommaPullback.snd W x y Q a = u₂)
    (hv₂ : v₀ ≫ JTTargetCommaPullback.snd W x y Q b = v₂)
    (h₁ : u₁ ≫ (underDiagram W x y).map f = r ≫ v₁)
    (h₂ : u₂ = r ≫ v₂) :
    u₀ ≫ (JTTargetCommaPullback.diagram W x y Q).map f = r ≫ v₀ := by
  apply (IsPullback.of_hasPullback ((underCocone W x y).app b)
    (JTTargetCommaPullback.targetMap W x y Q)).hom_ext
  · change (u₀ ≫ (JTTargetCommaPullback.diagram W x y Q).map f) ≫
        JTTargetCommaPullback.fst W x y Q b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.fst W x y Q b
    rw [Category.assoc, JTTargetCommaPullback.map_fst W x y Q f,
      ← Category.assoc u₀, hu₁, Category.assoc r, hv₁]
    exact h₁
  · change (u₀ ≫ (JTTargetCommaPullback.diagram W x y Q).map f) ≫
        JTTargetCommaPullback.snd W x y Q b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.snd W x y Q b
    rw [Category.assoc, JTTargetCommaPullback.map_snd W x y Q f,
      hu₂, Category.assoc r, hv₂]
    exact h₂

end
end DaggerModels.PartII.JTGraphCoveredComparisonEquations
