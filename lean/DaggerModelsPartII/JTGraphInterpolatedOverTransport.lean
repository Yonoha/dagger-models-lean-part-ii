import DaggerModelsPartII.JTGraphInterpolatedTargetCone

/-! Target transport of an interpolated comparison in the original slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedOverTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (Fiber comparisonFunctor)
open JTGraphInterpolatedOverOriginal
open JTGraphInterpolatedTransport (transportComparison transportPresentation transportTargetEq
  transportComparison_eq_presentation)
open JTGraphInterpolatedTargetOperators (transported_collapse)
open JTGraphInterpolatedTargetCone (sourceCone targetCone
  presentation_transport_triangle)
open JTNecklaceEndpointCylinder (under)
open JTTargetCommaPullback (diagram toPullback equivalence)
open BoundaryNecklaceComma (necklaceUnder)
open JTBoundaryNecklaceConeTriangle (mapCone_triangle overHom)
open JTBoundaryNecklaceConeReindex (mapCone)

noncomputable section

private theorem removeIdentitySource {J C : Type*} [Category* J] [Category* C]
    {F G : J ⥤ C} {M : J ⥤ J} (hM : M = 𝟭 J) (hG : M ⋙ G = G)
    {X Y : C} (τ : F ⟶ (Functor.const J).obj X) (σ : G ⟶ (Functor.const J).obj Y)
    (α : F ⟶ M ⋙ G) (a : X ⟶ Y)
    (h : α ≫ Functor.whiskerLeft M σ = τ ≫ (Functor.const J).map a) :
    (α ≫ eqToHom hG) ≫ σ = τ ≫ (Functor.const J).map a := by
  subst M
  have he : hG = rfl := Subsingleton.elim _ _
  rw [he, eqToHom_refl, Category.comp_id]
  exact h

private theorem mapCone_identity_source {J C D : Type*}
    [Category* J] [Category* C] [Category* D]
    {M : J ⥤ J} {F F' : J ⥤ C} {X X' : C}
    (τ : F ⟶ (Functor.const J).obj X) (τ' : F' ⟶ (Functor.const J).obj X')
    (α : F ⟶ M ⋙ F') (d : X ⟶ X')
    (h : α ≫ Functor.whiskerLeft M τ' = τ ≫ (Functor.const J).map d)
    (K : C ⥤ D) {Y Y' : D} (k : K.obj X ⟶ Y) (k' : K.obj X' ⟶ Y') (d' : Y ⟶ Y')
    (hk : K.map d ≫ k' = k ≫ d')
    (hM : M = 𝟭 J) (hF : M ⋙ (F' ⋙ K) = F' ⋙ K) :
    (Functor.whiskerRight α K ≫ eqToHom hF) ≫ mapCone τ' K k' =
      mapCone τ K k ≫ (Functor.const J).map d' :=
  removeIdentitySource hM hF (mapCone τ K k) (mapCone τ' K k')
    (Functor.whiskerRight α K) d' (mapCone_triangle M τ τ' α d h K k k' d' hk)

private def overHom_transport {J C : Type*} [Category* J] [Category* C]
    {F G : J ⥤ C} {X Y : C} (τ : F ⟶ (Functor.const J).obj X)
    (σ : G ⟶ (Functor.const J).obj Y) (α : F ⟶ G) (a : X ⟶ Y)
    (h : α ≫ σ = τ ≫ (Functor.const J).map a) :
    Over.lift F τ ⋙ Over.map a ⟶ Over.lift G σ :=
  overHom (τ ≫ (Functor.const J).map a) σ α h

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (a : U ⟶ V)

private abbrev transported := fun i ↦ (D i).transport a.left

private abbrev inv := (equivalence W x y Q).inverse

private abbrev fromPullback (U : TargetComma Q) :=
  ((equivalence W x y Q).unitIso.app U).inv

private theorem source_eq_mapCone :
    comparisonToOriginal c D hD = mapCone (sourceCone c D hD) inv (fromPullback U) :=
  rfl

set_option maxHeartbeats 480000 in
private theorem target_eq_mapCone :
    comparisonToOriginal (n := n) (c ≫ a.left.fiber.left) (transported D a)
        (transported_collapse c D hD a) =
      mapCone (targetCone c D hD a) inv (fromPullback V) :=
  source_eq_mapCone (U := V) (c ≫ a.left.fiber.left) (transported D a)
    (transported_collapse c D hD a)

set_option maxHeartbeats 240000 in
private theorem mapped_transport_triangle :
    (Functor.whiskerRight (transportPresentation c D hD a) inv ≫
        eqToHom (transportTargetEq c D hD a)) ≫
          mapCone (targetCone c D hD a) inv (fromPullback V) =
      mapCone (sourceCone c D hD) inv (fromPullback U) ≫ (Functor.const (Fiber S n)).map a :=
  mapCone_identity_source (sourceCone c D hD) (targetCone c D hD a)
    (transportPresentation c D hD a) ((toPullback W x y Q).map a)
    (presentation_transport_triangle c D hD a) inv (fromPullback U) (fromPullback V)
    a ((equivalence W x y Q).unitInv_naturality a)
    (JTCylinderOverTargetBaseChangeTime.map_id ((under S).obj n)) (transportTargetEq c D hD a)

set_option maxHeartbeats 180000 in
/-- Transport commutes with the two comparison cones to the original comma objects. -/
theorem comparisonToOriginal_transport :
    transportComparison c D hD a ≫
      comparisonToOriginal (n := n) (c ≫ a.left.fiber.left) (transported D a)
        (transported_collapse c D hD a) =
      comparisonToOriginal (n := n) c D hD ≫ (Functor.const (Fiber S n)).map a := by
  rw [transportComparison_eq_presentation, target_eq_mapCone, source_eq_mapCone]
  exact mapped_transport_triangle c D hD a

set_option maxHeartbeats 180000 in
/-- Target transport compares the actual slice functors over the original codomain. -/
def overTransportComparison :
    overOriginal (n := n) c D hD ⋙ Over.map a ⟶
      overOriginal (n := n) (c ≫ a.left.fiber.left) (transported D a)
        (transported_collapse c D hD a) :=
  overHom_transport (comparisonToOriginal (n := n) c D hD)
    (comparisonToOriginal (n := n) (c ≫ a.left.fiber.left) (transported D a)
      (transported_collapse c D hD a)) (transportComparison c D hD a) a
    (comparisonToOriginal_transport c D hD a)

end

end DaggerModels.PartII.JTGraphInterpolatedOverTransport
