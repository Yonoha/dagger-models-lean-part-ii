import DaggerModelsPartII.JTCylinderOverTargetBaseChange

/-!
# Time restriction of a fixed-target cylinder comparison
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCylinderOverTargetBaseChangeTime

open JTCylinderOverTargetBaseChange
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

/-- The full original necklace fiber, mapped to the Grothendieck construction. -/
abbrev atIndex {I : Type} [SmallCategory I] (E : I ⥤ Under B)
    {i : I} {A : Under B} (p : A ⟶ E.obj i) :=
  CostructuredArrow.map p ⋙ Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i

theorem map_comp {A B' C : Under B} (u : A ⟶ B') (v : B' ⟶ C) :
    CostructuredArrow.map (S := necklaceUnder) (u ≫ v) =
      CostructuredArrow.map u ⋙ CostructuredArrow.map v :=
  congrArg Cat.Hom.toFunctor (BoundaryNecklaceComma.diagram.map_comp u v)

theorem map_id (A : Under B) :
    CostructuredArrow.map (𝟙 A) = 𝟭 (CostructuredArrow necklaceUnder A) :=
  congrArg Cat.Hom.toFunctor (BoundaryNecklaceComma.diagram.map_id A)

section TimeRestriction

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {i' i : I} {A₀' A₀ A' A : Under B}
variable (p₀' : A₀' ⟶ E.obj i') (p₀ : A₀ ⟶ E.obj i)
variable (p' : A' ⟶ E.obj i') (p : A ⟶ E.obj i)
variable (u' : A₀' ⟶ A') (u : A₀ ⟶ A)
variable (g₀ : A₀' ⟶ A₀) (g : A' ⟶ A) (a : i' ⟶ i)
variable (hp' : u' ≫ p' = p₀') (hp : u ≫ p = p₀)
variable (hu : u' ≫ g = g₀ ≫ u)
variable (h₀ : p₀' ≫ E.map a = g₀ ≫ p₀) (h : p' ≫ E.map a = g ≫ p)

include hp' in
theorem source_eq :
    CostructuredArrow.map u' ⋙ atIndex E p' = atIndex E p₀' := by
  rw [← Functor.assoc, ← map_comp, hp']

/-- Reindex the source and target of a comparison along a commuting square. -/
theorem reindex_target {C : Type*} [Category* C] {A₀' A₀ A' A : Under B}
    (u' : A₀' ⟶ A') (u : A₀ ⟶ A) (g₀ : A₀' ⟶ A₀) (g : A' ⟶ A)
    (F₀ : CostructuredArrow necklaceUnder A₀ ⥤ C)
    (F : CostructuredArrow necklaceUnder A ⥤ C)
    (hu : u' ≫ g = g₀ ≫ u) (hF : CostructuredArrow.map u ⋙ F = F₀) :
    CostructuredArrow.map u' ⋙ CostructuredArrow.map g ⋙ F =
      CostructuredArrow.map g₀ ⋙ F₀ := by
  rw [← Functor.assoc, ← map_comp, hu, map_comp, Functor.assoc, hF]

include hp hu in
theorem target_eq :
    CostructuredArrow.map u' ⋙ CostructuredArrow.map g ⋙ atIndex E p =
      CostructuredArrow.map g₀ ⋙ atIndex E p₀ := by
  exact reindex_target u' u g₀ g _ _ hu (source_eq E p₀ p u hp)

/-- Components on a time restriction agree with the smaller comparison after the
canonical endpoint identifications. -/
theorem comparisonOfSquare_reindex :
    Functor.whiskerLeft (CostructuredArrow.map u') (comparisonOfSquare E p' p g a h) ≫
        eqToHom (target_eq E p₀ p u' u g₀ g hp hu) =
      eqToHom (source_eq E p₀' p' u' hp') ≫ comparisonOfSquare E p₀' p₀ g₀ a h₀ := by
  ext : 1
  funext P
  apply JTTargetCommaPullback.operator_ext
  · simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      Grothendieck.comp_base, comparisonOfSquare_base, Grothendieck.base_eqToHom]
    change a ≫ 𝟙 i = 𝟙 i' ≫ a
    rw [Category.comp_id, Category.id_comp]
  · let C := BoundaryNecklaceComma.sourceCode E
    change C.map ((Functor.whiskerLeft (CostructuredArrow.map u')
        (comparisonOfSquare E p' p g a h) ≫
        eqToHom (target_eq E p₀ p u' u g₀ g hp hu)).app P) =
      C.map ((eqToHom (source_eq E p₀' p' u' hp') ≫
        comparisonOfSquare E p₀' p₀ g₀ a h₀).app P)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      Functor.map_comp, eqToHom_map, C, comparisonOfSquare_code]
    change 𝟙 P.left ≫ 𝟙 P.left = 𝟙 P.left ≫ 𝟙 P.left
    rfl

end TimeRestriction

/-- Postcomposition preserves a commuting square of transformations with
equality identifications on both ends. -/
theorem whiskerRight_conjugacy
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {A B A' B' : C ⥤ D} (K : D ⥤ E)
    (α : A ⟶ B) (β : A' ⟶ B') (hs : A = A') (ht : B = B')
    (h : α ≫ eqToHom ht = eqToHom hs ≫ β) :
    Functor.whiskerRight α K ≫ eqToHom (congrArg (fun F ↦ F ⋙ K) ht) =
      eqToHom (congrArg (fun F ↦ F ⋙ K) hs) ≫ Functor.whiskerRight β K := by
  subst A' B'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h ⊢
  rw [h]


section Whisker

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {C : Type*} [Category* C] (K : BoundaryNecklaceComma.Presentation E ⥤ C)
variable {i' i : I} {A₀' A₀ A' A : Under B}
variable (p₀' : A₀' ⟶ E.obj i') (p₀ : A₀ ⟶ E.obj i)
variable (p' : A' ⟶ E.obj i') (p : A ⟶ E.obj i)
variable (u' : A₀' ⟶ A') (u : A₀ ⟶ A)
variable (g₀ : A₀' ⟶ A₀) (g : A' ⟶ A) (a : i' ⟶ i)
variable (hp' : u' ≫ p' = p₀') (hp : u ≫ p = p₀)
variable (hu : u' ≫ g = g₀ ≫ u)
variable (h₀ : p₀' ≫ E.map a = g₀ ≫ p₀) (h : p' ≫ E.map a = g ≫ p)

/-- Time coherence persists after mapping the presentation to any category. -/
theorem comparisonOfSquare_reindex_whiskerRight :
    Functor.whiskerLeft (CostructuredArrow.map u')
        (Functor.whiskerRight (comparisonOfSquare E p' p g a h) K) ≫
      eqToHom (reindex_target u' u g₀ g (atIndex E p₀ ⋙ K) (atIndex E p ⋙ K) hu
        (congrArg (fun F ↦ F ⋙ K) (source_eq E p₀ p u hp))) =
    eqToHom (congrArg (fun F ↦ F ⋙ K) (source_eq E p₀' p' u' hp')) ≫
      Functor.whiskerRight (comparisonOfSquare E p₀' p₀ g₀ a h₀) K :=
  whiskerRight_conjugacy K
    (Functor.whiskerLeft (CostructuredArrow.map u') (comparisonOfSquare E p' p g a h))
    (comparisonOfSquare E p₀' p₀ g₀ a h₀)
    (source_eq E p₀' p' u' hp') (target_eq E p₀ p u' u g₀ g hp hu)
    (comparisonOfSquare_reindex E p₀' p₀ p' p u' u g₀ g a hp' hp hu h₀ h)

end Whisker

section Actual

open JTCylinderOverTarget JTTargetCommaPullback JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (i' i : DecoratedNecklaceHomDiagram.Index W x y)
variable (R S : NecklaceCode) {m n : SimplexCategory} (j : m ⟶ n)
variable (hmR : (under R).obj m ⟶ (underDiagram W x y).obj i')
variable (hnR : (under R).obj n ⟶ (underDiagram W x y).obj i')
variable (hmS : (under S).obj m ⟶ (underDiagram W x y).obj i)
variable (hnS : (under S).obj n ⟶ (underDiagram W x y).obj i)
variable (dR : R ⟶ Q.code) (dS : S ⟶ Q.code)
variable (hrmR : hmR.right ≫ ((underCocone W x y).app i').right =
  augmentation R m ≫ dR.map ≫ Q.map)
variable (hrnR : hnR.right ≫ ((underCocone W x y).app i').right =
  augmentation R n ≫ dR.map ≫ Q.map)
variable (hrmS : hmS.right ≫ ((underCocone W x y).app i).right =
  augmentation S m ≫ dS.map ≫ Q.map)
variable (hrnS : hnS.right ≫ ((underCocone W x y).app i).right =
  augmentation S n ≫ dS.map ≫ Q.map)
variable (gm : (under R).obj m ⟶ (under S).obj m)
variable (gn : (under R).obj n ⟶ (under S).obj n)
variable (a : i' ⟶ i)
variable (hR : (under R).map j ≫ hnR = hmR)
variable (hS : (under S).map j ≫ hnS = hmS)
variable (htime : (under R).map j ≫ gn = gm ≫ (under S).map j)
variable (hDm : hmR ≫ (underDiagram W x y).map a = gm ≫ hmS)
variable (hDn : hnR ≫ (underDiagram W x y).map a = gn ≫ hnS)
variable (hNm : native W x y Q R m dR = gm ≫ native W x y Q S m dS)
variable (hNn : native W x y Q R n dR = gn ≫ native W x y Q S n dS)


set_option maxHeartbeats 400000 in
/-- Changing the time simplex gives the same natural transformation into the
original fixed-target comma after the canonical functor identifications. -/
theorem compare_reindex :
    Functor.whiskerLeft (CostructuredArrow.map ((under R).map j))
        (compare W x y Q i' i R S n n hnR hnS dR dS hrnR hrnS gn a hDn hNn) ≫
      eqToHom (reindex_target ((under R).map j) ((under S).map j) gm gn _ _ htime
        (JTCylinderOverTargetReindex.functor_reindex W x y Q i S m n j hmS hnS dS hrmS hrnS hS)) =
    eqToHom (JTCylinderOverTargetReindex.functor_reindex W x y Q i' R m n j hmR hnR dR hrmR hrnR hR) ≫
      compare W x y Q i' i R S m m hmR hmS dR dS hrmR hrmS gm a hDm hNm := by
  let pmR := JTCylinderOverTarget.lift W x y Q i' R m hmR dR hrmR
  let pnR := JTCylinderOverTarget.lift W x y Q i' R n hnR dR hrnR
  let pmS := JTCylinderOverTarget.lift W x y Q i S m hmS dS hrmS
  let pnS := JTCylinderOverTarget.lift W x y Q i S n hnS dS hrnS
  have hpR : ((under R).map j) ≫ pnR = pmR :=
    JTCylinderOverTargetReindex.lift_reindex W x y Q i' R m n j hmR hnR dR hrmR hrnR hR
  have hpS : ((under S).map j) ≫ pnS = pmS :=
    JTCylinderOverTargetReindex.lift_reindex W x y Q i S m n j hmS hnS dS hrmS hrnS hS
  have hm : pmR ≫ (diagram W x y Q).map a = gm ≫ pmS :=
    lift_compare W x y Q i' i R S m m hmR hmS dR dS hrmR hrmS gm a hDm hNm
  have hn : pnR ≫ (diagram W x y Q).map a = gn ≫ pnS :=
    lift_compare W x y Q i' i R S n n hnR hnS dR dS hrnR hrnS gn a hDn hNn
  have H := comparisonOfSquare_reindex_whiskerRight (diagram W x y Q)
    (equivalence W x y Q).inverse pmR pmS pnR pnS ((under R).map j) ((under S).map j)
    gm gn a hpR hpS htime hm hn
  unfold JTCylinderOverTargetBaseChange.compare comparePresentation
  exact H

end Actual

end

end DaggerModels.PartII.JTCylinderOverTargetBaseChangeTime
