import SimplexIndexLastVertexWeak
import NativeRawHomotopyWeakInvariance

/-!
# The full-parameter to last-vertex homotopy

The switch takes place in the actual last simplex of a lifted-index chain.
No fibrancy hypothesis is used.
-/

set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerNativeSimplexIndexResolution
open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)
open DaggerModels.PartII.SimplexResolutionLastOrdinal
open DaggerModels.PartII.SimplexResolutionSwitch
open DaggerModels.PartII.SimplexIndexLastVertexWeak
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SimplexIndexLastVertexHomotopy
noncomputable section

variable (X : SSet.{0})

private abbrev Res := DaggerBisimplicialDiagonal.diag (resolution X)

private abbrev suffix {q : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q) : first F ⟶ last F :=
  F.map (homOfLE (Fin.zero_le (Fin.last q.unop.len)))

private theorem triangle {q r : SimplexCategoryᵒᵖ}
    (F : (nerve (LiftedIndex X)).obj q) (α : q ⟶ r) :
    suffix X F = initialArrow α F ≫
      suffix X ((nerve (LiftedIndex X)).map α F) ≫ lastArrow α F := by
  change F.map (homOfLE _) = F.map (homOfLE _) ≫ F.map (homOfLE _) ≫ F.map (homOfLE _)
  rw [← F.map_comp, ← F.map_comp]
  rfl

private theorem first_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (Res X).obj q) :
    firstOrdinal X ((Res X).map α s).1 ((Res X).map α s).2 ≫
        (degree X).map (lastArrow α s.1) =
      α.unop ≫ firstOrdinal X s.1 s.2 := by
  rcases s with ⟨F, t⟩
  change (α.unop ≫ t.down ≫ (degree X).map (initialArrow α F)) ≫
      (degree X).map (suffix X ((nerve (LiftedIndex X)).map α F)) ≫
        (degree X).map (lastArrow α F) =
    α.unop ≫ (t.down ≫ (degree X).map (suffix X F))
  rw [triangle X F α, (degree X).map_comp, (degree X).map_comp]
  simp only [Category.assoc]

private theorem time_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (Res X).obj q) (u : (Δ[1] : SSet.{0}).obj q) :
    timeOrdinal X ((Res X).map α s).1 ((Res X).map α s).2
        ((Δ[1] : SSet.{0}).map α u) ≫ (degree X).map (lastArrow α s.1) =
      α.unop ≫ timeOrdinal X s.1 s.2 u := by
  unfold timeOrdinal
  rw [switch_postcomp, precomp_switch]
  have h₀ := first_natural X α s
  have h₁ : lastOrdinal (degree X) ((Res X).map α s).1 ≫
      (degree X).map (lastArrow α s.1) =
        α.unop ≫ lastOrdinal (degree X) s.1 :=
    lastOrdinal_natural (degree X) s.1 α
  have hu : SSet.stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map α u) =
      α.unop ≫ SSet.stdSimplex.objEquiv u := rfl
  exact congrArg (fun t : r.unop ⟶ ⦋1⦌ ↦ switch _ _ _ t) hu |>.trans
    (by
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      funext i
      simp only [switch, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
      rw [h₀, h₁]
      rfl)

private theorem timeOrdinalPoint_natural {q r : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (s : (Res X).obj q) (u : (Δ[1] : SSet.{0}).obj q) :
    ((diagram X).map (lastArrow α s.1)).app r
        (ULift.up (timeOrdinal X ((Res X).map α s).1 ((Res X).map α s).2
          ((Δ[1] : SSet.{0}).map α u))) =
      ((diagram X).obj (last s.1)).map α
        (ULift.up (timeOrdinal X s.1 s.2 u)) := by
  apply ULift.ext
  change timeOrdinal X ((Res X).map α s).1 ((Res X).map α s).2
      ((Δ[1] : SSet.{0}).map α u) ≫ (degree X).map (lastArrow α s.1) =
    α.unop ≫ timeOrdinal X s.1 s.2 u
  exact time_natural X α s u

/-- The switch evaluates the whole simplex at time zero and the last ordinal at time one. -/
def comparisonMap : Res X ⊗ Δ[1] ⟶ X where
  app q s := ((diagramAugmentation X).app (last s.1.1)).app q
    (ULift.up (timeOrdinal X s.1.1 s.1.2 s.2))
  naturality {q r} α := by
    funext s
    let F := s.1.1
    let g := lastArrow α F
    let v := ULift.up (timeOrdinal X ((Res X).map α s.1).1
      ((Res X).map α s.1).2 ((Δ[1] : SSet.{0}).map α s.2))
    have hw := congrFun (NatTrans.congr_app
      ((diagramAugmentation X).naturality g) r) v
    change ((diagramAugmentation X).app (last F)).app r
        (((diagram X).map g).app r v) =
      ((diagramAugmentation X).app (last ((nerve (LiftedIndex X)).map α F))).app r v
      at hw
    calc
      ((diagramAugmentation X).app
          (last ((nerve (LiftedIndex X)).map α F))).app r v =
          ((diagramAugmentation X).app (last F)).app r
            (((diagram X).map g).app r v) := hw.symm
      _ = ((diagramAugmentation X).app (last F)).app r
            (((diagram X).obj (last F)).map α
              (ULift.up (timeOrdinal X F s.1.2 s.2))) :=
          congrArg (((diagramAugmentation X).app (last F)).app r)
            (timeOrdinalPoint_natural X α s.1 s.2)
      _ = X.map α (((diagramAugmentation X).app (last F)).app q
            (ULift.up (timeOrdinal X F s.1.2 s.2))) :=
          congrFun (((diagramAugmentation X).app (last F)).naturality α)
            (ULift.up (timeOrdinal X F s.1.2 s.2))

private theorem comparison_zero : SSet.ι₀ ≫ comparisonMap X = toOriginal X := by
  apply NatTrans.ext
  funext q s
  rcases s with ⟨F, t⟩
  change ((diagramAugmentation X).app (last F)).app q
      (ULift.up (timeOrdinal X F t
        (SSet.stdSimplex.objEquiv.symm (q.unop.const ⦋1⦌ 0)))) =
    ((diagramAugmentation X).app (first F)).app q t
  refine (congrArg
    (fun j : q.unop ⟶ (degree X).obj (last F) ↦
      ((diagramAugmentation X).app (last F)).app q (ULift.up j))
    (timeOrdinal_zero X F t)).trans ?_
  have hw := congrFun (NatTrans.congr_app
    ((diagramAugmentation X).naturality (suffix X F)) q) t
  change ((diagramAugmentation X).app (last F)).app q
      (ULift.up (firstOrdinal X F t)) =
    ((diagramAugmentation X).app (first F)).app q t at hw
  exact hw

private theorem comparison_one :
    SSet.ι₁ ≫ comparisonMap X = toLiftedNerve X ≫ lastVertexMap X := by
  apply NatTrans.ext
  funext q s
  rcases s with ⟨F, t⟩
  change ((diagramAugmentation X).app (last F)).app q
      (ULift.up (timeOrdinal X F t
        (SSet.stdSimplex.objEquiv.symm (q.unop.const ⦋1⦌ 1)))) =
    (lastVertexMap X).app q F
  exact congrArg
    (fun j : q.unop ⟶ (degree X).obj (last F) ↦
      ((diagramAugmentation X).app (last F)).app q (ULift.up j))
    (timeOrdinal_one X F t)

/-- The comparison retains the actual first and last simplex evaluations. -/
def comparison : SSet.Homotopy (toOriginal X)
    (toLiftedNerve X ≫ lastVertexMap X) :=
  SSet.Homotopy.mk (comparisonMap X) (comparison_zero X) (comparison_one X)

/-- The last-vertex evaluation is a weak equivalence for every simplicial set. -/
theorem lastVertexMap_weak : WeakEquivalence (lastVertexMap X) := by
  have hOriginal : WeakEquivalence (toOriginal X) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeSimplexIndexNerveWeakContractibility.toOriginal_GW X)
  have hLifted : WeakEquivalence (toLiftedNerve X) :=
    (weakEquivalence_iff_GW _).mpr (toLiftedNerve_GW X)
  have hComposite : WeakEquivalence (toLiftedNerve X ≫ lastVertexMap X) :=
    (DaggerNativeRawHomotopyWeakInvariance.weakEquivalence_iff_homotopy
      (comparison X)).mp hOriginal
  have : WeakEquivalence (toLiftedNerve X) := hLifted
  have : WeakEquivalence (toLiftedNerve X ≫ lastVertexMap X) := hComposite
  exact weakEquivalence_of_precomp (toLiftedNerve X) (lastVertexMap X)

#print axioms first_natural
#print axioms time_natural
#print axioms comparisonMap
#print axioms comparison
#print axioms lastVertexMap_weak

end
end DaggerModels.PartII.SimplexIndexLastVertexHomotopy
