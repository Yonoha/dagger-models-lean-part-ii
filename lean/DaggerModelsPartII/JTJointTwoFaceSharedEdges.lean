import DaggerModelsPartII.JTJointSubcomplexRelativeLift

/-! One relative edge can serve both incident support faces of a shared endpoint row. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointTwoFaceSharedEdges

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTEndpointNormalizationLifts (identityFamily)
open JTJointSubcomplexRelativeLift (boundaryPair reverseBoundaryPair)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {k : SimplexCategory}

/-- Constancy on both subcomplexes is precisely enough for constancy on their union. -/
theorem constant_on_union (S T : (std.obj k).Subcomplex)
    (f : std.obj k ⟶ row W ⦋0⦌) (z : Vertex W)
    (hS : S.ι ≫ f = term S.toSSet ≫ vertexPoint W z)
    (hT : T.ι ≫ f = term T.toSSet ≫ vertexPoint W z) :
    (S ⊔ T).ι ≫ f = term (S ⊔ T).toSSet ≫ vertexPoint W z := by
  let sq : SSet.Subcomplex.BicartSq (S ⊓ T) S T (S ⊔ T) := ⟨rfl, rfl⟩
  apply sq.isPushout.hom_ext
  · rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι, hS, ← Category.assoc]
    have ht : SSet.Subcomplex.homOfLE (le_sup_left : S ≤ S ⊔ T) ≫
        term (S ⊔ T).toSSet = term S.toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht]
  · rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι, hT, ← Category.assoc]
    have ht : SSet.Subcomplex.homOfLE (le_sup_right : T ≤ S ⊔ T) ≫
        term (S ⊔ T).toSSet = term T.toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht]

private theorem identity_restrict {X : SSet.{0}} (z : Vertex W)
    (S T : X.Subcomplex) (e : X ⟶ row W ⦋1⦌)
    (he : (S ⊔ T).ι ≫ e =
      term (S ⊔ T).toSSet ≫ vertexPoint W z ≫ identityFamily W) :
    (S.ι ≫ e = term S.toSSet ≫ vertexPoint W z ≫ identityFamily W) ∧
      (T.ι ≫ e = term T.toSSet ≫ vertexPoint W z ≫ identityFamily W) := by
  constructor
  · have h := congrArg
      (fun a ↦ SSet.Subcomplex.homOfLE (le_sup_left : S ≤ S ⊔ T) ≫ a) he
    simpa only [← Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.stdSimplex.isTerminalObj₀.comp_from] using h
  · have h := congrArg
      (fun a ↦ SSet.Subcomplex.homOfLE (le_sup_right : T ≤ S ⊔ T) ≫ a) he
    simpa only [← Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.stdSimplex.isTerminalObj₀.comp_from] using h

variable {m : ℕ} (S T : Finset (Fin (m + 1)))
variable (v : Fin (m + 1)) (hvS : v ∈ S) (hvT : v ∈ T)
variable (f : std.obj ⦋m⦌ ⟶ row W ⦋0⦌) (z : Vertex W)
variable (hS : (SSet.stdSimplex.face S).ι ≫ f =
  term (SSet.stdSimplex.face S).toSSet ≫ vertexPoint W z)
variable (hT : (SSet.stdSimplex.face T).ι ≫ f =
  term (SSet.stdSimplex.face T).toSSet ≫ vertexPoint W z)

include v hvS hvT hS hT in
/-- A single strict relative edge is stationary on BOTH incident faces. -/
theorem exists_shared_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ e : std.obj ⦋m⦌ ⟶ row W ⦋1⦌,
      (SSet.stdSimplex.face S).ι ≫ e =
        term (SSet.stdSimplex.face S).toSSet ≫ vertexPoint W z ≫ identityFamily W ∧
      (SSet.stdSimplex.face T).ι ≫ e =
        term (SSet.stdSimplex.face T).toSSet ≫ vertexPoint W z ≫ identityFamily W ∧
      e ≫ endpointArrow W = boundaryPair W f z := by
  have h := constant_on_union (SSet.stdSimplex.face S) (SSet.stdSimplex.face T) f z hS hT
  obtain ⟨e, he, hb⟩ := (JTJointSubcomplexRelativeLift.twoFace_exists_edges
    W S T v hvS hvT f z h hW).1
  obtain ⟨heS, heT⟩ := identity_restrict z _ _ e he
  exact ⟨e, heS, heT, hb⟩

include v hvS hvT hS hT in
/-- The opposite orientation can use the same two support-face constraints. -/
theorem exists_shared_reverse_edge
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    ∃ e : std.obj ⦋m⦌ ⟶ row W ⦋1⦌,
      (SSet.stdSimplex.face S).ι ≫ e =
        term (SSet.stdSimplex.face S).toSSet ≫ vertexPoint W z ≫ identityFamily W ∧
      (SSet.stdSimplex.face T).ι ≫ e =
        term (SSet.stdSimplex.face T).toSSet ≫ vertexPoint W z ≫ identityFamily W ∧
      e ≫ endpointArrow W = reverseBoundaryPair W f z := by
  have h := constant_on_union (SSet.stdSimplex.face S) (SSet.stdSimplex.face T) f z hS hT
  obtain ⟨e, he, hb⟩ := (JTJointSubcomplexRelativeLift.twoFace_exists_edges
    W S T v hvS hvT f z h hW).2
  obtain ⟨heS, heT⟩ := identity_restrict z _ _ e he
  exact ⟨e, heS, heT, hb⟩

end
end DaggerModels.PartII.JTJointTwoFaceSharedEdges
