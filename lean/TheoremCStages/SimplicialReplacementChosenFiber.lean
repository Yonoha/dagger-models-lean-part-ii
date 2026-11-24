import NativeSimplicialReplacement
import TopCatModelCategory.SSet.Fiber

/-! The literal chosen fiber of the full simplicial-replacement diagonal projection. -/
set_option autoImplicit false
set_option warningAsError true
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerOriginalProductGadget DaggerBisimplicialDiagonal
universe u
namespace DaggerSimplicialReplacementChosenFiber
noncomputable section

variable {C : Type u} [Category.{u} C]

/-- The original constant chain on the supplied object in every outer degree. -/
def constantChain (c : C) (q : SimplexCategoryᵒᵖ) : (nerve C).obj q :=
  (Functor.const (Fin (q.unop.len + 1))).obj c

theorem constantChain_map (c : C) {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (nerve C).map α (constantChain c q) = constantChain c r := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

theorem initialArrow_constantChain (c : C) {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    initialArrow α (constantChain c q) = 𝟙 c := rfl

/-- The chosen object is a coherent vertex of the entire nerve. -/
def chainPoint (c : C) : (Δ[0] : SSet.{u}) ⟶ nerve C where
  app q _ := constantChain c q
  naturality q r α := by
    funext _
    exact (constantChain_map c α).symm

/-- The unique map to the actual zero-simplex object. -/
def zeroMap (X : SSet.{u}) : X ⟶ (Δ[0] : SSet.{u}) where
  app q _ := default
  naturality q r α := by
    funext _
    exact Subsingleton.elim _ _

/-- Insert the same original parameter simplex at the full constant chain. -/
def diagonalInclusion (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ⟶ DaggerBisimplicialDiagonal.diag (replacement G) where
  app q x := ⟨constantChain c q, x⟩
  naturality q r α := by
    funext x
    change (⟨constantChain c r, (G.obj c).map α x⟩ : Cell G r r) =
      vertical G r α (horizontal G α q ⟨constantChain c q, x⟩)
    apply Sigma.ext (constantChain_map c α).symm
    apply heq_of_eq
    change (G.obj c).map α x =
      (G.obj c).map α ((G.map (𝟙 c)).app q x)
    exact congrArg ((G.obj c).map α)
      (congrFun (NatTrans.congr_app (G.map_id c) q) x).symm

theorem diagonalProjection_app (G : C ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (x : (DaggerBisimplicialDiagonal.diag (replacement G)).obj q) :
    (diagonalProjection G).app q x = x.1 := rfl

theorem diagonalInclusion_square (G : C ⥤ SSet.{u}) (c : C) :
    diagonalInclusion G c ≫ diagonalProjection G = zeroMap (G.obj c) ≫ chainPoint c := by
  apply NatTrans.ext
  funext q x
  rfl

theorem diagonalInclusion_app_isPullback (G : C ⥤ SSet.{u}) (c : C)
    (q : SimplexCategoryᵒᵖ) :
    IsPullback ((diagonalInclusion G c).app q) ((zeroMap (G.obj c)).app q)
      ((diagonalProjection G).app q) ((chainPoint c).app q) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (diagonalInclusion_square G c) q, ?_, ?_⟩
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj h.1).2
  · intro z t h
    obtain ⟨γ, x⟩ := z
    change γ = constantChain c q at h
    subst γ
    refine ⟨x, rfl, ?_⟩
    exact Subsingleton.elim _ _

theorem diagonalInclusion_isPullback (G : C ⥤ SSet.{u}) (c : C) :
    IsPullback (diagonalInclusion G c) (zeroMap (G.obj c))
      (diagonalProjection G) (chainPoint c) := by
  let cone := PullbackCone.mk (diagonalInclusion G c) (zeroMap (G.obj c))
    (diagonalInclusion_square G c)
  apply IsPullback.of_isLimit (c := cone)
  apply evaluationJointlyReflectsLimits
  intro q
  let h := diagonalInclusion_app_isPullback G c q
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

/-- The chosen strict diagonal fiber is exactly the original value `G.obj c`. -/
def chosenFiberIso (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ≅ pullback (diagonalProjection G) (chainPoint c) :=
  (diagonalInclusion_isPullback G c).isoPullback

#print axioms diagonalInclusion_isPullback
#print axioms chosenFiberIso

end
end DaggerSimplicialReplacementChosenFiber
