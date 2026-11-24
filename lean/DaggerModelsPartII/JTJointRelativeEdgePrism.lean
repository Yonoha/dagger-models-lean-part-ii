import DaggerModelsPartII.JTJointRelativeEdgeChoiceDiagram
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-! Complete relative edge maps on coefficient-time products. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory MonoidalClosed DaggerModels

namespace DaggerModels.PartII.JTJointRelativeEdgePrism

open JTJointEndpointRelativeLift JTJointEndpointLiftSpaceRestriction
open JTJointRelativeEdgeChoiceDiagram JTProjectiveOrderedFiberComparison
open JTFixedLiftSpaceTimeEquiv

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- Restricting either component of an exact fixed-square lift simplex is
literal precomposition on its complete coefficient-time map. -/
theorem timeMap_precompSquare {A B A' B' X Y : SSet.{0}}
    {t : A ⟶ X} {i : A ⟶ B} {b : B ⟶ Y}
    {t' : A' ⟶ X} {i' : A' ⟶ B'} {b' : B' ⟶ Y}
    {p : X ⟶ Y} (sq : CommSq t i p b) (sq' : CommSq t' i' p b')
    (jA : A' ⟶ A) (jB : B' ⟶ B)
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t = t') (hb : jB ≫ b = b')
    (n : SimplexCategory)
    (x : (SSet.ihomToPullbackFiber sq).obj (op n)) :
    timeMap sq' n ((precompSquare sq sq' jA jB hi ht hb).app _ x) =
      (jB ▷ Δ n) ≫ timeMap sq n x := by
  have h : SSet.yonedaEquiv.symm
      ((precompSquare sq sq' jA jB hi ht hb).app _ x) ≫
        (SSet.ihomToPullbackFiber sq').ι =
      (SSet.yonedaEquiv.symm x ≫ (SSet.ihomToPullbackFiber sq).ι) ≫
        (MonoidalClosed.pre jB).app X := by
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
      precompSquare_ι, Category.assoc]
  unfold timeMap
  rw [h, uncurry_pre_app]

variable {I : Type} [SmallCategory I] (W : Source)
  (s k : I ⥤ SimplexCategory) (u : s ⟶ k)
  (f : k ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
  (z : (row W ⦋0⦌).obj (op ⦋0⦌))
  (hf : ∀ a : I, std.map (u.app a) ≫ f.app a =
    term (Δ (s.obj a)) ≫ vertexPoint W z)

/-- The complete variable-left relative edge map represented by a choice simplex. -/
def leftMap (a : I) (n : SimplexCategory)
    (x : ((leftChoices W s k u f z hf).obj (op a)).obj (op n)) :
    Δ (k.obj a) ⊗ Δ n ⟶ row W ⦋1⦌ :=
  timeMap (square W (u.app a) (f.app a) z (hf a)) n x

/-- The complete variable-right relative edge map represented by a choice simplex. -/
def rightMap (a : I) (n : SimplexCategory)
    (x : ((rightChoices W s k u f z hf).obj (op a)).obj (op n)) :
    Δ (k.obj a) ⊗ Δ n ⟶ row W ⦋1⦌ :=
  timeMap (reverseSquare W (u.app a) (f.app a) z (hf a)) n x

/-- The left edge is the degenerate identity edge on the whole moving face. -/
theorem leftMap_face (a : I) (n : SimplexCategory)
    (x : ((leftChoices W s k u f z hf).obj (op a)).obj (op n)) :
    (std.map (u.app a) ▷ Δ n) ≫ leftMap W s k u f z hf a n x =
      fst (Δ (s.obj a)) (Δ n) ≫ identityOnFace W z :=
  (timeMap_conditions (square W (u.app a) (f.app a) z (hf a)) n x).1

/-- The left edge retains the prescribed ordered endpoint pair throughout time. -/
theorem leftMap_endpoints (a : I) (n : SimplexCategory)
    (x : ((leftChoices W s k u f z hf).obj (op a)).obj (op n)) :
    leftMap W s k u f z hf a n x ≫ endpointArrow W =
      fst (Δ (k.obj a)) (Δ n) ≫ boundaryPair W (f.app a) z :=
  (timeMap_conditions (square W (u.app a) (f.app a) z (hf a)) n x).2

theorem rightMap_face (a : I) (n : SimplexCategory)
    (x : ((rightChoices W s k u f z hf).obj (op a)).obj (op n)) :
    (std.map (u.app a) ▷ Δ n) ≫ rightMap W s k u f z hf a n x =
      fst (Δ (s.obj a)) (Δ n) ≫ identityOnFace W z :=
  (timeMap_conditions (reverseSquare W (u.app a) (f.app a) z (hf a)) n x).1

theorem rightMap_endpoints (a : I) (n : SimplexCategory)
    (x : ((rightChoices W s k u f z hf).obj (op a)).obj (op n)) :
    rightMap W s k u f z hf a n x ≫ endpointArrow W =
      fst (Δ (k.obj a)) (Δ n) ≫ reverseBoundaryPair W (f.app a) z :=
  (timeMap_conditions (reverseSquare W (u.app a) (f.app a) z (hf a)) n x).2

private theorem face_natural {a b : I} (α : a ⟶ b) :
    std.map (s.map α) ≫ std.map (u.app b) =
      std.map (u.app a) ≫ std.map (k.map α) := by
  simpa only [std.map_comp] using congrArg std.map (u.naturality α)

private theorem row_natural {a b : I} (α : a ⟶ b) :
    std.map (k.map α) ≫ f.app b = f.app a := by
  have h := f.naturality α
  change std.map (k.map α) ≫ f.app b = f.app a ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem left_boundary_natural {a b : I} (α : a ⟶ b) :
    std.map (k.map α) ≫ boundaryPair W (f.app b) z =
      boundaryPair W (f.app a) z := by
  rw [boundaryPair_natural, row_natural W k f α]

private theorem right_boundary_natural {a b : I} (α : a ⟶ b) :
    std.map (k.map α) ≫ reverseBoundaryPair W (f.app b) z =
      reverseBoundaryPair W (f.app a) z := by
  rw [reverseBoundaryPair_natural, row_natural W k f α]

private theorem tensor_mixed {a b n m : SimplexCategory}
    (α : a ⟶ b) (β : n ⟶ m) :
    (std.obj a ◁ std.map β) ≫ (std.map α ▷ std.obj m) =
      std.map α ⊗ₘ std.map β := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- Coefficient restriction and every time operator act on the complete
left edge map by the expected two-variable precomposition. -/
theorem leftMap_restrict {a b : I} (α : a ⟶ b)
    {n m : SimplexCategory} (β : n ⟶ m)
    (x : ((leftChoices W s k u f z hf).obj (op b)).obj (op m)) :
    leftMap W s k u f z hf a n
      (((leftChoices W s k u f z hf).obj (op a)).map β.op
        (((leftChoices W s k u f z hf).map α.op).app (op m) x)) =
      (std.map (k.map α) ⊗ₘ std.map β) ≫
        leftMap W s k u f z hf b m x := by
  let sqA := square W (u.app a) (f.app a) z (hf a)
  let sqB := square W (u.app b) (f.app b) z (hf b)
  have hi := face_natural s k u α
  have ht := identityOnFace_natural W z (s.map α)
  have hb := left_boundary_natural W k f z α
  have hc : timeMap sqA m
      (((leftChoices W s k u f z hf).map α.op).app (op m) x) =
      (std.map (k.map α) ▷ Δ m) ≫ timeMap sqB m x := by
    change timeMap sqA m
      ((precompSquare sqB sqA (std.map (s.map α)) (std.map (k.map α))
        hi ht hb).app (op m) x) = _
    exact timeMap_precompSquare sqB sqA _ _ hi ht hb m x
  change timeMap sqA n
    ((SSet.ihomToPullbackFiber sqA : SSet.{0}).map β.op
      (((leftChoices W s k u f z hf).map α.op).app (op m) x)) = _
  rw [timeMap_map, hc, ← Category.assoc, tensor_mixed]
  rfl

/-- The same complete two-variable naturality for the variable-right edge. -/
theorem rightMap_restrict {a b : I} (α : a ⟶ b)
    {n m : SimplexCategory} (β : n ⟶ m)
    (x : ((rightChoices W s k u f z hf).obj (op b)).obj (op m)) :
    rightMap W s k u f z hf a n
      (((rightChoices W s k u f z hf).obj (op a)).map β.op
        (((rightChoices W s k u f z hf).map α.op).app (op m) x)) =
      (std.map (k.map α) ⊗ₘ std.map β) ≫
        rightMap W s k u f z hf b m x := by
  let sqA := reverseSquare W (u.app a) (f.app a) z (hf a)
  let sqB := reverseSquare W (u.app b) (f.app b) z (hf b)
  have hi := face_natural s k u α
  have ht := identityOnFace_natural W z (s.map α)
  have hb := right_boundary_natural W k f z α
  have hc : timeMap sqA m
      (((rightChoices W s k u f z hf).map α.op).app (op m) x) =
      (std.map (k.map α) ▷ Δ m) ≫ timeMap sqB m x := by
    change timeMap sqA m
      ((precompSquare sqB sqA (std.map (s.map α)) (std.map (k.map α))
        hi ht hb).app (op m) x) = _
    exact timeMap_precompSquare sqB sqA _ _ hi ht hb m x
  change timeMap sqA n
    ((SSet.ihomToPullbackFiber sqA : SSet.{0}).map β.op
      (((rightChoices W s k u f z hf).map α.op).app (op m) x)) = _
  rw [timeMap_map, hc, ← Category.assoc, tensor_mixed]
  rfl

end

end DaggerModels.PartII.JTJointRelativeEdgePrism
