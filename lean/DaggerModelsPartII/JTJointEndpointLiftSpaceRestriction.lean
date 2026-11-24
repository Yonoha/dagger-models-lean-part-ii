import DaggerModelsPartII.JTJointEndpointRelativeLift

/-! Restriction of the full relative endpoint lift space along ordinal squares. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits MonoidalClosed Simplicial Opposite DaggerModels

namespace DaggerModels.PartII.JTJointEndpointLiftSpaceRestriction

open JTJointEndpointRelativeLift JTProjectiveOrderedFiberComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- Precomposition of every simplex of a fixed-square lift space, allowing
both the domain and the prescribed subobject to change. -/
def precompSquare {A B A' B' X Y : SSet.{0}}
    {t : A ⟶ X} {i : A ⟶ B} {b : B ⟶ Y}
    {t' : A' ⟶ X} {i' : A' ⟶ B'} {b' : B' ⟶ Y}
    {p : X ⟶ Y} (sq : CommSq t i p b) (sq' : CommSq t' i' p b')
    (jA : A' ⟶ A) (jB : B' ⟶ B)
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t = t') (hb : jB ≫ b = b') :
    (SSet.ihomToPullbackFiber sq : SSet.{0}) ⟶
      SSet.ihomToPullbackFiber sq' :=
  SSet.Subcomplex.lift
    ((SSet.ihomToPullbackFiber sq).ι ≫ (MonoidalClosed.pre jB).app X) (by
      apply (SSet.range_le_ihomToPullbackFiber_iff sq' _).mpr
      constructor
      · rw [Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map,
          ← hi, MonoidalClosed.pre_map, NatTrans.comp_app,
          ← Category.assoc, SSet.ihomToPullbackFiber_pre_app,
          SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp, ht]
      · rw [Category.assoc, MonoidalClosed.pre_comm_ihom_map,
          ← Category.assoc, SSet.ihomToPullbackFiber_ihom_map,
          SSet.const_comp, ← SSet.ihom₀Equiv_symm_comp, hb])

@[reassoc]
theorem precompSquare_ι {A B A' B' X Y : SSet.{0}}
    {t : A ⟶ X} {i : A ⟶ B} {b : B ⟶ Y}
    {t' : A' ⟶ X} {i' : A' ⟶ B'} {b' : B' ⟶ Y}
    {p : X ⟶ Y} (sq : CommSq t i p b) (sq' : CommSq t' i' p b')
    (jA : A' ⟶ A) (jB : B' ⟶ B)
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t = t') (hb : jB ≫ b = b') :
    precompSquare sq sq' jA jB hi ht hb ≫
        (SSet.ihomToPullbackFiber sq').ι =
      (SSet.ihomToPullbackFiber sq).ι ≫ (MonoidalClosed.pre jB).app X := rfl

/-- The identity square induces the identity on the entire lift space. -/
theorem precompSquare_id {A B X Y : SSet.{0}}
    {t : A ⟶ X} {i : A ⟶ B} {b : B ⟶ Y} {p : X ⟶ Y}
    (sq : CommSq t i p b)
    (hi : (𝟙 A) ≫ i = i ≫ (𝟙 B))
    (ht : (𝟙 A) ≫ t = t) (hb : (𝟙 B) ≫ b = b) :
    precompSquare sq sq (𝟙 A) (𝟙 B) hi ht hb = 𝟙 _ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber sq).ι).mp
  rw [precompSquare_ι, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp]

/-- Precomposition is strictly contravariantly compatible with composition. -/
theorem precompSquare_comp
    {A₀ B₀ A₁ B₁ A₂ B₂ X Y : SSet.{0}}
    {t₀ : A₀ ⟶ X} {i₀ : A₀ ⟶ B₀} {b₀ : B₀ ⟶ Y}
    {t₁ : A₁ ⟶ X} {i₁ : A₁ ⟶ B₁} {b₁ : B₁ ⟶ Y}
    {t₂ : A₂ ⟶ X} {i₂ : A₂ ⟶ B₂} {b₂ : B₂ ⟶ Y}
    {p : X ⟶ Y} (sq₀ : CommSq t₀ i₀ p b₀)
    (sq₁ : CommSq t₁ i₁ p b₁) (sq₂ : CommSq t₂ i₂ p b₂)
    (a₁ : A₁ ⟶ A₀) (b₁₀ : B₁ ⟶ B₀)
    (a₂ : A₂ ⟶ A₁) (b₂₁ : B₂ ⟶ B₁)
    (hi₁ : a₁ ≫ i₀ = i₁ ≫ b₁₀)
    (ht₁ : a₁ ≫ t₀ = t₁) (hb₁ : b₁₀ ≫ b₀ = b₁)
    (hi₂ : a₂ ≫ i₁ = i₂ ≫ b₂₁)
    (ht₂ : a₂ ≫ t₁ = t₂) (hb₂ : b₂₁ ≫ b₁ = b₂)
    (hi : (a₂ ≫ a₁) ≫ i₀ = i₂ ≫ (b₂₁ ≫ b₁₀))
    (ht : (a₂ ≫ a₁) ≫ t₀ = t₂)
    (hb : (b₂₁ ≫ b₁₀) ≫ b₀ = b₂) :
    precompSquare sq₀ sq₁ a₁ b₁₀ hi₁ ht₁ hb₁ ≫
        precompSquare sq₁ sq₂ a₂ b₂₁ hi₂ ht₂ hb₂ =
      precompSquare sq₀ sq₂ (a₂ ≫ a₁) (b₂₁ ≫ b₁₀) hi ht hb := by
  apply (cancel_mono (SSet.ihomToPullbackFiber sq₂).ι).mp
  rw [Category.assoc, precompSquare_ι, precompSquare_ι_assoc,
    precompSquare_ι, MonoidalClosed.pre_map, NatTrans.comp_app]

/-- On zero simplices, restriction is literal precomposition by the large face. -/
theorem precompSquare_zero {A B A' B' X Y : SSet.{0}}
    {t : A ⟶ X} {i : A ⟶ B} {b : B ⟶ Y}
    {t' : A' ⟶ X} {i' : A' ⟶ B'} {b' : B' ⟶ Y}
    {p : X ⟶ Y} (sq : CommSq t i p b) (sq' : CommSq t' i' p b')
    (jA : A' ⟶ A) (jB : B' ⟶ B)
    (hi : jA ≫ i = i' ≫ jB) (ht : jA ≫ t = t') (hb : jB ≫ b = b')
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋0⦌)) :
    SSet.ihom₀Equiv (((precompSquare sq sq' jA jB hi ht hb).app _ v).val) =
      jB ≫ SSet.ihom₀Equiv v.val := by
  apply SSet.ihom₀Equiv.symm.injective
  rw [Equiv.symm_apply_apply, SSet.ihom₀Equiv_symm_comp,
    Equiv.symm_apply_apply]
  exact congrFun
    (NatTrans.congr_app (precompSquare_ι sq sq' jA jB hi ht hb) (op ⦋0⦌)) v

private theorem faceCompat (W : Source) {l k l' k' : SimplexCategory}
    (u : l ⟶ k) (u' : l' ⟶ k') (a : l' ⟶ l) (b : k' ⟶ k)
    (h : a ≫ u = u' ≫ b) (f : Δ k ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    std.map u' ≫ (std.map b ≫ f) =
      term (Δ l') ≫ vertexPoint W z := by
  have hi : std.map a ≫ std.map u = std.map u' ≫ std.map b := by
    simpa only [std.map_comp] using congrArg std.map h
  calc
    std.map u' ≫ (std.map b ≫ f) = std.map a ≫ (std.map u ≫ f) := by
      rw [← Category.assoc, ← Category.assoc, ← hi, Category.assoc]
    _ = std.map a ≫ (term (Δ l) ≫ vertexPoint W z) := by rw [hf]
    _ = term (Δ l') ≫ vertexPoint W z := by
      rw [← Category.assoc]
      congr 1

/-- The full simplicial restriction map for the variable-left endpoint. -/
def restrictLiftSpace (W : Source) {l k l' k' : SimplexCategory}
    (u : l ⟶ k) (u' : l' ⟶ k') (a : l' ⟶ l) (b : k' ⟶ k)
    (h : a ≫ u = u' ≫ b) (f : Δ k ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    liftSpace W u f z hf ⟶
      liftSpace W u' (std.map b ≫ f) z (faceCompat W u u' a b h f z hf) :=
  precompSquare (square W u f z hf)
    (square W u' (std.map b ≫ f) z (faceCompat W u u' a b h f z hf))
    (std.map a) (std.map b)
    (by simpa only [std.map_comp] using congrArg std.map h)
    (identityOnFace_natural W z a)
    (boundaryPair_natural W z b f)

/-- The full simplicial restriction map for the variable-right endpoint. -/
def restrictReverseLiftSpace (W : Source) {l k l' k' : SimplexCategory}
    (u : l ⟶ k) (u' : l' ⟶ k') (a : l' ⟶ l) (b : k' ⟶ k)
    (h : a ≫ u = u' ≫ b) (f : Δ k ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : std.map u ≫ f = term (Δ l) ≫ vertexPoint W z) :
    reverseLiftSpace W u f z hf ⟶
      reverseLiftSpace W u' (std.map b ≫ f) z (faceCompat W u u' a b h f z hf) :=
  precompSquare (reverseSquare W u f z hf)
    (reverseSquare W u' (std.map b ≫ f) z (faceCompat W u u' a b h f z hf))
    (std.map a) (std.map b)
    (by simpa only [std.map_comp] using congrArg std.map h)
    (identityOnFace_natural W z a)
    (reverseBoundaryPair_natural W z b f)

end

end DaggerModels.PartII.JTJointEndpointLiftSpaceRestriction
