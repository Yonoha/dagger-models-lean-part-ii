import ChosenNecklaceVertices
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Image factorization of a simplex in a native necklace

The selected face uses an ordinal section of the surjective image map.
The original simplex is recovered after the corresponding degeneracy.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeSimplexImage

noncomputable section

private instance : SSet.stdSimplex.{0}.Full :=
  inferInstanceAs (uliftYoneda.{0} (C := SimplexCategory)).Full

private instance : SSet.stdSimplex.{0}.Faithful :=
  inferInstanceAs (uliftYoneda.{0} (C := SimplexCategory)).Faithful

/-- A split ordinal image factorization of an actual necklace simplex. -/
structure Factor (T : NecklaceCode) (d : ℕ)
    (g : (Δ[d] : SSet.{0}) ⟶ T.toSSet) where
  middle : SimplexCategory
  epi : ⦋d⦌ ⟶ middle
  epi_surjective : Function.Surjective epi.toOrderHom
  select : middle ⟶ ⦋d⦌
  select_epi : select ≫ epi = 𝟙 middle
  face : SSet.stdSimplex.obj middle ⟶ T.toSSet
  face_eq : face = SSet.stdSimplex.map select ≫ g
  ambientFace : middle ⟶ ⦋T.len⦌
  ambientFace_injective : Function.Injective ambientFace.toOrderHom
  face_inclusion : face ≫ T.inclusion = SSet.stdSimplex.map ambientFace
  factor : SSet.stdSimplex.map epi ≫ face = g

/-- The ambient ordinal image supplies a monotone section in the original simplex. -/
def factor (T : NecklaceCode) (d : ℕ)
    (g : (Δ[d] : SSet.{0}) ⟶ T.toSSet) : Factor T d g := by
  let θ : ⦋d⦌ ⟶ ⦋T.len⦌ := SSet.stdSimplex.preimage (g ≫ T.inclusion)
  let u : ⦋d⦌ ⟶ image θ := factorThruImage θ
  haveI : IsSplitEpi u := isSplitEpi_of_epi u
  let b : image θ ⟶ ⦋d⦌ := section_ u
  have hb : b ≫ u = 𝟙 (image θ) := IsSplitEpi.id u
  have hθ : (u ≫ b) ≫ θ = θ := by
    calc
      (u ≫ b) ≫ θ = (u ≫ b) ≫ (u ≫ image.ι θ) :=
        congrArg (fun f ↦ (u ≫ b) ≫ f) (image.fac θ).symm
      _ = u ≫ (b ≫ u) ≫ image.ι θ := by simp only [Category.assoc]
      _ = u ≫ image.ι θ := by rw [hb, Category.id_comp]
      _ = θ := image.fac θ
  have hg : SSet.stdSimplex.map θ = g ≫ T.inclusion :=
    SSet.stdSimplex.map_preimage _
  have hface : b ≫ θ = image.ι θ := by
    calc
      b ≫ θ = b ≫ (u ≫ image.ι θ) :=
        congrArg (fun f ↦ b ≫ f) (image.fac θ).symm
      _ = (b ≫ u) ≫ image.ι θ := by rw [Category.assoc]
      _ = image.ι θ := by rw [hb, Category.id_comp]
  refine {
    middle := image θ
    epi := u
    epi_surjective := (SimplexCategory.epi_iff_surjective).mp inferInstance
    select := b
    select_epi := hb
    face := SSet.stdSimplex.map b ≫ g
    face_eq := rfl
    ambientFace := image.ι θ
    ambientFace_injective := (SimplexCategory.mono_iff_injective).mp inferInstance
    face_inclusion := ?_
    factor := ?_
  }
  · calc
      (SSet.stdSimplex.map b ≫ g) ≫ T.inclusion =
          SSet.stdSimplex.map b ≫ (g ≫ T.inclusion) := Category.assoc _ _ _
      _ = SSet.stdSimplex.map b ≫ SSet.stdSimplex.map θ := by rw [hg]
      _ = SSet.stdSimplex.map (b ≫ θ) := (SSet.stdSimplex.map_comp _ _).symm
      _ = SSet.stdSimplex.map (image.ι θ) := by rw [hface]
  apply (cancel_mono T.inclusion).mp
  calc
    (SSet.stdSimplex.map u ≫ (SSet.stdSimplex.map b ≫ g)) ≫ T.inclusion =
        SSet.stdSimplex.map (u ≫ b) ≫ (g ≫ T.inclusion) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = SSet.stdSimplex.map (u ≫ b) ≫ SSet.stdSimplex.map θ := by rw [hg]
    _ = SSet.stdSimplex.map ((u ≫ b) ≫ θ) := (SSet.stdSimplex.map_comp _ _).symm
    _ = SSet.stdSimplex.map θ := by rw [hθ]
    _ = g ≫ T.inclusion := hg

/-- The selected face gives the exact original value under any target map. -/
theorem factor_target {X : SSet.{0}} (T : NecklaceCode) (d : ℕ)
    (g : (Δ[d] : SSet.{0}) ⟶ T.toSSet) (f : T.toSSet ⟶ X) :
    (SSet.stdSimplex.map (factor T d g).epi ≫ (factor T d g).face) ≫ f = g ≫ f :=
  congrArg (· ≫ f) (factor T d g).factor

/-- The operator between the selected image faces of two related simplices. -/
def faceOperator {T U : NecklaceCode} {d e : ℕ}
    (g₁ : (Δ[d] : SSet.{0}) ⟶ T.toSSet)
    (g₂ : (Δ[e] : SSet.{0}) ⟶ U.toSSet)
    (σ : ⦋d⦌ ⟶ ⦋e⦌) :
    (factor T d g₁).middle ⟶ (factor U e g₂).middle :=
  (factor T d g₁).select ≫ σ ≫ (factor U e g₂).epi

/-- The image operator makes the ordinal quotient square commute exactly. -/
theorem faceOperator_fac {T U : NecklaceCode} {d e : ℕ}
    (g₁ : (Δ[d] : SSet.{0}) ⟶ T.toSSet)
    (g₂ : (Δ[e] : SSet.{0}) ⟶ U.toSSet)
    (f : T.toSSet ⟶ U.toSSet) (σ : ⦋d⦌ ⟶ ⦋e⦌)
    (h : g₁ ≫ f = SSet.stdSimplex.map σ ≫ g₂) :
    (factor T d g₁).epi ≫ faceOperator g₁ g₂ σ =
      σ ≫ (factor U e g₂).epi := by
  let A := factor T d g₁
  let B := factor U e g₂
  change A.epi ≫ A.select ≫ σ ≫ B.epi = σ ≫ B.epi
  have : Mono B.ambientFace :=
    (SimplexCategory.mono_iff_injective).mpr B.ambientFace_injective
  apply (cancel_mono B.ambientFace).mp
  apply SSet.stdSimplex.map_injective
  have hA : SSet.stdSimplex.map (A.epi ≫ A.select) ≫ g₁ = g₁ := by
    rw [Functor.map_comp, Category.assoc, ← A.face_eq]
    exact A.factor
  have hB : SSet.stdSimplex.map B.epi ≫ SSet.stdSimplex.map B.ambientFace =
      g₂ ≫ U.inclusion := by
    rw [← B.face_inclusion, ← Category.assoc, B.factor]
  calc
    SSet.stdSimplex.map ((A.epi ≫ A.select ≫ σ ≫ B.epi) ≫ B.ambientFace) =
        SSet.stdSimplex.map (A.epi ≫ A.select) ≫
          (SSet.stdSimplex.map σ ≫
            (SSet.stdSimplex.map B.epi ≫ SSet.stdSimplex.map B.ambientFace)) := by
              simp only [Functor.map_comp, Category.assoc]
    _ = SSet.stdSimplex.map (A.epi ≫ A.select) ≫
        (SSet.stdSimplex.map σ ≫ (g₂ ≫ U.inclusion)) := by rw [hB]
    _ = SSet.stdSimplex.map (A.epi ≫ A.select) ≫
        ((SSet.stdSimplex.map σ ≫ g₂) ≫ U.inclusion) := by
          simp only [Category.assoc]
    _ = SSet.stdSimplex.map (A.epi ≫ A.select) ≫ ((g₁ ≫ f) ≫ U.inclusion) :=
      congrArg (fun t ↦ SSet.stdSimplex.map (A.epi ≫ A.select) ≫ (t ≫ U.inclusion))
        h.symm
    _ = (SSet.stdSimplex.map (A.epi ≫ A.select) ≫ g₁) ≫ f ≫ U.inclusion := by
      simp only [Category.assoc]
    _ = g₁ ≫ f ≫ U.inclusion := by rw [hA]
    _ = SSet.stdSimplex.map σ ≫ (g₂ ≫ U.inclusion) := by
      simpa only [Category.assoc] using congrArg (· ≫ U.inclusion) h
    _ = SSet.stdSimplex.map (σ ≫ B.epi ≫ B.ambientFace) := by
      rw [← hB]
      simp only [Functor.map_comp]

/-- The selected faces form an exact square in the target necklace. -/
theorem faceOperator_square {T U : NecklaceCode} {d e : ℕ}
    (g₁ : (Δ[d] : SSet.{0}) ⟶ T.toSSet)
    (g₂ : (Δ[e] : SSet.{0}) ⟶ U.toSSet)
    (f : T.toSSet ⟶ U.toSSet) (σ : ⦋d⦌ ⟶ ⦋e⦌)
    (h : g₁ ≫ f = SSet.stdSimplex.map σ ≫ g₂) :
    SSet.stdSimplex.map (faceOperator g₁ g₂ σ) ≫ (factor U e g₂).face =
      (factor T d g₁).face ≫ f := by
  let A := factor T d g₁
  let B := factor U e g₂
  change SSet.stdSimplex.map (A.select ≫ σ ≫ B.epi) ≫ B.face = A.face ≫ f
  calc
    _ = SSet.stdSimplex.map A.select ≫
        (SSet.stdSimplex.map σ ≫ (SSet.stdSimplex.map B.epi ≫ B.face)) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = SSet.stdSimplex.map A.select ≫ (SSet.stdSimplex.map σ ≫ g₂) := by
      rw [B.factor]
    _ = SSet.stdSimplex.map A.select ≫ (g₁ ≫ f) := by rw [← h]
    _ = (SSet.stdSimplex.map A.select ≫ g₁) ≫ f := by
      simp only [Category.assoc]
    _ = A.face ≫ f := by rw [A.face_eq]

/-- The quotient square determines the face operator uniquely. -/
theorem faceOperator_unique {T U : NecklaceCode} {d e : ℕ}
    (g₁ : (Δ[d] : SSet.{0}) ⟶ T.toSSet)
    (g₂ : (Δ[e] : SSet.{0}) ⟶ U.toSSet)
    (f : T.toSSet ⟶ U.toSSet) (σ : ⦋d⦌ ⟶ ⦋e⦌)
    (h : g₁ ≫ f = SSet.stdSimplex.map σ ≫ g₂)
    (k : (factor T d g₁).middle ⟶ (factor U e g₂).middle)
    (hk : (factor T d g₁).epi ≫ k = σ ≫ (factor U e g₂).epi) :
    k = faceOperator g₁ g₂ σ := by
  have : Epi (factor T d g₁).epi :=
    SimplexCategory.epi_iff_surjective.mpr (factor T d g₁).epi_surjective
  apply (cancel_epi (factor T d g₁).epi).mp
  exact hk.trans (faceOperator_fac g₁ g₂ f σ h).symm

/-- The selected image operator of an identity is the identity. -/
theorem faceOperator_id (T : NecklaceCode) (d : ℕ)
    (g : (Δ[d] : SSet.{0}) ⟶ T.toSSet) :
    faceOperator g g (𝟙 ⦋d⦌) = 𝟙 (factor T d g).middle := by
  symm
  apply faceOperator_unique g g (𝟙 T.toSSet) (𝟙 ⦋d⦌) (by simp) (𝟙 _) (by simp)

/-- Image operators respect composition of actual simplex triangles. -/
theorem faceOperator_comp {T U V : NecklaceCode} {d e k : ℕ}
    (g₁ : (Δ[d] : SSet.{0}) ⟶ T.toSSet)
    (g₂ : (Δ[e] : SSet.{0}) ⟶ U.toSSet)
    (g₃ : (Δ[k] : SSet.{0}) ⟶ V.toSSet)
    (f₁ : T.toSSet ⟶ U.toSSet) (f₂ : U.toSSet ⟶ V.toSSet)
    (σ₁ : ⦋d⦌ ⟶ ⦋e⦌) (σ₂ : ⦋e⦌ ⟶ ⦋k⦌)
    (h₁ : g₁ ≫ f₁ = SSet.stdSimplex.map σ₁ ≫ g₂)
    (h₂ : g₂ ≫ f₂ = SSet.stdSimplex.map σ₂ ≫ g₃) :
    faceOperator g₁ g₃ (σ₁ ≫ σ₂) =
      faceOperator g₁ g₂ σ₁ ≫ faceOperator g₂ g₃ σ₂ := by
  have h : g₁ ≫ (f₁ ≫ f₂) = SSet.stdSimplex.map (σ₁ ≫ σ₂) ≫ g₃ := by
    calc
      _ = (g₁ ≫ f₁) ≫ f₂ := (Category.assoc _ _ _).symm
      _ = (SSet.stdSimplex.map σ₁ ≫ g₂) ≫ f₂ := by rw [h₁]
      _ = SSet.stdSimplex.map σ₁ ≫ (g₂ ≫ f₂) := Category.assoc _ _ _
      _ = SSet.stdSimplex.map σ₁ ≫ (SSet.stdSimplex.map σ₂ ≫ g₃) := by rw [h₂]
      _ = (SSet.stdSimplex.map σ₁ ≫ SSet.stdSimplex.map σ₂) ≫ g₃ :=
        (Category.assoc _ _ _).symm
      _ = SSet.stdSimplex.map (σ₁ ≫ σ₂) ≫ g₃ := by rw [Functor.map_comp]
  symm
  apply faceOperator_unique g₁ g₃ (f₁ ≫ f₂) (σ₁ ≫ σ₂) h _
  calc
    _ = ((factor T d g₁).epi ≫ faceOperator g₁ g₂ σ₁) ≫
        faceOperator g₂ g₃ σ₂ := (Category.assoc _ _ _).symm
    _ = (σ₁ ≫ (factor U e g₂).epi) ≫ faceOperator g₂ g₃ σ₂ := by
      rw [faceOperator_fac g₁ g₂ f₁ σ₁ h₁]
    _ = σ₁ ≫ ((factor U e g₂).epi ≫ faceOperator g₂ g₃ σ₂) :=
      Category.assoc _ _ _
    _ = σ₁ ≫ (σ₂ ≫ (factor V k g₃).epi) := by
      rw [faceOperator_fac g₂ g₃ f₂ σ₂ h₂]
    _ = (σ₁ ≫ σ₂) ≫ (factor V k g₃).epi := (Category.assoc _ _ _).symm

end

end DaggerModels.PartII.JTNativeSimplexImage
