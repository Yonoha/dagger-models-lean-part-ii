import DaggerModelsPartII.JTCylinderQuotientImages
import NativeMonoRestrictionParameterizedWalkingLifting
import TopCatModelCategory.ColimitsType
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Lean.Elab.Tactic.Omega

/-!
# Height-preserving prism embeddings in the actual reduced cylinder

A prism map preserving the interval projection descends through the
literal reduced-cylinder pushouts.  When the prism map is mono, so is
the descended map.  The gap embedding inserts one width coordinate in
the terminal row and is an instance of this construction.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial

namespace DaggerModels.PartII.JTCylinderPrismEmbedding

open JTXiEndpointCollapse

noncomputable section

private abbrev prism (n : ℕ) : SSet.{0} := interval ⊗ (Δ[n] : SSet.{0})
private abbrev seam (n : ℕ) : SSet.{0} := boundary ⊗ (Δ[n] : SSet.{0})

private abbrev inclusion (n : ℕ) : seam n ⟶ prism n :=
  (ReducedCylinder.tensorInclusion JTCylinderFrame.j).app (Δ[n] : SSet.{0})

private abbrev projection (n : ℕ) : seam n ⟶ boundary :=
  (ReducedCylinder.tensorProjection boundary).app (Δ[n] : SSet.{0})

/-- The boundary-cylinder map forced by a height-preserving prism map. -/
def seamMap {n m : ℕ} (φ : prism n ⟶ prism m) : seam n ⟶ seam m :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst boundary (Δ[n] : SSet.{0}))
    (inclusion n ≫ φ ≫
      CartesianMonoidalCategory.snd interval (Δ[m] : SSet.{0}))

private theorem seamMap_projection {n m : ℕ} (φ : prism n ⟶ prism m) :
    seamMap φ ≫ projection m = projection n := by
  change seamMap φ ≫ CartesianMonoidalCategory.fst boundary
      (Δ[m] : SSet.{0}) =
    CartesianMonoidalCategory.fst boundary (Δ[n] : SSet.{0})
  exact CartesianMonoidalCategory.lift_fst _ _

private theorem seamMap_inclusion {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0})) :
    inclusion n ≫ φ = seamMap φ ≫ inclusion m := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      (inclusion n ≫ φ) ≫
          CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
        inclusion n ≫
          CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0}) := by
          rw [Category.assoc, hφ]
      _ = projection n ≫ JTCylinderFrame.j := by
          change (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[n] : SSet.{0})) ≫
            CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0}) = _
          simpa only [Category.comp_id] using
            CartesianMonoidalCategory.tensorHom_fst JTCylinderFrame.j
              (𝟙 (Δ[n] : SSet.{0}))
      _ = (seamMap φ ≫ inclusion m) ≫
          CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) := by
          change projection n ≫ JTCylinderFrame.j =
            (seamMap φ ≫
              (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[m] : SSet.{0}))) ≫
                CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0})
          rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst]
          exact congrArg (fun f => f ≫ JTCylinderFrame.j)
            (seamMap_projection φ).symm
  · calc
      (inclusion n ≫ φ) ≫
          CartesianMonoidalCategory.snd interval (Δ[m] : SSet.{0}) =
        seamMap φ ≫ CartesianMonoidalCategory.snd boundary
          (Δ[m] : SSet.{0}) := by
          rw [Category.assoc]
          exact (CartesianMonoidalCategory.lift_snd _ _).symm
      _ = (seamMap φ ≫ inclusion m) ≫
          CartesianMonoidalCategory.snd interval (Δ[m] : SSet.{0}) := by
          change seamMap φ ≫ CartesianMonoidalCategory.snd boundary
            (Δ[m] : SSet.{0}) =
              (seamMap φ ≫
                (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[m] : SSet.{0}))) ≫
                  CartesianMonoidalCategory.snd interval (Δ[m] : SSet.{0})
          rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
          simp only [Category.comp_id]

/-- The map between the *actual* reduced-cylinder pushouts. -/
def reducedMap {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0})) :
    JTCylinderFrame.value.obj ⦋n⦌ ⟶ JTCylinderFrame.value.obj ⦋m⦌ :=
  (JTCylinderFrame.isPushout ⦋n⦌).desc
    (φ ≫ JTCylinderFrame.cylinder ⦋m⦌)
    (JTCylinderFrame.boundary.app ⦋m⦌)
    (by
      calc
        inclusion n ≫ (φ ≫ JTCylinderFrame.cylinder ⦋m⦌) =
          (seamMap φ ≫ inclusion m) ≫
            JTCylinderFrame.cylinder ⦋m⦌ := by
              rw [← Category.assoc, seamMap_inclusion φ hφ]
        _ = seamMap φ ≫
            (projection m ≫ JTCylinderFrame.boundary.app ⦋m⦌) := by
              rw [Category.assoc, (JTCylinderFrame.isPushout ⦋m⦌).w]
        _ = projection n ≫ JTCylinderFrame.boundary.app ⦋m⦌ := by
              rw [← Category.assoc, seamMap_projection])

/-- Exact calibration on the uncollapsed prism leg. -/
theorem cylinder_reducedMap {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0})) :
    JTCylinderFrame.cylinder ⦋n⦌ ≫ reducedMap φ hφ =
      φ ≫ JTCylinderFrame.cylinder ⦋m⦌ :=
  (JTCylinderFrame.isPushout ⦋n⦌).inl_desc _ _ _

/-- The original ordered boundary is fixed by every descended map. -/
theorem boundary_reducedMap {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0})) :
    JTCylinderFrame.boundary.app ⦋n⦌ ≫ reducedMap φ hφ =
      JTCylinderFrame.boundary.app ⦋m⦌ :=
  (JTCylinderFrame.isPushout ⦋n⦌).inr_desc _ _ _

/-- The original interval augmentations are preserved strictly. -/
theorem reducedMap_augmentation {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0})) :
    reducedMap φ hφ ≫ JTCylinderFrame.augmentation.app ⦋m⦌ =
      JTCylinderFrame.augmentation.app ⦋n⦌ := by
  apply (JTCylinderFrame.isPushout ⦋n⦌).hom_ext
  · rw [← Category.assoc, cylinder_reducedMap, Category.assoc,
      JTCylinderFrame.cylinder_augmentation, hφ,
      JTCylinderFrame.cylinder_augmentation]
  · rw [← Category.assoc, boundary_reducedMap,
      JTCylinderFrame.boundary_augmentation,
      JTCylinderFrame.boundary_augmentation]

/-- A height-preserving mono of uncollapsed prisms remains mono after
both fixed boundary cylinders have been collapsed. -/
theorem reducedMap_mono {n m : ℕ} (φ : prism n ⟶ prism m)
    (hφ : φ ≫ CartesianMonoidalCategory.fst interval (Δ[m] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0}))
    [Mono φ] : Mono (reducedMap φ hφ) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      apply (mono_iff_injective _).2
      intro z z' hzz'
      have hqPoint : Epi ((JTCylinderFrame.cylinder ⦋n⦌).app
          (Opposite.op ⦋d⦌)) :=
        (NatTrans.epi_iff_epi_app (JTCylinderFrame.cylinder ⦋n⦌)).1
          (JTCylinderQuotientImages.cylinder_epi n) _
      obtain ⟨x, rfl⟩ := (epi_iff_surjective _).1 hqPoint z
      obtain ⟨y, rfl⟩ := (epi_iff_surjective _).1 hqPoint z'
      have hraw : (JTCylinderFrame.cylinder ⦋n⦌).app
          (Opposite.op ⦋d⦌) x =
          (JTCylinderFrame.cylinder ⦋n⦌).app
            (Opposite.op ⦋d⦌) y := by
        have htarget : ((JTCylinderFrame.cylinder ⦋m⦌).app
            (Opposite.op ⦋d⦌)) ((φ.app (Opposite.op ⦋d⦌)) x) =
          ((JTCylinderFrame.cylinder ⦋m⦌).app
            (Opposite.op ⦋d⦌)) ((φ.app (Opposite.op ⦋d⦌)) y) := by
          change ((JTCylinderFrame.cylinder ⦋n⦌ ≫
            reducedMap φ hφ).app (Opposite.op ⦋d⦌) x) =
              ((JTCylinderFrame.cylinder ⦋n⦌ ≫
                reducedMap φ hφ).app (Opposite.op ⦋d⦌) y) at hzz'
          rw [cylinder_reducedMap] at hzz'
          simpa only [NatTrans.comp_app] using hzz'
        have hinc : Function.Injective ((inclusion m).app
            (Opposite.op ⦋d⦌)) := by
          haveI : Mono (inclusion m) := by
            change Mono (JTCylinderFrame.j ▷ (Δ[m] : SSet.{0}))
            exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono
              JTCylinderFrame.j (Δ[m] : SSet.{0})
          haveI : Mono ((inclusion m).app (Opposite.op ⦋d⦌)) :=
            (NatTrans.mono_iff_mono_app (inclusion m)).1 inferInstance _
          exact (mono_iff_injective _).1 inferInstance
        have hsq := (JTCylinderFrame.isPushout ⦋m⦌).map
          ((SSet.evaluation.obj (Opposite.op ⦋d⦌)))
        change IsPushout ((inclusion m).app (Opposite.op ⦋d⦌))
          ((projection m).app (Opposite.op ⦋d⦌))
          ((JTCylinderFrame.cylinder ⦋m⦌).app (Opposite.op ⦋d⦌))
          ((JTCylinderFrame.boundary.app ⦋m⦌).app
            (Opposite.op ⦋d⦌)) at hsq
        rcases (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
          hsq.isColimit hinc _ _).1 htarget with hequal | ⟨s, t, hs, ht, hp⟩
        · have hφapp : Function.Injective
              (φ.app (Opposite.op ⦋d⦌)) := by
            haveI : Mono (φ.app (Opposite.op ⦋d⦌)) :=
              (NatTrans.mono_iff_mono_app φ).1 inferInstance _
            exact (mono_iff_injective _).1 inferInstance
          exact congrArg ((JTCylinderFrame.cylinder ⦋n⦌).app
            (Opposite.op ⦋d⦌)) (hφapp hequal)
        · have hheight := NatTrans.congr_app hφ (Opposite.op ⦋d⦌)
          have hxfirst : x.1 = JTCylinderFrame.j.app
              (Opposite.op ⦋d⦌) s.1 := by
            have hh := congrFun hheight x
            change ((φ.app (Opposite.op ⦋d⦌)) x).1 = x.1 at hh
            have hsfirst := congrArg Prod.fst hs
            change ((φ.app (Opposite.op ⦋d⦌)) x).1 =
              JTCylinderFrame.j.app (Opposite.op ⦋d⦌) s.1 at hsfirst
            exact hh.symm.trans hsfirst
          have hyfirst : y.1 = JTCylinderFrame.j.app
              (Opposite.op ⦋d⦌) t.1 := by
            have hh := congrFun hheight y
            change ((φ.app (Opposite.op ⦋d⦌)) y).1 = y.1 at hh
            have htfirst := congrArg Prod.fst ht
            change ((φ.app (Opposite.op ⦋d⦌)) y).1 =
              JTCylinderFrame.j.app (Opposite.op ⦋d⦌) t.1 at htfirst
            exact hh.symm.trans htfirst
          have hs' : ((inclusion n).app (Opposite.op ⦋d⦌))
              (s.1, x.2) = x := by
            apply Prod.ext
            · exact hxfirst.symm
            · rfl
          have ht' : ((inclusion n).app (Opposite.op ⦋d⦌))
              (t.1, y.2) = y := by
            apply Prod.ext
            · exact hyfirst.symm
            · rfl
          have hp' : s.1 = t.1 := by
            change s.1 = t.1 at hp
            exact hp
          have hw := NatTrans.congr_app
            (JTCylinderFrame.isPushout ⦋n⦌).w
            (Opposite.op ⦋d⦌)
          calc
            (JTCylinderFrame.cylinder ⦋n⦌).app (Opposite.op ⦋d⦌) x =
              (JTCylinderFrame.cylinder ⦋n⦌).app
                (Opposite.op ⦋d⦌) ((inclusion n).app
                  (Opposite.op ⦋d⦌) (s.1, x.2)) := by rw [hs']
            _ = (JTCylinderFrame.boundary.app ⦋n⦌).app
                  (Opposite.op ⦋d⦌) s.1 := by
                  exact congrFun hw (s.1, x.2)
            _ = (JTCylinderFrame.boundary.app ⦋n⦌).app
                  (Opposite.op ⦋d⦌) t.1 := by rw [hp']
            _ = (JTCylinderFrame.cylinder ⦋n⦌).app
                (Opposite.op ⦋d⦌) y := by
                  rw [← ht']
                  exact (congrFun hw (t.1, y.2)).symm
      exact hraw

/-- Insert one width position in the terminal row while fixing the
initial row and the interval coordinate. -/
def gapOrder (n : ℕ) :
    Fin 2 × Fin (n + 1) →o Fin 2 × Fin (n + 2) where
  toFun x := (x.1, ⟨x.2.val + x.1.val, by
    have hi := x.2.isLt
    have he := x.1.isLt
    omega⟩)
  monotone' x y h := by
    constructor
    · exact h.1
    · apply Fin.le_iff_val_le_val.mpr
      change x.2.val + x.1.val ≤ y.2.val + y.1.val
      exact add_le_add (Fin.le_iff_val_le_val.mp h.2)
        (Fin.le_iff_val_le_val.mp h.1)

theorem gapOrder_injective (n : ℕ) : Function.Injective (gapOrder n) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg (fun z : Fin 2 × Fin (n + 2) => z.2.val) h
  apply Prod.ext
  · exact h₁
  · apply Fin.ext
    change x.2.val + x.1.val = y.2.val + y.1.val at h₂
    change x.1 = y.1 at h₁
    have hv := congrArg Fin.val h₁
    omega

/-- The actual simplicial map induced by the product-poset gap
embedding in every simplicial degree. -/
def gapPrism (n : ℕ) : prism n ⟶ prism (n + 1) where
  app q := by
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        exact fun z => SSet.prodStdSimplex.objEquiv.symm
          ((gapOrder n).comp (SSet.prodStdSimplex.objEquiv z))
  naturality := by
    intro q r f
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        induction r using Opposite.rec with | op r =>
          induction r using SimplexCategory.rec with | h e =>
            funext z
            apply SSet.prodStdSimplex.objEquiv.injective
            rfl

theorem gapPrism_objEquiv (n d : ℕ)
    (x : (prism n).obj (Opposite.op ⦋d⦌)) :
    SSet.prodStdSimplex.objEquiv
        ((gapPrism n).app (Opposite.op ⦋d⦌) x) =
      (gapOrder n).comp (SSet.prodStdSimplex.objEquiv x) := by
  rfl

theorem gapPrism_mono (n : ℕ) : Mono (gapPrism n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      apply (mono_iff_injective _).2
      intro x y hxy
      apply SSet.prodStdSimplex.objEquiv.injective
      apply OrderHom.ext
      funext i
      have hcoord := congrArg SSet.prodStdSimplex.objEquiv hxy
      rw [gapPrism_objEquiv, gapPrism_objEquiv] at hcoord
      exact gapOrder_injective n (DFunLike.congr_fun hcoord i)

/-- The gap does not move the interval coordinate. -/
theorem gapPrism_height (n : ℕ) :
    gapPrism n ≫ CartesianMonoidalCategory.fst interval
        (Δ[n + 1] : SSet.{0}) =
      CartesianMonoidalCategory.fst interval (Δ[n] : SSet.{0}) := by
  apply NatTrans.ext
  funext q
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      funext x
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      have he := congrArg (fun f : Fin (d + 1) →o
          Fin 2 × Fin (n + 2) => (f i).1)
        (gapPrism_objEquiv n d x)
      exact he

/-- The literal gap map on the two actual reduced-cylinder pushouts. -/
def gapReduced (n : ℕ) :
    JTCylinderFrame.value.obj ⦋n⦌ ⟶
      JTCylinderFrame.value.obj ⦋n + 1⦌ :=
  reducedMap (gapPrism n) (gapPrism_height n)

theorem cylinder_gapReduced (n : ℕ) :
    JTCylinderFrame.cylinder ⦋n⦌ ≫ gapReduced n =
      gapPrism n ≫ JTCylinderFrame.cylinder ⦋n + 1⦌ :=
  cylinder_reducedMap (gapPrism n) (gapPrism_height n)

theorem gapReduced_boundary (n : ℕ) :
    JTCylinderFrame.boundary.app ⦋n⦌ ≫ gapReduced n =
      JTCylinderFrame.boundary.app ⦋n + 1⦌ :=
  boundary_reducedMap (gapPrism n) (gapPrism_height n)

theorem gapReduced_augmentation (n : ℕ) :
    gapReduced n ≫ JTCylinderFrame.augmentation.app ⦋n + 1⦌ =
      JTCylinderFrame.augmentation.app ⦋n⦌ :=
  reducedMap_augmentation (gapPrism n) (gapPrism_height n)

theorem gapReduced_mono (n : ℕ) : Mono (gapReduced n) := by
  letI : Mono (gapPrism n) := gapPrism_mono n
  exact reducedMap_mono (gapPrism n) (gapPrism_height n)

end
end DaggerModels.PartII.JTCylinderPrismEmbedding
