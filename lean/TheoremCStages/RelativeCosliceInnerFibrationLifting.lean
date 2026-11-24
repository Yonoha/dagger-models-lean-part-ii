import OriginalJoinedBoundarySuffixGluing
import NativeInnerHornFactorization

/-!
# Relative joined horn filling for an actual inner fibration

The original boundary and suffix horn in `C` glue to the same native joined
inner horn. A prescribed full simplex in `D` supplies its relative base.
The facewise equations below are the exact compatibility needed to apply the
inner-fibration lifting property; the filler in `C` is constructed here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedSuffixFaceMaps
open DaggerOriginalJoinedSuffixHornGluing DaggerOriginalJoinedBoundarySuffixGluing
open DaggerNativeInnerHornFactorization

universe u

namespace DaggerOriginalRelativeCosliceInnerFibrationLifting

noncomputable section

private theorem suffixFaceMap_over {C D : SSet.{u}} (p : C ⟶ D)
    (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ C)
    (μD : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ D)
    (hface : joinedHornCoface k n i j hj φ ≫ p =
      SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD) :
    suffixFaceMap k n i j hj φ ≫ p =
      (SSet.stdSimplex.face {suffixIndex k (n + 1) j}ᶜ).ι ≫ μD := by
  let e := SSet.stdSimplex.faceSingletonComplIso.{u} (suffixIndex k (n + 1) j)
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (suffixFaceMap k n i j hj φ ≫ p) =
        joinedHornCoface k n i j hj φ ≫ p := by
      simp only [e, suffixFaceMap, Category.assoc, Iso.hom_inv_id_assoc]
    _ = SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD := hface
    _ = e.hom ≫
        ((SSet.stdSimplex.face {suffixIndex k (n + 1) j}ᶜ).ι ≫ μD) := by
      simp only [e, SSet.stdSimplex.faceSingletonComplIso_hom_ι_assoc]

private theorem suffixHornMap_over {C D : SSet.{u}} (p : C ⟶ D)
    (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ C)
    (μD : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ D)
    (hface : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      joinedHornCoface k n i j hj φ ≫ p =
        SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD) :
    suffixHornMap k n i φ ≫ p = (suffixHorn k (n + 1) i).ι ≫ μD := by
  ext q s
  have hs : s.val ∈ (suffixHorn k (n + 1) i).obj q := s.property
  simp only [suffixHorn, Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨j, hj⟩ := hs
  let t : (SSet.stdSimplex.face {suffixIndex k (n + 1) j.val}ᶜ : SSet.{u}).obj q :=
    ⟨s.val, hj⟩
  have hrestriction := congrArg (fun f ↦ f.app q t) (suffixHornMap_face k n i φ j)
  have hbase := congrArg (fun f ↦ f.app q t)
    (suffixFaceMap_over p k n i j.val j.property φ μD (hface j.val j.property))
  calc
    (suffixHornMap k n i φ ≫ p).app q s =
        (suffixFaceMap k n i j.val j.property φ ≫ p).app q t :=
      congrArg (p.app q) hrestriction
    _ = ((SSet.stdSimplex.face {suffixIndex k (n + 1) j.val}ᶜ).ι ≫ μD).app q t :=
      hbase
    _ = ((suffixHorn k (n + 1) i).ι ≫ μD).app q s := rfl

/-- The original joined horn lifts relative to a prescribed full base simplex.
The prescribed boundary and every original suffix coface remain exact. -/
theorem joined_horn_extension_over {C D : SSet.{u}} (p : C ⟶ D)
    (hp : innerFibrations p) (k n : ℕ) (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ C)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k C)
    (w : φ ≫ joinedBoundaryRestriction k C = Λ[n + 1, i].ι ≫ β)
    (μD : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ D)
    (hboundary : SSet.yonedaEquiv β ≫ p = (prefixBoundary k (n + 1)).ι ≫ μD)
    (hface : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      joinedHornCoface k n i j hj φ ≫ p =
        SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD) :
    ∃ μC : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ C,
      (prefixBoundary k (n + 1)).ι ≫ μC = SSet.yonedaEquiv β ∧
      (∀ (j : Fin (n + 2)) (hj : j ≠ i),
        SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μC =
          joinedHornCoface k n i j hj φ) ∧
      μC ≫ p = μD := by
  obtain ⟨Γ, hΓleft, hΓright⟩ := glue_all_horn k n i φ β w
  let A := prefixBoundary.{u} k (n + 1)
  let S := suffixHorn.{u} k (n + 1) i
  have hΓbase : Γ ≫ p = (A ⊔ S).ι ≫ μD := by
    have sq : SSet.Subcomplex.BicartSq (A ⊓ S) A S (A ⊔ S) := ⟨rfl, rfl⟩
    apply sq.isPushout.hom_ext
    · calc
        SSet.Subcomplex.homOfLE le_sup_left ≫ (Γ ≫ p) =
            (SSet.yonedaEquiv β) ≫ p := by rw [← Category.assoc, hΓleft]
        _ = A.ι ≫ μD := hboundary
        _ = SSet.Subcomplex.homOfLE le_sup_left ≫ ((A ⊔ S).ι ≫ μD) := by
          simp only [SSet.Subcomplex.homOfLE_ι_assoc]
    · calc
        SSet.Subcomplex.homOfLE le_sup_right ≫ (Γ ≫ p) =
            suffixHornMap k n i φ ≫ p := by rw [← Category.assoc, hΓright]
        _ = S.ι ≫ μD := suffixHornMap_over p k n i φ μD hface
        _ = SSet.Subcomplex.homOfLE le_sup_right ≫ ((A ⊔ S).ι ≫ μD) := by
          simp only [SSet.Subcomplex.homOfLE_ι_assoc]
  have hinner := suffixIndex_inner k (n + 1) i hi
  haveI : HasLiftingProperty
      (A ⊔ S).ι p := by
    change HasLiftingProperty
      (prefixBoundary k (n + 1) ⊔ suffixHorn k (n + 1) i).ι p
    rw [prefixBoundary_sup_suffixHorn]
    exact (innerFibrations_iff p).mp hp (k + n) (suffixIndex k (n + 1) i)
      hinner.1 hinner.2
  let sq : CommSq Γ (A ⊔ S).ι p μD := ⟨hΓbase⟩
  haveI := HasLiftingProperty.sq_hasLift sq
  let μC := sq.lift
  have hμ : Γ = (A ⊔ S).ι ≫ μC := sq.fac_left.symm
  have hμbase : μC ≫ p = μD := sq.fac_right
  have hμboundary : A.ι ≫ μC = SSet.yonedaEquiv β := by
    simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc] using hΓleft
  have hμsuffix : S.ι ≫ μC = suffixHornMap k n i φ := by
    simpa only [hμ, SSet.Subcomplex.homOfLE_ι_assoc] using hΓright
  refine ⟨μC, hμboundary, ?_, hμbase⟩
  intro j hj
  have hf := suffixHornMap_face k n i φ ⟨j, hj⟩
  rw [← hμsuffix] at hf
  have hc := congrArg (fun f ↦
    (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k (n + 1) j)).hom ≫ f) hf
  dsimp only at hc
  simpa only [suffixFaceMap, SSet.Subcomplex.homOfLE_ι_assoc,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι_assoc,
    Iso.hom_inv_id_assoc] using hc

#print axioms joined_horn_extension_over

end

end DaggerOriginalRelativeCosliceInnerFibrationLifting
