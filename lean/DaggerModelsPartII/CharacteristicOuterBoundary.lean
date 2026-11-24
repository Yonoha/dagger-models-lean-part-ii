import DaggerModelsPartII.FreeDaggerPathChains
import DaggerModelsPartII.ReversalOuterFaceSubobject

/-!
# Characteristic maps send outer faces to the preceding length stage

Deleting the first or last vertex of a letter chain deletes one letter.
Every element of the literal outer-face subpresheaf factors through one of
these two cofaces; subsequent reversal-simplex pullback cannot increase length.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.CharacteristicOuterBoundary

open DaggerNerveLengthFiltration FreeDaggerPathChains ReversalOuterFaceSubobject

noncomputable section

/-- Omitting the first vertex deletes one letter from a chain of letters. -/
theorem totalLength_firstOuterCoface {m t : ℕ}
    (F : Fin (t + 2) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin (t + 1),
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1) :
    totalLength t m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap (firstOuterCoface t) F) = t := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  rw [X.extensionMap_monotone (firstOuterCoface t) (by
    intro i j h
    exact Fin.succ_le_succ_iff.mpr h)]
  rw [totalLength]
  have hterm : ∀ i : Fin t,
      letterLength ((X.toSSet.map
        (ReverseSimplex.monotoneHom (firstOuterCoface t) (by
          intro i j h
          exact Fin.succ_le_succ_iff.mpr h)).op F).map
            (homOfLE (Fin.castSucc_le_succ i))) = 1 := by
    intro i
    exact hF i.succ
  simp_rw [hterm]
  simp

/-- Omitting the last vertex deletes one letter from a chain of letters. -/
theorem totalLength_lastOuterCoface {m t : ℕ}
    (F : Fin (t + 2) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin (t + 1),
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1) :
    totalLength t m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap (lastOuterCoface t) F) = t := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  rw [X.extensionMap_monotone (lastOuterCoface t) (by
    intro i j h
    exact Fin.castSucc_le_castSucc_iff.mpr h)]
  rw [totalLength]
  have hterm : ∀ i : Fin t,
      letterLength ((X.toSSet.map
        (ReverseSimplex.monotoneHom (lastOuterCoface t) (by
          intro i j h
          exact Fin.castSucc_le_castSucc_iff.mpr h)).op F).map
            (homOfLE (Fin.castSucc_le_succ i))) = 1 := by
    intro i
    exact hF i.castSucc
  simp_rw [hterm]
  simp

/-- Every pullback of a letter chain along the outer-face union has lost
at least one letter. -/
theorem totalLength_outerFace {m t : ℕ}
    (F : Fin (t + 2) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin (t + 1),
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {k : ReverseSimplex} (φ : k ⟶ (⟨t + 1⟩ : ReverseSimplex))
    (hφ : φ ∈ (outerFaceSubpresheaf t).obj (op k)) :
    totalLength k.len m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ F) ≤ t := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  rcases hφ with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · change ψ ≫ firstOuterCoface t = φ at hψ
    rw [← hψ, X.extensionMap_comp]
    exact (totalLength_extensionMap m ψ _).trans_eq (totalLength_firstOuterCoface F hF)
  · change ψ ≫ lastOuterCoface t = φ at hψ
    rw [← hψ, X.extensionMap_comp]
    exact (totalLength_extensionMap m ψ _).trans_eq (totalLength_lastOuterCoface F hF)

/-- The same boundary estimate with the manuscript's target-length indexing. -/
theorem totalLength_outerFaceAt {m l : ℕ} (hl : 1 ≤ l)
    (F : Fin (l + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin l,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {k : ReverseSimplex} (φ : k ⟶ (⟨l⟩ : ReverseSimplex))
    (hφ : φ ∈ (outerFaceSubpresheafAt l hl).obj (op k)) :
    totalLength k.len m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ F) ≤ l - 1 := by
  cases l with
  | zero => omega
  | succ t =>
    exact totalLength_outerFace F hF φ (by
      simpa [outerFaceSubpresheafAt] using hφ)

/-- The characteristic map of every positive-length path sends the literal
outer-face subpresheaf into the preceding total-length stage. -/
theorem characteristic_outerFace_length {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) (hp : 1 ≤ letterLength p)
    {k : ReverseSimplex} (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : φ ∈ (outerFaceSubpresheafAt (letterLength p) hp).obj (op k)) :
    (characteristic p).app (op k) φ ∈
      (lengthFiltration m (letterLength p - 1)).obj (op k) := by
  rw [characteristic_app]
  exact totalLength_outerFaceAt hp (letterChain p) (letterChain_adjacent_length p) φ hφ

/-- The attaching map on the outer faces, with codomain the preceding
length subfunctor rather than the entire nerve. -/
def boundaryCharacteristic {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) (hp : 1 ≤ letterLength p) :
    (outerFaceSubpresheafAt (letterLength p) hp).toFunctor ⟶
      (lengthFiltration m (letterLength p - 1)).toFunctor where
  app k φ := ⟨(characteristic p).app k φ.val,
    characteristic_outerFace_length p hp φ.val φ.property⟩
  naturality _ _ f := by
    funext φ
    apply Subtype.ext
    exact congrFun ((characteristic p).naturality f) φ.val

/-- The boundary attaching map is the actual restriction of the specified
characteristic map. -/
theorem boundaryCharacteristic_ι {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) (hp : 1 ≤ letterLength p) :
    boundaryCharacteristic p hp ≫ (lengthFiltration m (letterLength p - 1)).ι =
      (outerFaceSubpresheafAt (letterLength p) hp).ι ≫ characteristic p := by
  rfl

/-- The full characteristic map has values in its path's length stage. -/
def stageCharacteristic {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) : yoneda.obj (⟨letterLength p⟩ : ReverseSimplex) ⟶
      (lengthFiltration m (letterLength p)).toFunctor where
  app k φ := ⟨(characteristic p).app k φ, by
    change totalLength k.unop.len m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤ letterLength p
    exact (totalLength_extensionMap m φ (letterChain p)).trans_eq
      (totalLength_letterChain p)⟩
  naturality _ _ f := by
    funext φ
    apply Subtype.ext
    exact congrFun ((characteristic p).naturality f) φ

/-- Including the length stage recovers the specified characteristic map. -/
theorem stageCharacteristic_ι {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) :
    stageCharacteristic p ≫ (lengthFiltration m (letterLength p)).ι =
      characteristic p := by
  rfl

/-- The characteristic map and its outer-face restriction give the
literal commutative attaching square between successive length stages. -/
theorem boundaryCharacteristic_square {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) (hp : 1 ≤ letterLength p) :
    boundaryCharacteristic p hp ≫
        Subfunctor.homOfLe (lengthFiltration_mono m (Nat.sub_le (letterLength p) 1)) =
      (outerFaceSubpresheafAt (letterLength p) hp).ι ≫ stageCharacteristic p := by
  rfl

end

end DaggerModels.PartII.CharacteristicOuterBoundary
