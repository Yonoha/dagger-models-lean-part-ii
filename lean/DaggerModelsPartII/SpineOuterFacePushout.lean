import DaggerModelsPartII.ReversalOuterFaceLocality
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The two pushout squares underlying the outer-face comparison

The outer-face union is the pushout of its faces along their intersection.
The ordinary spine has the parallel pushout presentation by its intersections
with those faces. These are the literal simplicial-set pushout squares needed
for a local gluing argument.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.SpineOuterFacePushout

open ReversalOuterFaceLocality

noncomputable section

/-- The outer face omitting the initial vertex. -/
def firstOuterFace (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {(0 : Fin (t + 3))}ᶜ

/-- The outer face omitting the final vertex. -/
def lastOuterFace (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {(Fin.last (t + 2))}ᶜ

/-- The middle face is the intersection of the two outer faces. -/
def middleFace (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  firstOuterFace t ⊓ lastOuterFace t

theorem outerFaces_eq_sup (t : ℕ) :
    ordinaryOuterFaces.{u} t = firstOuterFace t ⊔ lastOuterFace t := rfl

/-- The outer-face union is a literal pushout in simplicial sets. -/
def outerFaceBicart (t : ℕ) :
    SSet.Subcomplex.BicartSq (middleFace.{u} t) (firstOuterFace t)
      (lastOuterFace t) (ordinaryOuterFaces t) := ⟨rfl, rfl⟩

def outerFacePushout (t : ℕ) : IsPushout
    (SSet.Subcomplex.homOfLE (inf_le_left : middleFace.{u} t ≤ firstOuterFace t))
    (SSet.Subcomplex.homOfLE (inf_le_right : middleFace.{u} t ≤ lastOuterFace t))
    (SSet.Subcomplex.homOfLE (le_sup_left : firstOuterFace.{u} t ≤ ordinaryOuterFaces t))
    (SSet.Subcomplex.homOfLE (le_sup_right : lastOuterFace.{u} t ≤ ordinaryOuterFaces t)) :=
  (outerFaceBicart t).isPushout

/-- The part of the spine lying in the first outer face. -/
def firstSpinePart (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  DaggerNativeStandardSpineInner.spine (t + 2) ⊓ firstOuterFace t

/-- The part of the spine lying in the final outer face. -/
def lastSpinePart (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  DaggerNativeStandardSpineInner.spine (t + 2) ⊓ lastOuterFace t

/-- Their intersection, the middle portion of the spine. -/
def middleSpinePart (t : ℕ) : (Δ[t + 2] : SSet.{u}).Subcomplex :=
  firstSpinePart t ⊓ lastSpinePart t

/-- Every spine simplex lies in one of the two outer faces. -/
theorem spineParts_sup (t : ℕ) :
    firstSpinePart.{u} t ⊔ lastSpinePart t =
      DaggerNativeStandardSpineInner.spine (t + 2) := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro q c hc
    have hu := spine_le_ordinaryOuterFaces t q hc
    change c ∈ (firstOuterFace t ⊔ lastOuterFace t).obj q at hu
    rcases hu with hf | hg
    · exact Or.inl ⟨hc, hf⟩
    · exact Or.inr ⟨hc, hg⟩

/-- The spine is also a literal pushout of its two outer-face parts. -/
def spinePartsBicart (t : ℕ) :
    SSet.Subcomplex.BicartSq (middleSpinePart.{u} t) (firstSpinePart t)
      (lastSpinePart t) (DaggerNativeStandardSpineInner.spine (t + 2)) :=
  ⟨spineParts_sup t, rfl⟩

def spinePartsPushout (t : ℕ) : IsPushout
    (SSet.Subcomplex.homOfLE
      (inf_le_left : middleSpinePart.{u} t ≤ firstSpinePart t))
    (SSet.Subcomplex.homOfLE
      (inf_le_right : middleSpinePart.{u} t ≤ lastSpinePart t))
    (SSet.Subcomplex.homOfLE
      (inf_le_left : firstSpinePart.{u} t ≤
        DaggerNativeStandardSpineInner.spine (t + 2)))
    (SSet.Subcomplex.homOfLE
      (inf_le_left : lastSpinePart.{u} t ≤
        DaggerNativeStandardSpineInner.spine (t + 2))) :=
  (spinePartsBicart t).isPushout

end

end DaggerModels.PartII.SpineOuterFacePushout
