import DaggerModelsPartII.JTJointSideWhiskerParameterTransport

/-! Full-time parameter transport through an unbased middle replacement. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTThreePieceParameterOperators

open JTComposedPrismLabels (parameter parameter_left)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev first (T : NecklaceCode) := pointAt T (ULift.up 0)
private abbrev last (T : NecklaceCode) := pointAt T (ULift.up (Fin.last T.len))

variable {P M R : NecklaceCode} {k : SimplexCategory} {I : SSet.{0}}
variable (p : P.toSSet ⊗ I ⟶ J.obj k) (m : M.toSSet ⊗ I ⟶ J.obj k)
variable (r : R.toSSet ⊗ I ⟶ J.obj k)
variable (hP : (last P ⊗ₘ 𝟙 I) ≫ p = (first M ⊗ₘ 𝟙 I) ≫ m)
variable (hR : (last M ⊗ₘ 𝟙 I) ≫ m = (first R ⊗ₘ 𝟙 I) ≫ r)

include hP in
private theorem outer_join : (last P ⊗ₘ 𝟙 I) ≫ p =
    (first (wedge M R) ⊗ₘ 𝟙 I) ≫ parameter m r hR := by
  rw [first, ← pointAt_first_left M R]
  rw [← Category.id_comp (𝟙 I), ← tensorHom_comp_tensorHom,
    Category.assoc, parameter_left]
  exact hP

/-- Paste the three COMPLETE time parameters, with both actual seam equations. -/
def tripleParameter : (wedge P (wedge M R)).toSSet ⊗ I ⟶ J.obj k :=
  parameter p (parameter m r hR) (outer_join p m r hP hR)

variable {P' M' R' : NecklaceCode} {l : SimplexCategory} {I' : SSet.{0}}
variable (p' : P'.toSSet ⊗ I' ⟶ J.obj l) (m' : M'.toSSet ⊗ I' ⟶ J.obj l)
variable (r' : R'.toSSet ⊗ I' ⟶ J.obj l)
variable (hP' : (last P' ⊗ₘ 𝟙 I') ≫ p' = (first M' ⊗ₘ 𝟙 I') ≫ m')
variable (hR' : (last M' ⊗ₘ 𝟙 I') ≫ m' = (first R' ⊗ₘ 𝟙 I') ≫ r')
variable (f : P ⟶ P') (g : M ⟶ M') (h : R ⟶ R') (v : I ⟶ I') (a : k ⟶ l)

/-- Any exact three native, time and coefficient operators act on the entire
pasted prism. In particular the whiskered triangle arrows retain the full time. -/
theorem tripleParameter_map
    (hp : (f.map ⊗ₘ v) ≫ p' = p ≫ J.map a)
    (hm : (g.map ⊗ₘ v) ≫ m' = m ≫ J.map a)
    (hr : (h.map ⊗ₘ v) ≫ r' = r ≫ J.map a) :
    ((wedgeMap f (wedgeMap g h)).map ⊗ₘ v) ≫
        tripleParameter p' m' r' hP' hR' = tripleParameter p m r hP hR ≫ J.map a := by
  have hi := JTJointSideWhiskerParameterTransport.parameter_map g h v a
    m r m' r' hR hR' hm hr
  exact JTJointSideWhiskerParameterTransport.parameter_map f (wedgeMap g h) v a
    p (parameter m r hR) p' (parameter m' r' hR')
    (outer_join p m r hP hR) (outer_join p' m' r' hP' hR') hp hi

/-- The middle can use the original seam trace at EVERY native point and time. -/
def middleTrace (M : NecklaceCode) (q : I ⟶ J.obj k) : M.toSSet ⊗ I ⟶ J.obj k :=
  snd M.toSSet I ≫ q

/-- Its restriction to either endpoint is the same full original time trace. -/
theorem middleTrace_endpoint (M : NecklaceCode) (q : I ⟶ J.obj k)
    (i : (Δ[0] : SSet.{0}) ⟶ M.toSSet) :
    (i ⊗ₘ 𝟙 I) ≫ middleTrace M q = snd (Δ[0] : SSet.{0}) I ≫ q := by
  rw [middleTrace, ← Category.assoc, tensorHom_snd, Category.comp_id]

/-- Spine, long-edge and identity-collapse operators all preserve this whole trace. -/
theorem middleTrace_map (g : M ⟶ M') (q : I ⟶ J.obj k) :
    (g.map ⊗ₘ 𝟙 I) ≫ middleTrace M' q = middleTrace M q := by
  rw [middleTrace, ← Category.assoc, tensorHom_snd, Category.comp_id]
  rfl

end
end DaggerModels.PartII.JTThreePieceParameterOperators
