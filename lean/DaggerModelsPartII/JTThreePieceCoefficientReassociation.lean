import DaggerModelsPartII.TripleBeadEndpointLabel
import ChosenNecklaceWedgeAssoc
import DaggerModelsPartII.JTNativeCutPointAssembly

/-!
# Reassociation of COMPLETE mapping-space coefficients

The three whole coefficients have matching joint restrictions; their endpoint
rows may vary over the entire coefficient simplex. Existing native associators
and mapping-space pullbacks identify BOTH gluings. No equality of raw values,
point-target reduction or extra endpoint constancy is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTThreePieceCoefficientReassociation

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue
  glue_first glue_last glue_left glue_right wedgeMappingPullback)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (free.map f) W

private theorem pre_comp (W : Source) {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pre W (f ≫ g) = pre W g ≫ pre W f := by
  rw [pre, free.map_comp, diagramMappingPrecomp_comp]

private theorem pre_id (W : Source) (X : SSet.{0}) : pre W (𝟙 X) = 𝟙 _ := by
  rw [pre, free.map_id, diagramMappingPrecomp_id]

variable (W : Source) (P M R : NecklaceCode) (k : SimplexCategory)
variable (a : std.obj k ⟶ labels W P) (b : std.obj k ⟶ labels W M)
variable (c : std.obj k ⟶ labels W R)
variable (hab : a ≫ lastRestriction W P = b ≫ firstRestriction W M)
variable (hbc : b ≫ lastRestriction W M = c ≫ firstRestriction W R)

include hbc in
private theorem leftJoint :
    glue W P M k a b hab ≫ lastRestriction W (wedge P M) =
      c ≫ firstRestriction W R := by
  rw [glue_last]
  exact hbc

include hab in
private theorem rightJoint :
    a ≫ lastRestriction W P =
      glue W M R k b c hbc ≫ firstRestriction W (wedge M R) := by
  rw [glue_first]
  exact hab

/-- The complete coefficient with the first two native pieces glued first. -/
def leftCoefficient : std.obj k ⟶ labels W (wedge (wedge P M) R) :=
  glue W (wedge P M) R k (glue W P M k a b hab) c
    (leftJoint W P M R k a b c hab hbc)

/-- The same three complete coefficients with the last two pieces glued first. -/
def rightCoefficient : std.obj k ⟶ labels W (wedge P (wedge M R)) :=
  glue W P (wedge M R) k a (glue W M R k b c hbc)
    (rightJoint W P M R k a b c hab hbc)

private theorem left_first : leftCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleLeftT P M R) = a := by
  rw [tripleLeftT, pre_comp, ← Category.assoc, leftCoefficient, glue_left, glue_left]

private theorem left_middle : leftCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleLeftU P M R) = b := by
  rw [tripleLeftU, pre_comp, ← Category.assoc, leftCoefficient, glue_left, glue_right]

private theorem left_last : leftCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleLeftV P M R) = c := by
  rw [tripleLeftV, leftCoefficient, glue_right]

private theorem right_first : rightCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleRightT P M R) = a := by
  rw [tripleRightT, rightCoefficient, glue_left]

private theorem right_middle : rightCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleRightU P M R) = b := by
  rw [tripleRightU, pre_comp, ← Category.assoc, rightCoefficient, glue_right, glue_left]

private theorem right_last : rightCoefficient W P M R k a b c hab hbc ≫
    pre W (tripleRightV P M R) = c := by
  rw [tripleRightV, pre_comp, ← Category.assoc, rightCoefficient, glue_right, glue_right]

private theorem left_ext {X : SSet.{0}}
    {u v : X ⟶ labels W (wedge (wedge P M) R)}
    (hP : u ≫ pre W (tripleLeftT P M R) = v ≫ pre W (tripleLeftT P M R))
    (hM : u ≫ pre W (tripleLeftU P M R) = v ≫ pre W (tripleLeftU P M R))
    (hR : u ≫ pre W (tripleLeftV P M R) = v ≫ pre W (tripleLeftV P M R)) : u = v := by
  apply (wedgeMappingPullback W (wedge P M) R).hom_ext
  · apply (wedgeMappingPullback W P M).hom_ext
    · simpa only [tripleLeftT, pre_comp, Category.assoc] using hP
    · simpa only [tripleLeftU, pre_comp, Category.assoc] using hM
  · exact hR

/-- The FULL coefficient is preserved by the original forward native associator. -/
theorem associator_coefficient : leftCoefficient W P M R k a b c hab hbc =
    rightCoefficient W P M R k a b c hab hbc ≫ pre W (wedgeAssocHom P M R) := by
  apply left_ext
  · rw [left_first, Category.assoc, ← pre_comp, wedgeAssocHom_T, right_first]
  · rw [left_middle, Category.assoc, ← pre_comp, wedgeAssocHom_U, right_middle]
  · rw [left_last, Category.assoc, ← pre_comp, wedgeAssocHom_V, right_last]

/-- Reassociation in the reverse direction preserves that SAME full coefficient. -/
theorem inverse_associator_coefficient : rightCoefficient W P M R k a b c hab hbc =
    leftCoefficient W P M R k a b c hab hbc ≫ pre W (wedgeAssocInv P M R) := by
  rw [associator_coefficient, Category.assoc, ← pre_comp]
  change rightCoefficient W P M R k a b c hab hbc =
    rightCoefficient W P M R k a b c hab hbc ≫
      pre W ((wedgeAssoc P M R).inv ≫ (wedgeAssoc P M R).hom)
  rw [Iso.inv_hom_id, pre_id]
  exact (Category.comp_id (rightCoefficient W P M R k a b c hab hbc)).symm

private theorem zero_retract (Z : NecklaceCode) (hZ : Z.len = 0) :
    SSet.stdSimplex.isTerminalObj₀.from Z.toSSet ≫
      pointAt Z (ULift.up (Fin.last Z.len)) = 𝟙 Z.toSSet := by
  obtain rfl := code_eq_point_of_zero Z hZ
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Removing a zero-length native piece preserves its WHOLE glued coefficient.
The joint row may vary over the entire coefficient simplex. -/
theorem zeroUnit_coefficient (Z : NecklaceCode) (hZ : Z.len = 0) (T : NecklaceCode)
    (z : std.obj k ⟶ labels W Z) (r : std.obj k ⟶ labels W T)
    (h : z ≫ lastRestriction W Z = r ≫ firstRestriction W T) :
    glue W Z T k z r h = r ≫ pre W (JTNativeCutPointAssembly.zeroUnit Z T hZ).map := by
  have hz : z = (r ≫ firstRestriction W T) ≫
      pre W (SSet.stdSimplex.isTerminalObj₀.from Z.toSSet) := by
    rw [← h]
    change z = (z ≫ pre W (pointAt Z (ULift.up (Fin.last Z.len)))) ≫
      pre W (SSet.stdSimplex.isTerminalObj₀.from Z.toSSet)
    rw [Category.assoc, ← pre_comp, zero_retract Z hZ, pre_id]
    exact (Category.comp_id z).symm
  apply (wedgeMappingPullback W Z T).hom_ext
  · rw [glue_left, Category.assoc, ← pre_comp, JTNativeCutPointAssembly.zeroUnit_left,
      pre_comp, ← Category.assoc]
    exact hz
  · rw [glue_right, Category.assoc, ← pre_comp, JTNativeCutPointAssembly.zeroUnit_right,
      pre_id]
    exact (Category.comp_id r).symm

end
end DaggerModels.PartII.JTThreePieceCoefficientReassociation
