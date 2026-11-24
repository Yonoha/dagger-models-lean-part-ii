import DaggerModelsPartII.JTParameterVertexKan
import SSetSM7
import TopCatModelCategory.SSet.KeyLemma

/-!
# The fixed-square lift space for a simplicial vertex inclusion

The native SM7 corner and fixed-square fiber retain both original maps and
the two strict lifting equations. No endpoint fiber or comma category is
asserted contractible. Actual parameter-vertex specialization uses the SAME
checked vertex map, without a replacement interval.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra MonoidalClosed
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ParameterVertexLiftSpace

noncomputable section

universe u

/-- The full fixed-square lift space is a Kan weakly contractible simplicial
set.  This is the existing native cotensor corner, not the endpoint fiber
of `p` and not a space of all squares. -/
theorem fixedSquare_liftSpace_toPoint_weak
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [Fibration p] [WeakEquivalence i]
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    WeakEquivalence
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.ihomToPullbackFiber sq : SSet.{u})) := by
  haveI : Fibration (SSet.ihomToPullback i p) :=
    (DaggerSSetSM7.corner_sm7 i p).1
  haveI : WeakEquivalence (SSet.ihomToPullback i p) :=
    (DaggerSSetSM7.corner_sm7 i p).2 (Or.inl inferInstance)
  change WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.Subcomplex.fiber (SSet.ihomToPullback i p)
        (SSet.ihomToPullbackTgt₀Mk sq) : SSet.{u}))
  exact SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
    (SSet.Subcomplex.fiber_isPullback (SSet.ihomToPullback i p)
      (SSet.ihomToPullbackTgt₀Mk sq))

/-- The same fixed lift space is Kan.  The instance is already provided by
the native mapping-fiber API. -/
theorem fixedSquare_liftSpace_kan
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [Fibration p]
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    (SSet.ihomToPullbackFiber sq : SSet.{u}).KanComplex := by
  infer_instance

/-- An actual zero-simplex of the SAME fixed lift space, with BOTH strict equations. -/
def liftVertex {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [Fibration p] [WeakEquivalence i]
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    (SSet.ihomToPullbackFiber sq).obj (Opposite.op ⦋0⦌) := by
  have : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff i).mpr inferInstance
  exact ⟨SSet.ihom₀Equiv.symm sq.lift,
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff sq sq.lift).mpr
      ⟨sq.fac_left, sq.fac_right⟩⟩

/-- Weak contractibility for the ACTUAL groupoid-parameter vertex and fixed square. -/
theorem parameterVertex_liftSpace_toPoint_weak
    (k : SimplexCategory) (j : Fin (k.len + 1)) {X Y : SSet.{0}} {p : X ⟶ Y}
    [Fibration p] {t : (Δ[0] : SSet.{0}) ⟶ X}
    {b : GroupoidSimplex.parameter.obj k ⟶ Y}
    (sq : CommSq t (JTParameterContraction.parameterVertex k j) p b) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.ihomToPullbackFiber sq : SSet.{0})) := by
  have : Mono (JTParameterContraction.parameterVertex k j) :=
    JTParameterVertexKan.vertex_mono k j
  have : WeakEquivalence (JTParameterContraction.parameterVertex k j) :=
    JTParameterVertexKan.vertex_weak k j
  exact fixedSquare_liftSpace_toPoint_weak sq

end

end DaggerModels.PartII.ParameterVertexLiftSpace
