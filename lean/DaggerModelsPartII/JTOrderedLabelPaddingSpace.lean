import DaggerModelsPartII.JTPaddedTimeOperators
import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.ParameterVertexLiftSpace

/-! The literal simplicial space of padded extensions of one coefficient simplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingSpace

noncomputable section

/-- The original time simplex includes as the interior of its padded simplex. -/
def embedding (k : SimplexCategory) :
    (Δ[k.len] : SSet.{0}) ⟶ Δ[(JTPaddedTimeOperators.pad k).len] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk (JTPaddedTimeOperators.inside k))

theorem embedding_mono (k : SimplexCategory) : Mono (embedding k) := by
  apply (SSet.stdSimplex.mono_iff k.len (embedding k)).2
  intro a b hab
  apply SSet.stdSimplex.obj₀Equiv.injective
  have hv := congrArg SSet.stdSimplex.obj₀Equiv hab
  change JTPaddedTimeOperators.inside k (SSet.stdSimplex.obj₀Equiv a) =
    JTPaddedTimeOperators.inside k (SSet.stdSimplex.obj₀Equiv b) at hv
  apply Fin.ext
  have hw := congrArg Fin.val hv
  change (SSet.stdSimplex.obj₀Equiv a).val + 1 =
    (SSet.stdSimplex.obj₀Equiv b).val + 1 at hw
  omega

theorem embedding_weak (k : SimplexCategory) : WeakEquivalence (embedding k) :=
  JTInterleavedParameter.standardMap_weak _

/-- The fixed square asks for an extension of the given original coefficient simplex. -/
def square (Y : SSet.{0}) (k : SimplexCategory)
    (a : Y.obj (op k)) :
    CommSq (SSet.yonedaEquiv.symm a) (embedding k)
      (SSet.stdSimplex.isTerminalObj₀.from Y)
      (SSet.stdSimplex.isTerminalObj₀.from
        (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0})) := by
  refine ⟨?_⟩
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The full simplicial fiber of padded extensions, with the original simplex fixed. -/
def extensionSpace (Y : SSet.{0}) (k : SimplexCategory)
    (a : Y.obj (op k)) : SSet.{0} :=
  SSet.ihomToPullbackFiber (square Y k a)

/-- A literal point of the fiber is precisely a padded simplex restricting to `a`. -/
theorem extension_mem_iff (Y : SSet.{0}) (k : SimplexCategory)
    (a : Y.obj (op k))
    (f : (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0}) ⟶ Y) :
    SSet.ihom₀Equiv.symm f ∈
      (SSet.ihomToPullbackFiber (square Y k a)).obj (op ⦋0⦌) ↔
        embedding k ≫ f = SSet.yonedaEquiv.symm a := by
  rw [SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- Insert a padded simplex satisfying the strict restriction equation as a point. -/
def extensionVertex (Y : SSet.{0}) (k : SimplexCategory)
    (a : Y.obj (op k))
    (f : (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0}) ⟶ Y)
    (h : embedding k ≫ f = SSet.yonedaEquiv.symm a) :
    (extensionSpace Y k a).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm f, (extension_mem_iff Y k a f).mpr h⟩

/-- Every padded extension space of a simplex in a Kan simplicial set is Kan. -/
theorem extensionSpace_kan (Y : SSet.{0}) [IsFibrant Y]
    (k : SimplexCategory) (a : Y.obj (op k)) :
    (extensionSpace Y k a).KanComplex := by
  letI : Mono (embedding k) := embedding_mono k
  letI : Fibration (SSet.stdSimplex.isTerminalObj₀.from Y) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (square Y k a)

/-- The literal simplicial fiber of padded extensions is weakly contractible. -/
theorem extensionSpace_toPoint_weak (Y : SSet.{0}) [IsFibrant Y]
    (k : SimplexCategory) (a : Y.obj (op k)) :
    WeakEquivalence
      (SSet.stdSimplex.isTerminalObj₀.from (extensionSpace Y k a)) := by
  letI : Mono (embedding k) := embedding_mono k
  letI : WeakEquivalence (embedding k) := embedding_weak k
  letI : Fibration (SSet.stdSimplex.isTerminalObj₀.from Y) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak (square Y k a)

end

end DaggerModels.PartII.JTOrderedLabelPaddingSpace
