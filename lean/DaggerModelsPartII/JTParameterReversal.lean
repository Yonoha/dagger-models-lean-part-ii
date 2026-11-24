import DaggerModelsPartII.JTReversalIndex
import DaggerModelsPartII.GroupoidSimplexReversal
import OriginalStandardSimplexReversal
import DaggerModels.FreeDaggerPushout

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTParameterReversal

open OrdinaryJTRealization JTReversalIndex GroupoidSimplexReversal

noncomputable section

example (X Y : SSet.{0}) : (X ⊗ Y).op = X.op ⊗ Y.op := rfl

example {X X' Y Y' : SSet.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.opFunctor.map (f ⊗ₘ g) =
      SSet.opFunctor.map f ⊗ₘ SSet.opFunctor.map g := rfl

example (X Y : SSet.{0}) :
    SSet.opFunctorCompOpFunctorIso.hom.app (X ⊗ Y) =
      (SSet.opFunctorCompOpFunctorIso.hom.app X) ⊗ₘ
        (SSet.opFunctorCompOpFunctorIso.hom.app Y) := rfl

/-- Reversing the simplex coordinate commutes with every ordinary simplex
operator; the source and target simplices are the literal standard simplices. -/
theorem standardSimplexReversal_natural {m n : SimplexCategory} (f : m ⟶ n) :
    SSet.stdSimplex.map f ≫
        (DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso n.len).symm.hom =
      (DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso m.len).symm.hom ≫
        SSet.opFunctor.map (SSet.stdSimplex.map (SimplexCategory.rev.map f)) := by
  ext q s
  apply SSet.opObjEquiv.injective
  apply SSet.stdSimplex.objEquiv.injective
  change SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s ≫ f) =
    SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s) ≫
      SimplexCategory.rev.map f
  exact Functor.map_comp _ _ _

/-- The two exact factors of the JT parameter reverse independently. -/
def tReversalComponent (p : Index) :
    tFunctor.obj p ≅ (tFunctor.obj (indexReversal.obj p)).op :=
  tensorIso
    (DaggerOriginalStandardSimplexReversal.standardSimplexReversalIso p.1.len).symm
    (GroupoidSimplexReversal.daggerParameter.obj p.2).daggerIso

/-- Opposite simplicial sets distribute strictly over the chosen pointwise
Cartesian product, including its action on maps. -/
private theorem op_tensorHom {X X' Y Y' : SSet.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.opFunctor.map (f ⊗ₘ g) =
      SSet.opFunctor.map f ⊗ₘ SSet.opFunctor.map g := rfl

/-- Naturality of the two factor reversals, before packaging as a NatIso. -/
private theorem tReversalComponent_natural {p q : Index} (f : p ⟶ q) :
    tFunctor.map f ≫ (tReversalComponent q).hom =
      (tReversalComponent p).hom ≫
        SSet.opFunctor.map (tFunctor.map (indexReversal.map f)) := by
  rw [tFunctor_map, indexReversal_map, tFunctor_map]
  simp only [tReversalComponent, tensorIso_hom, op_tensorHom,
    tensorHom_comp_tensorHom]
  exact congrArg₂ (fun a b => a ⊗ₘ b)
    (standardSimplexReversal_natural f.1)
    ((GroupoidSimplexReversal.daggerParameter.map f.2).comm)

/-- Natural reversal of the literal JT parameter, before any realization or
coend quotient is formed. -/
def tReversalIso :
    tFunctor ≅ indexReversal ⋙ tFunctor ⋙ SSet.opFunctor :=
  NatIso.ofComponents tReversalComponent (by
    intro p q f
    exact tReversalComponent_natural f)

/-- The retained dagger parameter has exactly the original ordinary nerve. -/
theorem parameter_underlying (k : SimplexCategory) :
    (daggerParameter.obj k).toSSet = GroupoidSimplex.parameter.obj k :=
  congrArg (fun F : SimplexCategory ⥤ SSet.{0} => F.obj k) underlying_eq

/-- The two parameter factors reverse an ordinary simplex operator and a
groupoid chain independently. -/
theorem tReversal_app (p : Index) (n : SimplexCategory)
    (α : (SSet.stdSimplex.obj p.1).obj (op n))
    (ξ : (GroupoidSimplex.parameter.obj p.2).obj (op n)) :
    SSet.opObjEquiv ((tReversalIso.hom.app p).app (op n) (α, ξ)) =
      (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α)),
        (GroupoidSimplexReversal.daggerParameter.obj p.2).daggerSimplex (n := n.len)
          ((parameter_underlying p.2).symm ▸ ξ)) :=
  rfl

/-- Reversing both factors of the JT parameter twice is the identity. -/
theorem tReversal_twice (p : Index) :
    tReversalIso.hom.app p ≫
      SSet.opFunctor.map (tReversalIso.hom.app (indexReversal.obj p)) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (tFunctor.obj p) =
        𝟙 (tFunctor.obj p) := by
  ext n x
  rcases x with ⟨α, ξ⟩
  apply Prod.ext
  · apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map
      (SSet.stdSimplex.objEquiv α)) = SSet.stdSimplex.objEquiv α
    exact DaggerOriginalStandardSimplexReversal.reverse_operator_twice _
  · exact (daggerParameter.obj p.2).involutive n.unop.len ξ

end
end DaggerModels.PartII.JTParameterReversal
