import DaggerModelsPartII.JTPrismMixedCoefficient

/-! The full used coefficient support is functorial on an entire mixed prism diagram. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTFullPrismSupportedDiagram

open JTPrismRectangle (sample supportMap supportMap_inclusion supportedParameter
  supportedParameter_factor supportedParameter_natural)
open JTRowGraphParameterSupport (inclusion inclusion_mono supportOrdinal)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I]

/-- The whole prism diagram, with independently varying horizontal and time degrees. -/
abbrev prisms (D T : I ⥤ SimplexCategory) :=
  ((D ⋙ std).prod' (T ⋙ J)) ⋙ MonoidalCategory.tensor SSet.{0}

variable {D T k : I ⥤ SimplexCategory}
variable (p : prisms D T ⟶ k ⋙ J)

private abbrev sampleParameter (x : I) := sample (D.obj x) (T.obj x) ≫ p.app x
private abbrev ι (x : I) := inclusion (sampleParameter p x)

private def operator {x y : I} (f : x ⟶ y) :
    supportOrdinal (sampleParameter p x) ⟶ supportOrdinal (sampleParameter p y) :=
  supportMap (p.app x) (p.app y) ((prisms D T).map f) (k.map f) (p.naturality f)

private theorem operator_fac {x y : I} (f : x ⟶ y) :
    operator p f ≫ ι p y = ι p x ≫ k.map f :=
  supportMap_inclusion (p.app x) (p.app y) ((prisms D T).map f) (k.map f) (p.naturality f)

/-- On every mixed arrow use precisely the images of all the used vertices. -/
def support : I ⥤ SimplexCategory where
  obj x := supportOrdinal (sampleParameter p x)
  map f := operator p f
  map_id x := by
    have : Mono (ι p x) := inclusion_mono (sampleParameter p x)
    apply (cancel_mono (ι p x)).mp
    change operator p (𝟙 x) ≫ ι p x = 𝟙 _ ≫ ι p x
    rw [operator_fac, k.map_id, Category.comp_id, Category.id_comp]
  map_comp {x y z} f g := by
    have : Mono (ι p z) := inclusion_mono (sampleParameter p z)
    apply (cancel_mono (ι p z)).mp
    change operator p (f ≫ g) ≫ ι p z = (operator p f ≫ operator p g) ≫ ι p z
    rw [operator_fac, Category.assoc, operator_fac, ← Category.assoc,
      operator_fac, Category.assoc, k.map_comp]

/-- The varying used supports include naturally in the original coefficient degrees. -/
def incl : support p ⟶ k where
  app := ι p
  naturality _ _ f := operator_fac p f

/-- The full parameter lands in its actual used support, with every operator retained. -/
def parameter : prisms D T ⟶ support p ⋙ J where
  app x := supportedParameter (p.app x)
  naturality x y f :=
    supportedParameter_natural (p.app x) (p.app y) ((prisms D T).map f) (k.map f)
      (p.naturality f)

/-- The supported parameter recovers the original full parameter exactly. -/
theorem parameter_fac : parameter p ≫ Functor.whiskerRight (incl p) J = p := by
  apply NatTrans.ext
  funext x
  exact supportedParameter_factor (p.app x)

section Coefficients

open OrdinaryJTRealization
open JTPrismRectangle (prismValue usedCoefficient usedCoefficient_mixed)

variable {W : BiPresheaf}
variable (w : ∀ x : I, W.obj (op (D.obj x, k.obj x)))
variable (r : prisms D T ⟶ (Functor.const I).obj (realization.obj W))
variable (hr : ∀ x, prismValue (w x) (p.app x) = r.app x)

/-- The product of the actual horizontal degree and the actual coefficient support. -/
abbrev degrees := D.prod' (support p)

include hr in
/-- The full-support coefficient equation holds over the actual arrow of the degree diagram. -/
theorem coefficient_natural {x y : I} (f : x ⟶ y) :
    usedCoefficient (w x) (p.app x) =
      W.map ((degrees p).map f).op (usedCoefficient (w y) (p.app y)) := by
  have hp : (std.map (D.map f) ⊗ₘ J.map (T.map f)) ≫ p.app y = p.app x ≫ J.map (k.map f) :=
    p.naturality f
  apply usedCoefficient_mixed (D.map f) (T.map f) (k.map f) _ _ _ _ hp
  rw [hr x, hr y]
  exact ((r.naturality f).trans (Category.comp_id _)).symm

/-- The recovered coefficients form a natural section of the bisimplicial
presheaf pulled back to their actual degrees. -/
def coefficientSection :
    (Functor.const Iᵒᵖ).obj (PUnit : Type) ⟶ (degrees p).op ⋙ W where
  app x := fun _ ↦ usedCoefficient (w x.unop) (p.app x.unop)
  naturality x y f := by
    funext u
    exact coefficient_natural p w r hr f.unop

end Coefficients
end
end DaggerModels.PartII.JTFullPrismSupportedDiagram
