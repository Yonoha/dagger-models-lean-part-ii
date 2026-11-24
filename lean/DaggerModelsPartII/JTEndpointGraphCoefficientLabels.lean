import DaggerModelsPartII.JTEndpointGraphCoefficientFamilies
import DaggerModelsPartII.JTMixedGraphOrderedLabelTransport

/-! Simultaneous horizontal, coefficient, and time maps of the actual enlarged labels. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTEndpointGraphCoefficientLabels

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientChoices JTEndpointGraphCoefficientFamilies
open OrderedNecklaceVertexPoints
open scoped Prod

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

variable {W : Source} {d : ℕ}
variable {q : std.obj ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

abbrev nativeCodes : Index P hx hy ⥤ NecklaceCode := base P hx hy ⋙ codes P
abbrev time : Index P hx hy ⥤ SimplexCategory :=
  semiTime P hx hy ⋙ SemiSimplexCategory.toSimplexCategory

abbrev decoratedIndices := (nativeCodes P hx hy).prod' (enlarged P hx hy)

private abbrev orderedPoint (U : Index P hx hy) :=
  JTMixedGraphOrderedLabel.orderedPoint (families P hx hy U)

private theorem middle_map {U V : Index P hx hy} (f : U ⟶ V) :
    std.map (JTCommonCoefficientParameter.base (coeff P hx hy U) (timeDegree P hx hy U)) ≫
        parentRow P (child P hx hy U) =
      std.map ((enlarged P hx hy).map f) ≫
        (std.map (JTCommonCoefficientParameter.base (coeff P hx hy V) (timeDegree P hx hy V)) ≫
          parentRow P (child P hx hy V)) ≫
        (rows W).map (((base P hx hy).map f).left.unop.base.unop.left.1.op) := by
  let u := (base P hx hy).map f
  let g := (coefficients P).map u
  let j := (semiTime P hx hy).map f
  have h := JTCommonCoefficientParameter.map_base g.left (Over.w g)
    (SemiSimplexCategory.toSimplexCategory.map j) (SemiSimplexCategory.homEquiv j).injective
  have he : (enlarged P hx hy).map f ≫
      JTCommonCoefficientParameter.base (coeff P hx hy V) (timeDegree P hx hy V) =
      JTCommonCoefficientParameter.base (coeff P hx hy U) (timeDegree P hx hy U) := h
  let b := JTCommonCoefficientParameter.base (coeff P hx hy U) (timeDegree P hx hy U)
  let b' := JTCommonCoefficientParameter.base (coeff P hx hy V) (timeDegree P hx hy V)
  let r := (rows W).map u.left.unop.base.unop.left.1.op
  let a := (enlarged P hx hy).map f
  calc
    _ = std.map b ≫ (parentRow P (child P hx hy V) ≫ r) :=
      congrArg (std.map b ≫ ·) (parentRow_natural P u).symm
    _ = (std.map a ≫ std.map b') ≫ (parentRow P (child P hx hy V) ≫ r) := by
      rw [← std.map_comp, he]
    _ = _ := by
      simp only [Category.assoc]
      rfl

private theorem orderedPoint_map {U V : Index P hx hy} (f : U ⟶ V) :
    (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)).map
      (((decoratedIndices P hx hy).map f).op) (orderedPoint P hx hy V) =
      orderedPoint P hx hy U := by
  let u := (base P hx hy).map f
  let a : ⦋dim P hx hy U⦌ ⟶ ⦋dim P hx hy V⦌ := u.left.unop.base.unop.left.1
  let g := (enlarged P hx hy).map f
  have h := choice_maps P hx hy f
  exact (JTMixedGraphOrderedLabelTransport.orderedPoint_mixed_reindex_joint a
    u.left.unop.base.unop.left.2.1 u.left.unop.base.unop.left.2.2 g
    (families P hx hy U) (families P hx hy V) h.1 (middle_map P hx hy f) h.2).symm

/-- Every exact enlarged family gives its actual decorated label and its complete operators. -/
def labelIndex : Index P hx hy ⥤ OrderedLabelElements.Index W (boundaryPoint W x y) where
  obj U := op ⟨op ((decoratedIndices P hx hy).obj U), orderedPoint P hx hy U⟩
  map f := Quiver.Hom.op ⟨((decoratedIndices P hx hy).map f).op, orderedPoint_map P hx hy f⟩
  map_id U := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((decoratedIndices P hx hy).map_id U)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((decoratedIndices P hx hy).map_comp f g)

end
end DaggerModels.PartII.JTEndpointGraphCoefficientLabels
