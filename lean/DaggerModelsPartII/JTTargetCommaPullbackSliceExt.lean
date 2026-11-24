import DaggerModelsPartII.JTTargetCommaPullbackSliceProjection

/-!
# Identifying a slice arrow by its two original operators
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaPullbackSliceExt

open JTTargetCommaPullback (Presentation diagram fromObj equivalence)
open JTTargetCommaPullbackSliceProjection (comparisonIso comparison_arrow pair_fromObj)
open BoundaryNecklaceComma (fiberDiagram sourceCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- Remember the two original operators of the decorated base arrow. -/
abbrev decoratedProjection :=
  Grothendieck.forget (fiberDiagram (diagram W x y Q)) ⋙
    OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

/-- Equality transports at the endpoints do not change the projected arrow
once their endpoint identifications are used. -/
private theorem map_cast_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A A' B B' : C} (hA : A = A') (hB : B = B') (f : A' ⟶ B') :
    HEq (F.map (eqToHom hA ≫ f ≫ eqToHom hB.symm)) (F.map f) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem projected_ext {P P' : Presentation W x y Q} {f g : P ⟶ P'}
    (hb : (decoratedProjection W x y Q).map f = (decoratedProjection W x y Q).map g)
    (hc : (sourceCode (diagram W x y Q)).map f = (sourceCode (diagram W x y Q)).map g) :
    f = g := by
  apply JTTargetCommaPullback.operator_ext (hc := hc)
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun t ↦ t.op) hb

/-- After identifying the explicit slice objects with the original graph
objects, a comparison arrow is determined by its two projected operators. -/
theorem conjugate_eq_of_operators {P P' : Presentation W x y Q}
    {A A' : CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q}
    (h : fromObj W x y Q P = A) (h' : fromObj W x y Q P' = A')
    (f : P ⟶ P') (g : A ⟶ A')
    (hb : HEq ((decoratedProjection W x y Q).map f)
      ((decoratedProjection W x y Q).map ((equivalence W x y Q).functor.map g)))
    (hc : HEq ((sourceCode (diagram W x y Q)).map f)
      ((sourceCode (diagram W x y Q)).map ((equivalence W x y Q).functor.map g))) :
    ((comparisonIso W x y Q P).trans (eqToIso h)).inv ≫
        (equivalence W x y Q).inverse.map f ≫
          ((comparisonIso W x y Q P').trans (eqToIso h')).hom = g := by
  subst A A'
  simp only [eqToIso_refl, Iso.trans_refl]
  apply (equivalence W x y Q).functor.map_injective
  rw [comparison_arrow]
  apply projected_ext W x y Q
  · exact eq_of_heq ((map_cast_heq (decoratedProjection W x y Q)
      (pair_fromObj W x y Q P) (pair_fromObj W x y Q P') f).trans hb)
  · exact eq_of_heq ((map_cast_heq (sourceCode (diagram W x y Q))
      (pair_fromObj W x y Q P) (pair_fromObj W x y Q P') f).trans hc)

end

end DaggerModels.PartII.JTTargetCommaPullbackSliceExt
