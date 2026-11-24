import DaggerModelsPartII.JTGraphTransportNaturality

/-!
# Commutation of transport and native restriction in the actual raw comma
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphTransportRestriction

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphRestrictionRaw (predecessor commaRestriction)
open JTGraphTransportRaw (commaTransport)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev F := DecoratedCylinderNecklacePresentation.toTarget W x y
variable {U V : CostructuredArrow (F (W := W) (x := x) (y := y)) Q}
variable {S T : NecklaceCode}

private abbrev presentationOf := CostructuredArrow.proj
  (DecoratedCylinderNecklacePresentation.toTarget W x y) Q
private abbrev baseOf := presentationOf (Q := Q) ⋙
  DecoratedCylinderNecklacePresentation.projection W x y ⋙ projection
private abbrev codeOf := presentationOf (Q := Q) ⋙
  BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

/-- Transport and restriction commute on the entire graph lift. -/
theorem transport_restrict (E : GraphLift U.left T) (g : S ⟶ T) (a : U ⟶ V) :
    (restrict E g).transport a.left = restrict (E.transport a.left) g := by
  apply GraphLift.ext
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _

/-- Transport to an explicitly identified graph lift in the original target comma. -/
def transportAlongEq (D : GraphLift U.left S) (a : U ⟶ V)
    (G : GraphLift V.left S) (h : D.transport a.left = G) :
    predecessor D ⟶ predecessor G :=
  commaTransport D a ≫ eqToHom (congrArg (fun H ↦ predecessor H) h)

theorem transportAlongEq_base (D : GraphLift U.left S) (a : U ⟶ V)
    (G : GraphLift V.left S) (h : D.transport a.left = G) :
    baseOf.map (transportAlongEq D a G h) = (𝟙 S, degreeOperator a.left) := by
  subst G
  simp only [transportAlongEq, eqToHom_refl, Category.comp_id]
  rfl

theorem transportAlongEq_code (D : GraphLift U.left S) (a : U ⟶ V)
    (G : GraphLift V.left S) (h : D.transport a.left = G) :
    codeOf.map (transportAlongEq D a G h) = 𝟙 S := by
  subst G
  simp only [transportAlongEq, eqToHom_refl, Category.comp_id]
  rfl

/-- The identified transport arrow compares to the original presentation arrow. -/
theorem transportAlongEq_natural (D : GraphLift U.left S) (a : U ⟶ V)
    (G : GraphLift V.left S) (h : D.transport a.left = G) :
    transportAlongEq D a G h ≫ JTGraphTransportNaturality.toComma G =
      JTGraphTransportNaturality.toComma D ≫ a := by
  subst G
  simpa only [transportAlongEq, eqToHom_refl, Category.comp_id] using
    JTGraphTransportNaturality.commaTransport_natural D a

/-- The restriction-transport square commutes in the fixed raw-target comma. -/
theorem commaTransport_restriction_square (E : GraphLift U.left T)
    (g : S ⟶ T) (a : U ⟶ V) :
    transportAlongEq (restrict E g) a (restrict (E.transport a.left) g)
        (transport_restrict E g a) ≫ commaRestriction (E.transport a.left) g =
      commaRestriction E g ≫ commaTransport E a := by
  have hb : baseOf.map
      (transportAlongEq (restrict E g) a (restrict (E.transport a.left) g)
        (transport_restrict E g a) ≫ commaRestriction (E.transport a.left) g) =
      baseOf.map (commaRestriction E g ≫ commaTransport E a) := by
    rw [Functor.map_comp, Functor.map_comp, transportAlongEq_base]
    change (𝟙 S ≫ g, degreeOperator a.left ≫ 𝟙 (degree V.left)) =
      (g ≫ 𝟙 T, 𝟙 (degree U.left) ≫ degreeOperator a.left)
    exact Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hc : codeOf.map
      (transportAlongEq (restrict E g) a (restrict (E.transport a.left) g)
        (transport_restrict E g a) ≫ commaRestriction (E.transport a.left) g) =
      codeOf.map (commaRestriction E g ≫ commaTransport E a) := by
    rw [Functor.map_comp, Functor.map_comp, transportAlongEq_code]
    change 𝟙 S ≫ g = g ≫ 𝟙 T
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  apply CostructuredArrow.hom_ext
  apply JTTargetCommaPullback.operator_ext
    (F := DecoratedCylinderNecklacePresentation.underDiagram W x y) (hc := hc)
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  exact congrArg (fun f ↦ f.op) hb

end

end DaggerModels.PartII.JTGraphTransportRestriction
