import DaggerModelsPartII.JTGraphTransportUnder
import DaggerModelsPartII.JTGraphRestrictionNaturality

/-!
# Native restriction as a natural comparison of under-category graph diagrams
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphTransportUnderRestriction

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphRestrictionRaw (predecessor commaRestriction)
open JTGraphTransportNaturality (toComma)
open JTGraphTransportRestriction (transport_restrict transportAlongEq_base transportAlongEq_code)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev F := DecoratedCylinderNecklacePresentation.toTarget W x y
private abbrev TargetComma := CostructuredArrow (F (W := W) (x := x) (y := y)) Q
variable {U : TargetComma (Q := Q)} {S T : NecklaceCode}

private abbrev presentationOf := CostructuredArrow.proj
  (DecoratedCylinderNecklacePresentation.toTarget W x y) Q
private abbrev baseOf := presentationOf (Q := Q) ⋙
  DecoratedCylinderNecklacePresentation.projection W x y ⋙ projection
private abbrev codeOf := presentationOf (Q := Q) ⋙
  BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

private theorem comma_hom_ext {A B : TargetComma (Q := Q)} {f g : A ⟶ B}
    (hbase : baseOf.map f = baseOf.map g) (hcode : codeOf.map f = codeOf.map g) : f = g := by
  apply CostructuredArrow.hom_ext
  apply JTTargetCommaPullback.operator_ext
    (F := DecoratedCylinderNecklacePresentation.underDiagram W x y) (hc := hcode)
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  exact congrArg (fun f ↦ f.op) hbase

private theorem predecessor_cast_base {V : TargetComma (Q := Q)}
    {D G : GraphLift V.left S} (h : D = G) :
    baseOf.map (eqToHom (congrArg (fun H ↦ predecessor H) h)) =
      𝟙 (S, degree V.left) := by
  cases h
  change baseOf.map (𝟙 (predecessor D)) = _
  exact (baseOf (Q := Q)).map_id (predecessor D)

private theorem predecessor_cast_code {V : TargetComma (Q := Q)}
    {D G : GraphLift V.left S} (h : D = G) :
    codeOf.map (eqToHom (congrArg (fun H ↦ predecessor H) h)) = 𝟙 S := by
  cases h
  change codeOf.map (𝟙 (predecessor D)) = _
  exact (codeOf (Q := Q)).map_id (predecessor D)

private theorem predecessor_cast_toComma {V : TargetComma (Q := Q)}
    {D G : GraphLift V.left S} (h : D = G) :
    eqToHom (congrArg (fun H ↦ predecessor H) h) ≫ toComma G = toComma D := by
  cases h
  simp

private theorem liftAt_restrict (E : GraphLift U.left T) (g : S ⟶ T)
    (A : Under U) :
    JTGraphTransportUnder.liftAt (restrict E g) A =
      restrict (JTGraphTransportUnder.liftAt E A) g := by
  change (restrict E g).transport A.hom.left = restrict (E.transport A.hom.left) g
  exact transport_restrict E g A.hom

/-- The native restriction arrow at one object of the under-category. -/
def restrictionAt (E : GraphLift U.left T) (g : S ⟶ T) (A : Under U) :
    (JTGraphTransportUnder.functor (restrict E g)).obj A ⟶
      (JTGraphTransportUnder.functor E).obj A :=
  eqToHom (congrArg (fun H ↦ predecessor H) (liftAt_restrict E g A)) ≫
    commaRestriction (E.transport A.hom.left) g

private theorem restrictionAt_base (E : GraphLift U.left T) (g : S ⟶ T)
    (A : Under U) :
    baseOf.map (restrictionAt E g A) = (g, 𝟙 (degree A.right.left)) := by
  rw [restrictionAt, Functor.map_comp,
    predecessor_cast_base (h := liftAt_restrict E g A)]
  change (𝟙 S ≫ g, 𝟙 (degree A.right.left) ≫ 𝟙 (degree A.right.left)) =
    (g, 𝟙 (degree A.right.left))
  exact Prod.ext (Category.id_comp _) (Category.id_comp _)

private theorem restrictionAt_code (E : GraphLift U.left T) (g : S ⟶ T)
    (A : Under U) : codeOf.map (restrictionAt E g A) = g := by
  rw [restrictionAt, Functor.map_comp,
    predecessor_cast_code (h := liftAt_restrict E g A)]
  change 𝟙 S ≫ g = g
  exact Category.id_comp _

private theorem functor_map_base (D : GraphLift U.left S) {A B : Under U} (a : A ⟶ B) :
    baseOf.map ((JTGraphTransportUnder.functor D).map a) =
      (𝟙 S, degreeOperator a.right.left) := by
  rw [JTGraphTransportUnder.functor_map]
  exact transportAlongEq_base _ _ _ (JTGraphTransportUnder.liftAt_transport D a)

private theorem functor_map_code (D : GraphLift U.left S) {A B : Under U} (a : A ⟶ B) :
    codeOf.map ((JTGraphTransportUnder.functor D).map a) = 𝟙 S := by
  rw [JTGraphTransportUnder.functor_map]
  exact transportAlongEq_code _ _ _ (JTGraphTransportUnder.liftAt_transport D a)

private theorem restrictionAt_natural (E : GraphLift U.left T) (g : S ⟶ T)
    {A B : Under U} (a : A ⟶ B) :
    (JTGraphTransportUnder.functor (restrict E g)).map a ≫ restrictionAt E g B =
      restrictionAt E g A ≫ (JTGraphTransportUnder.functor E).map a := by
  let f := (JTGraphTransportUnder.functor (restrict E g)).map a ≫ restrictionAt E g B
  let k := restrictionAt E g A ≫ (JTGraphTransportUnder.functor E).map a
  have hb : baseOf.map f = baseOf.map k := by
    dsimp only [f, k]
    rw [Functor.map_comp, Functor.map_comp, functor_map_base, restrictionAt_base,
      restrictionAt_base, functor_map_base]
    change (𝟙 S ≫ g, degreeOperator a.right.left ≫ 𝟙 (degree B.right.left)) =
      (g ≫ 𝟙 T, 𝟙 (degree A.right.left) ≫ degreeOperator a.right.left)
    exact Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hc : codeOf.map f = codeOf.map k := by
    dsimp only [f, k]
    rw [Functor.map_comp, Functor.map_comp, functor_map_code, restrictionAt_code,
      restrictionAt_code, functor_map_code]
    change 𝟙 S ≫ g = g ≫ 𝟙 T
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  exact comma_hom_ext hb hc

/-- Restriction of graph lifts is natural over the whole under-category. -/
def restrictionComparison (E : GraphLift U.left T) (g : S ⟶ T) :
    JTGraphTransportUnder.functor (restrict E g) ⟶ JTGraphTransportUnder.functor E :=
  @CategoryTheory.NatTrans.mk _ _ _ _
    (JTGraphTransportUnder.functor (restrict E g)) (JTGraphTransportUnder.functor E)
    (restrictionAt E g) (fun _ _ a ↦ restrictionAt_natural E g a)

set_option maxHeartbeats 50000 in
/-- Every restriction component preserves the map to the original diagram. -/
theorem restrictionAt_comparison (E : GraphLift U.left T)
    (g : S ⟶ T) (A : Under U) :
    restrictionAt E g A ≫ toComma (E.transport A.hom.left) =
      toComma ((restrict E g).transport A.hom.left) := by
  rw [restrictionAt, Category.assoc,
    JTGraphRestrictionNaturality.commaRestriction_natural]
  exact predecessor_cast_toComma (liftAt_restrict E g A)

end

end DaggerModels.PartII.JTGraphTransportUnderRestriction
