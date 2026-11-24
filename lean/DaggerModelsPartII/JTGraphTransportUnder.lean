import DaggerModelsPartII.JTGraphTransportRestriction

/-!
# Compatible graph predecessors over an entire under-category
-/

set_option autoImplicit false
set_option maxHeartbeats 20000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphTransportUnder

open JTProjectiveOrderedFiberComparison
open JTGraphLiftTransport
open JTGraphRestrictionRaw (predecessor)
open JTGraphTransportNaturality (toComma)
open JTGraphTransportRestriction (transportAlongEq transportAlongEq_base transportAlongEq_code
  transportAlongEq_natural)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
private abbrev TargetComma (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable {U V : TargetComma Q} {S : NecklaceCode}

private abbrev presentationOf := CostructuredArrow.proj
  (DecoratedCylinderNecklacePresentation.toTarget W x y) Q
private abbrev baseOf := presentationOf (Q := Q) ⋙
  DecoratedCylinderNecklacePresentation.projection W x y ⋙ projection
private abbrev codeOf := presentationOf (Q := Q) ⋙
  BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

private theorem comma_hom_ext {A B : TargetComma Q} {f g : A ⟶ B}
    (hbase : baseOf.map f = baseOf.map g) (hcode : codeOf.map f = codeOf.map g) : f = g := by
  apply CostructuredArrow.hom_ext
  apply JTTargetCommaPullback.operator_ext
    (F := DecoratedCylinderNecklacePresentation.underDiagram W x y) (hc := hcode)
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  exact congrArg (fun f ↦ f.op) hbase

private theorem degree_id (A : TargetComma Q) :
    degreeOperator (𝟙 A : A ⟶ A).left = 𝟙 (degree A.left) :=
  congrArg Prod.snd ((baseOf (Q := Q)).map_id A)

private theorem degree_comp {A B C : TargetComma Q} (a : A ⟶ B) (b : B ⟶ C) :
    degreeOperator (a ≫ b).left = degreeOperator a.left ≫ degreeOperator b.left :=
  congrArg Prod.snd ((baseOf (Q := Q)).map_comp a b)

variable (D : GraphLift U.left S)

/-- Transport a lift along the specified arrow out of the cone apex. -/
def liftAt (A : Under U) : GraphLift A.right.left S := D.transport A.hom.left

/-- The original cone equation identifies successive graph transports. -/
theorem liftAt_transport {A B : Under U} (a : A ⟶ B) :
    (liftAt D A).transport a.right.left = liftAt D B := by
  let p := presentationOf (Q := Q)
  have h : p.map A.hom ≫ p.map a.right = p.map B.hom := by
    rw [← Functor.map_comp, Under.w a]
  change (D.transport (p.map A.hom)).transport (p.map a.right) = D.transport (p.map B.hom)
  exact (D.transport_comp _ _).trans
    (congrArg (fun f : p.obj U ⟶ p.obj B.right ↦ D.transport f) h)

private abbrev graphAt (A : Under U) : TargetComma Q := predecessor (liftAt D A)

private def arrowAt {A B : Under U} (a : A ⟶ B) : graphAt D A ⟶ graphAt D B :=
  transportAlongEq (liftAt D A) a.right (liftAt D B) (liftAt_transport D a)

private theorem arrowAt_base {A B : Under U} (a : A ⟶ B) :
    baseOf.map (arrowAt D a) = (𝟙 S, degreeOperator a.right.left) :=
  transportAlongEq_base _ _ _ _

private theorem arrowAt_code {A B : Under U} (a : A ⟶ B) :
    codeOf.map (arrowAt D a) = 𝟙 S :=
  transportAlongEq_code _ _ _ _

private theorem arrowAt_id (A : Under U) : arrowAt D (𝟙 A) = 𝟙 (graphAt D A) := by
  refine comma_hom_ext (f := arrowAt D (𝟙 A)) (g := 𝟙 (graphAt D A)) ?_ ?_
  · have h : (𝟙 S, degreeOperator (𝟙 A.right : A.right ⟶ A.right).left) =
        (𝟙 S, 𝟙 (degree A.right.left)) := Prod.ext rfl (degree_id A.right)
    exact (arrowAt_base D (𝟙 A)).trans
      (h.trans ((baseOf (Q := Q)).map_id (graphAt D A)).symm)
  · exact (arrowAt_code D (𝟙 A)).trans ((codeOf (Q := Q)).map_id (graphAt D A)).symm

private theorem arrowAt_comp {A B C : Under U} (a : A ⟶ B) (b : B ⟶ C) :
    arrowAt D (a ≫ b) = arrowAt D a ≫ arrowAt D b := by
  refine comma_hom_ext (f := arrowAt D (a ≫ b)) (g := arrowAt D a ≫ arrowAt D b) ?_ ?_
  · calc
      _ = (𝟙 S, degreeOperator ((a ≫ b).right).left) := arrowAt_base D (a ≫ b)
      _ = (𝟙 S ≫ 𝟙 S, degreeOperator a.right.left ≫ degreeOperator b.right.left) :=
        Prod.ext (Category.id_comp _).symm (degree_comp a.right b.right)
      _ = baseOf.map (arrowAt D a) ≫ baseOf.map (arrowAt D b) := by
        exact (congrArg₂ (fun (f : (S, degree A.right.left) ⟶ (S, degree B.right.left))
          (g : (S, degree B.right.left) ⟶ (S, degree C.right.left)) ↦ f ≫ g)
          (arrowAt_base D a) (arrowAt_base D b)).symm
      _ = _ := ((baseOf (Q := Q)).map_comp (arrowAt D a) (arrowAt D b)).symm
  · calc
      _ = 𝟙 S := arrowAt_code D (a ≫ b)
      _ = 𝟙 S ≫ 𝟙 S := (Category.id_comp _).symm
      _ = codeOf.map (arrowAt D a) ≫ codeOf.map (arrowAt D b) :=
        (congrArg₂ (fun (f g : S ⟶ S) ↦ f ≫ g) (arrowAt_code D a) (arrowAt_code D b)).symm
      _ = _ := ((codeOf (Q := Q)).map_comp (arrowAt D a) (arrowAt D b)).symm

/-- Every arrow out of the same initial comma object has a compatible graph
predecessor with the same native source code. -/
def functor : Under U ⥤ TargetComma Q :=
  @CategoryTheory.Functor.mk (Under U) _ (TargetComma Q) _ (graphAt D)
    (@arrowAt W x y Q U S D) (@arrowAt_id W x y Q U S D) (@arrowAt_comp W x y Q U S D)

theorem functor_obj (A : Under U) : (functor D).obj A = predecessor (liftAt D A) := rfl

theorem functor_map {A B : Under U} (a : A ⟶ B) :
    (functor D).map a =
      transportAlongEq (liftAt D A) a.right (liftAt D B) (liftAt_transport D a) := rfl

/-- The graph predecessors compare naturally to the original diagram. -/
def comparison : functor D ⟶ Under.forget U where
  app A := toComma (liftAt D A)
  naturality {A B} a :=
    transportAlongEq_natural (liftAt D A) a.right (liftAt D B) (liftAt_transport D a)

/-- Pull the natural comparison back to an original diagram with a chosen cone. -/
def coneComparison {I : Type} [SmallCategory I] (G : I ⥤ TargetComma Q)
    (η : (Functor.const I).obj U ⟶ G) : Under.lift G η ⋙ functor D ⟶ G where
  app i := toComma (liftAt D ((Under.lift G η).obj i))
  naturality {_ _} f := (comparison D).naturality ((Under.lift G η).map f)

/-- The cone construction retains the exact composite native collapse on each leg. -/
theorem coneCollapse {I : Type} [SmallCategory I] (G : I ⥤ TargetComma Q)
    (η : (Functor.const I).obj U ⟶ G) (i : I) :
    (liftAt D ((Under.lift G η).obj i)).collapse =
      D.collapse ≫ (η.app i).left.fiber.left := rfl

end

end DaggerModels.PartII.JTGraphTransportUnder
