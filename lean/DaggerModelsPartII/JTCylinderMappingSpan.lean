import DaggerModelsPartII.JTCylinderCEComparison
import DaggerModelsPartII.JTConeMappingPresentation
import DaggerModelsPartII.JTCEPlainMappingTarget
import DaggerModelsPartII.JTChosenRightMappingUnit

/-!
# The literal CE, cylinder and original cone Hom span

Precomposition with the two actual under-boundary frame maps gives
Hom(CE,X) -> Hom(Cyl,X) <- Hom(Cone,X), naturally in the actual target.
The chosen unit's cone Hom map is calibrated to its original native
right-cone mapping map and is Kan weak. No weakness of the frame span
maps or of the chosen unit's CE Hom map is asserted here.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTCylinderMappingSpan

noncomputable section

/-- Actual postcomposition on the literal under-boundary Hom simplicial set. -/
def postcompose (F : SimplexCategory ⥤ Under JTXiEndpointCollapse.boundary)
    {X Y : Under JTXiEndpointCollapse.boundary} (f : X ⟶ Y) :
    EndpointMappingFiber.mapping (Z := X) F ⟶
      EndpointMappingFiber.mapping (Z := Y) F :=
  Functor.whiskerLeft F.op (yoneda.map f)

/-- Literal under-boundary Hom from the standard-simplex reduced cylinder. -/
def cylinderHom (X : Under JTXiEndpointCollapse.boundary) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := X) JTCylinderFrame.under

/-- Literal under-boundary Hom from the original ordinary right cone. -/
def coneHom (X : Under JTXiEndpointCollapse.boundary) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := X) JTCylinderConeComparison.coneUnder

/-- The actual CE-to-cylinder Hom restriction is precomposition with
the reduced-cylinder map of the original groupoid completion unit. -/
def fromCE (X : Under JTXiEndpointCollapse.boundary) :
    JTCEPlainMappingTarget.plainCEHom X ⟶ cylinderHom X :=
  EndpointMappingFiber.precomp (Z := X) JTCylinderCEComparison.underComparison

/-- The actual cone-to-cylinder Hom restriction uses the original
product-order cylinder-to-cone map under the same two endpoints. -/
def fromCone (X : Under JTXiEndpointCollapse.boundary) :
    coneHom X ⟶ cylinderHom X :=
  EndpointMappingFiber.precomp (Z := X) JTCylinderConeComparison.comparisonUnder

/-- On each CE simplex, restriction preserves the exact underlying map. -/
theorem fromCE_app_right (X : Under JTXiEndpointCollapse.boundary)
    (q : SimplexCategoryᵒᵖ)
    (g : (Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary).obj
      q.unop ⟶ X) :
    ((fromCE X).app q g).right =
      JTCylinderCEComparison.valueComparison.app q.unop ≫ g.right := rfl

/-- On each original cone simplex, restriction preserves the exact cone map. -/
theorem fromCone_app_right (X : Under JTXiEndpointCollapse.boundary)
    (q : SimplexCategoryᵒᵖ)
    (g : JTCylinderConeComparison.coneUnder.obj q.unop ⟶ X) :
    ((fromCone X).app q g).right =
      JTCylinderConeComparison.comparison.app q.unop ≫ g.right := rfl

/-- CE restriction is natural in the literal under-boundary target map. -/
theorem fromCE_naturality {X Y : Under JTXiEndpointCollapse.boundary} (f : X ⟶ Y) :
    JTCEPlainMappingTarget.plainCEHomMap f ≫ fromCE Y =
      fromCE X ≫ postcompose JTCylinderFrame.under f := by
  apply NatTrans.ext
  funext q g
  change JTCylinderCEComparison.underComparison.app q.unop ≫ (g ≫ f) =
    (JTCylinderCEComparison.underComparison.app q.unop ≫ g) ≫ f
  exact (Category.assoc _ _ _).symm

/-- Cone restriction is natural in the same literal target map. -/
theorem fromCone_naturality {X Y : Under JTXiEndpointCollapse.boundary} (f : X ⟶ Y) :
    postcompose JTCylinderConeComparison.coneUnder f ≫ fromCone Y =
      fromCone X ≫ postcompose JTCylinderFrame.under f := by
  apply NatTrans.ext
  funext q g
  change JTCylinderConeComparison.comparisonUnder.app q.unop ≫ (g ≫ f) =
    (JTCylinderConeComparison.comparisonUnder.app q.unop ≫ g) ≫ f
  exact (Category.assoc _ _ _).symm

open JTStrictificationCoefficients JTChosenOrdinaryAdjoint JTChosenCEUnitBoundary

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- On the exact chosen ordinary unit, the cone Hom map is the SAME native
right-cone mapping map after the literal endpoint-preserving isomorphisms. -/
theorem etaCone_naturality (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    postcompose JTCylinderConeComparison.coneUnder (etaUnder W x y) ≫
        (JTConeMappingPresentation.coneMappingIso (chosenNerve W)
          ((etaOrdinary W).app (op ⦋0⦌) x)
          ((etaOrdinary W).app (op ⦋0⦌) y)).hom =
      (JTConeMappingPresentation.coneMappingIso (chosenT W).toSSet x y).hom ≫
        DaggerActualGeneralRightConeMapping.map (etaOrdinary W) x y := by
  apply NatTrans.ext
  funext q g
  apply Subtype.ext
  rfl

/-- The literal chosen unit on original cone Hom simplicial sets is Kan
weak, without assuming whole ordinary Joyal weakness of that unit. -/
theorem etaCone_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence
      (postcompose JTCylinderConeComparison.coneUnder (etaUnder W x y)) := by
  let e : Arrow.mk
      (postcompose JTCylinderConeComparison.coneUnder (etaUnder W x y)) ≅
      Arrow.mk (DaggerActualGeneralRightConeMapping.map (etaOrdinary W) x y) :=
    Arrow.isoMk
      (JTConeMappingPresentation.coneMappingIso (chosenT W).toSSet x y)
      (JTConeMappingPresentation.coneMappingIso (chosenNerve W)
        ((etaOrdinary W).app (op ⦋0⦌) x)
        ((etaOrdinary W).app (op ⦋0⦌) y))
      (etaCone_naturality W x y).symm
  apply (weakEquivalence_iff _).2
  exact ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).2
    ((weakEquivalence_iff _).1
      (JTChosenRightMappingUnit.etaOrdinary_rightMapping_weak W x y))

end

end DaggerModels.PartII.JTCylinderMappingSpan
