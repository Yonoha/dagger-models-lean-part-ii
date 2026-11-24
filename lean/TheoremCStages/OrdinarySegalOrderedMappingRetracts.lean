import OrdinarySegalOrderedMappingEndpointTransport
import OrdinarySegalOrderedMappingIdentity
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Arrow retracts on the literal ordered Segal mapping fibers

An arrow retract of whole ordinary simplicial-space maps induces a retract
of their exact ordered pullback-fiber maps. The four legs retain the
endpoint equalities supplied by the original arrow retract.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory MorphismProperty Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalOrderedMappingRetracts

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (mappingFiber)
open OrdinarySegalOrderedMappingMaps (mappingMap)
open OrdinarySegalOrderedMappingEndpointTransport
  (transport transport_comp transport_map transport_refl)
open OrdinarySegalOrderedMappingEndpointTransport (map_of_eq)
open OrdinarySegalOrderedMappingComposition (mappingMap_comp)
open OrdinarySegalOrderedMappingIdentity (mappingMap_id)

noncomputable section

abbrev vertexMap {W V : Space} (f : W ⟶ V)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (V.obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
  ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x

@[simp] theorem vertexMap_comp {W V U : Space} (f : W ⟶ V) (g : V ⟶ U)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap (f ≫ g) x = vertexMap g (vertexMap f x) := rfl

@[simp] theorem vertexMap_id (W : Space)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap (𝟙 W) x = x := rfl

variable {W V W' V' : Space} {f : W ⟶ V} {g : W' ⟶ V'}
  (h : RetractArrow f g)

/-- The source-vertex split supplied by the original arrow retract. -/
def sourceSplit (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap h.r.left (vertexMap h.i.left x) = x := by
  simpa only [vertexMap_comp, vertexMap_id] using
    congrArg (fun k : W ⟶ W ↦ vertexMap k x) h.retract_left

/-- The target-vertex split supplied by the original arrow retract. -/
def targetSplit (z : (V.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap h.r.right (vertexMap h.i.right z) = z := by
  simpa only [vertexMap_comp, vertexMap_id] using
    congrArg (fun k : V ⟶ V ↦ vertexMap k z) h.retract_right

/-- Endpoint equality in the inclusion square. -/
def inclusionEndpoint (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap g (vertexMap h.i.left x) =
      vertexMap h.i.right (vertexMap f x) := by
  simpa only [vertexMap_comp] using
    congrArg (fun k : W ⟶ V' ↦ vertexMap k x) h.i_w

/-- Endpoint equality in the retraction square. -/
def retractionEndpoint (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    vertexMap h.r.right (vertexMap g (vertexMap h.i.left x)) =
      vertexMap f x := by
  have e : vertexMap f (vertexMap h.r.left (vertexMap h.i.left x)) =
      vertexMap h.r.right (vertexMap g (vertexMap h.i.left x)) := by
    simpa only [vertexMap_comp] using
      congrArg (fun k : W' ⟶ V ↦ vertexMap k (vertexMap h.i.left x)) h.r_w
  exact e.symm.trans (congrArg (vertexMap f) (sourceSplit h x))

/-- Inclusion of the original ordered source mapping fiber. -/
abbrev inclusionSource
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :=
  mappingMap h.i.left x y

/-- Inclusion of the original ordered target mapping fiber, with both endpoints cast. -/
def inclusionTarget
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber V (vertexMap f x) (vertexMap f y) ⟶
      mappingFiber V' (vertexMap g (vertexMap h.i.left x))
        (vertexMap g (vertexMap h.i.left y)) :=
  mappingMap h.i.right (vertexMap f x) (vertexMap f y) ≫
    transport V' (inclusionEndpoint h x).symm (inclusionEndpoint h y).symm

/-- Retraction of the ordered source mapping fiber to its original endpoints. -/
def retractionSource
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W' (vertexMap h.i.left x) (vertexMap h.i.left y) ⟶
      mappingFiber W x y :=
  mappingMap h.r.left (vertexMap h.i.left x) (vertexMap h.i.left y) ≫
    transport W (sourceSplit h x) (sourceSplit h y)

/-- Retraction of the ordered target mapping fiber to its original endpoints. -/
def retractionTarget
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber V' (vertexMap g (vertexMap h.i.left x))
      (vertexMap g (vertexMap h.i.left y)) ⟶
      mappingFiber V (vertexMap f x) (vertexMap f y) :=
  mappingMap h.r.right (vertexMap g (vertexMap h.i.left x))
      (vertexMap g (vertexMap h.i.left y)) ≫
    transport V (retractionEndpoint h x) (retractionEndpoint h y)

theorem inclusion_square (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    inclusionSource h x y ≫
        mappingMap g (vertexMap h.i.left x) (vertexMap h.i.left y) =
      mappingMap f x y ≫ inclusionTarget h x y := by
  have e := congrArg (fun t ↦ t ≫
    transport V' (inclusionEndpoint h x).symm (inclusionEndpoint h y).symm)
    (map_of_eq h.i_w x y)
  simpa only [← mappingMap_comp, Category.assoc, transport_comp,
    transport_refl, Category.comp_id, inclusionSource, inclusionTarget] using e

theorem retraction_square (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    retractionSource h x y ≫ mappingMap f x y =
      mappingMap g (vertexMap h.i.left x) (vertexMap h.i.left y) ≫
        retractionTarget h x y := by
  have e := congrArg (fun t ↦ t ≫
    transport V (retractionEndpoint h x) (retractionEndpoint h y))
    (map_of_eq h.r_w (vertexMap h.i.left x) (vertexMap h.i.left y))
  rw [retractionSource, Category.assoc, transport_map]
  simpa only [← mappingMap_comp, Category.assoc, transport_comp,
    retractionTarget] using e

theorem source_retract (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    inclusionSource h x y ≫ retractionSource h x y = 𝟙 _ := by
  calc
    _ = mappingMap (𝟙 W) x y := by
      simpa only [← mappingMap_comp, Category.assoc,
        inclusionSource, retractionSource] using map_of_eq h.retract_left x y
    _ = 𝟙 _ := mappingMap_id W x y

theorem target_retract (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    inclusionTarget h x y ≫ retractionTarget h x y = 𝟙 _ := by
  have t :
      transport V
        (congrArg (vertexMap h.r.right) (inclusionEndpoint h x).symm)
        (congrArg (vertexMap h.r.right) (inclusionEndpoint h y).symm) ≫
        transport V (retractionEndpoint h x) (retractionEndpoint h y) =
          transport V (targetSplit h (vertexMap f x))
            (targetSplit h (vertexMap f y)) :=
    transport_comp V _ _ _ _
  calc
    _ = mappingMap h.i.right (vertexMap f x) (vertexMap f y) ≫
        mappingMap h.r.right (vertexMap h.i.right (vertexMap f x))
          (vertexMap h.i.right (vertexMap f y)) ≫
        transport V (targetSplit h (vertexMap f x))
          (targetSplit h (vertexMap f y)) := by
      rw [inclusionTarget, retractionTarget, Category.assoc,
        ← Category.assoc (transport V' _ _) (mappingMap h.r.right _ _) _, transport_map]
      simpa only [Category.assoc] using congrArg
        (fun v ↦ mappingMap h.i.right (vertexMap f x) (vertexMap f y) ≫
          mappingMap h.r.right (vertexMap h.i.right (vertexMap f x))
            (vertexMap h.i.right (vertexMap f y)) ≫ v) t
    _ = 𝟙 _ := by
      calc
        _ = mappingMap (𝟙 V) (vertexMap f x) (vertexMap f y) := by
          simpa only [← mappingMap_comp, Category.assoc] using
            map_of_eq h.retract_right (vertexMap f x) (vertexMap f y)
        _ = 𝟙 _ := mappingMap_id V (vertexMap f x) (vertexMap f y)

/-- The actual ordered mapping-fiber arrow is a retract of the larger arrow. -/
def mappingRetract (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    RetractArrow (mappingMap f x y)
      (mappingMap g (vertexMap h.i.left x) (vertexMap h.i.left y)) where
  i := Arrow.homMk (inclusionSource h x y) (inclusionTarget h x y)
    (inclusion_square h x y)
  r := Arrow.homMk (retractionSource h x y) (retractionTarget h x y)
    (retraction_square h x y)
  retract := Arrow.hom_ext _ _ (source_retract h x y) (target_retract h x y)

/-- A property of all literal ordered mapping-fiber maps. -/
def orderedMappingProperty (P : MorphismProperty SSet.{0}) : MorphismProperty Space :=
  fun W _ f ↦ ∀ x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌), P (mappingMap f x y)

instance orderedMappingProperty_isStableUnderRetracts (P : MorphismProperty SSet.{0})
    [P.IsStableUnderRetracts] :
    (orderedMappingProperty P).IsStableUnderRetracts where
  of_retract h hg := by
    intro x y
    exact P.of_retract (mappingRetract h x y)
      (hg (vertexMap h.i.left x) (vertexMap h.i.left y))

#print axioms sourceSplit
#print axioms targetSplit
#print axioms inclusionEndpoint
#print axioms retractionEndpoint
#print axioms inclusion_square
#print axioms retraction_square
#print axioms source_retract
#print axioms target_retract
#print axioms mappingRetract
#print axioms orderedMappingProperty_isStableUnderRetracts

end
end DaggerModels.PartII.OrdinarySegalOrderedMappingRetracts
