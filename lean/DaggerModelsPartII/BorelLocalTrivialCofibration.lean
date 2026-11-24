import DaggerModelsPartII.EquivariantDiagramMapping
import DaggerModelsPartII.LocalizedMappingCorner
import DaggerModelsPartII.ParametrizedInitialLifting
import OriginalEC2SimplicialProjectiveCofibrancy

/-!
# The Borel image of a localized trivial cofibration

The scalar category is the already constructed native projective model on
`C₂`-simplicial sets. Its cofibrant parameter is the actual simplicial `EC₂`.
No model structure on actions of the localized diagram category is assumed.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory

universe u

namespace DaggerModels.PartII

open EquivariantDiagramMapping

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- Tensoring with a cofibrant native scalar action and taking strict orbits
sends a localized trivial cofibration of underlying diagrams to one. -/
theorem orbitTensor_localTrivialCofibration
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (hi : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations φ.hom)
    (hwi : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences φ.hom)
    (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations (((orbitTensorBifunctor C).map φ).app E) ∧
      (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences
          (((orbitTensorBifunctor C).map φ).app E) := by
  letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.localizedModelCategory C I s hs
  change trivialCofibrations (C ⥤ SSet.{u}) _
  rw [← llp_eq_of_wfs (trivialCofibrations (C ⥤ SSet.{u})) (fibrations (C ⥤ SSet.{u}))]
  intro Y Z p hp
  let corner := Functor.PullbackObjObj.ofHasPullback (mappingActionBifunctor C) φ p
  have hc := InjectiveKanDiagram.localized_mappingCorner_trivialFibration
    C I s hs φ.hom p hi hwi hp (underlyingMappingCorner C φ p corner)
  rw [underlyingMappingCorner_π] at hc
  haveI : Fibration corner.π.hom := (mem_trivialFibrations_iff _).mp hc |>.1
  haveI : WeakEquivalence corner.π.hom := (mem_trivialFibrations_iff _).mp hc |>.2
  haveI : Fibration corner.π :=
    (DaggerOriginalSimplicialActionModelCategory.fibration_iff_underlying _).mpr inferInstance
  haveI : WeakEquivalence corner.π :=
    (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).mpr
      inferInstance
  have hV : IsInitial (((orbitTensorBifunctor C).obj V).obj
      (⊥_ (Action SSet.{u} C2.{u}))) := by
    letI : PreservesColimits (orbitTensor C V) :=
      (orbitTensorAdjunction C V).leftAdjoint_preservesColimits
    exact initialIsInitial.isInitialObj (orbitTensor C V) _
  have hW : IsInitial (((orbitTensorBifunctor C).obj W).obj
      (⊥_ (Action SSet.{u} C2.{u}))) := by
    letI : PreservesColimits (orbitTensor C W) :=
      (orbitTensorAdjunction C W).leftAdjoint_preservesColimits
    exact initialIsInitial.isInitialObj (orbitTensor C W) _
  apply (parametrized_initial_lifting_iff (orbitTensorBifunctor C)
    (mappingActionBifunctor C) φ E hV hW (orbitTensorParametrizedAdjunction C)
    p corner).mpr
  haveI : Cofibration (initial.to E) := (isCofibrant_iff E).mp inferInstance
  infer_instance

/-- The manuscript's actual simplicial `EC₂` is an admissible cofibrant
parameter for the localized Borel construction. -/
theorem actualEC2_orbitTensor_localTrivialCofibration
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ k, Mono (s k).hom)
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (hi : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations φ.hom)
    (hwi : (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences φ.hom) :
    (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithCofibrations.cofibrations
          (((orbitTensorBifunctor C).map φ).app simplicialAction) ∧
      (InjectiveKanDiagram.localizedModelCategory
      C I s hs).categoryWithWeakEquivalences.weakEquivalences
          (((orbitTensorBifunctor C).map φ).app simplicialAction) :=
  orbitTensor_localTrivialCofibration C I s hs φ hi hwi simplicialAction

end

end DaggerModels.PartII
