import DaggerModelsPartII.JTProjectiveBar
import DaggerModelsPartII.DaggerJTRealization
import DaggerModels.RigidificationVertices
import OriginalActualGlobalWeakPropertiesRecovered

/-!
# Object condition for the actual bar density factor

The actual bar augmentation is surjective at every bisimplicial coefficient.
The literal JT realization coend is therefore surjective on vertices, and
the original rigidification vertex equivalence makes the prescribed
rigidified augmentation surjective on objects. This proves its coherent
unitary object condition without a local weak-equivalence premise.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModels.PartII
open DaggerModels.OrdinaryRigidification
open DaggerUnitaryInvariance

namespace DaggerModels.PartII.JTBarDensityEssentialSurj

open JTProjectiveBar JTReversalInput JTRealizationGenerators
open OrdinaryJTRealization DaggerJTRealization
open OrdinaryRigidification.DaggerRigidification

noncomputable section

/-- The identity-cell section of each row augmentation works in every
vertical simplex degree, including degree zero. -/
private theorem augmentationAt_surjective
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex)
    (q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((augmentationAt P d).app q) := by
  intro y
  let γ := (DaggerOriginalFlagFlankification.nerveDiscreteIso
    (P.obj (op d))).inv.app q y
  let σ := (nerveMap (sectionFunctor P d)).app q γ
  refine ⟨σ, ?_⟩
  change augmentationValue P d (σ.obj 0) = y
  change augmentationValue P d ((sectionFunctor P d).obj (γ.obj 0)) = y
  change augmentationValue P d (identityCell P d (γ.obj 0).as) = y
  rw [augmentationValue_identityCell]
  change ((DaggerOriginalFlagFlankification.discreteConstantChain
    (P.obj (op d)) q y).obj 0).as = y
  rfl

/-- All actual coefficients of the bar augmentation have preimages.
The published zero-degree theorem is a special case. -/
private theorem barAugmentation_coefficient_surjective
    (X : DaggerSSet.{0}) (p : Index) :
    Function.Surjective
      ((ordinaryInput.map (barAugmentation.app X)).app (op p)) := by
  rcases p with ⟨m, k⟩
  change Function.Surjective
    (((barAugmentation.app X).app
      (op (ReverseSimplex.inclusion.obj m))).app (op k))
  exact augmentationAt_surjective (DaggerSSet.toPresheaf.obj X)
    (ReverseSimplex.inclusion.obj m) (op k)

/-- Coend generators transport coefficient surjectivity to vertices of the
literal dagger JT realization. -/
private theorem realization_vertex_surjective
    {W V : SegalLocalizers.ReverseDaggerSpace.{0}} (f : W ⟶ V)
    (hf : ∀ p : Index,
      Function.Surjective ((ordinaryInput.map f).app (op p))) :
    Function.Surjective ((daggerRealization.map f).hom.app (op ⦋0⦌)) := by
  intro y
  obtain ⟨p, w, s, hs⟩ :=
    exists_generator (ordinaryInput.obj V) (op ⦋0⦌) y
  obtain ⟨w₀, hw₀⟩ := hf p w
  refine ⟨(generator (ordinaryInput.obj W) p w₀).app (op ⦋0⦌) s, ?_⟩
  change ((generator (ordinaryInput.obj W) p w₀ ≫
    realization.map (ordinaryInput.map f)).app (op ⦋0⦌)) s = y
  rw [generator_naturality (ordinaryInput.map f) p w₀, hw₀]
  exact hs

/-- The actual bar augmentation is surjective on vertices after the fixed
dagger JT realization. -/
private theorem bar_realization_vertex_surjective (X : DaggerSSet.{0}) :
    Function.Surjective
      ((daggerRealization.map (barAugmentation.app X)).hom.app (op ⦋0⦌)) :=
  realization_vertex_surjective (barAugmentation.app X)
    (barAugmentation_coefficient_surjective X)

/-- Strict surjectivity on objects for the **specified** density factor,
without changing the map or asking for local weakness. -/
theorem rigidified_barAugmentation_object_surjective (X : DaggerSSet.{0}) :
    Function.Surjective
      ((daggerRigidification.map
        (daggerRealization.map (barAugmentation.app X))).obj) := by
  let f := daggerRealization.map (barAugmentation.app X)
  let eS := RigidificationVertices.vertexEquiv
    (daggerRealization.obj (barOnDagger.obj X)).toSSet
  let eT := RigidificationVertices.vertexEquiv
    (daggerRealization.obj (ConstantVertexAdjunction.delta.obj X)).toSSet
  intro y
  obtain ⟨v, rfl⟩ := eT.surjective y
  obtain ⟨w, hw⟩ := bar_realization_vertex_surjective X v
  refine ⟨eS w, ?_⟩
  change (rigidification.map f.hom).obj (eS w) = eT v
  rw [RigidificationVertices.vertexEquiv_naturality f.hom w, hw]

/-- The object condition of the actual middle bar-density factor is
coherent-unitary essential surjectivity for the original replacement. -/
theorem rigidified_barAugmentation_coherentlyEssentiallySurjective
    (X : DaggerSSet.{0}) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective standardReplacement
      (daggerRigidification.map
        (daggerRealization.map (barAugmentation.app X))) := by
  exact DaggerGlobalDK.coherentlyEssentiallySurjective_of_surjective
    standardReplacement _ (rigidified_barAugmentation_object_surjective X)

end

end DaggerModels.PartII.JTBarDensityEssentialSurj
