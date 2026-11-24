import DaggerModels.FreeDaggerCofibration
import NativeStandardSpineGeometry
import NativeOrdinaryDaggerNerveLift
import OriginalWalkingIsoIntegerObstruction

/-!
# The literal reversal Segal localizers of Part II

This file formalizes `h1.not.discrete` and `h1.not.S`. It uses the actual
reversal presheaf of Part I, not the tagged reversal category.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

/-- Dagger simplicial spaces indexed by the actual reversal simplex category. -/
abbrev ReverseDaggerSpace := ReverseSimplexᵒᵖ ⥤ SSet.{u}

/-- Postcompose the Part I dagger presheaf with the discrete simplicial-set embedding. -/
def discreteDagger : DaggerSSet.{u} ⥤ ReverseDaggerSpace.{u} :=
  DaggerSSet.toPresheaf ⋙
    (Functor.whiskeringRight ReverseSimplexᵒᵖ (Type u) SSet.{u}).obj
      (SimplicialObject.const (Type u))

/-- The representable dagger simplex, before applying the discrete embedding. -/
def freeSimplex (n : ℕ) : DaggerSSet.{u} :=
  freeDagger.obj Δ[n]

/-- The discrete free dagger simplex `Δⁿ_rev`. -/
def daggerSimplex (n : ℕ) : ReverseDaggerSpace.{u} :=
  discreteDagger.obj (freeSimplex n)

/-- The ordinary standard spine, with its literal subcomplex inclusion. -/
def ordinarySpine (n : ℕ) : SSet.{u} :=
  (DaggerNativeStandardSpineInner.spine n).toSSet

/-- The spine used here is exactly the union of successive edges and vertices. -/
theorem ordinarySpine_eq_vertices_sup_edges (n : ℕ) :
    DaggerNativeStandardSpineInner.spine.{u} n =
      DaggerNativeStandardSpineGeometry.vertices n ⊔
        DaggerNativeStandardSpineGeometry.edges n :=
  DaggerNativeStandardSpineGeometry.spine_eq_vertices_sup_edges n

/-- The discrete free dagger spine `Sp[n]_rev`. -/
def daggerSpine (n : ℕ) : ReverseDaggerSpace.{u} :=
  discreteDagger.obj (freeDagger.obj (ordinarySpine n))

/-- Discretization preserves monomorphisms from the Part I dagger presheaf. -/
theorem discreteDagger_map_mono {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (discreteDagger.map f) := by
  letI : DaggerSSet.toPresheaf.{u}.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction
      daggerSSetEquivalencePresheaf.{u}.symm.toAdjunction
  have h : Mono (DaggerSSet.toPresheaf.map f) := inferInstance
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [NatTrans.mono_iff_mono_app]
  intro n
  change Mono ((DaggerSSet.toPresheaf.map f).app a)
  exact (NatTrans.mono_iff_mono_app _).mp h a

/-- The Segal map induced by the standard spine inclusion. -/
def segalMap (n : ℕ) : daggerSpine.{u} n ⟶ daggerSimplex.{u} n :=
  discreteDagger.map (freeDagger.map (DaggerNativeStandardSpineInner.spine n).ι)

open DaggerModels.OriginalWalkingIsoIntegerObstruction

/-- Every Segal localizer is a levelwise monomorphism. -/
theorem segalMap_mono (n : ℕ) : Mono (segalMap.{u} n) := by
  have h := freeDagger_map_isFreeCofibration (DaggerNativeStandardSpineInner.spine.{u} n).ι
  letI : Mono (freeDagger.map (DaggerNativeStandardSpineInner.spine.{u} n).ι) := h.1
  exact discreteDagger_map_mono _

/-- The unique arrows of the ordinary walking isomorphism are unitary. -/
private instance walkingIsoDagger : DaggerCategory walkingIso.{u} where
  dagger _ := ⟨⟨⟩⟩
  dagger_involutive _ := rfl
  dagger_id _ := rfl
  dagger_comp _ _ := rfl

/-- The generating arrow is unitary for the canonical dagger on the walking isomorphism. -/
theorem walkingForward_unitary : IsUnitary walkingForward.{u} := ⟨rfl, rfl⟩

/-- The strict dagger nerve of the walking unitary isomorphism. -/
def walkingUnitaryNerve : DaggerSSet.{u} :=
  DaggerNativeOrdinaryDaggerNerveLift.daggerNerve walkingIso.{u}

/-- The ordinary presentation agrees with the dagger coherent nerve of the
constant enrichment of the walking unitary. -/
def walkingUnitaryCoherentNerveIso :
    OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj
      (DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{u}) ≅ walkingUnitaryNerve.{u} :=
  DaggerNativeOrdinaryDaggerNerveLift.comparisonIso walkingIso.{u}

/-- The selected zero vertex of the walking unitary nerve. -/
def zeroVertex : (walkingUnitaryNerve.{u}).toSSet _⦋0⦌ :=
  ComposableArrows.mk₀ walkingZero.{u}

/-- Adjunction transpose of the zero vertex, `ε₀ : Δ⁰_† ⟶ E_†`. -/
def unitaryVertex : freeSimplex.{u} 0 ⟶ walkingUnitaryNerve.{u} :=
  (freeDaggerAdjunction.{u}.homEquiv (Δ[0] : SSet.{u}) walkingUnitaryNerve.{u}).symm
    (SSet.yonedaEquiv.symm zeroVertex)

/-- `E_rev = δ(E_†)`. -/
def walkingUnitarySpace : ReverseDaggerSpace.{u} :=
  discreteDagger.obj walkingUnitaryNerve.{u}

/-- The unitary completeness map `δ(ε₀) : Δ⁰_rev ⟶ E_rev`. -/
def unitaryCompletenessMap : daggerSimplex.{u} 0 ⟶ walkingUnitarySpace.{u} :=
  discreteDagger.map unitaryVertex

/-- A small index for all Segal maps in dimensions at least two and one completeness map. -/
abbrev LocalizerIndex : Type := {n : ℕ // 2 ≤ n} ⊕ Unit

/-- The indexed family of literal maps in `S_rev`. -/
def localizerMap : LocalizerIndex → (Σ A B : ReverseDaggerSpace.{u}, A ⟶ B) :=
  fun i ↦ match i with
  | .inl n => ⟨daggerSpine n, daggerSimplex n, segalMap n⟩
  | .inr _ => ⟨daggerSimplex 0, walkingUnitarySpace, unitaryCompletenessMap⟩

/-- Each higher Segal map occurs in the family at its own dimension. -/
theorem localizerMap_segal (n : ℕ) (hn : 2 ≤ n) :
    localizerMap.{u} (.inl ⟨n, hn⟩) =
      ⟨daggerSpine n, daggerSimplex n, segalMap n⟩ := rfl

/-- The one completeness map occurs in the family. -/
theorem localizerMap_completeness :
    localizerMap.{u} (.inr ()) =
      ⟨daggerSimplex 0, walkingUnitarySpace, unitaryCompletenessMap⟩ := rfl

/-- The small family `S_rev` of Part II, retaining its source and target data. -/
def S_rev : Set (Σ A B : ReverseDaggerSpace.{u}, A ⟶ B) :=
  Set.range localizerMap

/-- The same indexed family as a morphism property on reversal dagger spaces. -/
def localizingFamily : MorphismProperty ReverseDaggerSpace.{u} :=
  MorphismProperty.ofHoms (fun i : LocalizerIndex ↦ (localizerMap i).2.2)

instance localizingFamily_small : MorphismProperty.IsSmall.{u} localizingFamily.{u} :=
  MorphismProperty.isSmall_ofHoms _

end

end DaggerModels.PartII.SegalLocalizers
