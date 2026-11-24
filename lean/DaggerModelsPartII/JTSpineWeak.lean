import DaggerModelsPartII.JTBarFunctorWeak
import DaggerModelsPartII.SegalLocalizers
import ActualInnerAnodyneRigidification
import ActualDaggerQuillenEquivalenceReduction
import DaggerModels.FreeDaggerPushout
import ActualAntiInnerJoyalMappingWeak

/-!
# The actual free dagger spine in the original weak class

The underlying free dagger map is an inner-left map: lift on each copy of the
explicit vertex pushout and use surjectivity on vertices to glue the lifts.
Ordinary rigidification then gives Hom-wise weak equivalences and a bijection
on objects. This proves the original dagger Joyal weak conclusion for the
literal spine map in every available universe.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels Simplicial
open CategoryTheory.Limits
open DaggerModels.OrdinaryRigidification.DaggerRigidification

universe u

namespace DaggerModels.PartII.JTSpineWeak

noncomputable section

private def opAdjunction : SSet.opFunctor.{u} ⊣ SSet.opFunctor.{u} :=
  SSet.opEquivalence.{u}.toAdjunction

/-- Opposite preserves the exact right lifting class of all inner horns. -/
private theorem innerFibrations_op {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p) :
    DaggerNativeInnerHornFactorization.innerFibrations (SSet.opFunctor.map p) := by
  intro A B i hi
  obtain ⟨a⟩ := hi
  exact (opAdjunction.hasLiftingProperty_iff _ p).1
    (DaggerActualAntiInnerJoyalMappingWeak.opposite_horn_inner a p hp)

/-- Opposite preserves the full native inner-left class, not only its generators. -/
private theorem innerAnodyne_op {A B : SSet.{u}} (f : A ⟶ B)
    (hf : DaggerNativeInnerHornFactorization.innerAnodyne f) :
    DaggerNativeInnerHornFactorization.innerAnodyne (SSet.opFunctor.map f) := by
  intro X Y p hp
  exact (opAdjunction.hasLiftingProperty_iff f p).2
    (hf (SSet.opFunctor.map p) (innerFibrations_op p hp))

/-- A free dagger pushout map is inner-left when both copies are inner-left and
the common vertex map is epi. This is a direct lifting argument. -/
theorem pushoutMap_inner_of_epi {A B : SSet.{u}} (f : A ⟶ B)
    (hf : DaggerNativeInnerHornFactorization.innerAnodyne f)
    (hfop : DaggerNativeInnerHornFactorization.innerAnodyne (SSet.opFunctor.map f))
    [Epi (SSetVertices.map f)] :
    DaggerNativeInnerHornFactorization.innerAnodyne
      (FreeDaggerPushout.mapUnderlying f) := by
  intro X Y p hp
  haveI : HasLiftingProperty f p := hf p hp
  haveI : HasLiftingProperty (SSet.opFunctor.map f) p := hfop p hp
  constructor
  intro u v sq
  let sqL : CommSq (FreeDaggerPushout.inl A ≫ u) f p
      (FreeDaggerPushout.inl B ≫ v) := ⟨by
    simpa only [← Category.assoc, FreeDaggerPushout.inl_mapUnderlying] using
      congrArg (fun k ↦ FreeDaggerPushout.inl A ≫ k) sq.w⟩
  let sqR : CommSq (FreeDaggerPushout.inr A ≫ u) (SSet.opFunctor.map f) p
      (FreeDaggerPushout.inr B ≫ v) := ⟨by
    simpa only [← Category.assoc, FreeDaggerPushout.inr_mapUnderlying] using
      congrArg (fun k ↦ FreeDaggerPushout.inr A ≫ k) sq.w⟩
  have hcompat : SSetVertices.inclusion B ≫ sqL.lift =
      SSetVertices.opInclusion B ≫ sqR.lift := by
    apply (cancel_epi (SSetVertices.map f)).1
    simp only [← Category.assoc, SSetVertices.map_inclusion,
      SSetVertices.map_opInclusion]
    simp only [Category.assoc, sqL.fac_left, sqR.fac_left]
    exact congrArg (fun k ↦ k ≫ u)
      (pushout.condition (f := SSetVertices.inclusion A)
        (g := SSetVertices.opInclusion A))
  have hdescL : FreeDaggerPushout.inl B ≫
      pushout.desc sqL.lift sqR.lift hcompat = sqL.lift := by
    change pushout.inl _ _ ≫ pushout.desc sqL.lift sqR.lift hcompat = sqL.lift
    exact pushout.inl_desc _ _ _
  have hdescR : FreeDaggerPushout.inr B ≫
      pushout.desc sqL.lift sqR.lift hcompat = sqR.lift := by
    change pushout.inr _ _ ≫ pushout.desc sqL.lift sqR.lift hcompat = sqR.lift
    exact pushout.inr_desc _ _ _
  refine ⟨pushout.desc sqL.lift sqR.lift hcompat, ?_, ?_⟩
  · apply pushout.hom_ext
    · change FreeDaggerPushout.inl A ≫
        (FreeDaggerPushout.mapUnderlying f ≫ pushout.desc sqL.lift sqR.lift hcompat) =
          FreeDaggerPushout.inl A ≫ u
      calc
        _ = (FreeDaggerPushout.inl A ≫ FreeDaggerPushout.mapUnderlying f) ≫
            pushout.desc sqL.lift sqR.lift hcompat :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ FreeDaggerPushout.inl B) ≫
            pushout.desc sqL.lift sqR.lift hcompat :=
          congrArg (fun k ↦ k ≫ pushout.desc sqL.lift sqR.lift hcompat)
            (FreeDaggerPushout.inl_mapUnderlying f)
        _ = f ≫ sqL.lift := by
          simpa only [Category.assoc] using
            (congrArg (fun k ↦ f ≫ k) hdescL)
        _ = FreeDaggerPushout.inl A ≫ u := sqL.fac_left
    · change FreeDaggerPushout.inr A ≫
        (FreeDaggerPushout.mapUnderlying f ≫ pushout.desc sqL.lift sqR.lift hcompat) =
          FreeDaggerPushout.inr A ≫ u
      calc
        _ = (FreeDaggerPushout.inr A ≫ FreeDaggerPushout.mapUnderlying f) ≫
            pushout.desc sqL.lift sqR.lift hcompat :=
          (Category.assoc _ _ _).symm
        _ = (SSet.opFunctor.map f ≫ FreeDaggerPushout.inr B) ≫
            pushout.desc sqL.lift sqR.lift hcompat :=
          congrArg (fun k ↦ k ≫ pushout.desc sqL.lift sqR.lift hcompat)
            (FreeDaggerPushout.inr_mapUnderlying f)
        _ = SSet.opFunctor.map f ≫ sqR.lift := by
          simpa only [Category.assoc] using
            (congrArg (fun k ↦ SSet.opFunctor.map f ≫ k) hdescR)
        _ = FreeDaggerPushout.inr A ≫ u := sqR.fac_left
  · apply pushout.hom_ext
    · change FreeDaggerPushout.inl B ≫
        (pushout.desc sqL.lift sqR.lift hcompat ≫ p) =
          FreeDaggerPushout.inl B ≫ v
      calc
        _ = (FreeDaggerPushout.inl B ≫ pushout.desc sqL.lift sqR.lift hcompat) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = sqL.lift ≫ p := congrArg (fun k ↦ k ≫ p) hdescL
        _ = FreeDaggerPushout.inl B ≫ v := sqL.fac_right
    · change FreeDaggerPushout.inr B ≫
        (pushout.desc sqL.lift sqR.lift hcompat ≫ p) =
          FreeDaggerPushout.inr B ≫ v
      calc
        _ = (FreeDaggerPushout.inr B ≫ pushout.desc sqL.lift sqR.lift hcompat) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = sqR.lift ≫ p := congrArg (fun k ↦ k ≫ p) hdescR
        _ = FreeDaggerPushout.inr B ≫ v := sqR.fac_right

private local instance : ModelCategory DaggerSSet.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
private local instance : ModelCategory DaggerSimplicialCat.{u, u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

def spineFree (n : ℕ) :
    freeDagger.obj (DaggerNativeStandardSpineInner.spine.{u} n).toSSet ⟶
      freeDagger.obj (Δ[n] : SSet.{u}) :=
  freeDagger.map (DaggerNativeStandardSpineInner.spine n).ι

/-- The literal standard spine contains every vertex of its ambient simplex. -/
private theorem spine_vertex_surjective (n : ℕ) :
    Function.Surjective
      ((DaggerNativeStandardSpineInner.spine.{u} n).ι.app (Opposite.op ⦋0⦌)) := by
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [DaggerNativeStandardSpineInner.mem_spine_iff]
  have hindex : (Fin.last 0 : Fin 1) = 0 := rfl
  rw [hindex]
  omega

/-- Its common-vertex map in the free dagger pushout is epi. -/
private theorem spine_vertex_epi (n : ℕ) :
    Epi (SSetVertices.map (DaggerNativeStandardSpineInner.spine.{u} n).ι) := by
  rw [NatTrans.epi_iff_epi_app]
  intro q
  exact (epi_iff_surjective _).2 (spine_vertex_surjective n)

/-- The literal free dagger spine map is inner-anodyne after forgetting the dagger. -/
private theorem spineFree_underlying_inner (n : ℕ) :
    DaggerNativeInnerHornFactorization.innerAnodyne (spineFree.{u} n).hom := by
  let i := (DaggerNativeStandardSpineInner.spine.{u} n).ι
  have hi : DaggerNativeInnerHornFactorization.innerAnodyne i :=
    DaggerNativeStandardSpineInner.inclusion_innerAnodyne n
  have hiop : DaggerNativeInnerHornFactorization.innerAnodyne
      (SSet.opFunctor.map i) := innerAnodyne_op i hi
  letI : Epi (SSetVertices.map i) := spine_vertex_epi n
  have hpush : DaggerNativeInnerHornFactorization.innerAnodyne
      (FreeDaggerPushout.mapUnderlying i) := pushoutMap_inner_of_epi i hi hiop
  let e := Arrow.isoOfNatIso FreeDaggerPushout.isoFreeDagger (Arrow.mk i)
  let eUnderlying := DaggerSSet.forget.mapArrow.mapIso e
  haveI : DaggerNativeInnerHornFactorization.innerAnodyne.{u}.RespectsIso := by
    unfold DaggerNativeInnerHornFactorization.innerAnodyne
    infer_instance
  exact (DaggerNativeInnerHornFactorization.innerAnodyne.arrow_mk_iso_iff
    eUnderlying).1 hpush

/-- The exact remaining inner-left fact immediately gives the original dagger Joyal weakness. -/
theorem spineFree_weak_of_underlying_inner (n : ℕ)
    (hinner : DaggerNativeInnerHornFactorization.innerAnodyne (spineFree.{u} n).hom) :
    DaggerJoyalWeakProperties.standardJoyalWeakEquivalences (spineFree.{u} n) := by
  let f := spineFree.{u} n
  let F := daggerRigidification.map f
  have hobj : Function.Surjective F.obj :=
    (DaggerActualInnerAnodyneRigidification.object_bijective f.hom hinner).2
  have hlocal : DaggerGlobalDK.LocalGeometricWeakEquivalence F := by
    intro a b
    exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1
      (DaggerActualInnerAnodyneRigidification.hom_weak f.hom hinner a b)
  have hdk : DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement F :=
    DaggerGlobalDK.daggerDK_of_surjective_local _ F hobj hlocal
  change DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement F
  exact hdk

/-- Literal free dagger completion of every standard spine is an original dagger
Joyal weak equivalence, in every available universe. -/
theorem spineFree_weak (n : ℕ) :
    DaggerJoyalWeakProperties.standardJoyalWeakEquivalences (spineFree.{u} n) :=
  spineFree_weak_of_underlying_inner n (spineFree_underlying_inner n)

/-- The actual bar frame realization sends the literal free dagger spine map
to an original dagger Bergner weak equivalence at universe zero. -/
theorem frameRealization_bar_spine_weak (n : ℕ) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTFrameAdjunction.frameRealization.map
        (JTProjectiveBar.barOnDagger.map (spineFree.{0} n))) := by
  letI : ModelCategory DaggerSSet.{0} := DaggerActualRigidificationQuillen.modelD.{0}
  letI : ModelCategory DaggerSimplicialCat.{0, 0} :=
    DaggerActualRigidificationQuillen.modelG.{0}
  have hf : weakEquivalences DaggerSSet.{0} (spineFree.{0} n) := by
    rw [DaggerActualRigidificationQuillen.source_weak]
    exact spineFree_weak n
  exact JTBarFunctorWeak.frameRealization_bar_map_weak (spineFree.{0} n) hf

end

end DaggerModels.PartII.JTSpineWeak
