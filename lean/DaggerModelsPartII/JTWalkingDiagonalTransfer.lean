import DaggerModelsPartII.JTZeroCoskeletonMapping

/-! Weakness of the actual strict walking-unitary fibers implies weakness of
the corresponding chosen diagonal fibers for complete diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWalkingDiagonalTransfer

open SegalLocalizers JTZeroCoskeletonMapping JTUnitaryDiagonalPath
open OrderedNecklaceVertexPoints
open ChosenHomotopyFiberFunctor DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev K := (Δ[0] : SSet.{0})
private abbrev G := diagramMappingTarget OrderedNecklaceLabelDiagram.boundary
private abbrev F := diagramMappingTarget walkingUnitarySpace.{0}

private theorem boundaryIso_natural {W Z : S} (f : W ⟶ Z) :
    G.map f ≫ (boundaryMappingIso Z).hom = (boundaryMappingIso W).hom ≫ baseMap W f := by
  apply prod.hom_ext
  · rw [Category.assoc (G.map f), boundaryMappingIso_fst,
      Category.assoc (boundaryMappingIso W).hom]
    have hp : baseMap W f ≫ prod.fst =
        prod.fst ≫ diagramMappingPostcomp (daggerSimplex 0) f := prod.map_fst _ _
    calc
      _ = ((boundaryMappingIso W).hom ≫ prod.fst) ≫
          diagramMappingPostcomp (daggerSimplex 0) f := by
        rw [boundaryMappingIso_fst]
        apply NatTrans.ext
        funext q η
        rfl
      _ = (boundaryMappingIso W).hom ≫
          (prod.fst ≫ diagramMappingPostcomp (daggerSimplex 0) f) := Category.assoc _ _ _
      _ = _ := congrArg (fun t ↦ (boundaryMappingIso W).hom ≫ t) hp.symm
  · rw [Category.assoc (G.map f), boundaryMappingIso_snd,
      Category.assoc (boundaryMappingIso W).hom]
    have hp : baseMap W f ≫ prod.snd =
        prod.snd ≫ diagramMappingPostcomp (daggerSimplex 0) f := prod.map_snd _ _
    calc
      _ = ((boundaryMappingIso W).hom ≫ prod.snd) ≫
          diagramMappingPostcomp (daggerSimplex 0) f := by
        rw [boundaryMappingIso_snd]
        apply NatTrans.ext
        funext q η
        rfl
      _ = (boundaryMappingIso W).hom ≫
          (prod.snd ≫ diagramMappingPostcomp (daggerSimplex 0) f) := Category.assoc _ _ _
      _ = _ := congrArg (fun t ↦ (boundaryMappingIso W).hom ≫ t) hp.symm

private theorem boundaryIso_restrict (W : S) :
    restrict.app W ≫ (boundaryMappingIso W).hom = unitaryEndpoints W := by
  apply prod.hom_ext
  · change (diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion W ≫
      (boundaryMappingIso W).hom) ≫ prod.fst = _
    rw [Category.assoc, boundaryMappingIso_fst, ← diagramMappingPrecomp_comp]
    simp only [JTUnitaryEndpointsFibration.inclusion, coprod.inl_desc]
    exact (prod.lift_fst (diagramMappingPrecomp unitaryCompletenessMap W)
      (diagramMappingPrecomp otherEndpoint W)).symm
  · change (diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion W ≫
      (boundaryMappingIso W).hom) ≫ prod.snd = _
    rw [Category.assoc, boundaryMappingIso_snd, ← diagramMappingPrecomp_comp]
    simp only [JTUnitaryEndpointsFibration.inclusion, coprod.inr_desc]
    exact (prod.lift_snd (diagramMappingPrecomp unitaryCompletenessMap W)
      (diagramMappingPrecomp otherEndpoint W)).symm

private theorem boundaryFiber_square (W : S) (b : K ⟶ Zero W ⨯ Zero W)
    (c : K ⟶ G.obj W) (hc : c ≫ (boundaryMappingIso W).hom = b) :
    IsPullback (pullback.fst (restrict.app W) c) (pullback.snd (restrict.app W) c)
      (unitaryEndpoints W) b := by
  have sq : IsPullback (𝟙 (F.obj W)) (restrict.app W) (unitaryEndpoints W)
      (boundaryMappingIso W).hom :=
    IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (boundaryIso_restrict W).symm⟩
  have hp := (IsPullback.of_hasPullback (restrict.app W) c).paste_horiz sq
  rw [Category.comp_id, hc] at hp
  exact hp

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

private theorem chosenUnitaryMap_weak {W Z : S} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : ∀ c : K ⟶ G.obj W, WeakEquivalence (walkingFiberMap f c))
    (b : K ⟶ Zero W ⨯ Zero W) :
    WeakEquivalence
      (chosenMap (unitaryEndpoints W) (unitaryEndpoints Z) (F.map f) (baseMap W f)
        (pointedUnitaryMap W b f).right.w.symm b (b ≫ baseMap W f) rfl) := by
  let c := b ≫ (boundaryMappingIso W).inv
  let d := c ≫ G.map f
  have hc : c ≫ (boundaryMappingIso W).hom = b := by
    simp only [c, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hd : d ≫ (boundaryMappingIso Z).hom = b ≫ baseMap W f := by
    rw [show d = c ≫ G.map f from rfl, Category.assoc, boundaryIso_natural,
      ← Category.assoc, hc]
  let sw := boundaryFiber_square W b c hc
  let sz := boundaryFiber_square Z (b ≫ baseMap W f) d hd
  let a := fibreMap (unitaryEndpoints W) (unitaryEndpoints Z) (F.map f) (baseMap W f)
    (pointedUnitaryMap W b f).right.w.symm b (b ≫ baseMap W f) rfl
  have h : walkingFiberMap f c ≫ sz.isoPullback.hom = sw.isoPullback.hom ≫ a := by
    apply pullback.hom_ext
    · rw [Category.assoc (walkingFiberMap f c), Category.assoc sw.isoPullback.hom,
        sz.isoPullback_hom_fst, show
        a ≫ pullback.fst (unitaryEndpoints Z) (b ≫ baseMap W f) =
          pullback.fst (unitaryEndpoints W) b ≫ F.map f from fibreMap_fst _ _ _ _ _ _ _ _,
        ← Category.assoc sw.isoPullback.hom, sw.isoPullback_hom_fst]
      exact fibreMap_fst _ _ _ _ _ _ _ _
    · rw [Category.assoc (walkingFiberMap f c), Category.assoc sw.isoPullback.hom,
        sz.isoPullback_hom_snd, show
        a ≫ pullback.snd (unitaryEndpoints Z) (b ≫ baseMap W f) =
          pullback.snd (unitaryEndpoints W) b from fibreMap_snd _ _ _ _ _ _ _ _,
        sw.isoPullback_hom_snd]
      exact fibreMap_snd _ _ _ _ _ _ _ _
  letI : WeakEquivalence (walkingFiberMap f c) := hW c
  letI : WeakEquivalence a := weakEquivalence_of_precomp_of_fac h.symm
  letI : Fibration (unitaryEndpoints W) :=
    JTUnitaryEndpointsFibration.unitaryEndpoints_fibration W inferInstance
  letI : Fibration (unitaryEndpoints Z) :=
    JTUnitaryEndpointsFibration.unitaryEndpoints_fibration Z inferInstance
  letI := ChosenHomotopyFiberTriangle.inclusion_weak (unitaryEndpoints W) b
  letI := ChosenHomotopyFiberTriangle.inclusion_weak (unitaryEndpoints Z) (b ≫ baseMap W f)
  exact weakEquivalence_of_precomp_of_fac (inclusion_chosenMap
    (unitaryEndpoints W) (unitaryEndpoints Z) (F.map f) (baseMap W f)
    (pointedUnitaryMap W b f).right.w.symm b (b ≫ baseMap W f) rfl)

/-- The natural chosen diagonal-fiber map is weak for complete diagrams
when all of the actual strict walking-unitary fibers are weak. -/
theorem diagonalMap_weak {W Z : S} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : unitaryCompletenessCondition W) (hZ : unitaryCompletenessCondition Z)
    (h : ∀ c : K ⟶ G.obj W, WeakEquivalence (walkingFiberMap f c))
    (b : K ⟶ Zero W ⨯ Zero W) :
    WeakEquivalence
      (chosenMap (diagonal W) (diagonal Z) (diagramMappingPostcomp (daggerSimplex 0) f)
        (baseMap W f) (pointedDiagonalMap W b f).right.w.symm b (b ≫ baseMap W f) rfl) := by
  let Q := (weakEquivalences SSet.{0}).Q
  letI : IsIso (Q.map (diagonalToUnitary W b)) := Localization.inverts Q _ _
    ((weakEquivalence_iff _).mp (diagonalToUnitary_weak W hW b))
  letI : IsIso (Q.map (diagonalToUnitary Z (b ≫ baseMap W f))) := Localization.inverts Q _ _
    ((weakEquivalence_iff _).mp (diagonalToUnitary_weak Z hZ _))
  haveI : IsIso ((localizedFiberFunctor K).map (pointedUnitaryMap W b f)) :=
    Localization.inverts Q _ _ ((weakEquivalence_iff _).mp (chosenUnitaryMap_weak f h b))
  apply (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q _).mpr
  change IsIso ((localizedFiberFunctor K).map (pointedDiagonalMap W b f))
  apply (isIso_comp_right_iff _ (Q.map (diagonalToUnitary Z (b ≫ baseMap W f)))).mp
  rw [← diagonalToUnitary_localized_natural W b f]
  infer_instance

end

end DaggerModels.PartII.JTWalkingDiagonalTransfer
