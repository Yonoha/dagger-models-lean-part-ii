import DaggerModelsPartII.JTCoendMate

/-!
# Represented-generator calibration of the actual coend mate

The canonical represented generators and the two actual adjunctions identify
the right mate with precomposition by the original full-index frame map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTCoendMateFormula

open DaggerJTAdjunction JTCoendMate
open OrdinaryRigidification.DaggerRigidification

noncomputable section

local instance : HasColimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasColimits

/-- The original source object represented by the pair of simplex indices. -/
def representedInput (p : DaggerIndex) : SegalLocalizers.ReverseDaggerSpace.{0} :=
  sourceEquivalence.inverse.obj (uliftYoneda.{0}.obj p)

/-- The canonical inclusion of the frame into the realization of its generator. -/
def frameGenerator (p : DaggerIndex) :
    JTFrameAdjunction.frameParameter.obj p ⟶
      JTFrameAdjunction.frameRealization.obj (representedInput p) :=
  (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫
    JTFrameAdjunction.presheafRealization.map
      (sourceEquivalence.counitIso.inv.app (uliftYoneda.{0}.obj p))

/-- The actual capital comparison restricts to the original lower-case frame comparison. -/
theorem frameGenerator_comparison (p : DaggerIndex) :
    frameGenerator p ≫ JTCoendComparison.comparison.app (representedInput p) =
      JTCoendComparison.parameterComparison.app p := by
  dsimp only [frameGenerator, JTCoendComparison.comparison, Functor.whiskerLeft_app,
    NatTrans.comp_app]
  rw [Category.assoc, JTCoendComparison.presheafComparison.naturality_assoc,
    ← Category.assoc, JTCoendComparison.presheafComparison_fac_app_eq]
  change JTCoendComparison.parameterComparison.app p ≫
    daggerRigidification.map
      (DaggerJTRealization.daggerRealization.map
        (sourceEquivalence.inverse.map
          (sourceEquivalence.counitIso.inv.app (uliftYoneda.{0}.obj p)))) ≫
      daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map
          (sourceEquivalence.unitIso.inv.app (representedInput p))) = _
  have ht : sourceEquivalence.inverse.map
      (sourceEquivalence.counitIso.inv.app (uliftYoneda.{0}.obj p)) ≫
        sourceEquivalence.unitIso.inv.app (representedInput p) =
          𝟙 (representedInput p) :=
    sourceEquivalence.inverse_counitInv_comp (uliftYoneda.{0}.obj p)
  rw [← daggerRigidification.map_comp,
    ← DaggerJTRealization.daggerRealization.map_comp,
    ht]
  have hi := congrArg
    (fun a : DaggerJTRealization.daggerRealization.obj (representedInput p) ⟶
        DaggerJTRealization.daggerRealization.obj (representedInput p) ↦
      daggerRigidification.map a)
    (DaggerJTRealization.daggerRealization.map_id (representedInput p))
  have hi' := hi.trans
    (daggerRigidification.map_id
      (DaggerJTRealization.daggerRealization.obj (representedInput p)))
  exact (congrArg (fun a ↦ JTCoendComparison.parameterComparison.app p ≫ a) hi').trans
    (Category.comp_id _)

/-- Conjugation is compatible with the actual adjunction bijections. -/
theorem rightMate_homEquiv (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (C : DaggerSimplicialCat.{0, 0})
    (f : daggerRigidification.obj (DaggerJTRealization.daggerRealization.obj W) ⟶ C) :
    JTFrameAdjunction.adjunction.homEquiv W C
        (JTCoendComparison.comparison.app W ≫ f) =
      compositeAdjunction.homEquiv W C f ≫ rightMate.app C := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← unit_rightMate]
  simpa only [Category.assoc] using
    congrArg (fun g ↦ compositeAdjunction.unit.app W ≫ g)
      (rightMate.naturality f).symm

/-- A value of a presheaf in the original source is equivalently a map from its generator. -/
def representedEvaluation (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (p : DaggerIndex) :
    (representedInput p ⟶ W) ≃ (W.obj (op p.1)).obj (op p.2) :=
  (sourceEquivalence.symm.toAdjunction.homEquiv (uliftYoneda.{0}.obj p) W).trans
    uliftYonedaEquiv

/-- Evaluation of a represented map commutes with every actual source morphism. -/
theorem representedEvaluation_naturality
    {W V : SegalLocalizers.ReverseDaggerSpace.{0}} (p : DaggerIndex)
    (f : representedInput p ⟶ W) (g : W ⟶ V) :
    representedEvaluation V p (f ≫ g) =
      (g.app (op p.1)).app (op p.2) (representedEvaluation W p f) := by
  have h := congrArg
    (fun t : uliftYoneda.{0}.obj p ⟶ sourceEquivalence.functor.obj V ↦
      uliftYonedaEquiv t)
    (sourceEquivalence.symm.toAdjunction.homEquiv_naturality_right f g)
  exact h

instance frameGenerator_isIso (p : DaggerIndex) : IsIso (frameGenerator p) := by
  dsimp [frameGenerator]
  infer_instance

/-- The canonical represented frame isomorphism, with the actual inclusion as its hom. -/
def frameGeneratorIso (p : DaggerIndex) :
    JTFrameAdjunction.frameParameter.obj p ≅
      JTFrameAdjunction.frameRealization.obj (representedInput p) :=
  asIso (frameGenerator p)

/-- The actual composite adjunction gives the manuscript's represented Hom identification. -/
def compositeGeneratorEquiv (C : DaggerSimplicialCat.{0, 0}) (p : DaggerIndex) :
    (RigidifiedJTFrames.Xi.obj p ⟶ C) ≃
      ((compositeNerve.obj C).obj (op p.1)).obj (op p.2) :=
  (compositeAdjunction.homEquiv (representedInput p) C).trans
    (representedEvaluation (compositeNerve.obj C) p)

/-- The frame adjunction identifies a Hom from the same actual represented frame. -/
def frameGeneratorEquiv (C : DaggerSimplicialCat.{0, 0}) (p : DaggerIndex) :
    (JTFrameAdjunction.frameParameter.obj p ⟶ C) ≃
      ((JTFrameAdjunction.frameNerve.obj C).obj (op p.1)).obj (op p.2) :=
  (Iso.homCongr (frameGeneratorIso p) (Iso.refl C)).trans
    ((JTFrameAdjunction.adjunction.homEquiv (representedInput p) C).trans
      (representedEvaluation (JTFrameAdjunction.frameNerve.obj C) p))

/-- Under the canonical adjunction identifications, the actual right mate
is precomposition by the original full-index frame comparison. -/
theorem rightMate_generator (C : DaggerSimplicialCat.{0, 0}) (p : DaggerIndex)
    (f : RigidifiedJTFrames.Xi.obj p ⟶ C) :
    ((rightMate.app C).app (op p.1)).app (op p.2) (compositeGeneratorEquiv C p f) =
      frameGeneratorEquiv C p (JTCoendComparison.parameterComparison.app p ≫ f) := by
  change _ = representedEvaluation _ p
    (JTFrameAdjunction.adjunction.homEquiv _ C
      ((frameGeneratorIso p).inv ≫ (JTCoendComparison.parameterComparison.app p ≫ f)))
  rw [← frameGenerator_comparison]
  change _ = representedEvaluation _ p
    (JTFrameAdjunction.adjunction.homEquiv _ C
      ((frameGeneratorIso p).inv ≫
        ((frameGeneratorIso p).hom ≫ JTCoendComparison.comparison.app (representedInput p))
          ≫ f))
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg
    (representedEvaluation (JTFrameAdjunction.frameNerve.obj C) p)
    (rightMate_homEquiv (representedInput p) C f)
  exact (representedEvaluation_naturality p
    (compositeAdjunction.homEquiv (representedInput p) C f)
    (rightMate.app C)).symm.trans h.symm

/-- The bidegree formula uses the literal original comparison component. -/
theorem rightMate_bidegree (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) (k : SimplexCategory)
    (f : RigidifiedJTFrames.Xi.obj (m, k) ⟶ C) :
    ((rightMate.app C).app (op m)).app (op k) (compositeGeneratorEquiv C (m, k) f) =
      frameGeneratorEquiv C (m, k)
        ((JTRelativeReedyFrame.comparison.app k).app m ≫ f) := by
  simpa only [JTCoendComparison.parameterComparison_app] using
    rightMate_generator C (m, k) f

/-- At degree zero the represented-generator mate is the identity under the
two canonical Hom identifications, before the separate identification with `A`. -/
theorem rightMate_bidegree_zero (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) (f : RigidifiedJTFrames.Xi.obj (m, ⦋0⦌) ⟶ C) :
    ((rightMate.app C).app (op m)).app (op ⦋0⦌)
        (compositeGeneratorEquiv C (m, ⦋0⦌) f) =
      frameGeneratorEquiv C (m, ⦋0⦌) f := by
  simpa only [JTCoendComparison.parameterComparison_zero, Category.id_comp] using
    rightMate_generator C (m, ⦋0⦌) f

end

end DaggerModels.PartII.JTCoendMateFormula
