import OrdinaryFreeRestrictionEnriched

/-!
# Naturality of the arbitrary-source free-restriction mapping comparison

The checked enriched comparison is natural under every original horizontal
simplicial-set map. In particular, its spine and boundary instances keep
the literal ordinary source and the literal free dagger target in the same
reversal diagram `W`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels

namespace DaggerModels.PartII.OrdinaryFreeRestrictionCalibration

noncomputable section

private abbrev Source := OrdinaryCSSLocalization.Space
private abbrev Target := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev inclusion := ReverseSimplex.inclusion
private abbrev extension := extendIndexLeft.{0, 0} inclusion
private abbrev restriction := restrictIndex.{0, 0} inclusion
private abbrev discrete := OrdinaryCSSLocalization.discrete
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}

/-- The generic enriched left-Kan mapping comparison respects
precomposition in the entire original ordinary source diagram. -/
theorem mappingRestrictionIso_natural {A B : Source} (i : A ⟶ B)
    (W : Target) :
    diagramMappingPrecomp i (restriction.obj W) ≫
        (OrdinaryFreeRestrictionEnriched.mappingRestrictionIso A W).hom =
      (OrdinaryFreeRestrictionEnriched.mappingRestrictionIso B W).hom ≫
        diagramMappingPrecomp (extension.map i) W := by
  apply NatTrans.ext
  funext n η
  let K := SSet.stdSimplex.obj n.unop
  let T := simplicialPresheafProductRight.{0, 0}
  let a := extendIndexLeftAdjunction.{0, 0} inclusion
  let e := extendIndexLeft_productRight.{0, 0} inclusion K
  change e.inv.app A ≫
      (a.homEquiv ((T SimplexCategory K).obj A) W).symm
        ((T SimplexCategory K).map i ≫ η) =
    (T ReverseSimplex K).map (extension.map i) ≫
      (e.inv.app B ≫
        (a.homEquiv ((T SimplexCategory K).obj B) W).symm η)
  rw [a.homEquiv_naturality_left_symm]
  have h := e.inv.naturality i
  change (T ReverseSimplex K).map (extension.map i) ≫ e.inv.app B =
    e.inv.app A ≫ extension.map ((T SimplexCategory K).map i) at h
  rw [← Category.assoc, ← h]
  simp only [Category.assoc]

/-- Precomposition commutes with the target isomorphism identifying the
literal ordinary input and horizontal restriction. -/
private theorem input_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : Target) :
    diagramMappingPrecomp (discrete.map f)
        (JTRealizationDiagonal.ordinaryCurry.obj
          (JTReversalInput.ordinaryInput.obj W)) ≫
        ((diagramMappingTarget (discrete.obj K)).mapIso
          (OrdinaryFreeRestrictionEnriched.inputRestrictionIso W)).hom =
      ((diagramMappingTarget (discrete.obj L)).mapIso
          (OrdinaryFreeRestrictionEnriched.inputRestrictionIso W)).hom ≫
        diagramMappingPrecomp (discrete.map f) (restriction.obj W) := by
  apply NatTrans.ext
  funext n η
  apply NatTrans.ext
  funext c
  change ((discrete.map f).app c ▷ SSet.stdSimplex.obj n.unop) ≫
      η.app c ≫
        (OrdinaryFreeRestrictionEnriched.inputRestrictionIso W).hom.app c =
    ((discrete.map f).app c ▷ SSet.stdSimplex.obj n.unop) ≫
      (η.app c ≫
        (OrdinaryFreeRestrictionEnriched.inputRestrictionIso W).hom.app c)
  rfl

/-- The actual free-discrete Kan-extension isomorphism transports
precomposition by every original ordinary simplicial-set map. -/
private theorem free_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : Target) :
    diagramMappingPrecomp (extension.map (discrete.map f)) W ≫
        ((diagramMappingSource W).mapIso
          ((OrdinaryFreeDiscreteKan.discreteExtensionIso.app K).op)).symm.hom =
      ((diagramMappingSource W).mapIso
          ((OrdinaryFreeDiscreteKan.discreteExtensionIso.app L).op)).symm.hom ≫
        diagramMappingPrecomp (free.map f) W := by
  change diagramMappingPrecomp (extension.map (discrete.map f)) W ≫
      diagramMappingPrecomp
        (OrdinaryFreeDiscreteKan.discreteExtensionIso.inv.app K) W =
    diagramMappingPrecomp
        (OrdinaryFreeDiscreteKan.discreteExtensionIso.inv.app L) W ≫
      diagramMappingPrecomp (free.map f) W
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
  exact congrArg (fun g ↦ diagramMappingPrecomp g W)
    (OrdinaryFreeDiscreteKan.discreteExtensionIso.inv.naturality f).symm

/-- The exact arbitrary-`K` mapping isomorphism is natural under
precomposition by any original horizontal simplicial-set map. -/
theorem freeDiscreteMappingIso_natural {K L : SSet.{0}} (f : K ⟶ L)
    (W : Target) :
    diagramMappingPrecomp (discrete.map f)
        (JTRealizationDiagonal.ordinaryCurry.obj
          (JTReversalInput.ordinaryInput.obj W)) ≫
        (OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso K W).hom =
      (OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso L W).hom ≫
        diagramMappingPrecomp (free.map f) W := by
  let α (J : SSet.{0}) :=
    ((diagramMappingTarget (discrete.obj J)).mapIso
      (OrdinaryFreeRestrictionEnriched.inputRestrictionIso W)).hom
  let μ (J : SSet.{0}) :=
    (OrdinaryFreeRestrictionEnriched.mappingRestrictionIso
      (discrete.obj J) W).hom
  let β (J : SSet.{0}) :=
    ((diagramMappingSource W).mapIso
      ((OrdinaryFreeDiscreteKan.discreteExtensionIso.app J).op)).symm.hom
  change diagramMappingPrecomp (discrete.map f) _ ≫
      ((α K ≫ μ K) ≫ β K) =
    ((α L ≫ μ L) ≫ β L) ≫ diagramMappingPrecomp (free.map f) W
  have hα := input_natural f W
  have hμ := mappingRestrictionIso_natural (discrete.map f) W
  have hβ := free_natural f W
  change diagramMappingPrecomp (discrete.map f) _ ≫ α K =
    α L ≫ diagramMappingPrecomp (discrete.map f) (restriction.obj W) at hα
  change diagramMappingPrecomp (discrete.map f) (restriction.obj W) ≫ μ K =
    μ L ≫ diagramMappingPrecomp (extension.map (discrete.map f)) W at hμ
  change diagramMappingPrecomp (extension.map (discrete.map f)) W ≫ β K =
    β L ≫ diagramMappingPrecomp (free.map f) W at hβ
  let p := diagramMappingPrecomp (discrete.map f)
    (JTRealizationDiagonal.ordinaryCurry.obj
      (JTReversalInput.ordinaryInput.obj W))
  let q := diagramMappingPrecomp (discrete.map f) (restriction.obj W)
  let r := diagramMappingPrecomp (extension.map (discrete.map f)) W
  let s := diagramMappingPrecomp (free.map f) W
  change p ≫ ((α K ≫ μ K) ≫ β K) =
    ((α L ≫ μ L) ≫ β L) ≫ s
  change p ≫ α K = α L ≫ q at hα
  change q ≫ μ K = μ L ≫ r at hμ
  change r ≫ β K = β L ≫ s at hβ
  calc
    p ≫ ((α K ≫ μ K) ≫ β K) =
        ((p ≫ α K) ≫ μ K) ≫ β K := by
          simp only [Category.assoc]
    _ = ((α L ≫ q) ≫ μ K) ≫ β K := by rw [hα]
    _ = (α L ≫ (q ≫ μ K)) ≫ β K := by
      simp only [Category.assoc]
    _ = (α L ≫ (μ L ≫ r)) ≫ β K := by rw [hμ]
    _ = ((α L ≫ μ L) ≫ r) ≫ β K := by
      simp only [Category.assoc]
    _ = (α L ≫ μ L) ≫ (r ≫ β K) := by
      simp only [Category.assoc]
    _ = (α L ≫ μ L) ≫ (β L ≫ s) := by rw [hβ]
    _ = ((α L ≫ μ L) ≫ β L) ≫ s := by
      simp only [Category.assoc]

#print axioms mappingRestrictionIso_natural
#print axioms freeDiscreteMappingIso_natural

end

end DaggerModels.PartII.OrdinaryFreeRestrictionCalibration
