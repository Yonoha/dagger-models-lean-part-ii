import DaggerModelsPartII.StandardSimplexFrame
import DaggerModelsPartII.ReedyCoefficientChange
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Weighted simplex boundaries and actual cosimplicial latching maps

The standard boundary is already the colimit of its proper faces. A
colimit-preserving coefficient functor sends that boundary inclusion to the
native opposite matching comparison, up to a canonical arrow isomorphism.
For a Yoneda-weighted frame, the Yoneda extension unit identifies its
representable values with the original cosimplicial diagram. All degrees,
including zero, use the same construction.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

universe u

namespace DaggerModels.PartII.JTWeightedBoundaryLatching

noncomputable section

variable {C : Type u} [Category.{0} C]
variable [HasColimitsOfSize.{0, 0} C]

/-- The native coefficient-change comparison for the boundary arrow and the
proper-face matching arrow, before restricting to a Yoneda-weighted frame. -/
def coefficientBoundaryMatchingIso
    (G : SSet.{0} ⥤ C) [PreservesColimitsOfSize.{0, 0} G] (n : ℕ) :
    Arrow.mk ((G.op).map (SSet.boundary.{0} n).ι.op) ≅
      Arrow.mk ((matchingComparison n).app (SSet.stdSimplex.{0}.op ⋙ G.op)) := by
  letI : HasLimitsOfSize.{0, 0} Cᵒᵖ := inferInstance
  letI : PreservesLimitsOfSize.{0, 0} G.op := preservesLimitsOfSize_op _
  let eBoundary := (G.op).mapIso (matchingBoundaryIso.{0} n)
  let eCoeff := ReedyCoefficientChange.matchingObjectIso G.op n
    SSet.stdSimplex.{0}.op
  let eTarget : (G.op).obj (op (SSet.boundary.{0} n).toSSet) ≅
      (matchingFunctor n).obj (SSet.stdSimplex.{0}.op ⋙ G.op) :=
    eBoundary.symm ≪≫ eCoeff
  refine Arrow.isoMk (Iso.refl _) eTarget ?_
  simp only [Iso.refl_hom, Category.id_comp]
  symm
  have hfirst :
      (G.op).map (SSet.boundary.{0} n).ι.op ≫ eBoundary.inv =
        (G.op).map ((matchingComparison n).app SSet.stdSimplex.{0}.op) := by
    change (G.op).map (SSet.boundary.{0} n).ι.op ≫
      (G.op).map (matchingBoundaryIso.{0} n).inv = _
    rw [← Functor.map_comp, ← matchingBoundaryIso_comp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    (G.op).map (SSet.boundary.{0} n).ι.op ≫ eTarget.hom =
        ((G.op).map (SSet.boundary.{0} n).ι.op ≫ eBoundary.inv) ≫
          eCoeff.hom := by simp [eTarget, Category.assoc]
    _ = (G.op).map ((matchingComparison n).app SSet.stdSimplex.{0}.op) ≫
          eCoeff.hom := by rw [hfirst]
    _ = (matchingComparison n).app (SSet.stdSimplex.{0}.op ⋙ G.op) :=
      ReedyCoefficientChange.matchingComparison_map G.op n SSet.stdSimplex.{0}.op

/-- A natural representation of the simplex values of a colimit-preserving
weight functor identifies its boundary arrow with the native matching arrow. -/
def boundaryMatchingIsoOfRepresentation
    (G : SSet.{0} ⥤ C) [PreservesColimitsOfSize.{0, 0} G]
    (F : SimplexCategory ⥤ C)
    (eFrame : SSet.stdSimplex.{0} ⋙ G ≅ F) (n : ℕ) :
    Arrow.mk ((G.op).map (SSet.boundary.{0} n).ι.op) ≅
      Arrow.mk ((matchingComparison n).app F.op) := by
  letI : HasLimitsOfSize.{0, 0} Cᵒᵖ := inferInstance
  let eOpp : (SSet.stdSimplex.{0}.op ⋙ G.op) ≅ F.op :=
    (NatIso.op eFrame).symm
  let eMatching : Arrow.mk ((matchingComparison n).app
        (SSet.stdSimplex.{0}.op ⋙ G.op)) ≅
      Arrow.mk ((matchingComparison n).app F.op) :=
    Arrow.isoMk (asIso (eOpp.hom.app (op ⦋n⦌)))
      (asIso ((matchingFunctor n).map eOpp.hom))
      ((matchingComparison n).naturality eOpp.hom)
  exact coefficientBoundaryMatchingIso G n ≪≫ eMatching

/-- The same represented boundary arrow in the ordinary cosimplicial
latching direction, with the native opposite matching map unopposed. -/
def boundaryLatchingIsoOfRepresentation
    (G : SSet.{0} ⥤ C) [PreservesColimitsOfSize.{0, 0} G]
    (F : SimplexCategory ⥤ C)
    (eFrame : SSet.stdSimplex.{0} ⋙ G ≅ F) (n : ℕ) :
    Arrow.mk (G.map (SSet.boundary.{0} n).ι) ≅
      Arrow.mk (((matchingComparison n).app F.op).unop) := by
  let e := boundaryMatchingIsoOfRepresentation G F eFrame n
  exact Arrow.isoMk (Arrow.rightFunc.mapIso e.symm).unop
    (Arrow.leftFunc.mapIso e.symm).unop
    (Quiver.Hom.op_inj e.inv.w.symm)

/-- The weighted realization of a cosimplicial diagram. -/
def weighted (F : SimplexCategory ⥤ C) : SSet.{0} ⥤ C :=
  uliftYoneda.{0}.leftKanExtension F

/-- The actual Yoneda-weighted boundary inclusion, in the opposite category,
is isomorphic as an arrow to the native matching comparison of the frame. -/
def weightedBoundaryMatchingIso (F : SimplexCategory ⥤ C) (n : ℕ) :
    Arrow.mk (((weighted F).op).map (SSet.boundary.{0} n).ι.op) ≅
      Arrow.mk ((matchingComparison n).app F.op) := by
  letI : PreservesColimitsOfSize.{0, 0} (weighted F) :=
    Presheaf.preservesColimitsOfSize_leftKanExtension F
  exact boundaryMatchingIsoOfRepresentation (weighted F) F
    (Presheaf.isExtensionAlongULiftYoneda F) n

/-- The same canonical arrow isomorphism in the ordinary cosimplicial
latching direction, with the native opposite matching map unopposed. -/
def weightedBoundaryLatchingIso (F : SimplexCategory ⥤ C) (n : ℕ) :
    Arrow.mk ((weighted F).map (SSet.boundary.{0} n).ι) ≅
      Arrow.mk (((matchingComparison n).app F.op).unop) := by
  letI : PreservesColimitsOfSize.{0, 0} (weighted F) :=
    Presheaf.preservesColimitsOfSize_leftKanExtension F
  exact boundaryLatchingIsoOfRepresentation (weighted F) F
    (Presheaf.isExtensionAlongULiftYoneda F) n

end

end DaggerModels.PartII.JTWeightedBoundaryLatching
