import OrdinarySegalHorizontalCotensor
import OrdinarySegalWalkingEvaluation
import TopCatModelCategory.SSet.Monoidal

/-!
# The point-parameter horizontal cotensor

The actual first horizontal parameter `Δ[0]` is a tensor unit. The strict
mapping-space row of its cotensor is identified with the original row by
the native simplex-zero unitor and the checked discrete representable
mapping isomorphism. Naturality retains every original horizontal operator.
The constant section `W ⟶ W^K` then uses the unique map `K ⟶ Δ[0]`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalHorizontalCotensorPoint

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre constantMap)

noncomputable section

/-- Extend the checked representable mapping isomorphism from natural
number notation to the literal object of `SimplexCategory`. -/
private def simplexIsoAt (W : Space) (n : SimplexCategory) :
    diagramMappingSpace (discrete.obj (SSet.stdSimplex.obj n)) W ≅
      W.obj (op n) := by
  induction n using SimplexCategory.rec with | _ m =>
    exact OrdinarySegalWalkingEvaluation.simplexMappingIso W m

private theorem simplexIsoAt_natural (W : Space)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    diagramMappingPrecomp (discrete.map (SSet.stdSimplex.map θ)) W ≫
        (simplexIsoAt W m).hom =
      (simplexIsoAt W n).hom ≫ W.map θ.op := by
  induction m using SimplexCategory.rec with | _ a =>
    induction n using SimplexCategory.rec with | _ b =>
      exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W θ

/-- At one horizontal degree, the native simplex-zero left unitor and
the representable mapping isomorphism identify the exact cotensor row. -/
def pointRowIso (W : Space) (n : SimplexCategory) :
    (cotensor (Δ[0] : SSet.{0}) W).obj (op n) ≅ W.obj (op n) :=
  (diagramMappingSource W).mapIso
      (Iso.op ((discrete.mapIso
        (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n))).symm)) ≪≫
    simplexIsoAt W n

private theorem pointRowIso_hom (W : Space) (n : SimplexCategory) :
    (pointRowIso W n).hom =
      diagramMappingPrecomp
          (discrete.map
            (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n)).inv) W ≫
        (simplexIsoAt W n).hom := rfl

/-- The row isomorphisms commute with every original horizontal simplex
operator; this is the naturality of the same native tensor unitor. -/
theorem pointRowIso_natural (W : Space)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (cotensor (Δ[0] : SSet.{0}) W).map θ.op ≫ (pointRowIso W m).hom =
      (pointRowIso W n).hom ≫ W.map θ.op := by
  let u (q : SimplexCategory) :=
    (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj q)).inv
  have hu : u m ≫ ((Δ[0] : SSet.{0}) ◁ SSet.stdSimplex.map θ) =
      SSet.stdSimplex.map θ ≫ u n :=
    SSet.stdSimplex.leftUnitor_inv_naturality (SSet.stdSimplex.map θ)
  calc
    (cotensor (Δ[0] : SSet.{0}) W).map θ.op ≫ (pointRowIso W m).hom =
        diagramMappingPrecomp
            (discrete.map (u m ≫
              ((Δ[0] : SSet.{0}) ◁ SSet.stdSimplex.map θ))) W ≫
          (simplexIsoAt W m).hom := by
            rw [OrdinarySegalHorizontalCotensor.cotensor_map,
              pointRowIso_hom, ← Category.assoc,
              ← diagramMappingPrecomp_comp, ← discrete.map_comp]
    _ = diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.map θ ≫ u n)) W ≫
          (simplexIsoAt W m).hom := by rw [hu]
    _ = (pointRowIso W n).hom ≫ W.map θ.op := by
      rw [discrete.map_comp, diagramMappingPrecomp_comp, Category.assoc,
        simplexIsoAt_natural, ← Category.assoc, pointRowIso_hom]

/-- The complete original simplicial space is the point-parameter
horizontal cotensor, not merely a family of objectwise row equivalences. -/
def pointIso (W : Space) : cotensor (Δ[0] : SSet.{0}) W ≅ W :=
  NatIso.ofComponents (fun n ↦ pointRowIso W n.unop) (by
    intro m n θ
    exact pointRowIso_natural W θ.unop)

/-- The actual constant horizontal maps into the exact cotensor by `K`
start at the original simplicial space `W`. -/
def constantSection (K : SSet.{0}) (W : Space) : W ⟶ cotensor K W :=
  (pointIso W).inv ≫ constantMap K W

/-- The chosen horizontal vertex evaluates a constant map to the identity
on `W`, retaining the original object and vertex map. -/
theorem constantSection_evaluateVertex (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    constantSection K W ≫
        OrdinarySegalHorizontalCotensor.evaluateVertex K W v =
      (pointIso W).inv := by
  rw [constantSection, OrdinarySegalHorizontalCotensor.evaluateVertex,
    constantMap, Category.assoc, ← OrdinarySegalHorizontalCotensor.pre_comp]
  have hv : v ≫ SSet.stdSimplex.isTerminalObj₀.from K =
      𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hv, OrdinarySegalHorizontalCotensor.pre_id, Category.comp_id]

#print axioms pointRowIso
#print axioms pointRowIso_natural
#print axioms pointIso
#print axioms constantSection
#print axioms constantSection_evaluateVertex

end

end DaggerModels.PartII.OrdinarySegalHorizontalCotensorPoint
