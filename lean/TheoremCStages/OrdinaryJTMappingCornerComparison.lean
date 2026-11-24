import OrdinaryJTMappingCornerFibration

/-!
# Literal ordinary JT mapping corner

The opposite-category diagram Hom is naturally the plain ordinary JT row
in both the coefficient and horizontal-frame variables. Transporting its
pullback corner through these natural isomorphisms gives the literal
two-variable mapping corner, with no replacement of the target pullback.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTMappingCornerComparison

open OrdinaryJTMappingFrameWeak OrdinaryJTMappingCornerFibration

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

/-- The row isomorphism respects horizontal restriction on the full JT frame. -/
theorem rowIso_restriction (X : SSet.{0}) {A B : SSet.{0}} (u : A ⟶ B) :
    diagramHomPostcomp (op X) (NatTrans.op (frameMap u)) ≫ (rowIso X A).hom =
      (rowIso X B).hom ≫ restriction X u :=
  (StrictFrameMappingWeak.nativeStrictIso X).hom.naturality
    (NatTrans.op (frameMap u))

/-- The row isomorphism respects postcomposition in the ordinary target. -/
theorem rowIso_post {X Y : SSet.{0}} (p : X ⟶ Y) (A : SSet.{0}) :
    diagramHomPrecomp p.op (frame A).op ≫ (rowIso Y A).hom =
      (rowIso X A).hom ≫ mappingPost p A := by
  apply NatTrans.ext
  funext k f
  rfl

/-- Both pullback legs are transported by the same three row isomorphisms. -/
def cornerTargetIso {X Y A B : SSet.{0}} (p : X ⟶ Y) (u : A ⟶ B) :
    pullback
        (diagramHomPostcomp (op Y) (NatTrans.op (frameMap u)))
        (diagramHomPrecomp p.op (frame A).op) ≅
      pullback (restriction Y u) (mappingPost p A) :=
  asIso (pullback.map
    (diagramHomPostcomp (op Y) (NatTrans.op (frameMap u)))
    (diagramHomPrecomp p.op (frame A).op)
    (restriction Y u) (mappingPost p A)
    (rowIso Y B).hom (rowIso X A).hom (rowIso Y A).hom
    (rowIso_restriction Y u) (rowIso_post p A))

/-- The proved diagram-Hom corner is exactly the literal ordinary JT
mapping-row corner after the three canonical plain-Hom isomorphisms. -/
def cornerArrowIso {X Y A B : SSet.{0}} (p : X ⟶ Y) (u : A ⟶ B) :
    Arrow.mk (diagramHomCorner p.op (NatTrans.op (frameMap u))) ≅
      Arrow.mk (corner p u) := by
  refine Arrow.isoMk (rowIso X B) (cornerTargetIso p u) ?_
  apply pullback.hom_ext
  · change (rowIso X B).hom ≫ corner p u ≫ pullback.fst _ _ =
      diagramHomCorner p.op (NatTrans.op (frameMap u)) ≫
        (cornerTargetIso p u).hom ≫ pullback.fst _ _
    simpa only [← Category.assoc, diagramHomCorner, corner, cornerTargetIso,
      asIso_hom, pullback.map, pullback.lift_fst] using (rowIso_post p B).symm
  · change (rowIso X B).hom ≫ corner p u ≫ pullback.snd _ _ =
      diagramHomCorner p.op (NatTrans.op (frameMap u)) ≫
        (cornerTargetIso p u).hom ≫ pullback.snd _ _
    simpa only [← Category.assoc, diagramHomCorner, corner, cornerTargetIso,
      asIso_hom, pullback.map, pullback.lift_snd] using
        (rowIso_restriction X u).symm

/-- For an ordinary Joyal fibration and a horizontal monomorphism, the
literal two-variable ordinary JT mapping corner is a Kan fibration. -/
theorem corner_fibration {X Y A B : SSet.{0}} (p : X ⟶ Y)
    (hp : ordinaryJoyalModel.categoryWithFibrations.fibrations p)
    (u : A ⟶ B) [Mono u] :
    Fibration (corner p u) := by
  have h := diagram_corner_fibration p hp u
  exact (fibration_iff _).mpr
    (((fibrations SSet.{0}).arrow_mk_iso_iff (cornerArrowIso p u)).1
      ((fibration_iff _).mp h))

#print axioms cornerTargetIso
#print axioms corner_fibration

end

end DaggerModels.PartII.OrdinaryJTMappingCornerComparison
