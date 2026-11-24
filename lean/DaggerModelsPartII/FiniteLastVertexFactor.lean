import DaggerModelsPartII.NerveSubcomplexLastVertexCriterion
import DaggerModels.SSetMonoRLPRetraction
import OriginalSimplicialPiZeroWeakEquivalence

/-! Finite last-vertex maps can be contracted by a weak factorization on a resolution. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerNerveHomotopy DaggerSSetGluing
open DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteLastVertexFactor

noncomputable section

private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

private theorem weak_toPoint {X : SSet.{0}} (h : GW (pointMap X)) :
    WeakEquivalence (toPoint X) := by
  let e := pointIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  letI : WeakEquivalence (pointMap X) := (weakEquivalence_iff_GW _).mpr h
  rw [SSet.stdSimplex.isTerminalObj₀.hom_ext (toPoint X) (pointMap X ≫ e.hom)]
  infer_instance

private def homotopy_in_contractible {X Y : SSet.{0}} (f g : X ⟶ R.obj Y)
    (h : GW (pointMap Y)) : SSet.Homotopy f g := by
  let p := toPoint (R.obj Y)
  letI : WeakEquivalence (toPoint Y) := weak_toPoint h
  letI : WeakEquivalence p := by
    have hh : sSetTopAdj.unit.app Y ≫ p = toPoint Y :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    exact weakEquivalence_of_precomp_of_fac hh
  letI : Fibration p :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  let e := SSetMonoRLPRetraction.endpoints X
  letI : Mono e := SSetMonoRLPRetraction.mono_endpoints X
  letI : Cofibration e := (SSet.modelCategoryQuillen.cofibration_iff e).mpr inferInstance
  let sq : CommSq (coprod.desc f g) e p (toPoint _) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  refine SSet.Homotopy.mk sq.lift ?_ ?_
  · rw [← SSetMonoRLPRetraction.inl_endpoints, Category.assoc, sq.fac_left, coprod.inl_desc]
  · rw [← SSetMonoRLPRetraction.inr_endpoints, Category.assoc, sq.fac_left, coprod.inr_desc]

private theorem nonempty_vertices {X : SSet.{0}} (h : GW (pointMap X)) :
    Nonempty (X.obj (op ⦋0⦌)) := by
  letI : WeakEquivalence (toPoint X) := weak_toPoint h
  have hp := DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero (toPoint X)
  obtain ⟨a, _⟩ := hp.2 (SSet.π₀.mk (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))))
  obtain ⟨v, _⟩ := SSet.π₀.mk_surjective a
  exact ⟨v⟩

/-- Two maps through the same weakly contractible simplicial set become
homotopic after singular realization. -/
def homotopic_through {X Y Z : SSet.{0}} (p q : X ⟶ Y) (f : Y ⟶ Z)
    (h : GW (pointMap Y)) :
    SSet.Homotopy (R.map (p ≫ f)) (R.map (q ≫ f)) :=
  ((homotopy_in_contractible (R.map p) (R.map q) h).postcomp (R.map f)).congr
    (R.map_comp p f).symm (R.map_comp q f).symm

/-- Natural comparisons into the same weakly contractible intermediate
category identify the two evaluations after singular realization. -/
def homotopy_of_roof {A B C : Type} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    {L M : A ⥤ C} {F G : A ⥤ B} {E : B ⥤ C}
    (α : L ⟶ F ⋙ E) (β : M ⟶ G ⋙ E) (hE : GW (pointMap (nerve B))) :
    SSet.Homotopy (R.map (nerveMap L)) (R.map (nerveMap M)) := by
  have h : SSet.Homotopy (R.map (nerveMap (F ⋙ E))) (R.map (nerveMap (G ⋙ E))) :=
    homotopic_through (nerveMap F) (nerveMap G) (nerveMap E) hE
  exact (natTransHomotopyR α).trans (h.trans (natTransHomotopyR β).symm)

/-- A map factoring through an actual weakly contractible simplicial set
becomes nullhomotopic after singular realization. -/
theorem nullhomotopic {X Y Z : SSet.{0}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (h : GW (pointMap Y)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ Z,
      Nonempty (SSet.Homotopy (R.map (p ≫ q)) (R.map (toPoint X ≫ v))) := by
  let v := SSet.yonedaEquiv.symm (nonempty_vertices h).some
  have H := (homotopy_in_contractible (R.map p) (R.map (toPoint X ≫ v)) h).postcomp (R.map q)
  exact ⟨v ≫ q, ⟨H.congr (R.map_comp p q).symm
    ((R.map_comp _ q).symm.trans (congrArg R.map (Category.assoc _ _ _)))⟩⟩

/-- A weak categorical cover suffices to compare the evaluation to a
factor through a weakly contractible category. -/
theorem nerveMap_nullhomotopic_of_weak_cover {C D E B : Type}
    [SmallCategory C] [SmallCategory D] [SmallCategory E] [SmallCategory B]
    (P : D ⥤ B) [WeakEquivalence (nerveMap P)]
    (L : B ⥤ C) (F : D ⥤ E) (G : E ⥤ C) (hE : GW (pointMap (nerve E)))
    (h : NatTransZigzag (P ⋙ L) (F ⋙ G)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
      Nonempty (SSet.Homotopy (R.map (nerveMap L))
        (R.map (toPoint (nerve B) ≫ v))) := by
  letI : WeakEquivalence (R.map (nerveMap P)) := FiniteWeakCover.weak_singular _
  obtain ⟨v, ⟨H⟩⟩ := nullhomotopic (nerveMap F) (nerveMap G) hE
  have hp : nerveMap P ≫ toPoint (nerve B) = toPoint (nerve D) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨v, ⟨FiniteWeakCover.homotopyOfPrecomp (R.map (nerveMap P)) ?_⟩⟩
  have K := (zigzagHomotopy h).some.trans H
  rw [← R.map_comp, ← R.map_comp, ← Category.assoc, hp]
  exact K

/-- A weak categorical resolution of a finite last-vertex diagram may use a
comparison into any given weakly contractible category over the original one. -/
theorem last_vertex_nullhomotopic {C D E : Type}
    [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (A : (nerve C).Subcomplex) (P : D ⥤ A.toSSet.Elementsᵒᵖ)
    [WeakEquivalence (nerveMap P)] (F : D ⥤ E) (G : E ⥤ C)
    (hE : GW (pointMap (nerve E)))
    (h : NatTransZigzag (P ⋙ NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex C A) (F ⋙ G)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
      Nonempty (SSet.Homotopy
        (R.map (nerveMap (NerveSimplexResolutionHomotopy.lastVertexOnSubcomplex C A)))
        (R.map (toPoint (nerve A.toSSet.Elementsᵒᵖ) ≫ v))) :=
  nerveMap_nullhomotopic_of_weak_cover P _ F G hE h

end
end DaggerModels.PartII.FiniteLastVertexFactor
