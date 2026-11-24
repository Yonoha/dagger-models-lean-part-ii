import DaggerModelsPartII.OrdinaryCellCobaseComparison
import DaggerModelsPartII.OrdinaryPointCellComparison

/-!
# Local comparison for the full ordinary generating family

Every actual pushout of an original ordinary boundary or object generator
has monic Hom maps and preserves the local geometric comparison under a
further supplied cobase change. Arbitrary boundary attaching functors are
classified by the existing two-object cell equivalence. Transfinite closure
is a separate obligation.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerModels.OrdinaryGeneratorCobase

noncomputable section

/-- The exact whole generator family has the Hom-monic and local-comparison
properties at every actual pushout, with no restriction on its attaching map. -/
theorem generator_pushout_properties
    {A B C PC : SimplicialCat.{u, u}}
    (g : A ⟶ B) (hg : OrdinaryBergnerGenerators.generators g)
    (a : A ⟶ C) (b : B ⟶ PC) (i : C ⟶ PC)
    (sqC : IsPushout g a b i) :
    (∀ x y : C.Obj, Mono (i.map x y)) ∧
      (∀ {D PD : SimplicialCat.{u, u}}
        (F : C ⟶ D) (j : D ⟶ PD) (Fplus : PC ⟶ PD),
        IsPushout F i j Fplus →
        (∀ x y : C.Obj, DaggerOrdinaryCellComparisonGeometric.GW (F.map x y)) →
        ∀ p q : PC.Obj,
          DaggerOrdinaryCellComparisonGeometric.GW (Fplus.map p q)) := by
  change OrdinaryBergnerGenerators.boundaryGenerators g ∨
    OrdinaryBergnerGenerators.objectGenerators g at hg
  rcases hg with hg | hg
  · cases hg with
    | mk n =>
      have sq' : IsPushout (OrdinaryTwoObjectCell.map (SSet.boundary.{u} n).ι)
          (OrdinaryTwoObjectCell.fromData (SSet.boundary n) C
            (a.obj TwoObjectDaggerGraph.left) (a.obj TwoObjectDaggerGraph.right)
            (a.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right)) b i := by
        simpa only [OrdinaryTwoObjectCell.fromData_classify] using sqC
      refine ⟨?_, ?_⟩
      · exact (OrdinaryCellCobaseComparison.one_cell_injective_and_hom_mono
          (x := a.obj TwoObjectDaggerGraph.left)
          (y := a.obj TwoObjectDaggerGraph.right)
          (k := (SSet.boundary n).ι)
          (u0 := a.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right)
          (gC := b) (iC := i) (sqC := sq')).2
      · intro D PD F j Fplus sq hF p q
        exact OrdinaryCellCobaseComparison.one_cell_cobase_local
          (F := F) (x := a.obj TwoObjectDaggerGraph.left)
          (y := a.obj TwoObjectDaggerGraph.right)
          (k := (SSet.boundary n).ι)
          (u0 := a.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right)
          (gC := b) (iC := i) (sqC := sq')
          (j := j) (Fplus := Fplus) (sq := sq) hF p q
  · cases hg with
    | mk _ =>
      refine ⟨OrdinaryPointCellComparison.supplied_old_hom_mono i b sqC.flip, ?_⟩
      intro D PD F j Fplus sq hF p q
      exact OrdinaryPointCellComparison.point_cell_cobase_local
        i b sqC.flip F j Fplus sq hF p q

end

end DaggerModels.OrdinaryGeneratorCobase
