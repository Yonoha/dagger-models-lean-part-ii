import OriginalOrdinaryCellComparisonGeometricRecovered
import OrdinaryCellMonicity
import DaggerModels.OrdinaryTwoObjectCell

/-!
# Cobase comparison for one actual ordinary free cell

This transports the retained ordinary one-cell Hom comparison to a supplied
pushout square along that cell. It uses the same simplicial-category maps,
apexes, and endpoint transports, and requires only that the simplicial-set
attaching map is monic. No model-category structure is installed.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DaggerModels

universe u

namespace DaggerModels.OrdinaryCellCobaseComparison

noncomputable section

variable {C D PC PD : SimplicialCat.{u, u}} (F : C ⟶ D)
  (x y : C.Obj) {K L : SSet.{u}} (k : K ⟶ L)
  (u0 : K ⟶ (x ⟶[SSet] y))
  (gC : OrdinaryTwoObjectCell.cell L ⟶ PC) (iC : C ⟶ PC)
  (sqC : IsPushout (OrdinaryTwoObjectCell.map k)
    (OrdinaryTwoObjectCell.fromData K C x y u0) gC iC)
  (j : D ⟶ PD) (Fplus : PC ⟶ PD)
  (sq : IsPushout F iC j Fplus)

include sqC sq in
/-- Pasting the original cell square with its cobase square gives the
target cell square with the transported attaching map. -/
theorem target_cell_isPushout :
    IsPushout (OrdinaryTwoObjectCell.map k)
      (OrdinaryTwoObjectCell.fromData K D (F.obj x) (F.obj y)
        (u0 ≫ F.map x y))
      (gC ≫ Fplus) j := by
  simpa only [OrdinaryTwoObjectCell.fromData_naturality_right] using
    (sqC.flip.paste_horiz sq).flip

variable [Mono k]

include sqC sq in
/-- An ordinary local geometric weak equivalence remains local after a
single monic free-cell cobase change, for all original target objects. -/
theorem one_cell_cobase_local
    (hF : ∀ a b : C.Obj,
      DaggerOrdinaryCellComparisonGeometric.GW (F.map a b))
    (p q : PC.Obj) :
    DaggerOrdinaryCellComparisonGeometric.GW (Fplus.map p q) := by
  exact DaggerOrdinaryCellComparisonGeometric.ordinary_cell_comparison_geometric
    F x y k u0 gC iC sqC (gC ≫ Fplus) j
      (target_cell_isPushout F x y k u0 gC iC sqC j Fplus sq)
      Fplus sq.w.symm rfl hF p q

include sqC in
/-- The same original ordinary cell attachment is injective on objects and
monic on every original Hom, for use at filtered limit stages. -/
theorem one_cell_injective_and_hom_mono :
    Function.Bijective iC.obj ∧
      ∀ a b : C.Obj, Mono (iC.map a b) :=
  DaggerOrdinaryCellMonicity.ordinary_cell_part_one C x y k u0 gC iC sqC

end

end DaggerModels.OrdinaryCellCobaseComparison
