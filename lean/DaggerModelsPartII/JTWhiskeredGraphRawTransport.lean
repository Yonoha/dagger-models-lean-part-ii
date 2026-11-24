import DaggerModelsPartII.JTWhiskerEdgeGraphRaw

/-!
Transport an exact old raw equation from any covered graph domain, without
requiring that domain to be the full native-time product. The calculation
reuses `JTWhiskerEdgeGraphRaw.coefficient_reindex` and `native_restrict`,
followed by the Cartesian `comp_lift` equation for the map to the old graph.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTWhiskeredGraphRawTransport

open JTNecklaceLabelRealization (realizedLabel)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev pre (W : Source) {S T : SSet.{0}} (i : S ⟶ T) :=
  diagramMappingPrecomp (discreteFree.map i) W

/-- An exact old graph raw equation transfers along a native restriction and
a coefficient reindexing whenever both coordinates map into that old graph. -/
theorem raw (W : Source) {X Y : SSet.{0}} {S T : NecklaceCode}
    {k l : SimplexCategory}
    (oldH : Y ⟶ T.toSSet) (oldθ : Y ⟶ J.obj k)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W T)
    (g : T.toSSet ⟶ Raw W)
    (oldraw : lift oldH oldθ ≫
      realizedLabel T.toSSet W k (SSet.yonedaEquiv c) = oldH ≫ g)
    (h : X ⟶ S.toSSet) (q : X ⟶ J.obj l) (η : X ⟶ Y)
    (i : S.toSSet ⟶ T.toSSet) (α : l ⟶ k)
    (d : std.obj l ⟶ TripleBeadEndpointLabel.labels W S)
    (hd : d = std.map α ≫ c ≫ pre W i)
    (hn : η ≫ oldH = h ≫ i)
    (hq : q ≫ J.map α = η ≫ oldθ) :
    lift h q ≫ realizedLabel S.toSSet W l (SSet.yonedaEquiv d) =
      h ≫ i ≫ g := by
  rw [hd]
  rw [← JTWhiskerEdgeGraphRaw.coefficient_reindex W α h q (c ≫ pre W i)]
  rw [← JTWhiskerEdgeGraphRaw.native_restrict W i h (q ≫ J.map α) c]
  rw [hq, ← hn]
  calc
    lift (η ≫ oldH) (η ≫ oldθ) ≫
        realizedLabel T.toSSet W k (SSet.yonedaEquiv c) =
      η ≫ lift oldH oldθ ≫
        realizedLabel T.toSSet W k (SSet.yonedaEquiv c) := by
          rw [← comp_lift]
          simp only [Category.assoc]
    _ = η ≫ oldH ≫ g := by rw [oldraw]
    _ = h ≫ i ≫ g := by rw [← Category.assoc, hn, Category.assoc]

end
end DaggerModels.PartII.JTWhiskeredGraphRawTransport
