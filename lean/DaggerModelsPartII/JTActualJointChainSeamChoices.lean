import DaggerModelsPartII.JTActualJointChainSeamData
import DaggerModelsPartII.JTChosenSeamChainDiagram

/-!
Relative seam triangles for the actual ending and starting correction edges.
The original Family supplies every support, row and boundary input. The complete
higher filler space and all common chains are retained. Weakness is proved over
the actual exact-cut chain source, not over the original weak marked source.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainSeamChoices

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row vertexPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev K := JTActualJointChoiceChainGraph.ordinals F j
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev U := JTActualJointChainSeamData.supportSSet F j
private abbrev incl := JTActualJointChainSeamData.supportIncl F j
private abbrev f := JTActualJointChainSeamData.endpointRows F j
private abbrev e := JTActualJointChoiceChainGraph.chainEnding F j
private abbrev s := JTActualJointChoiceChainGraph.chainStarting F j
private abbrev he := JTActualJointChainSeamData.ending_boundary F j
private abbrev hs := JTActualJointChainSeamData.starting_boundary F j
private abbrev hfU := JTActualJointChainSeamData.supported_endpoint F j
private abbrev heU := JTActualJointChainSeamData.ending_supported F j
private abbrev hsU := JTActualJointChainSeamData.starting_supported F j

/-- All actual higher relative seam triangle fillers, with no selected filler. -/
abbrev spaces : (I F j)ᵒᵖ ⥤ SSet.{0} :=
  JTSeamTriangleChoiceDiagram.spaces W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- Every higher filler simplex and every common coefficient-choice chain. -/
abbrev Index :=
  JTChosenSeamChainDiagram.Index W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- Forget the filler and its full chain, retaining the actual original cut chain. -/
abbrev toOriginal : Index F j ⥤ I F j :=
  JTChosenSeamChainDiagram.toOriginal W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- This actual seam refinement is weak over the exact-cut chain source. -/
theorem toOriginal_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toOriginal F j)) :=
  JTChosenSeamChainDiagram.toOriginal_weak W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
    (JTActualJointChainSeamData.supportIncl_mono F j)
    (JTActualJointChainSeamData.supportIncl_weak F j) hW

/-- The whole ordinal on the common old-coefficient and triangle-choice chain. -/
abbrev ordinals : Index F j ⥤ SimplexCategory :=
  JTChosenSeamChainDiagram.ordinals W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- The unchanged old chain coefficient coordinate. -/
abbrev toOld : ordinals F j ⟶ toOriginal F j ⋙ K F j :=
  JTChosenSeamChainDiagram.toOld W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- The full row-two triangle on the genuine higher-choice chain cover. -/
abbrev triangle : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋2⦌) :=
  JTChosenSeamChainDiagram.triangle W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- The varying original endpoint row on the common triangle-choice chain. -/
abbrev seamRow : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋0⦌) :=
  JTChosenSeamChainDiagram.seamRow W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- Every triangle face is the corresponding full actual correction edge. -/
theorem triangle_edge (p : Index F j) (n : Fin 3) :
    (triangle F j).app p ≫ JTRelativeSeamTriangle.rowEdge W n =
      std.map ((toOld F j).app p) ≫
        JTSeamTriangleChoiceDiagram.edges W (K F j) (f F j) (e F j) (s F j)
          ((toOriginal F j).obj p) n :=
  JTChosenSeamChainDiagram.triangle_edge W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) p n

/-- The long face is exactly the identity on the actual varying endpoint row. -/
theorem triangle_long (p : Index F j) :
    (triangle F j).app p ≫ JTRelativeSeamTriangle.rowEdge W 1 =
      (seamRow F j).app p ≫ JTEndpointNormalizationLifts.identityFamily W :=
  JTChosenSeamChainDiagram.triangle_long W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) p

/-- The full triangle is stationary on the exact original natural support. -/
theorem triangle_onSupport (p : Index F j) (d : SimplexCategory)
    (v : d ⟶ (ordinals F j).obj p)
    (a : std.obj d ⟶ (U F j).obj ((toOriginal F j).obj p))
    (h : std.map v ≫ std.map ((toOld F j).app p) =
      a ≫ (incl F j).app ((toOriginal F j).obj p)) :
    std.map v ≫ (triangle F j).app p =
      term (std.obj d) ≫ vertexPoint W (z j) ≫
        JTRelativeSeamTriangle.identityTriangle W :=
  JTChosenSeamChainDiagram.triangle_onSupport W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) p d v a h

end
end DaggerModels.PartII.JTActualJointChainSeamChoices
