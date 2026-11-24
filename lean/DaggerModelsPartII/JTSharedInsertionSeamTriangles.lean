import DaggerModelsPartII.JTSharedInsertionIncidentEdges
import DaggerModelsPartII.JTChosenSeamChainDiagram

/-!
Actual full relative triangles at the inserted mark on the shared chain.
The old row and both edges are derived from the original all-vertex tuple;
their entire incident-support inverse image is stationary. Every higher filler
and every full coefficient/filler chain is retained, with a weak projection
under the original injective fibrancy hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionSeamTriangles

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem chain_constant {S U D K N X : SSet.{0}}
    (i : S ⟶ D) (j : S ⟶ U) (u : U ⟶ K) (α : D ⟶ K) (β : D ⟶ N)
    (h : j ≫ u = i ≫ α) (E : K ⊗ N ⟶ X) (c : (Δ[0] : SSet.{0}) ⟶ X)
    (hE : (u ▷ N) ≫ E = fst U N ≫ term U ≫ c) :
    i ≫ lift α β ≫ E = term S ≫ c := by
  have hc : i ≫ lift α β = lift j (i ≫ β) ≫ (u ▷ N) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerRight_fst, lift_fst_assoc]
      exact h.symm
    · simp only [Category.assoc, lift_snd, whiskerRight_snd]
  rw [← Category.assoc, hc, Category.assoc, hE, ← Category.assoc, lift_fst]
  rw [← Category.assoc]
  congr 1

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev U := JTSharedInsertionChainSupport.diagram F j 1
private abbrev K := JTSharedInsertionChoices.ordinals F j
private abbrev incl := JTSharedInsertionChainSupport.inclusion F j 1
private abbrev f := JTSharedInsertionChainSupport.rows F j 1
private abbrev e := JTSharedInsertionIncidentEdges.ending F j 1
private abbrev s := JTSharedInsertionIncidentEdges.starting F j 1
private abbrev he := JTSharedInsertionIncidentEdges.ending_endpoints F j 1
private abbrev hs := JTSharedInsertionIncidentEdges.starting_endpoints F j 1
private abbrev hfU := JTSharedInsertionChainSupport.row_on_support F j 1
private abbrev heU := JTSharedInsertionIncidentEdges.ending_on_support F j 1
private abbrev hsU := JTSharedInsertionIncidentEdges.starting_on_support F j 1

/-- Every higher relative seam triangle at the actual inserted mark. -/
abbrev spaces := JTSeamTriangleChoiceDiagram.spaces W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- All full triangle fillers and every common higher simplex operator. -/
abbrev Cover := JTChosenSeamChainDiagram.Cover W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- Forget the triangle filler while retaining the actual shared insertion chain. -/
abbrev projection := JTChosenSeamChainDiagram.projection W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- The full relative triangle choice cover is weak under original injective fibrancy. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) :=
  JTSeamTriangleChoiceDiagram.projection_weak W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
    (JTSharedInsertionChainSupport.inclusion_mono F j 1)
    (JTSharedInsertionChainSupport.inclusion_weak F j 1) hW

/-- Each complete higher relative triangle space is Kan. -/
theorem spaces_kan
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (JTSharedInsertionChoices.Index F j)ᵒᵖ) : ((spaces F j).obj p).KanComplex :=
  JTSeamTriangleChoiceDiagram.spaces_kan W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
    (JTSharedInsertionChainSupport.inclusion_mono F j 1) hW p

/-- Every relative triangle space has weak terminal projection. -/
theorem spaces_toPoint_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (JTSharedInsertionChoices.Index F j)ᵒᵖ) :
    WeakEquivalence (term ((spaces F j).obj p)) :=
  JTSeamTriangleChoiceDiagram.spaces_toPoint_weak W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
    (JTSharedInsertionChainSupport.inclusion_mono F j 1)
    (JTSharedInsertionChainSupport.inclusion_weak F j 1) hW p

/-- One full chain retains the shared old coefficient and every triangle-filler simplex. -/
abbrev Index := JTChosenSeamChainDiagram.Index W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

abbrev chainBase := JTChosenSeamChainDiagram.chainBase W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

abbrev ordinals := JTChosenSeamChainDiagram.ordinals W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

abbrev toOld := JTChosenSeamChainDiagram.toOld W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

abbrev toChoice := JTChosenSeamChainDiagram.toChoice W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

/-- Projection through all triangle choices and full chains to the actual shared insertion index. -/
abbrev toOriginal := JTChosenSeamChainDiagram.toOriginal W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

theorem toOriginal_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toOriginal F j)) :=
  JTChosenSeamChainDiagram.toOriginal_weak W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)
    (JTSharedInsertionChainSupport.inclusion_mono F j 1)
    (JTSharedInsertionChainSupport.inclusion_weak F j 1) hW

/-- The full naturally varying row-two triangle on every chosen complete chain. -/
abbrev triangle := JTChosenSeamChainDiagram.triangle W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

abbrev seamRow := JTChosenSeamChainDiagram.seamRow W (z j) (U F j) (K F j) (incl F j)
  (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)

private abbrev edges := JTSeamTriangleChoiceDiagram.edges W (K F j) (f F j) (e F j) (s F j)

/-- All THREE ordinary triangle faces are the prescribed shared-chain edges. -/
theorem triangle_edge (p : Index F j) (i : Fin 3) :
    (triangle F j).app p ≫ JTRelativeSeamTriangle.rowEdge W i =
      std.map ((toOld F j).app p) ≫ edges F j ((toOriginal F j).obj p) i :=
  JTChosenSeamChainDiagram.triangle_edge W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) p i

/-- The long face is the identity edge of the unchanged varying actual seam row. -/
theorem triangle_long (p : Index F j) :
    (triangle F j).app p ≫ JTRelativeSeamTriangle.rowEdge W 1 =
      (seamRow F j).app p ≫ JTEndpointNormalizationLifts.identityFamily W :=
  JTChosenSeamChainDiagram.triangle_long W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) p

/-- The FULL support on the final triangle chain, as its genuine subcomplex preimage. -/
def fullSupport (p : Index F j) : (std.obj ((ordinals F j).obj p)).Subcomplex :=
  (JTSharedInsertionChainSupport.support F j 1 ((toOriginal F j).obj p)).preimage
    (std.map ((toOld F j).app p))

/-- The entire actual triangle is constant on that full support in every simplicial degree. -/
theorem triangle_on_fullSupport (p : Index F j) :
    (fullSupport F j p).ι ≫ (triangle F j).app p =
      term (fullSupport F j p).toSSet ≫ vertexPoint W (z j) ≫
        JTRelativeSeamTriangle.identityTriangle W := by
  let b := (toOriginal F j).obj p
  let c := (chainBase F j).obj p
  let U₀ := JTSharedInsertionChainSupport.support F j 1 b
  let α := std.map ((toOld F j).app p)
  let β := std.map ((toChoice F j).app p)
  let E := (JTChosenSeamChainDiagram.trianglePrism W (z j) (U F j) (K F j) (incl F j)
    (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)).app c
  have hE : ((incl F j).app b ▷ std.obj
      ((JTChosenSeamChainDiagram.choiceTime W (z j) (U F j) (K F j) (incl F j)
        (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j)).obj c)) ≫
      E = fst (U F j |>.obj b) _ ≫ term (U F j |>.obj b) ≫
        (vertexPoint W (z j) ≫ JTRelativeSeamTriangle.identityTriangle W) :=
    JTSeamTriangleChoiceDiagram.timeMap_support W (z j) (U F j) (K F j) (incl F j)
      (f F j) (e F j) (s F j) (he F j) (hs F j) (hfU F j) (heU F j) (hsU F j) b _ c.unop.2
  exact chain_constant (fullSupport F j p).ι (U₀.fromPreimage α) (incl F j |>.app b)
    α β (U₀.fromPreimage_ι α) E
    (vertexPoint W (z j) ≫ JTRelativeSeamTriangle.identityTriangle W) hE

end
end DaggerModels.PartII.JTSharedInsertionSeamTriangles
