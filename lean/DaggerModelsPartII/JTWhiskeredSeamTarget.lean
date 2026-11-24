import DaggerModelsPartII.JTWhiskeredSeamDiagram
import DaggerModelsPartII.JTSeamNativeCoefficients
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-! Native collapses of the whole seam diagram into one original target. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskeredSeamTarget

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {P R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}

/-- Read the native operator from a decorated-label natural transformation. -/
def nativeOf {L L' : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    (η : L ⟶ L') : codes L ⟶ codes L' :=
  Functor.whiskerRight η
    (OrderedLabelElements.projection W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.fst NecklaceCode SimplexCategory)

@[simp] theorem nativeOf_app {L L' : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    (η : L ⟶ L') (a : I) :
    (nativeOf η).app a =
      ((OrderedLabelElements.projection W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map (η.app a)).1 := rfl

/-- The triangle's full native two-simplex collapses to the single vertex. -/
def collapseTriangle : single 2 ⟶ single 0 :=
  JTMixedGraphHorizontalTraversal.singleOperator
    (SimplexCategory.isTerminalZero.from ⦋2⦌)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)

theorem longEdge_collapseTriangle :
    JTSeamNativeCoefficients.longEdge ≫ collapseTriangle =
      JTSeamNativeCoefficients.collapseIdentity := by
  apply NecklaceCode.Hom.ext
  have ht : IsTerminal ((single 0).toSSet : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.ofIso (singleIso 0).symm
  exact ht.hom_ext _ _

private theorem hom_id_comp {S T : NecklaceCode} (f : S ⟶ T) :
    Hom.comp (𝟙 S) f = f := Hom.ext (Category.id_comp f.map)

private theorem hom_comp_id {S T : NecklaceCode} (f : S ⟶ T) :
    Hom.comp f (𝟙 T) = f := Hom.ext (Category.comp_id f.map)

private theorem family_codes_map {M : NecklaceCode}
    (F : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K)
    {a b : I} (f : a ⟶ b) :
    (codes F.labels).map f =
      wedgeMap (P.map f) (wedgeMap (𝟙 M) (R.map f)) := by
  exact congrArg Prod.fst (JTWhiskeredSeamDiagram.Family.arrow_projection F f)

variable (F : JTWhiskeredSeamDiagram.SeamFamily (W := W) (x := x) (y := y) P R K)

/-- Collapse only the native triangle middle, naturally in both outer codes. -/
def triangleToCollapsed : codes F.triangle.labels ⟶
    codes (JTWhiskeredSeamDiagram.collapsedFamily F).labels where
  app a := wedgeMap (𝟙 (P.obj a))
    (wedgeMap collapseTriangle (𝟙 (R.obj a)))
  naturality {a b} f := by
    rw [family_codes_map F.triangle f,
      family_codes_map (JTWhiskeredSeamDiagram.collapsedFamily F) f]
    change Hom.comp
        (wedgeMap (P.map f) (wedgeMap (𝟙 (single 2)) (R.map f)))
        (wedgeMap (𝟙 (P.obj b)) (wedgeMap collapseTriangle (𝟙 (R.obj b)))) =
      Hom.comp
        (wedgeMap (𝟙 (P.obj a)) (wedgeMap collapseTriangle (𝟙 (R.obj a))))
        (wedgeMap (P.map f) (wedgeMap (𝟙 (single 0)) (R.map f)))
    rw [← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp]
    simp only [hom_id_comp, hom_comp_id]

/-- The long edge followed by the triangle collapse is exactly the original
identity-edge collapse, as natural native transformations. -/
theorem long_triangle_collapsed :
    nativeOf (JTWhiskeredSeamDiagram.longToTriangle F) ≫
      triangleToCollapsed F =
        nativeOf (JTWhiskeredSeamDiagram.longToCollapsed F) := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, nativeOf_app, nativeOf_app]
  rw [JTWhiskeredSeamDiagram.longToTriangle_projection,
    JTWhiskeredSeamDiagram.longToCollapsed_projection]
  change Hom.comp
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap JTSeamNativeCoefficients.longEdge (𝟙 (R.obj a))))
      (wedgeMap (𝟙 (P.obj a)) (wedgeMap collapseTriangle (𝟙 (R.obj a)))) =
    wedgeMap (𝟙 (P.obj a))
      (wedgeMap JTSeamNativeCoefficients.collapseIdentity (𝟙 (R.obj a)))
  rw [← wedgeMap_comp, ← wedgeMap_comp]
  simp only [hom_comp_id]
  exact congrArg (wedgeMap (𝟙 (P.obj a)))
    (congrArg (fun g : single 1 ⟶ single 0 ↦ wedgeMap g (𝟙 (R.obj a)))
      longEdge_collapseTriangle)

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c₀ : codes (JTWhiskeredSeamDiagram.collapsedFamily F).labels ⟶
  (Functor.const I).obj Q.code)

/-- The triangle reaches the same original target by native collapse. -/
def triangleTarget : codes F.triangle.labels ⟶ (Functor.const I).obj Q.code :=
  triangleToCollapsed F ≫ c₀

/-- The long-edge native target is the original collapsed target. -/
def longTarget : codes (JTWhiskeredSeamDiagram.longFamily F).labels ⟶
    (Functor.const I).obj Q.code :=
  nativeOf (JTWhiskeredSeamDiagram.longToCollapsed F) ≫ c₀

/-- The detour native target factors through the triangle in that same Q. -/
def detourTarget : codes (JTWhiskeredSeamDiagram.detourFamily F).labels ⟶
    (Functor.const I).obj Q.code :=
  nativeOf (JTWhiskeredSeamDiagram.detourToTriangle F) ≫
    triangleTarget F Q c₀

theorem detour_target_square :
    nativeOf (JTWhiskeredSeamDiagram.detourToTriangle F) ≫
      triangleTarget F Q c₀ = detourTarget F Q c₀ := rfl

theorem long_target_square :
    nativeOf (JTWhiskeredSeamDiagram.longToTriangle F) ≫
      triangleTarget F Q c₀ = longTarget F Q c₀ := by
  rw [triangleTarget, longTarget, ← Category.assoc, long_triangle_collapsed]

theorem collapsed_target_square :
    nativeOf (JTWhiskeredSeamDiagram.longToCollapsed F) ≫ c₀ =
      longTarget F Q c₀ := rfl

end
end DaggerModels.PartII.JTWhiskeredSeamTarget
