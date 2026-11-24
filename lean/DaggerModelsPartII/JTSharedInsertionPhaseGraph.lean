import DaggerModelsPartII.JTSharedInsertionPhaseNative
import DaggerModelsPartII.JTSharedInsertionOldGraph
import DaggerModelsPartII.JTSharedInsertionSeamGraph
import DaggerModelsPartII.JTPrismChainGraphTransport

/-!
# All four insertion phase graphs on the same original time

Every phase maps natively into the actual collapsed code. Its coarse parameter
is pulled from the corrected old split graph, retaining the entire original
time and all final coefficient lifts. The native phase squares give canonical
graph maps with exact projection and trace squares. No product Family, section,
raw theorem or global normalized comparison is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionPhaseGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev toSSet := NecklaceCode.simplicialFunctor.{0}

/-- A native natural transformation acts with identity on the full time coordinate. -/
def mapWithTime {C : Type} [SmallCategory C] {N M : C ⥤ NecklaceCode}
    (n : N ⟶ M) (t : C ⥤ SimplexCategory) :
    JTGraphCoveredProductInterface.product N t ⟶ JTGraphCoveredProductInterface.product M t :=
  Functor.whiskerRight
    (NatTrans.prod' (Functor.whiskerRight n toSSet) (𝟙 (t ⋙ J)))
    (MonoidalCategory.tensor SSet.{0})

/-- Native identity keeps the entire original-time product strictly unchanged. -/
theorem mapWithTime_id {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (t : C ⥤ SimplexCategory) :
    mapWithTime (𝟙 N) t = 𝟙 _ := by
  apply NatTrans.ext
  funext p
  change (𝟙 (N.obj p).toSSet ⊗ₘ 𝟙 (J.obj (t.obj p))) = 𝟙 _
  simp

/-- Native composition acts functorially on the full original-time product. -/
theorem mapWithTime_comp {C : Type} [SmallCategory C]
    {N M P : C ⥤ NecklaceCode} (f : N ⟶ M) (g : M ⟶ P) (t : C ⥤ SimplexCategory) :
    mapWithTime f t ≫ mapWithTime g t = mapWithTime (f ≫ g) t := by
  apply NatTrans.ext
  funext p
  change ((f.app p).map ⊗ₘ 𝟙 _) ≫ ((g.app p).map ⊗ₘ 𝟙 _) =
    ((f.app p).map ≫ (g.app p).map) ⊗ₘ 𝟙 _
  rw [tensorHom_comp_tensorHom, Category.id_comp]

/-- Native/time transport into a reindexed product, with no component choice. -/
def reindexedProductMap {C B : Type} [SmallCategory C] [SmallCategory B]
    (G : C ⥤ B) {N : C ⥤ NecklaceCode} {M : B ⥤ NecklaceCode}
    (n : N ⟶ G ⋙ M) (t : B ⥤ SimplexCategory) :
    JTGraphCoveredProductInterface.product N (G ⋙ t) ⟶
      G ⋙ JTGraphCoveredProductInterface.product M t := mapWithTime n (G ⋙ t)

/-- The native/time component formula at abstract functor arguments. -/
theorem reindexedProductMap_app {C B : Type} [SmallCategory C] [SmallCategory B]
    (G : C ⥤ B) {N : C ⥤ NecklaceCode} {M : B ⥤ NecklaceCode}
    (n : N ⟶ G ⋙ M) (t : B ⥤ SimplexCategory) (p : C) :
    (reindexedProductMap G n t).app p =
      (n.app p).map ⊗ₘ 𝟙 (J.obj (t.obj (G.obj p))) := rfl

private def reindexedNative {C B D : Type} [SmallCategory C] [SmallCategory B]
    [SmallCategory D] (G : C ⥤ B) (P : D ⥤ NecklaceCode)
    {L : B ⥤ D} {M : C ⥤ D} (r : M ⟶ G ⋙ L) : M ⋙ P ⟶ G ⋙ (L ⋙ P) :=
  Functor.whiskerRight r P

private theorem parameter_natural {C : Type} [SmallCategory C]
    {N M P : C ⥤ NecklaceCode} (f : N ⟶ M) (u : N ⟶ P) (v : M ⟶ P)
    (h : f ≫ v = u) (t : C ⥤ SimplexCategory) {Y : C ⥤ SSet.{0}}
    (θ : JTGraphCoveredProductInterface.product P t ⟶ Y) :
    mapWithTime f t ≫ (mapWithTime v t ≫ θ) = mapWithTime u t ≫ θ := by
  rw [← Category.assoc, mapWithTime_comp, h]

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- All actual triangle-filler choices and their one complete final coefficient chain. -/
abbrev Index := JTSharedInsertionNormalizedSeam.Index F j

/-- Forget only the triangle filler and its extra chain, retaining all shared choices. -/
abbrev base := JTSharedInsertionSeamTriangles.toOriginal F j

/-- The original time of the corrected split label pulled to these actual choices. -/
abbrev oldTime := base F j ⋙ JTSharedInsertionOldGraph.oldTime F j

/-- This is the very same original time as the checked actual triangle graph. -/
theorem oldTime_eq : oldTime F j = JTSharedInsertionSeamGraph.oldTime F j := rfl

private abbrev seam := JTSharedInsertionNormalizedSeam.seamFamily F j

/-- The complete collapsed corrected label, not the uncorrected original label. -/
abbrev collapsedCodes := codes (JTWhiskeredSeamDiagram.collapsedFamily (seam F j)).labels

/-- The whole native product retains the entire original clock. -/
abbrev X (N : Index F j ⥤ NecklaceCode) :=
  JTGraphCoveredProductInterface.product N (oldTime F j)

/-- The exact native part of the actual collapsed-to-old decorated comparison. -/
def nativeToOld : collapsedCodes F j ⟶
    base F j ⋙ codes (JTSharedInsertionOldGraph.oldFamily F j).labels :=
  reindexedNative (base F j)
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.fst NecklaceCode SimplexCategory)
    (JTSharedInsertionNormalizedSeam.collapsedToOld F j)

/-- Full corrected native/time map into the original-degree split graph product. -/
def oldProductMap : X F j (collapsedCodes F j) ⟶
    base F j ⋙ JTSharedInsertionOldGraph.X F j :=
  reindexedProductMap (base F j) (nativeToOld F j) (JTSharedInsertionOldGraph.oldTime F j)

/-- The exact product construction, kept at natural-transformation level. -/
theorem oldProductMap_eq : oldProductMap F j =
    reindexedProductMap (base F j) (nativeToOld F j)
      (JTSharedInsertionOldGraph.oldTime F j) := rfl

/-- Coarse parameter inherited from the actual corrected old split and original F.time. -/
def collapsedParameter : X F j (collapsedCodes F j) ⟶
    JTSharedInsertionNormalizedSeam.oldDegrees F j ⋙ J :=
  oldProductMap F j ≫
    Functor.whiskerLeft (base F j) (JTSharedInsertionOldGraph.coarseParameter F j)

variable {N M : Index F j ⥤ NecklaceCode}

/-- Every native phase uses this SAME corrected old parameter, before choosing any lift. -/
def coarseParameter (u : N ⟶ collapsedCodes F j) :
    X F j N ⟶ JTSharedInsertionNormalizedSeam.oldDegrees F j ⋙ J :=
  mapWithTime u (oldTime F j) ≫ collapsedParameter F j

/-- Retain ALL lifts through the actual final composite coefficient projection. -/
abbrev graph (u : N ⟶ collapsedCodes F j) :=
  JTPrismChainGraphCover.cover (X F j N) (coarseParameter F j u)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)

/-- The full graph projection, keeping the entire native code and original time. -/
abbrev projection (u : N ⟶ collapsedCodes F j) :=
  JTPrismChainGraphCover.projection (X F j N) (coarseParameter F j u)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)

/-- Its full lifted final coefficient parameter. -/
abbrev parameter (u : N ⟶ collapsedCodes F j) :=
  JTPrismChainGraphCover.parameter (X F j N) (coarseParameter F j u)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)

/-- Each phase graph is an actual trivial-fibration cover of its whole original-time product. -/
theorem projection_trivialFibration (u : N ⟶ collapsedCodes F j) (p : Index F j) :
    trivialFibrations SSet.{0} ((projection F j u).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration _ _ _
    (JTSharedInsertionNormalizedSeam.coefficientProjection_surjective F j) p

/-- A commuting native phase triangle acts canonically on all coefficient lifts. -/
def map (u : N ⟶ collapsedCodes F j) (v : M ⟶ collapsedCodes F j)
    (f : N ⟶ M) (h : f ≫ v = u) : graph F j u ⟶ graph F j v :=
  JTPrismChainGraphTransport.map (X F j N) (X F j M)
    (coarseParameter F j u) (coarseParameter F j v)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j) (𝟙 _)
    (Category.id_comp _) (mapWithTime f (oldTime F j))
    (parameter_natural f u v h (oldTime F j) (collapsedParameter F j))

/-- Every phase comparison preserves the whole native/time projection exactly. -/
theorem map_projection (u : N ⟶ collapsedCodes F j) (v : M ⟶ collapsedCodes F j)
    (f : N ⟶ M) (h : f ≫ v = u) :
    map F j u v f h ≫ projection F j v = projection F j u ≫ mapWithTime f (oldTime F j) :=
  JTPrismChainGraphTransport.map_projection _ _ _ _ _ _ _ _ _ _

/-- Every phase comparison preserves the entire lifted final parameter. -/
theorem map_parameter (u : N ⟶ collapsedCodes F j) (v : M ⟶ collapsedCodes F j)
    (f : N ⟶ M) (h : f ≫ v = u) : map F j u v f h ≫ parameter F j v = parameter F j u := by
  simpa using JTPrismChainGraphTransport.map_parameter (X F j N) (X F j M)
    (coarseParameter F j u) (coarseParameter F j v)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j) (𝟙 _)
    (Category.id_comp _) (mapWithTime f (oldTime F j))
    (parameter_natural f u v h (oldTime F j) (collapsedParameter F j))

/-- The coarse parameter for the collapsed graph is literally the inherited old parameter. -/
theorem collapsed_coarseParameter :
    coarseParameter F j (𝟙 (collapsedCodes F j)) = collapsedParameter F j := by
  rw [coarseParameter, mapWithTime_id, Category.id_comp]

abbrev triangleToCollapsed := JTWhiskeredSeamTarget.triangleToCollapsed (seam F j)
abbrev longToCollapsedNative :=
  JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.longToCollapsed F j)
abbrev detourToCollapsed :=
  JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.detourToTriangle F j) ≫
    triangleToCollapsed F j

abbrev collapsedGraph := graph F j (𝟙 (collapsedCodes F j))
abbrev collapsedProjection := projection F j (𝟙 (collapsedCodes F j))
abbrev collapsedTrace := parameter F j (𝟙 (collapsedCodes F j))
abbrev triangleGraph := graph F j (triangleToCollapsed F j)
abbrev longGraph := graph F j (longToCollapsedNative F j)
abbrev detourGraph := graph F j (detourToCollapsed F j)

/-- The full detour graph maps into the full triangle graph, without selecting lifts. -/
def detourToTriangle : detourGraph F j ⟶ triangleGraph F j :=
  map F j (detourToCollapsed F j) (triangleToCollapsed F j)
    (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.detourToTriangle F j)) rfl

/-- The full identity-edge graph maps into that SAME full triangle graph. -/
def longToTriangle : longGraph F j ⟶ triangleGraph F j :=
  map F j (longToCollapsedNative F j) (triangleToCollapsed F j)
    (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.longToTriangle F j))
    (JTWhiskeredSeamTarget.long_triangle_collapsed (seam F j))

/-- The same full identity-edge graph maps into the collapsed graph. -/
def longToCollapsed : longGraph F j ⟶ collapsedGraph F j :=
  map F j (longToCollapsedNative F j) (𝟙 _) (longToCollapsedNative F j) (Category.comp_id _)

end
end DaggerModels.PartII.JTSharedInsertionPhaseGraph
