import DaggerModelsPartII.JTSharedInsertionNativeAssembly
import DaggerModelsPartII.JTSharedInsertionNormalizedSeam
import DaggerModelsPartII.JTNativeCutPointAssembly
import DaggerModelsPartII.JTWhiskeredSeamTarget

/-!
# The corrected insertion seam over the same original native target

The full modified left and right surroundings collapse naturally into the old
cuts at the inserted vertex. The complete collapsed and triangle phases then
map into the SAME original necklace and fixed Q. Original coefficient projections
remain separate from the old time parameter. No raw-label equation or global
finite-support contraction is asserted by this native construction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionSeamNative

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private theorem wedge_square {P P' R R' C C' D D' : NecklaceCode}
    (f : NecklaceCode.Hom.{0} P P') (g : NecklaceCode.Hom.{0} R R')
    (l : NecklaceCode.Hom.{0} P C) (l' : NecklaceCode.Hom.{0} P' C')
    (r : NecklaceCode.Hom.{0} R D) (r' : NecklaceCode.Hom.{0} R' D')
    (u : NecklaceCode.Hom.{0} C C') (v : NecklaceCode.Hom.{0} D D')
    (hl : NecklaceCode.Hom.comp f l' = NecklaceCode.Hom.comp l u)
    (hr : NecklaceCode.Hom.comp g r' = NecklaceCode.Hom.comp r v) :
    NecklaceCode.Hom.comp
        (wedgeMap f (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) g))
        (wedgeMap l' (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) r')) =
      NecklaceCode.Hom.comp
        (wedgeMap l (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) r))
        (wedgeMap u (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) v)) := by
  rw [← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp]
  exact congrArg₂ wedgeMap hl (congrArg₂ wedgeMap rfl hr)

private theorem native_assoc {A B C D : NecklaceCode}
    (f : NecklaceCode.Hom.{0} A B) (g : NecklaceCode.Hom.{0} B C)
    (h : NecklaceCode.Hom.{0} C D) :
    NecklaceCode.Hom.comp (NecklaceCode.Hom.comp f g) h =
      NecklaceCode.Hom.comp f (NecklaceCode.Hom.comp g h) :=
  NecklaceCode.Hom.ext (Category.assoc f.map g.map h.map)

private def reindexedCompose {I J B : Type} [SmallCategory I] [SmallCategory J]
    [SmallCategory B] (G : J ⥤ I) (O : I ⥤ B) (C : B ⥤ NecklaceCode)
    {P : I ⥤ NecklaceCode} {R : J ⥤ NecklaceCode}
    (α : P ⟶ O ⋙ C) (β : R ⟶ G ⋙ P) : R ⟶ (G ⋙ O) ⋙ C :=
  β ≫ Functor.whiskerLeft G α

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev I := JTSharedInsertionChoices.Index F j
private abbrev old := JTSharedInsertionNormalizedSeam.oldFamily F j
private abbrev P := JTSharedInsertionSeamSurroundings.leftNative F j
private abbrev R := JTSharedInsertionSeamSurroundings.rightNative F j
private abbrev originalBase := JTSharedInsertionChainSupport.originalBase F j
private abbrev marked := JTSharedInsertionChainSupport.marks F j 1
private abbrev T (p : I F j) := (codes L).obj ((originalBase F j).obj p)
private abbrev v (p : I F j) := ((marked F j).obj p).2.val
private abbrev l := JTSharedInsertionNativeAssembly.leftToCut F j
private abbrev r := JTSharedInsertionNativeAssembly.rightToCut F j

/-- The complete corrected split label maps naturally into the original source. -/
def oldAssembly : codes (old F j).labels ⟶ originalBase F j ⋙ codes L where
  app p :=
    wedgeMap ((l F j).app p) (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) ((r F j).app p)) ≫
      JTNativeCutPointAssembly.assembly (T F j p) (v F j p)
  naturality {p q} g := by
    have h := congrArg Prod.fst (JTWhiskeredSeamDiagram.Family.arrow_projection (old F j) g)
    change (codes (old F j).labels).map g =
      wedgeMap ((P F j).map g) (wedgeMap (NecklaceCode.Hom.id.{0} (single 0)) ((R F j).map g)) at h
    rw [h]
    have hs := wedge_square ((P F j).map g) ((R F j).map g)
      ((l F j).app p) ((l F j).app q) ((r F j).app p) ((r F j).app q)
      ((JTSharedInsertionNativeAssembly.leftCuts F j).map g)
      ((JTSharedInsertionNativeAssembly.rightCuts F j).map g)
      ((l F j).naturality g) ((r F j).naturality g)
    have ha := JTNativeCutPointAssembly.assembly_natural
      ((codes L).map ((originalBase F j).map g)) (v F j p) (v F j q)
      (JTExactlyMarkedSourceDiagram.cut_map F j ((marked F j).map g))
    change NecklaceCode.Hom.comp _ (NecklaceCode.Hom.comp _ _) =
      NecklaceCode.Hom.comp (NecklaceCode.Hom.comp _ _) _
    rw [← native_assoc, hs, native_assoc]
    change NecklaceCode.Hom.comp _
      (NecklaceCode.Hom.comp _ (JTNativeCutPointAssembly.assembly (T F j q) (v F j q))) = _
    have ha' : NecklaceCode.Hom.comp
        (wedgeMap ((JTSharedInsertionNativeAssembly.leftCuts F j).map g)
          (wedgeMap (NecklaceCode.Hom.id.{0} (single 0))
            ((JTSharedInsertionNativeAssembly.rightCuts F j).map g)))
        (JTNativeCutPointAssembly.assembly (T F j q) (v F j q)) =
      NecklaceCode.Hom.comp (JTNativeCutPointAssembly.assembly (T F j p) (v F j p))
        ((codes L).map ((originalBase F j).map g)) := ha
    rw [ha', ← native_assoc]
    rfl


/-- All actual higher relative seam choices and their full chains. -/
abbrev Index := JTSharedInsertionNormalizedSeam.Index F j

/-- The same original source object and every original operator under the seam cover. -/
abbrev original := JTSharedInsertionNormalizedSeam.original F j

private abbrev base := JTSharedInsertionSeamTriangles.toOriginal F j
private abbrev seam := JTSharedInsertionNormalizedSeam.seamFamily F j

set_option maxHeartbeats 850000 in
/-- Collapse the entire corrected identity phase into the original source naturally. -/
def collapsedNative :
    codes (JTWhiskeredSeamDiagram.collapsedFamily (seam F j)).labels ⟶
      original F j ⋙ codes L :=
  reindexedCompose (base F j) (originalBase F j) (codes L) (oldAssembly F j)
    (JTWhiskeredSeamTarget.nativeOf (JTSharedInsertionNormalizedSeam.collapsedToOld F j))

/-- The complete actual triangle returns to the SAME original native source. -/
def wholeNative : codes (seam F j).triangle.labels ⟶ original F j ⋙ codes L :=
  JTWhiskeredSeamTarget.triangleToCollapsed (seam F j) ≫ collapsedNative F j

/-- The whole collapsed phase reaches the original fixed Q naturally. -/
def collapsedTarget :
    codes (JTWhiskeredSeamDiagram.collapsedFamily (seam F j)).labels ⟶
      (Functor.const (Index F j)).obj Q.code :=
  collapsedNative F j ≫ Functor.whiskerLeft (original F j) F.collapse

/-- This whole triangle has the original fixed target Q, with both old endpoints. -/
def triangleTarget :=
  JTWhiskeredSeamTarget.triangleTarget (seam F j) Q (collapsedTarget F j)

/-- The triangle target is the full native assembly followed by the old collapse. -/
theorem triangleTarget_whole : triangleTarget F j =
    wholeNative F j ≫ Functor.whiskerLeft (original F j) F.collapse := by
  dsimp only [triangleTarget, JTWhiskeredSeamTarget.triangleTarget,
    collapsedTarget, wholeNative]
  rw [Category.assoc]

/-- The complete long edge has that SAME original target. -/
def longTarget := JTWhiskeredSeamTarget.longTarget (seam F j) Q (collapsedTarget F j)

/-- The complete two-edge detour has that SAME original target. -/
def detourTarget := JTWhiskeredSeamTarget.detourTarget (seam F j) Q (collapsedTarget F j)

/-- The whole detour-to-triangle comparison commutes over original Q. -/
theorem detour_target_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.detourToTriangle F j) ≫ triangleTarget F j =
      detourTarget F j :=
  JTWhiskeredSeamTarget.detour_target_square (seam F j) Q (collapsedTarget F j)

/-- The whole long-edge-to-triangle comparison commutes over original Q. -/
theorem long_target_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.longToTriangle F j) ≫ triangleTarget F j =
      longTarget F j :=
  JTWhiskeredSeamTarget.long_target_square (seam F j) Q (collapsedTarget F j)

/-- The identity-edge collapse also commutes over that same original Q. -/
theorem collapsed_target_square :
    JTWhiskeredSeamTarget.nativeOf
        (JTSharedInsertionNormalizedSeam.longToCollapsed F j) ≫ collapsedTarget F j =
      longTarget F j :=
  JTWhiskeredSeamTarget.collapsed_target_square (seam F j) Q (collapsedTarget F j)

end
end DaggerModels.PartII.JTSharedInsertionSeamNative
