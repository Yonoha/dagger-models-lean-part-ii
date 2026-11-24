import DaggerModelsPartII.JTActualJointChainSideGraph
import DaggerModelsPartII.JTWhiskerEdgeGraphRaw
import DaggerModelsPartII.JTActualJointChainInverseFace

/-! Raw evaluation of corrected side labels on the full chain graph covers. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointChainSideRaw

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private theorem pullback_point {X Y Z : SSet.{0}} (h : X ⟶ Z) (i : Y ⟶ Z)
    (n : ℕ) (x : X.obj (op ⦋n⦌)) (y : Y.obj (op ⦋n⦌))
    (w : h.app _ x = i.app _ y) :
    ∃ z, (pullback.fst h i).app (op ⦋n⦌) z = x := by
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback h i).map ((evaluation _ _).obj (op ⦋n⦌))) x y w
  exact ⟨z, hz⟩

/-- The two inverse images of the native beads cover any source over their wedge. -/
theorem binary_cover {T U : NecklaceCode} {X : SSet.{0}}
    (h : X ⟶ (wedge T U).toSSet) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (∃ z, (pullback.fst h (wedgeιLeft T U)).app (op ⦋n⦌) z = x) ∨
      (∃ z, (pullback.fst h (wedgeιRight T U)).app (op ⦋n⦌) z = x) := by
  rcases wedge_degree_cover T U (h.app (op ⦋n⦌) x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl (pullback_point h _ n x y hy.symm)
  · exact Or.inr (pullback_point h _ n x y hy.symm)

/-- Equality of raw maps is detected on the actual two inverse images. -/
theorem binary_hom_ext {T U : NecklaceCode} {X Y : SSet.{0}}
    (h : X ⟶ (wedge T U).toSSet) {p q : X ⟶ Y}
    (hl : pullback.fst h (wedgeιLeft T U) ≫ p =
      pullback.fst h (wedgeιLeft T U) ≫ q)
    (hr : pullback.fst h (wedgeιRight T U) ≫ p =
      pullback.fst h (wedgeιRight T U) ≫ q) : p = q := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  funext x
  rcases binary_cover h n x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · simpa only [SSet.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app hl (op ⦋n⦌)) z
  · simpa only [SSet.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app hr (op ⦋n⦌)) z

private theorem lift_pre {X Y Z I : SSet.{0}} (f : X ⟶ Y)
    (h : Y ⟶ Z) (t : Y ⟶ I) :
    f ≫ lift h t = lift (f ≫ h) (f ≫ t) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]

private theorem inverseImage_projection {X B C I : SSet.{0}}
    (π : X ⟶ B ⊗ I) (i : C ⟶ B) :
    pullback.fst (π ≫ fst B I) i ≫ π =
      lift (pullback.snd (π ≫ fst B I) i)
        (pullback.fst (π ≫ fst B I) i ≫ π ≫ snd B I) ≫
          (i ⊗ₘ 𝟙 I) := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, tensorHom_fst, lift_fst_assoc, Category.comp_id] using
      (pullback.condition :
        pullback.fst (π ≫ fst B I) i ≫ (π ≫ fst B I) =
          pullback.snd (π ≫ fst B I) i ≫ i)
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]


private theorem lift_tensor {X B C I : SSet.{0}} (a : X ⟶ B) (t : X ⟶ I)
    (i : B ⟶ C) : lift a t ≫ (i ⊗ₘ 𝟙 I) = lift (a ≫ i) t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]


private theorem lift_product_parameter {X B I K : SSet.{0}}
    (h : X ⟶ B) (t : X ⟶ I) (p : B ⊗ I ⟶ K) :
    lift h (lift h t ≫ p) = lift h t ≫ lift (fst B I) p := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]


private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev choice := JTActualJointChoiceChainGraph.base F j
private abbrev marked := choice F j ⋙ JTActualJointChoiceCover.projection F j
private abbrev original := marked F j ⋙ JTExactlyMarkedSourceDiagram.base F j
private abbrev old (p : I F j) := (original F j).obj p
private abbrev v (p : I F j) := ((marked F j).obj p).2.val
private abbrev hv (p : I F j) := ((marked F j).obj p).2.property
private abbrev α (p : I F j) := (JTActualJointChoiceChainGraph.toOriginal F j).app p
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev Cleft (p : I F j) := JTActualJointChainSideLabels.leftCoefficients F j p
private abbrev Cright (p : I F j) := JTActualJointChainSideLabels.rightCoefficients F j p
private abbrev leftCode (p : I F j) :=
  ((JTActualJointChainSideGraph.leftCodes F j).obj p)
private abbrev rightCode (p : I F j) :=
  ((JTActualJointChainSideGraph.rightCodes F j).obj p)
private abbrev t (p : I F j) := J.obj ((JTActualJointChainSideGraph.oldTime F j).obj p)
private abbrev m (p : I F j) :=
  (JTActualJointChoiceChainGraph.ordinals F j).obj p

/-- The native coordinate of the covered left graph. -/
abbrev leftNativeCoordinate (p : I F j) :
    (JTActualJointChainSideGraph.leftGraph F j).obj p ⟶ (leftCode F j p).toSSet :=
  (JTActualJointChainSideGraph.leftProjection F j).app p ≫
    fst (leftCode F j p).toSSet (t F j p)

/-- The native coordinate of the covered right graph. -/
abbrev rightNativeCoordinate (p : I F j) :
    (JTActualJointChainSideGraph.rightGraph F j).obj p ⟶ (rightCode F j p).toSSet :=
  (JTActualJointChainSideGraph.rightProjection F j).app p ≫
    fst (rightCode F j p).toSSet (t F j p)

private abbrev leftTimeCoordinate (p : I F j) :=
  (JTActualJointChainSideGraph.leftProjection F j).app p ≫
    snd (leftCode F j p).toSSet (t F j p)
private abbrev rightTimeCoordinate (p : I F j) :=
  (JTActualJointChainSideGraph.rightProjection F j).app p ≫
    snd (rightCode F j p).toSSet (t F j p)

private abbrev leftTheta (p : I F j) :=
  (JTActualJointChainSideGraph.leftParameter F j).app p
private abbrev rightTheta (p : I F j) :=
  (JTActualJointChainSideGraph.rightParameter F j).app p

private theorem leftProjection_lift (p : I F j) :
    lift (leftNativeCoordinate F j p) (leftTimeCoordinate F j p) =
      (JTActualJointChainSideGraph.leftProjection F j).app p := by
  apply CartesianMonoidalCategory.hom_ext
  · exact lift_fst _ _
  · exact lift_snd _ _

private theorem rightProjection_lift (p : I F j) :
    lift (rightNativeCoordinate F j p) (rightTimeCoordinate F j p) =
      (JTActualJointChainSideGraph.rightProjection F j).app p := by
  apply CartesianMonoidalCategory.hom_ext
  · exact lift_fst _ _
  · exact lift_snd _ _

private theorem leftTheta_projection (p : I F j) :
    leftTheta F j p ≫ J.map (α F j p) =
      (JTActualJointChainSideGraph.leftProjection F j).app p ≫
        (JTActualJointChainSideGraph.leftCoarseParameter F j).app p :=
  NatTrans.congr_app (JTActualJointChainSideGraph.leftParameter_projection F j) p

private theorem rightTheta_projection (p : I F j) :
    rightTheta F j p ≫ J.map (α F j p) =
      (JTActualJointChainSideGraph.rightProjection F j).app p ≫
        (JTActualJointChainSideGraph.rightCoarseParameter F j).app p :=
  NatTrans.congr_app (JTActualJointChainSideGraph.rightParameter_projection F j) p


private abbrev leftCut (p : I F j) := cutLeft ((codes L).obj (old F j p)) (v F j p)
private abbrev rightCut (p : I F j) := cutRight ((codes L).obj (old F j p)) (v F j p)
private abbrev leftCutι (p : I F j) := wedgeιLeft (leftCut F j p) E
private abbrev leftEdgeι (p : I F j) := wedgeιRight (leftCut F j p) E
private abbrev rightEdgeι (p : I F j) := wedgeιLeft E (rightCut F j p)
private abbrev rightCutι (p : I F j) := wedgeιRight E (rightCut F j p)

private abbrev lcut₁ (p : I F j) :=
  pullback.fst (leftNativeCoordinate F j p) (leftCutι F j p)
private abbrev lcut₂ (p : I F j) :=
  pullback.snd (leftNativeCoordinate F j p) (leftCutι F j p)
private abbrev ledge₁ (p : I F j) :=
  pullback.fst (leftNativeCoordinate F j p) (leftEdgeι F j p)
private abbrev ledge₂ (p : I F j) :=
  pullback.snd (leftNativeCoordinate F j p) (leftEdgeι F j p)
private abbrev rcut₁ (p : I F j) :=
  pullback.fst (rightNativeCoordinate F j p) (rightCutι F j p)
private abbrev rcut₂ (p : I F j) :=
  pullback.snd (rightNativeCoordinate F j p) (rightCutι F j p)
private abbrev redge₁ (p : I F j) :=
  pullback.fst (rightNativeCoordinate F j p) (rightEdgeι F j p)
private abbrev redge₂ (p : I F j) :=
  pullback.snd (rightNativeCoordinate F j p) (rightEdgeι F j p)

private theorem leftCut_projection (p : I F j) :
    lcut₁ F j p ≫ (JTActualJointChainSideGraph.leftProjection F j).app p =
      lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTimeCoordinate F j p) ≫
        (leftCutι F j p ⊗ₘ 𝟙 (t F j p)) :=
  inverseImage_projection ((JTActualJointChainSideGraph.leftProjection F j).app p)
    (leftCutι F j p)

private theorem leftEdge_projection (p : I F j) :
    ledge₁ F j p ≫ (JTActualJointChainSideGraph.leftProjection F j).app p =
      lift (ledge₂ F j p) (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫
        (leftEdgeι F j p ⊗ₘ 𝟙 (t F j p)) :=
  inverseImage_projection ((JTActualJointChainSideGraph.leftProjection F j).app p)
    (leftEdgeι F j p)

private theorem rightCut_projection (p : I F j) :
    rcut₁ F j p ≫ (JTActualJointChainSideGraph.rightProjection F j).app p =
      lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTimeCoordinate F j p) ≫
        (rightCutι F j p ⊗ₘ 𝟙 (t F j p)) :=
  inverseImage_projection ((JTActualJointChainSideGraph.rightProjection F j).app p)
    (rightCutι F j p)

private theorem rightEdge_projection (p : I F j) :
    redge₁ F j p ≫ (JTActualJointChainSideGraph.rightProjection F j).app p =
      lift (redge₂ F j p) (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫
        (rightEdgeι F j p ⊗ₘ 𝟙 (t F j p)) :=
  inverseImage_projection ((JTActualJointChainSideGraph.rightProjection F j).app p)
    (rightEdgeι F j p)

private theorem leftCut_parameter (p : I F j) :
    (lcut₁ F j p ≫ leftTheta F j p) ≫ J.map (α F j p) =
      lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTimeCoordinate F j p) ≫
        JTActualJointCutPrism.leftParameter F (old F j p) (v F j p) := by
  rw [Category.assoc, leftTheta_projection, ← Category.assoc, leftCut_projection,
    Category.assoc, JTActualJointChainSideGraph.leftCoarse_interior]

private theorem rightCut_parameter (p : I F j) :
    (rcut₁ F j p ≫ rightTheta F j p) ≫ J.map (α F j p) =
      lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTimeCoordinate F j p) ≫
        JTActualJointCutPrism.rightParameter F (old F j p) (v F j p) := by
  rw [Category.assoc, rightTheta_projection, ← Category.assoc, rightCut_projection,
    Category.assoc, JTActualJointChainSideGraph.rightCoarse_interior]


private theorem leftEdge_parameter (p : I F j) :
    (ledge₁ F j p ≫ leftTheta F j p) ≫ J.map (α F j p) =
      lift (ledge₂ F j p ≫ term E.toSSet)
        (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫
          JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p) := by
  rw [Category.assoc, leftTheta_projection, ← Category.assoc, leftEdge_projection,
    Category.assoc, JTActualJointChainSideGraph.leftCoarse_whisker]
  change lift (ledge₂ F j p) (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫
    ((term E.toSSet ⊗ₘ 𝟙 (t F j p)) ≫
      JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p)) = _
  rw [← Category.assoc, lift_tensor]

private theorem rightEdge_parameter (p : I F j) :
    (redge₁ F j p ≫ rightTheta F j p) ≫ J.map (α F j p) =
      lift (redge₂ F j p ≫ term E.toSSet)
        (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫
          JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p) := by
  rw [Category.assoc, rightTheta_projection, ← Category.assoc, rightEdge_projection,
    Category.assoc, JTActualJointChainSideGraph.rightCoarse_whisker]
  change lift (redge₂ F j p) (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫
    ((term E.toSSet ⊗ₘ 𝟙 (t F j p)) ≫
      JTActualSourceJointSupport.timeParameter F (old F j p) (v F j p)) = _
  rw [← Category.assoc, lift_tensor]


private abbrev oldFaceParameter (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (old F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j
      (v F j p) (hv F j p))

private theorem leftEdge_factor (p : I F j) :
    (ledge₁ F j p ≫ leftTheta F j p) ≫ J.map (α F j p) =
      (lift (ledge₂ F j p ≫ term E.toSSet)
        (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫ oldFaceParameter F j p) ≫
          J.map ((JTExactlyMarkedSourceDiagram.incl F j).app ((marked F j).obj p)) := by
  rw [leftEdge_parameter]
  have ht := (JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
    (v F j p) (hv F j p)).symm
  exact (congrArg (fun q ↦ lift (ledge₂ F j p ≫ term E.toSSet)
    (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫ q) ht).trans
      ((Category.assoc _ _ _).symm)

private theorem rightEdge_factor (p : I F j) :
    (redge₁ F j p ≫ rightTheta F j p) ≫ J.map (α F j p) =
      (lift (redge₂ F j p ≫ term E.toSSet)
        (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫ oldFaceParameter F j p) ≫
          J.map ((JTExactlyMarkedSourceDiagram.incl F j).app ((marked F j).obj p)) := by
  rw [rightEdge_parameter]
  have ht := (JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
    (v F j p) (hv F j p)).symm
  exact (congrArg (fun q ↦ lift (redge₂ F j p ≫ term E.toSSet)
    (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫ q) ht).trans
      ((Category.assoc _ _ _).symm)


private theorem leftEdge_eval (p : I F j) :
    lift (ledge₂ F j p) (ledge₁ F j p ≫ leftTheta F j p) ≫
      realizedLabel E.toSSet W (m F j p)
        (SSet.yonedaEquiv ((JTActualJointChoiceChainGraph.chainEnding F j).app p ≫
          TwoBeadEndpointLabel.edgeLabelFromRow W)) =
    ledge₂ F j p ≫ term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) :=
  JTActualJointChainInverseFace.ending_raw F j p (ledge₂ F j p)
    (ledge₁ F j p ≫ leftTheta F j p)
    (lift (ledge₂ F j p ≫ term E.toSSet)
      (ledge₁ F j p ≫ leftTimeCoordinate F j p) ≫ oldFaceParameter F j p)
    (leftEdge_factor F j p)

private theorem rightEdge_eval (p : I F j) :
    lift (redge₂ F j p) (redge₁ F j p ≫ rightTheta F j p) ≫
      realizedLabel E.toSSet W (m F j p)
        (SSet.yonedaEquiv ((JTActualJointChoiceChainGraph.chainStarting F j).app p ≫
          TwoBeadEndpointLabel.edgeLabelFromRow W)) =
    redge₂ F j p ≫ term E.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W (z j)) :=
  JTActualJointChainInverseFace.starting_raw F j p (redge₂ F j p)
    (redge₁ F j p ≫ rightTheta F j p)
    (lift (redge₂ F j p ≫ term E.toSSet)
      (redge₁ F j p ≫ rightTimeCoordinate F j p) ≫ oldFaceParameter F j p)
    (rightEdge_factor F j p)


private theorem leftCut_eval (p : I F j) :
    lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p) ≫
      realizedLabel (leftCut F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv ((Cleft F j p).left)) =
    lcut₂ F j p ≫ cutLeftι ((codes L).obj (old F j p)) (v F j p) ≫
      (F.collapse.app (old F j p)).map ≫ Q.map := by
  let t' := lcut₁ F j p ≫ leftTimeCoordinate F j p
  let p' := JTActualJointCutPrism.leftParameter F (old F j p) (v F j p)
  let c' := JTActualJointCutPrism.leftCoefficient (L := L) (old F j p) (v F j p)
  have hc := JTWhiskerEdgeGraphRaw.coefficient_reindex W (α F j p)
    (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p) c'
  change lift (lcut₂ F j p) ((lcut₁ F j p ≫ leftTheta F j p) ≫ J.map (α F j p)) ≫
      realizedLabel (leftCut F j p).toSSet W _ (SSet.yonedaEquiv c') =
    lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p) ≫
      realizedLabel (leftCut F j p).toSSet W _
        (SSet.yonedaEquiv (SSet.stdSimplex.map (α F j p) ≫ c')) at hc
  change lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p) ≫
    realizedLabel (leftCut F j p).toSSet W (m F j p)
      (SSet.yonedaEquiv (SSet.stdSimplex.map (α F j p) ≫ c')) = _
  rw [← hc, leftCut_parameter]
  have hraw := JTActualJointCutPrism.left_raw F (old F j p) (v F j p)
  change lift (fst (leftCut F j p).toSSet (t F j p)) p' ≫
      realizedLabel (leftCut F j p).toSSet W _ (SSet.yonedaEquiv c') =
    fst (leftCut F j p).toSSet (t F j p) ≫
      cutLeftι ((codes L).obj (old F j p)) (v F j p) ≫
        (F.collapse.app (old F j p)).map ≫ Q.map at hraw
  rw [lift_product_parameter]
  have hpre := congrArg (fun q ↦ lift (lcut₂ F j p) t' ≫ q) hraw
  simpa only [Category.assoc, lift_fst_assoc] using hpre


private theorem rightCut_eval (p : I F j) :
    lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p) ≫
      realizedLabel (rightCut F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv ((Cright F j p).right)) =
    rcut₂ F j p ≫ cutRightι ((codes L).obj (old F j p)) (v F j p) ≫
      (F.collapse.app (old F j p)).map ≫ Q.map := by
  let t' := rcut₁ F j p ≫ rightTimeCoordinate F j p
  let p' := JTActualJointCutPrism.rightParameter F (old F j p) (v F j p)
  let c' := JTActualJointCutPrism.rightCoefficient (L := L) (old F j p) (v F j p)
  have hc := JTWhiskerEdgeGraphRaw.coefficient_reindex W (α F j p)
    (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p) c'
  change lift (rcut₂ F j p) ((rcut₁ F j p ≫ rightTheta F j p) ≫ J.map (α F j p)) ≫
      realizedLabel (rightCut F j p).toSSet W _ (SSet.yonedaEquiv c') =
    lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p) ≫
      realizedLabel (rightCut F j p).toSSet W _
        (SSet.yonedaEquiv (SSet.stdSimplex.map (α F j p) ≫ c')) at hc
  change lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p) ≫
    realizedLabel (rightCut F j p).toSSet W (m F j p)
      (SSet.yonedaEquiv (SSet.stdSimplex.map (α F j p) ≫ c')) = _
  rw [← hc, rightCut_parameter]
  have hraw := JTActualJointCutPrism.right_raw F (old F j p) (v F j p)
  change lift (fst (rightCut F j p).toSSet (t F j p)) p' ≫
      realizedLabel (rightCut F j p).toSSet W _ (SSet.yonedaEquiv c') =
    fst (rightCut F j p).toSSet (t F j p) ≫
      cutRightι ((codes L).obj (old F j p)) (v F j p) ≫
        (F.collapse.app (old F j p)).map ≫ Q.map at hraw
  rw [lift_product_parameter]
  have hpre := congrArg (fun q ↦ lift (rcut₂ F j p) t' ≫ q) hraw
  simpa only [Category.assoc, lift_fst_assoc] using hpre


private theorem leftCut_restrict (p : I F j) :
    lcut₁ F j p ≫
        (lift (leftNativeCoordinate F j p) (leftTheta F j p) ≫
          realizedLabel (leftCode F j p).toSSet W (m F j p)
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cleft F j p)))) =
      lift (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p) ≫
        realizedLabel (leftCut F j p).toSSet W (m F j p)
          (SSet.yonedaEquiv (Cleft F j p).left) := by
  rw [← Category.assoc, lift_pre]
  have hp : lcut₁ F j p ≫ leftNativeCoordinate F j p =
      lcut₂ F j p ≫ leftCutι F j p := pullback.condition
  rw [hp]
  have h := JTWhiskerEdgeGraphRaw.native_restrict W (leftCutι F j p)
    (lcut₂ F j p) (lcut₁ F j p ≫ leftTheta F j p)
    (JTComposedPrismLabels.coefficient (Cleft F j p))
  simpa only [JTComposedPrismLabels.coefficient,
    TripleBeadEndpointLabel.glue_left] using h

private theorem leftEdge_restrict (p : I F j) :
    ledge₁ F j p ≫
        (lift (leftNativeCoordinate F j p) (leftTheta F j p) ≫
          realizedLabel (leftCode F j p).toSSet W (m F j p)
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cleft F j p)))) =
      lift (ledge₂ F j p) (ledge₁ F j p ≫ leftTheta F j p) ≫
        realizedLabel E.toSSet W (m F j p)
          (SSet.yonedaEquiv (Cleft F j p).right) := by
  rw [← Category.assoc, lift_pre]
  have hp : ledge₁ F j p ≫ leftNativeCoordinate F j p =
      ledge₂ F j p ≫ leftEdgeι F j p := pullback.condition
  rw [hp]
  have h := JTWhiskerEdgeGraphRaw.native_restrict W (leftEdgeι F j p)
    (ledge₂ F j p) (ledge₁ F j p ≫ leftTheta F j p)
    (JTComposedPrismLabels.coefficient (Cleft F j p))
  simpa only [JTComposedPrismLabels.coefficient,
    TripleBeadEndpointLabel.glue_right] using h

private theorem rightEdge_restrict (p : I F j) :
    redge₁ F j p ≫
        (lift (rightNativeCoordinate F j p) (rightTheta F j p) ≫
          realizedLabel (rightCode F j p).toSSet W (m F j p)
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cright F j p)))) =
      lift (redge₂ F j p) (redge₁ F j p ≫ rightTheta F j p) ≫
        realizedLabel E.toSSet W (m F j p)
          (SSet.yonedaEquiv (Cright F j p).left) := by
  rw [← Category.assoc, lift_pre]
  have hp : redge₁ F j p ≫ rightNativeCoordinate F j p =
      redge₂ F j p ≫ rightEdgeι F j p := pullback.condition
  rw [hp]
  have h := JTWhiskerEdgeGraphRaw.native_restrict W (rightEdgeι F j p)
    (redge₂ F j p) (redge₁ F j p ≫ rightTheta F j p)
    (JTComposedPrismLabels.coefficient (Cright F j p))
  simpa only [JTComposedPrismLabels.coefficient,
    TripleBeadEndpointLabel.glue_left] using h

private theorem rightCut_restrict (p : I F j) :
    rcut₁ F j p ≫
        (lift (rightNativeCoordinate F j p) (rightTheta F j p) ≫
          realizedLabel (rightCode F j p).toSSet W (m F j p)
            (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cright F j p)))) =
      lift (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p) ≫
        realizedLabel (rightCut F j p).toSSet W (m F j p)
          (SSet.yonedaEquiv (Cright F j p).right) := by
  rw [← Category.assoc, lift_pre]
  have hp : rcut₁ F j p ≫ rightNativeCoordinate F j p =
      rcut₂ F j p ≫ rightCutι F j p := pullback.condition
  rw [hp]
  have h := JTWhiskerEdgeGraphRaw.native_restrict W (rightCutι F j p)
    (rcut₂ F j p) (rcut₁ F j p ≫ rightTheta F j p)
    (JTComposedPrismLabels.coefficient (Cright F j p))
  simpa only [JTComposedPrismLabels.coefficient,
    TripleBeadEndpointLabel.glue_right] using h

/-- The corrected left label evaluates to the actual left target on the full chain cover. -/
theorem left_raw (p : I F j) :
    lift (leftNativeCoordinate F j p) (leftTheta F j p) ≫
      realizedLabel (leftCode F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cleft F j p))) =
    leftNativeCoordinate F j p ≫
      ((JTActualJointChainSideGraph.leftNative F j).app p).map ≫
        (JTActualJointMarkedEvaluation.left Q j).map := by
  apply binary_hom_ext (leftNativeCoordinate F j p)
  · have hcut := (leftCut_restrict F j p).trans (leftCut_eval F j p)
    have hp : lcut₁ F j p ≫ leftNativeCoordinate F j p =
        lcut₂ F j p ≫ leftCutι F j p := pullback.condition
    calc
      _ = lcut₂ F j p ≫ cutLeftι ((codes L).obj (old F j p)) (v F j p) ≫
            (F.collapse.app (old F j p)).map ≫ Q.map := by
          simpa only [Category.assoc] using hcut
      _ = _ := by
        have hn := congrArg (fun q ↦ q ≫
          ((JTActualJointChainSideGraph.leftNative F j).app p).map ≫
            (JTActualJointMarkedEvaluation.left Q j).map) hp
        change (lcut₁ F j p ≫ leftNativeCoordinate F j p) ≫
            (JTActualJointSideWhiskerNative.leftNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map =
          (lcut₂ F j p ≫ leftCutι F j p) ≫
            (JTActualJointSideWhiskerNative.leftNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map at hn
        have hnative := congrArg (fun q ↦ lcut₂ F j p ≫ q)
          (JTActualJointSideWhiskerNative.left_raw_interior Q j
            (F.collapse.app (old F j p)) (v F j p) (hv F j p))
        have hn' : lcut₂ F j p ≫
            (leftCutι F j p ≫
              (JTActualJointSideWhiskerNative.leftNative Q j
                (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map) =
          lcut₁ F j p ≫ leftNativeCoordinate F j p ≫
            ((JTActualJointChainSideGraph.leftNative F j).app p).map ≫
              (JTActualJointMarkedEvaluation.left Q j).map := by
          simpa only [Category.assoc] using hn.symm
        simpa only [Category.assoc] using hnative.symm.trans hn'
  · have hedge := (leftEdge_restrict F j p).trans (leftEdge_eval F j p)
    have hp : ledge₁ F j p ≫ leftNativeCoordinate F j p =
        ledge₂ F j p ≫ leftEdgeι F j p := pullback.condition
    have hc : (JTOrderedLabelJointInsertion.toPoint E).map =
        term E.toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    calc
      _ = ledge₂ F j p ≫ term E.toSSet ≫
            SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
          simpa only [Category.assoc] using hedge
      _ = _ := by
        have hn := congrArg (fun q ↦ q ≫
          ((JTActualJointChainSideGraph.leftNative F j).app p).map ≫
            (JTActualJointMarkedEvaluation.left Q j).map) hp
        change (ledge₁ F j p ≫ leftNativeCoordinate F j p) ≫
            (JTActualJointSideWhiskerNative.leftNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map =
          (ledge₂ F j p ≫ leftEdgeι F j p) ≫
            (JTActualJointSideWhiskerNative.leftNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map at hn
        have ht := congrArg (fun g ↦ ledge₂ F j p ≫ term E.toSSet ≫ g)
          (JTJointPaddedOverlapEvaluation.target_map (Q := Q) j).symm
        have hnative := congrArg (fun q ↦ ledge₂ F j p ≫ q)
          (JTActualJointSideWhiskerNative.left_raw_whisker Q j
            (F.collapse.app (old F j p)) (v F j p) (hv F j p))
        have hn' : ledge₂ F j p ≫
            (leftEdgeι F j p ≫
              (JTActualJointSideWhiskerNative.leftNative Q j
                (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.left Q j).map) =
          ledge₁ F j p ≫ leftNativeCoordinate F j p ≫
            ((JTActualJointChainSideGraph.leftNative F j).app p).map ≫
              (JTActualJointMarkedEvaluation.left Q j).map := by
          simpa only [Category.assoc] using hn.symm
        have hresult := hnative.symm.trans hn'
        simp only [Category.assoc, hc] at hresult
        simpa only [Category.assoc] using ht.symm.trans hresult


/-- The corrected right label evaluates to the actual right target on the full chain cover. -/
theorem right_raw (p : I F j) :
    lift (rightNativeCoordinate F j p) (rightTheta F j p) ≫
      realizedLabel (rightCode F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (Cright F j p))) =
    rightNativeCoordinate F j p ≫
      ((JTActualJointChainSideGraph.rightNative F j).app p).map ≫
        (JTActualJointMarkedEvaluation.right Q j).map := by
  apply binary_hom_ext (rightNativeCoordinate F j p)
  · have hedge := (rightEdge_restrict F j p).trans (rightEdge_eval F j p)
    have hp : redge₁ F j p ≫ rightNativeCoordinate F j p =
        redge₂ F j p ≫ rightEdgeι F j p := pullback.condition
    have hc : (JTOrderedLabelJointInsertion.toPoint E).map =
        term E.toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    calc
      _ = redge₂ F j p ≫ term E.toSSet ≫
            SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
          simpa only [Category.assoc] using hedge
      _ = _ := by
        have hn := congrArg (fun q ↦ q ≫
          ((JTActualJointChainSideGraph.rightNative F j).app p).map ≫
            (JTActualJointMarkedEvaluation.right Q j).map) hp
        change (redge₁ F j p ≫ rightNativeCoordinate F j p) ≫
            (JTActualJointSideWhiskerNative.rightNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map =
          (redge₂ F j p ≫ rightEdgeι F j p) ≫
            (JTActualJointSideWhiskerNative.rightNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map at hn
        have ht := congrArg (fun g ↦ redge₂ F j p ≫ term E.toSSet ≫ g)
          (JTJointPaddedOverlapEvaluation.target_map (Q := Q) j).symm
        have hnative := congrArg (fun q ↦ redge₂ F j p ≫ q)
          (JTActualJointSideWhiskerNative.right_raw_whisker Q j
            (F.collapse.app (old F j p)) (v F j p) (hv F j p))
        have hn' : redge₂ F j p ≫
            (rightEdgeι F j p ≫
              (JTActualJointSideWhiskerNative.rightNative Q j
                (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map) =
          redge₁ F j p ≫ rightNativeCoordinate F j p ≫
            ((JTActualJointChainSideGraph.rightNative F j).app p).map ≫
              (JTActualJointMarkedEvaluation.right Q j).map := by
          simpa only [Category.assoc] using hn.symm
        have hresult := hnative.symm.trans hn'
        simp only [Category.assoc, hc] at hresult
        simpa only [Category.assoc] using ht.symm.trans hresult
  · have hcut := (rightCut_restrict F j p).trans (rightCut_eval F j p)
    have hp : rcut₁ F j p ≫ rightNativeCoordinate F j p =
        rcut₂ F j p ≫ rightCutι F j p := pullback.condition
    calc
      _ = rcut₂ F j p ≫ cutRightι ((codes L).obj (old F j p)) (v F j p) ≫
            (F.collapse.app (old F j p)).map ≫ Q.map := by
          simpa only [Category.assoc] using hcut
      _ = _ := by
        have hn := congrArg (fun q ↦ q ≫
          ((JTActualJointChainSideGraph.rightNative F j).app p).map ≫
            (JTActualJointMarkedEvaluation.right Q j).map) hp
        change (rcut₁ F j p ≫ rightNativeCoordinate F j p) ≫
            (JTActualJointSideWhiskerNative.rightNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map =
          (rcut₂ F j p ≫ rightCutι F j p) ≫
            (JTActualJointSideWhiskerNative.rightNative Q j
              (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map at hn
        have hnative := congrArg (fun q ↦ rcut₂ F j p ≫ q)
          (JTActualJointSideWhiskerNative.right_raw_interior Q j
            (F.collapse.app (old F j p)) (v F j p) (hv F j p))
        have hn' : rcut₂ F j p ≫
            (rightCutι F j p ≫
              (JTActualJointSideWhiskerNative.rightNative Q j
                (F.collapse.app (old F j p)) (v F j p) (hv F j p)).map ≫
                (JTActualJointMarkedEvaluation.right Q j).map) =
          rcut₁ F j p ≫ rightNativeCoordinate F j p ≫
            ((JTActualJointChainSideGraph.rightNative F j).app p).map ≫
              (JTActualJointMarkedEvaluation.right Q j).map := by
          simpa only [Category.assoc] using hn.symm
        simpa only [Category.assoc] using hnative.symm.trans hn'


end
end DaggerModels.PartII.JTActualJointChainSideRaw
