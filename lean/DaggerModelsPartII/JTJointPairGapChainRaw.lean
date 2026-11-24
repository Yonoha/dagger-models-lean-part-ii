import DaggerModelsPartII.JTJointPairGapChainGraph
import DaggerModelsPartII.JTActualJointChainInverseFace
import DaggerModelsPartII.JTWhiskerEdgeGraphRaw

/-! Raw evaluation of the fully padded gap on the common pair-chain graph. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointPairGapChainRaw

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

private theorem pullback_point {X Y Z : SSet.{0}} (h : X ⟶ Z) (i : Y ⟶ Z)
    (n : ℕ) (x : X.obj (op ⦋n⦌)) (y : Y.obj (op ⦋n⦌))
    (w : h.app _ x = i.app _ y) :
    ∃ z, (pullback.fst h i).app (op ⦋n⦌) z = x := by
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback h i).map ((evaluation _ _).obj (op ⦋n⦌))) x y w
  exact ⟨z, hz⟩

private theorem triple_cover {T : NecklaceCode} {X : SSet.{0}}
    (h : X ⟶ (wedge E (wedge T E)).toSSet) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (∃ z, (pullback.fst h (wedgeιLeft E (wedge T E))).app (op ⦋n⦌) z = x) ∨
      (∃ z, (pullback.fst h
        (wedgeιLeft T E ≫ wedgeιRight E (wedge T E))).app (op ⦋n⦌) z = x) ∨
      (∃ z, (pullback.fst h
        (wedgeιRight T E ≫ wedgeιRight E (wedge T E))).app (op ⦋n⦌) z = x) := by
  rcases wedge_degree_cover E (wedge T E) (h.app (op ⦋n⦌) x) with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl (pullback_point h _ n x y hy.symm)
  · rcases wedge_degree_cover T E y with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact Or.inr (Or.inl (pullback_point h _ n x z
        ((congrArg ((wedgeιRight E (wedge T E)).app (op ⦋n⦌)) hz).trans hy).symm))
    · exact Or.inr (Or.inr (pullback_point h _ n x z
        ((congrArg ((wedgeιRight E (wedge T E)).app (op ⦋n⦌)) hz).trans hy).symm))

/-- Equality of simplicial maps is detected on all three actual native inverse images. -/
theorem triple_hom_ext {T : NecklaceCode} {X Y : SSet.{0}}
    (h : X ⟶ (wedge E (wedge T E)).toSSet) {p q : X ⟶ Y}
    (hf : pullback.fst h (wedgeιLeft E (wedge T E)) ≫ p =
      pullback.fst h (wedgeιLeft E (wedge T E)) ≫ q)
    (hi : pullback.fst h (wedgeιLeft T E ≫ wedgeιRight E (wedge T E)) ≫ p =
      pullback.fst h (wedgeιLeft T E ≫ wedgeιRight E (wedge T E)) ≫ q)
    (hb : pullback.fst h (wedgeιRight T E ≫ wedgeιRight E (wedge T E)) ≫ p =
      pullback.fst h (wedgeιRight T E ≫ wedgeιRight E (wedge T E)) ≫ q) : p = q := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  funext x
  rcases triple_cover h n x with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
  · simpa only [SSet.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app hf (op ⦋n⦌)) z
  · simpa only [SSet.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app hi (op ⦋n⦌)) z
  · simpa only [SSet.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app hb (op ⦋n⦌)) z

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev G := JTJointPairGapChainGraph.graph F j
private abbrev π := JTJointPairGapChainGraph.projection F j
private abbrev θ := JTJointPairGapChainGraph.parameter F j
private abbrev pair (p : I F j) := (JTJointPairGapChainLabels.oldPairs F j).obj p
private abbrev a (p : I F j) := (JTJointPairSourceDiagram.base F j).obj (pair F j p)
private abbrev v (p : I F j) := (pair F j p).2.left.val
private abbrev w (p : I F j) := (pair F j p).2.right.val
private abbrev hv (p : I F j) := (pair F j p).2.left.property
private abbrev hw (p : I F j) := (pair F j p).2.right.property
private abbrev B (p : I F j) := JTJointPairGapDiagram.code F j (pair F j p)
private abbrev C (p : I F j) := JTJointPairGapChainLabels.coefficients F j p
private abbrev code (p : I F j) := JTJointPairGapChainLabels.code F j p
private abbrev m (p : I F j) := (JTJointPairChainDiagram.ordinals F j).obj p
private abbrev α (p : I F j) := (JTJointPairChainDiagram.toOriginal F j).app p
private abbrev oldTime (p : I F j) :=
  J.obj ((JTJointPairGapChainParameter.oldTime F j).obj p)
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

private abbrev native (p : I F j) : (G F j).obj p ⟶ (code F j p).toSSet :=
  (π F j).app p ≫ fst (code F j p).toSSet (oldTime F j p)
private abbrev clock (p : I F j) : (G F j).obj p ⟶ oldTime F j p :=
  (π F j).app p ≫ snd (code F j p).toSSet (oldTime F j p)

private theorem θ_projection (p : I F j) :
    (θ F j).app p ≫ J.map (α F j p) =
      (π F j).app p ≫ (JTJointPairGapChainParameter.coarseParameter F j).app p :=
  NatTrans.congr_app (JTJointPairGapChainGraph.parameter_projection F j) p

private abbrev fι (p : I F j) := JTJointPairGapChainLabels.frontInclusion F j p
private abbrev iι (p : I F j) := JTJointPairGapChainLabels.interiorInclusion F j p
private abbrev bι (p : I F j) := JTJointPairGapChainLabels.backInclusion F j p
private abbrev f₁ (p : I F j) := pullback.fst (native F j p) (fι F j p)
private abbrev f₂ (p : I F j) := pullback.snd (native F j p) (fι F j p)
private abbrev i₁ (p : I F j) := pullback.fst (native F j p) (iι F j p)
private abbrev i₂ (p : I F j) := pullback.snd (native F j p) (iι F j p)
private abbrev b₁ (p : I F j) := pullback.fst (native F j p) (bι F j p)
private abbrev b₂ (p : I F j) := pullback.snd (native F j p) (bι F j p)

private theorem lift_pre {X Y Z I : SSet.{0}} (f : X ⟶ Y)
    (h : Y ⟶ Z) (t : Y ⟶ I) :
    f ≫ lift h t = lift (f ≫ h) (f ≫ t) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simp only [Category.assoc, lift_snd]

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

private theorem piece_projection {S : NecklaceCode} (p : I F j)
    (i : S.toSSet ⟶ (code F j p).toSSet) :
    (pullback.fst (native F j p) i ≫ (θ F j).app p) ≫ J.map (α F j p) =
      lift (pullback.snd (native F j p) i)
        (pullback.fst (native F j p) i ≫ clock F j p) ≫
          (i ⊗ₘ 𝟙 (oldTime F j p)) ≫
            JTJointPairGapChainParameter.parameter F j p := by
  let u := pullback.fst (native F j p) i
  let v := pullback.snd (native F j p) i
  have hp : u ≫ native F j p = v ≫ i := pullback.condition
  have hπ : lift (native F j p) (clock F j p) = (π F j).app p := by
    apply CartesianMonoidalCategory.hom_ext
    · exact lift_fst _ _
    · exact lift_snd _ _
  calc
    _ = u ≫ (π F j).app p ≫
          (JTJointPairGapChainParameter.coarseParameter F j).app p := by
        rw [Category.assoc, θ_projection]
    _ = lift (u ≫ native F j p) (u ≫ clock F j p) ≫
          JTJointPairGapChainParameter.parameter F j p := by
        rw [← lift_pre, hπ]
        rfl
    _ = lift (v ≫ i) (u ≫ clock F j p) ≫
          JTJointPairGapChainParameter.parameter F j p := by rw [hp]
    _ = _ := by rw [← lift_tensor, Category.assoc]

private theorem piece_restrict {S : NecklaceCode} (p : I F j)
    (i : S.toSSet ⟶ (code F j p).toSSet)
    (c : std.obj (m F j p) ⟶ TripleBeadEndpointLabel.labels W S)
    (hc : JTComposedPrismLabels.coefficient (C F j p) ≫ pre W i = c) :
    pullback.fst (native F j p) i ≫
      (lift (native F j p) ((θ F j).app p) ≫
        realizedLabel (code F j p).toSSet W (m F j p)
          (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (C F j p)))) =
      lift (pullback.snd (native F j p) i)
        (pullback.fst (native F j p) i ≫ (θ F j).app p) ≫
          realizedLabel S.toSSet W (m F j p) (SSet.yonedaEquiv c) := by
  rw [← Category.assoc, lift_pre]
  have hp : pullback.fst (native F j p) i ≫ native F j p =
      pullback.snd (native F j p) i ≫ i := pullback.condition
  rw [hp]
  have hr := JTWhiskerEdgeGraphRaw.native_restrict W i
    (pullback.snd (native F j p) i)
    (pullback.fst (native F j p) i ≫ (θ F j).app p)
    (JTComposedPrismLabels.coefficient (C F j p))
  simpa only [hc] using hr

private theorem piece_constant {S : NecklaceCode} (p : I F j)
    (i : S.toSSet ⟶ (code F j p).toSSet) :
    pullback.fst (native F j p) i ≫
      (native F j p ≫ term (code F j p).toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j))) =
      pullback.snd (native F j p) i ≫ term S.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  have hp : pullback.fst (native F j p) i ≫ native F j p =
      pullback.snd (native F j p) i ≫ i := pullback.condition
  have ht : i ≫ term (code F j p).toSSet = term S.toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hn := congrArg (fun q ↦ q ≫ term (code F j p).toSSet ≫
    SSet.yonedaEquiv.symm (rawVertex W (z j))) hp
  have hi := congrArg (fun q ↦ pullback.snd (native F j p) i ≫ q ≫
    SSet.yonedaEquiv.symm (rawVertex W (z j))) ht
  simpa only [Category.assoc] using hn.trans hi

private theorem interior_parameter (p : I F j) :
    (i₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
      lift (i₂ F j p) (i₁ F j p ≫ clock F j p) ≫
        JTJointPairGapChainParameter.oldParameter F j p := by
  have hp := piece_projection F j p (iι F j p)
  have hr := congrArg (fun q ↦
    lift (i₂ F j p) (i₁ F j p ≫ clock F j p) ≫ q)
      (JTJointPairGapChainParameter.parameter_interior F j p)
  simp only [Category.assoc] at hp hr
  exact hp.trans hr

private theorem interior_eval (p : I F j) :
    lift (i₂ F j p) (i₁ F j p ≫ (θ F j).app p) ≫
      realizedLabel (B F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv (JTJointPairGapChainLabels.gapCoefficient F j p)) =
      i₂ F j p ≫ term (B F j p).toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  let t' := i₁ F j p ≫ clock F j p
  let p' := JTJointPairGapChainParameter.oldParameter F j p
  let c' := JTJointPairGapDiagram.coefficient F j (pair F j p)
  have hc := JTWhiskerEdgeGraphRaw.coefficient_reindex W (α F j p)
    (i₂ F j p) (i₁ F j p ≫ (θ F j).app p) c'
  change lift (i₂ F j p) ((i₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p)) ≫
      realizedLabel (B F j p).toSSet W _ (SSet.yonedaEquiv c') =
    lift (i₂ F j p) (i₁ F j p ≫ (θ F j).app p) ≫
      realizedLabel (B F j p).toSSet W _
        (SSet.yonedaEquiv (std.map (α F j p) ≫ c')) at hc
  change lift (i₂ F j p) (i₁ F j p ≫ (θ F j).app p) ≫
    realizedLabel (B F j p).toSSet W (m F j p)
      (SSet.yonedaEquiv (std.map (α F j p) ≫ c')) = _
  rw [← hc, interior_parameter]
  have hraw := JTJointPairGapDiagram.raw_constant F j (pair F j p)
  change lift (fst (B F j p).toSSet (oldTime F j p)) p' ≫
      realizedLabel (B F j p).toSSet W _ (SSet.yonedaEquiv c') =
    fst (B F j p).toSSet (oldTime F j p) ≫
      term (B F j p).toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j)) at hraw
  rw [lift_product_parameter]
  have hpre := congrArg (fun q ↦ lift (i₂ F j p) t' ≫ q) hraw
  simpa only [Category.assoc, lift_fst_assoc] using hpre

private theorem front_parameter (p : I F j) :
    (f₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
      lift (f₂ F j p ≫ term E.toSSet) (f₁ F j p ≫ clock F j p) ≫
        JTActualSourceJointSupport.timeParameter F (a F j p) (v F j p) := by
  have hp := piece_projection F j p (fι F j p)
  have hr := congrArg (fun q ↦
    lift (f₂ F j p) (f₁ F j p ≫ clock F j p) ≫ q)
      (JTJointPairGapChainParameter.parameter_front F j p)
  simp only [Category.assoc] at hp hr
  have ht := hp.trans hr
  change (f₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
    lift (f₂ F j p) (f₁ F j p ≫ clock F j p) ≫
      ((term E.toSSet ⊗ₘ 𝟙 (oldTime F j p)) ≫
        JTActualSourceJointSupport.timeParameter F (a F j p) (v F j p)) at ht
  rw [← Category.assoc, lift_tensor] at ht
  exact ht

private theorem back_parameter (p : I F j) :
    (b₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
      lift (b₂ F j p ≫ term E.toSSet) (b₁ F j p ≫ clock F j p) ≫
        JTActualSourceJointSupport.timeParameter F (a F j p) (w F j p) := by
  have hp := piece_projection F j p (bι F j p)
  have hr := congrArg (fun q ↦
    lift (b₂ F j p) (b₁ F j p ≫ clock F j p) ≫ q)
      (JTJointPairGapChainParameter.parameter_back F j p)
  simp only [Category.assoc] at hp hr
  have ht := hp.trans hr
  change (b₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
    lift (b₂ F j p) (b₁ F j p ≫ clock F j p) ≫
      ((term E.toSSet ⊗ₘ 𝟙 (oldTime F j p)) ≫
        JTActualSourceJointSupport.timeParameter F (a F j p) (w F j p)) at ht
  rw [← Category.assoc, lift_tensor] at ht
  exact ht

private abbrev frontOldFaceParameter (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (a F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (a F j p) j
      (v F j p) (hv F j p))

private abbrev backOldFaceParameter (p : I F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (a F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (a F j p) j
      (w F j p) (hw F j p))

private theorem front_factor (p : I F j) :
    (f₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
      (lift (f₂ F j p ≫ term E.toSSet) (f₁ F j p ≫ clock F j p) ≫
        frontOldFaceParameter F j p) ≫
          J.map ((JTExactlyMarkedSourceDiagram.incl F j).app
            ((JTJointPairSourceDiagram.leftCut F j).obj (pair F j p))) := by
  rw [front_parameter]
  have ht := (JTActualSourceJointSupport.timeParameter_factor F (a F j p) j
    (v F j p) (hv F j p)).symm
  exact (congrArg (fun q ↦ lift (f₂ F j p ≫ term E.toSSet)
    (f₁ F j p ≫ clock F j p) ≫ q) ht).trans ((Category.assoc _ _ _).symm)

private theorem back_factor (p : I F j) :
    (b₁ F j p ≫ (θ F j).app p) ≫ J.map (α F j p) =
      (lift (b₂ F j p ≫ term E.toSSet) (b₁ F j p ≫ clock F j p) ≫
        backOldFaceParameter F j p) ≫
          J.map ((JTExactlyMarkedSourceDiagram.incl F j).app
            ((JTJointPairSourceDiagram.rightCut F j).obj (pair F j p))) := by
  rw [back_parameter]
  have ht := (JTActualSourceJointSupport.timeParameter_factor F (a F j p) j
    (w F j p) (hw F j p)).symm
  exact (congrArg (fun q ↦ lift (b₂ F j p ≫ term E.toSSet)
    (b₁ F j p ≫ clock F j p) ≫ q) ht).trans ((Category.assoc _ _ _).symm)

private theorem front_eval (p : I F j) :
    lift (f₂ F j p) (f₁ F j p ≫ (θ F j).app p) ≫
      realizedLabel E.toSSet W (m F j p)
        (SSet.yonedaEquiv
          (JTJointPairGapChainLabels.coefficients F j p).left) =
      f₂ F j p ≫ term E.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j)) :=
  JTActualJointChainInverseFace.starting_raw F j
    ((JTJointPairChainDiagram.earlier F j).obj p) (f₂ F j p)
    (f₁ F j p ≫ (θ F j).app p)
    (lift (f₂ F j p ≫ term E.toSSet) (f₁ F j p ≫ clock F j p) ≫
      frontOldFaceParameter F j p) (front_factor F j p)

private theorem back_eval (p : I F j) :
    lift (b₂ F j p) (b₁ F j p ≫ (θ F j).app p) ≫
      realizedLabel E.toSSet W (m F j p)
        (SSet.yonedaEquiv
          (JTActualJointChainSideLabels.leftCoefficients F j
            ((JTJointPairChainDiagram.later F j).obj p)).right) =
      b₂ F j p ≫ term E.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W (z j)) :=
  JTActualJointChainInverseFace.ending_raw F j
    ((JTJointPairChainDiagram.later F j).obj p) (b₂ F j p)
    (b₁ F j p ≫ (θ F j).app p)
    (lift (b₂ F j p ≫ term E.toSSet) (b₁ F j p ≫ clock F j p) ≫
      backOldFaceParameter F j p) (back_factor F j p)

/-- The graph's padded label has the literal joint raw value in all simplicial degrees. -/
theorem raw (p : I F j) :
    lift (native F j p) ((θ F j).app p) ≫
      realizedLabel (code F j p).toSSet W (m F j p)
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient (C F j p))) =
    native F j p ≫ term (code F j p).toSSet ≫
      SSet.yonedaEquiv.symm (rawVertex W (z j)) := by
  apply triple_hom_ext (native F j p)
  · calc
      _ = lift (f₂ F j p) (f₁ F j p ≫ (θ F j).app p) ≫
            realizedLabel E.toSSet W (m F j p)
              (SSet.yonedaEquiv (C F j p).left) :=
        piece_restrict F j p (fι F j p) (C F j p).left
          (JTJointPairGapChainLabels.coefficient_front F j p)
      _ = f₂ F j p ≫ term E.toSSet ≫
            SSet.yonedaEquiv.symm (rawVertex W (z j)) := front_eval F j p
      _ = _ := (piece_constant F j p (fι F j p)).symm
  · calc
      _ = lift (i₂ F j p) (i₁ F j p ≫ (θ F j).app p) ≫
            realizedLabel (B F j p).toSSet W (m F j p)
              (SSet.yonedaEquiv (JTJointPairGapChainLabels.gapCoefficient F j p)) :=
        piece_restrict F j p (iι F j p)
          (JTJointPairGapChainLabels.gapCoefficient F j p)
          (JTJointPairGapChainLabels.coefficient_interior F j p)
      _ = i₂ F j p ≫ term (B F j p).toSSet ≫
            SSet.yonedaEquiv.symm (rawVertex W (z j)) := interior_eval F j p
      _ = _ := (piece_constant F j p (iι F j p)).symm
  · calc
      _ = lift (b₂ F j p) (b₁ F j p ≫ (θ F j).app p) ≫
            realizedLabel E.toSSet W (m F j p)
              (SSet.yonedaEquiv
                (JTActualJointChainSideLabels.leftCoefficients F j
                  ((JTJointPairChainDiagram.later F j).obj p)).right) :=
        piece_restrict F j p (bι F j p) _
          (JTJointPairGapChainLabels.coefficient_back F j p)
      _ = b₂ F j p ≫ term E.toSSet ≫
            SSet.yonedaEquiv.symm (rawVertex W (z j)) := back_eval F j p
      _ = _ := (piece_constant F j p (bι F j p)).symm

end
end DaggerModels.PartII.JTJointPairGapChainRaw
