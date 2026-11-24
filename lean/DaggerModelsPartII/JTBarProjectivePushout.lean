import DaggerModelsPartII.JTBarProjectiveCells

/-!
# Transporting the scalar successor pushout to the full bar diagram

The source and target of the diagrammatic attachment, its naturality,
and its commuting square are checked in `JTBarProjectiveCells`.
This module identifies the four edges after evaluation at every outer
reversal index with the retained scalar successor attachment.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels SSet

namespace DaggerModels.PartII.JTBarProjectivePushout

noncomputable section

open JTProjectiveBar JTBarNondegenerateCells JTBarProjectiveCells

/-- The represented outer arrow determines a generator of the evaluated
free boundary diagram, with the full nondegenerate label retained. -/
def pointwiseBoundaryInjection (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    (SSet.boundary r : SSet.{0}) ⟶
      (attachingBoundary P r).obj (op d) :=
  Sigma.ι (fun _ : op t.1.1.left ⟶ op d =>
      (SSet.boundary r : SSet.{0})) h ≫
    (Sigma.ι (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj (SSet.boundary r)) t).app (op d)

/-- The analogous generator of the evaluated free simplex diagram. -/
def pointwiseSimplexInjection (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    Δ[r] ⟶ (attachingSimplex P r).obj (op d) :=
  Sigma.ι (fun _ : op t.1.1.left ⟶ op d => Δ[r]) h ≫
    (Sigma.ι (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj Δ[r]) t).app (op d)

/-- On a represented generator, the pointwise boundary isomorphism is
the scalar coproduct injection at the corresponding bar simplex. -/
theorem pointwiseBoundaryIso_generator
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    pointwiseBoundaryInjection P d r t h ≫
        (pointwiseAttachingBoundaryIso P d r).hom =
      SSet.relativeCellComplexOfMono.ιA
        (pointwiseCellIndexEquiv P d r ⟨t, h⟩) := by
  simp only [pointwiseBoundaryInjection, pointwiseAttachingBoundaryIso,
    Iso.trans_hom, Category.assoc]
  simp only [ι_comp_sigmaObjIso_hom_assoc]
  simp only [sigmaSigmaIso_hom, Sigma.ι_desc_assoc]
  change Sigma.ι
      ((fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r =>
        (SSet.boundary r : SSet.{0})) ∘
        pointwiseCellIndexEquiv P d r) ⟨t, h⟩ ≫
        (Sigma.reindex (pointwiseCellIndexEquiv P d r)
          (fun _ : SSet.relativeCellComplexOfMono.ι
            (scalarInitialInclusion (barValue P d)) r =>
            (SSet.boundary r : SSet.{0}))).hom =
      Sigma.ι (fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r =>
        (SSet.boundary r : SSet.{0}))
        (pointwiseCellIndexEquiv P d r ⟨t, h⟩)
  exact Sigma.ι_reindex_hom (pointwiseCellIndexEquiv P d r)
    (fun _ : SSet.relativeCellComplexOfMono.ι
      (scalarInitialInclusion (barValue P d)) r =>
      (SSet.boundary r : SSet.{0})) ⟨t, h⟩

/-- On a represented generator, the pointwise simplex isomorphism is
the scalar coproduct injection at the same bar simplex. -/
theorem pointwiseSimplexIso_generator
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    pointwiseSimplexInjection P d r t h ≫
        (pointwiseAttachingSimplexIso P d r).hom =
      SSet.relativeCellComplexOfMono.ιB
        (pointwiseCellIndexEquiv P d r ⟨t, h⟩) := by
  simp only [pointwiseSimplexInjection, pointwiseAttachingSimplexIso,
    Iso.trans_hom, Category.assoc]
  simp only [ι_comp_sigmaObjIso_hom_assoc]
  simp only [sigmaSigmaIso_hom, Sigma.ι_desc_assoc]
  change Sigma.ι
      ((fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r => Δ[r]) ∘
        pointwiseCellIndexEquiv P d r) ⟨t, h⟩ ≫
        (Sigma.reindex (pointwiseCellIndexEquiv P d r)
          (fun _ : SSet.relativeCellComplexOfMono.ι
            (scalarInitialInclusion (barValue P d)) r => Δ[r])).hom =
      Sigma.ι (fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r => Δ[r])
        (pointwiseCellIndexEquiv P d r ⟨t, h⟩)
  exact Sigma.ι_reindex_hom (pointwiseCellIndexEquiv P d r)
    (fun _ : SSet.relativeCellComplexOfMono.ι
      (scalarInitialInclusion (barValue P d)) r => Δ[r]) ⟨t, h⟩

/-- The fourth edge of the scalar successor square: ordinary skeleton
inclusion agrees with the retained relative-skeleton inclusion. -/
theorem pointwiseStage_compat (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (barSkeletonMap P (Nat.le_succ r)).app (op d) ≫
        (scalarStageIso (barValue P d) (r + 1)).hom =
      (scalarStageIso (barValue P d) r).hom ≫
        SSet.relativeCellComplexOfMono.r
          (scalarInitialInclusion (barValue P d)) r := by
  apply NatTrans.ext
  funext q x
  apply Subtype.ext
  rfl

/-- The evaluated boundary attachment sends each represented boundary
generator to the same represented simplex generator. -/
theorem pointwiseBoundaryMap_generator
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    pointwiseBoundaryInjection P d r t h ≫
        (attachingBoundaryMap P r).app (op d) =
      (SSet.boundary r).ι ≫ pointwiseSimplexInjection P d r t h := by
  have houter := congrArg
    (fun η : (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).obj (SSet.boundary r) ⟶
        attachingSimplex P r => η.app (op d))
    (Sigma.ι_map (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).map (SSet.boundary r).ι) t)
  change (Sigma.ι (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj (SSet.boundary r)) t).app (op d) ≫
      (Limits.Sigma.map (fun t : NondegenerateLabel P r =>
        (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
          (op t.1.1.left)).map (SSet.boundary r).ι)).app (op d) =
    ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).map (SSet.boundary r).ι).app (op d) ≫
      (Sigma.ι (fun t : NondegenerateLabel P r =>
        (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
          (op t.1.1.left)).obj Δ[r]) t).app (op d) at houter
  simp only [pointwiseBoundaryInjection, pointwiseSimplexInjection,
    attachingBoundaryMap, Category.assoc]
  rw [houter]
  simp [ProjectiveKanDiagram.free, evaluationLeftAdjoint,
    Category.assoc]

/-- The represented boundary injections are jointly epimorphic after
evaluating the categorical coproduct of free outer diagrams. -/
theorem pointwiseBoundaryInjection_ext
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    {Z : SSet.{0}}
    (f g : (attachingBoundary P r).obj (op d) ⟶ Z)
    (h : ∀ (t : NondegenerateLabel P r)
      (k : op t.1.1.left ⟶ op d),
      pointwiseBoundaryInjection P d r t k ≫ f =
        pointwiseBoundaryInjection P d r t k ≫ g) : f = g := by
  let E := sigmaObjIso
    (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj (SSet.boundary r)) (op d)
  have H : E.inv ≫ f = E.inv ≫ g := by
    apply Sigma.hom_ext
    intro t
    apply Sigma.hom_ext
    intro k
    simpa only [pointwiseBoundaryInjection, E, Category.assoc,
      ι_comp_sigmaObjIso_inv_assoc] using h t k
  calc
    f = (E.hom ≫ E.inv) ≫ f := by simp
    _ = (E.hom ≫ E.inv) ≫ g := by
      simp only [Category.assoc, H]
    _ = g := by simp

/-- The evaluated top edge of the outer attachment corresponds to the
retained scalar coproduct of boundary inclusions. -/
theorem pointwiseBoundaryMap_compat
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ) :
    (attachingBoundaryMap P r).app (op d) ≫
        (pointwiseAttachingSimplexIso P d r).hom =
      (pointwiseAttachingBoundaryIso P d r).hom ≫
        SSet.relativeCellComplexOfMono.m
          (scalarInitialInclusion (barValue P d)) r := by
  apply pointwiseBoundaryInjection_ext P d r
  intro t k
  let s := pointwiseCellIndexEquiv P d r ⟨t, k⟩
  calc
    pointwiseBoundaryInjection P d r t k ≫
        ((attachingBoundaryMap P r).app (op d) ≫
          (pointwiseAttachingSimplexIso P d r).hom) =
      ((SSet.boundary r).ι ≫ pointwiseSimplexInjection P d r t k) ≫
        (pointwiseAttachingSimplexIso P d r).hom := by
          rw [← Category.assoc, pointwiseBoundaryMap_generator]
    _ = (SSet.boundary r).ι ≫
        SSet.relativeCellComplexOfMono.ιB s := by
          rw [Category.assoc, pointwiseSimplexIso_generator]
    _ = SSet.relativeCellComplexOfMono.ιA s ≫
        SSet.relativeCellComplexOfMono.m
          (scalarInitialInclusion (barValue P d)) r :=
      (SSet.relativeCellComplexOfMono.ιA_m s).symm
    _ = pointwiseBoundaryInjection P d r t k ≫
        ((pointwiseAttachingBoundaryIso P d r).hom ≫
          SSet.relativeCellComplexOfMono.m
            (scalarInitialInclusion (barValue P d)) r) := by
          rw [← Category.assoc, pointwiseBoundaryIso_generator]

/-- The represented simplex injections are jointly epimorphic after
evaluating the categorical coproduct of free outer diagrams. -/
theorem pointwiseSimplexInjection_ext
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    {Z : SSet.{0}}
    (f g : (attachingSimplex P r).obj (op d) ⟶ Z)
    (h : ∀ (t : NondegenerateLabel P r)
      (k : op t.1.1.left ⟶ op d),
      pointwiseSimplexInjection P d r t k ≫ f =
        pointwiseSimplexInjection P d r t k ≫ g) : f = g := by
  let E := sigmaObjIso
    (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj Δ[r]) (op d)
  have H : E.inv ≫ f = E.inv ≫ g := by
    apply Sigma.hom_ext
    intro t
    apply Sigma.hom_ext
    intro k
    simpa only [pointwiseSimplexInjection, E, Category.assoc,
      ι_comp_sigmaObjIso_inv_assoc] using h t k
  calc
    f = (E.hom ≫ E.inv) ≫ f := by simp
    _ = (E.hom ≫ E.inv) ≫ g := by
      simp only [Category.assoc, H]
    _ = g := by simp

/-- The top attachment sends a represented simplex generator to the
outer image of its distinguished labelled simplex. -/
theorem pointwiseTop_generator
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    pointwiseSimplexInjection P d r t h ≫
        (attachingTop P r).app (op d) =
      labelCellSucc P r t ≫ (barSkeleton P (r + 1)).map h := by
  simp [pointwiseSimplexInjection, attachingTop, freeLabelCellSucc,
    evaluationAdjunctionRight, Category.assoc]

/-- After the scalar stage isomorphism, that outer image is precisely
the retained scalar cell map at the corresponding nondegenerate bar
simplex. -/
theorem pointwiseTop_scalar_generator
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    (t : NondegenerateLabel P r)
    (h : op t.1.1.left ⟶ op d) :
    (labelCellSucc P r t ≫ (barSkeleton P (r + 1)).map h) ≫
        (scalarStageIso (barValue P d) (r + 1)).hom =
      SSet.relativeCellComplexOfMono.β
        (pointwiseCellIndexEquiv P d r ⟨t, h⟩) := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  change (barOuterMap P h.unop).app (op ⦋r⦌)
      (labelNondegenerate P r t).1 =
    (freeNondegenerateEquiv P d r ⟨t, h.unop⟩).1
  simpa only [freeNondegenerateOuterMap, Category.comp_id] using
    (freeNondegenerateEquiv_outer P h.unop r
      (⟨t, 𝟙 _⟩ : freeNondegenerateValue P t.1.1.left r)).symm

/-- The evaluated top edge agrees with the retained scalar `b` map. -/
theorem pointwiseTop_compat
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ) :
    (attachingTop P r).app (op d) ≫
        (scalarStageIso (barValue P d) (r + 1)).hom =
      (pointwiseAttachingSimplexIso P d r).hom ≫
        SSet.relativeCellComplexOfMono.b
          (scalarInitialInclusion (barValue P d)) r := by
  apply pointwiseSimplexInjection_ext P d r
  intro t h
  let s := pointwiseCellIndexEquiv P d r ⟨t, h⟩
  calc
    pointwiseSimplexInjection P d r t h ≫
        ((attachingTop P r).app (op d) ≫
          (scalarStageIso (barValue P d) (r + 1)).hom) =
      (labelCellSucc P r t ≫ (barSkeleton P (r + 1)).map h) ≫
        (scalarStageIso (barValue P d) (r + 1)).hom := by
          rw [← Category.assoc, pointwiseTop_generator]
    _ = SSet.relativeCellComplexOfMono.β s :=
      pointwiseTop_scalar_generator P d r t h
    _ = SSet.relativeCellComplexOfMono.ιB s ≫
        SSet.relativeCellComplexOfMono.b
          (scalarInitialInclusion (barValue P d)) r := by
          rw [SSet.relativeCellComplexOfMono.ιB_b]
    _ = pointwiseSimplexInjection P d r t h ≫
        ((pointwiseAttachingSimplexIso P d r).hom ≫
          SSet.relativeCellComplexOfMono.b
            (scalarInitialInclusion (barValue P d)) r) := by
          rw [← Category.assoc, pointwiseSimplexIso_generator]

/-- The remaining boundary-to-old-stage edge follows by cancellation
of the scalar skeletal inclusion. The outer and scalar squares commute,
and the other three edges have already been identified. -/
theorem pointwiseLeft_compat
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ) :
    (attachingLeft P r).app (op d) ≫
        (scalarStageIso (barValue P d) r).hom =
      (pointwiseAttachingBoundaryIso P d r).hom ≫
        SSet.relativeCellComplexOfMono.t
          (scalarInitialInclusion (barValue P d)) r := by
  let X := barValue P d
  let i := scalarInitialInclusion X
  rw [← cancel_mono (SSet.relativeCellComplexOfMono.r i r)]
  calc
    ((attachingLeft P r).app (op d) ≫
        (scalarStageIso X r).hom) ≫
        SSet.relativeCellComplexOfMono.r i r =
      (attachingLeft P r).app (op d) ≫
        ((barSkeletonMap P (Nat.le_succ r)).app (op d) ≫
          (scalarStageIso X (r + 1)).hom) := by
            rw [pointwiseStage_compat]
            rfl
    _ = ((attachingLeft P r ≫
          barSkeletonMap P (Nat.le_succ r)).app (op d)) ≫
            (scalarStageIso X (r + 1)).hom := rfl
    _ = ((attachingBoundaryMap P r ≫
          attachingTop P r).app (op d)) ≫
            (scalarStageIso X (r + 1)).hom := by
              rw [attachingSquare_comm]
    _ = (attachingBoundaryMap P r).app (op d) ≫
        ((attachingTop P r).app (op d) ≫
          (scalarStageIso X (r + 1)).hom) := rfl
    _ = (attachingBoundaryMap P r).app (op d) ≫
        ((pointwiseAttachingSimplexIso P d r).hom ≫
          SSet.relativeCellComplexOfMono.b i r) := by
            rw [pointwiseTop_compat]
    _ = ((pointwiseAttachingBoundaryIso P d r).hom ≫
        SSet.relativeCellComplexOfMono.m i r) ≫
          SSet.relativeCellComplexOfMono.b i r := by
            rw [← Category.assoc, pointwiseBoundaryMap_compat]
    _ = (pointwiseAttachingBoundaryIso P d r).hom ≫
        (SSet.relativeCellComplexOfMono.t i r ≫
          SSet.relativeCellComplexOfMono.r i r) := by
            rw [SSet.relativeCellComplexOfMono.w]
            simp only [Category.assoc]
    _ = ((pointwiseAttachingBoundaryIso P d r).hom ≫
        SSet.relativeCellComplexOfMono.t i r) ≫
          SSet.relativeCellComplexOfMono.r i r := by
            simp only [Category.assoc]

/-- Each evaluated attachment square is the retained scalar successor
pushout transported across the four explicit pointwise isomorphisms. -/
theorem pointwiseAttaching_isPushout
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ) :
    IsPushout
      ((attachingLeft P r).app (op d))
      ((attachingBoundaryMap P r).app (op d))
      ((barSkeletonMap P (Nat.le_succ r)).app (op d))
      ((attachingTop P r).app (op d)) := by
  let X := barValue P d
  let i := scalarInitialInclusion X
  apply (scalarInitialPushout X r).of_iso'
    (pointwiseAttachingBoundaryIso P d r)
    (scalarStageIso X r)
    (pointwiseAttachingSimplexIso P d r)
    (scalarStageIso X (r + 1))
  · exact (pointwiseLeft_compat P d r).symm
  · exact (pointwiseBoundaryMap_compat P d r).symm
  · exact (pointwiseStage_compat P d r).symm
  · exact (pointwiseTop_compat P d r).symm

/-- The actual outer bar skeleton successor is a pushout of the
projective free boundary coproduct indexed by full reversal chains. -/
theorem attaching_isPushout
    (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    IsPushout
      (attachingLeft P r)
      (attachingBoundaryMap P r)
      (barSkeletonMap P (Nat.le_succ r))
      (attachingTop P r) where
  w := attachingSquare_comm P r
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun d => by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (pointwiseAttaching_isPushout P d.unop r).isColimit)⟩

end

end DaggerModels.PartII.JTBarProjectivePushout
