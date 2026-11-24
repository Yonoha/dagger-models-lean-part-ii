import DaggerModelsPartII.JTBarFreePresheaf
import DaggerModelsPartII.ProjectiveKanDiagram
import TopCatModelCategory.SSet.Skeleton
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Outer-natural skeletal filtration of the full reversal-index bar

The scalar simplicial skeleton is applied to every outer value of the
actual bar and restricted along every outer reversal morphism. The
natural free-cell labels are supplied by `JTBarFreePresheaf`. The
successor attaching square and projective cofibrancy require further
identification with free boundary diagrams.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels SSet

namespace DaggerModels.PartII.JTBarProjectiveCells

noncomputable section

open JTProjectiveBar JTBarChains JTBarNondegenerateCells JTBarFreePresheaf

/-- A map of simplicial sets sends the `n`-skeleton into the `n`-skeleton.
This uses the native `Subcomplex.image_ofSimplex` and the defining iSup of
`skeleton`; no scalar cell attachment is reproved. -/
theorem skeleton_image_le {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n := by
  change (⨆ i : Fin n, ⨆ x : X.nonDegenerate i,
    Subcomplex.ofSimplex x.1).image f ≤ Y.skeleton n
  rw [Subcomplex.image_iSup]
  simp only [iSup_le_iff]
  intro i
  rw [Subcomplex.image_iSup]
  simp only [iSup_le_iff]
  intro x
  rw [Subcomplex.image_ofSimplex]
  exact Y.ofSimplex_le_skeleton (f.app (op ⦋i⦌) x.1) i.2

/-- At each outer index, the stage is the actual scalar `n`-skeleton.
The action is the restriction of the checked outer bar map. -/
def barSkeleton (P : ReverseSimplexᵒᵖ ⥤ Type) (n : ℕ) :
    ReverseSimplexᵒᵖ ⥤ SSet.{0} where
  obj d := (barValue P d.unop).skeleton n
  map {d e} f :=
    Subcomplex.lift
      (((barValue P d.unop).skeleton n).ι ≫ (barPresheaf P).map f)
      (by
        rw [← Subcomplex.image_eq_range]
        exact skeleton_image_le ((barPresheaf P).map f) n)
  map_id d := by
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    change ((barPresheaf P).map (𝟙 d)).app q x.1 = x.1
    rw [(barPresheaf P).map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    change ((barPresheaf P).map (f ≫ g)).app q x.1 =
      ((barPresheaf P).map g).app q (((barPresheaf P).map f).app q x.1)
    rw [(barPresheaf P).map_comp]
    rfl

/-- The natural inclusion of one skeleton stage into a later stage. -/
def barSkeletonMap (P : ReverseSimplexᵒᵖ ⥤ Type)
    {n m : ℕ} (h : n ≤ m) : barSkeleton P n ⟶ barSkeleton P m where
  app d := Subcomplex.homOfLE
    ((barValue P d.unop).skeleton.monotone h)
  naturality := by
    intro d e f
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    rfl

/-- The actual outer-diagram filtration indexed by natural numbers. -/
def barSkeletalDiagram (P : ReverseSimplexᵒᵖ ⥤ Type) :
    ℕ ⥤ ReverseSimplexᵒᵖ ⥤ SSet.{0} where
  obj n := barSkeleton P n
  map f := barSkeletonMap P (leOfHom f)
  map_id n := by
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    rfl

/-- The zero skeleton is initial at each outer index. -/
def scalarSkeletonZeroIsInitial (X : SSet.{0}) :
    IsInitial ((X.skeleton 0 : X.Subcomplex) : SSet.{0}) :=
  (Subcomplex.isInitialBot (X := X)).ofIso
    (Subcomplex.eqToIso (X.skeleton_zero).symm)

/-- The zero stage is the initial object of the outer diagram category. -/
def barSkeletonZeroIsInitial (P : ReverseSimplexᵒᵖ ⥤ Type) :
    IsInitial (barSkeleton P 0) :=
  IsInitial.ofUniqueHom
    (fun F =>
      { app d := (scalarSkeletonZeroIsInitial (barValue P d.unop)).to (F.obj d)
        naturality := by
          intro d e f
          apply (scalarSkeletonZeroIsInitial (barValue P d.unop)).hom_ext })
    (fun F η => by
      apply NatTrans.ext
      funext d
      apply (scalarSkeletonZeroIsInitial (barValue P d.unop)).hom_ext)
/-- Each skeleton stage includes naturally into the full bar diagram. -/
def barSkeletonIncl (P : ReverseSimplexᵒᵖ ⥤ Type)
    (n : ℕ) : barSkeleton P n ⟶ barPresheaf P where
  app d := ((barValue P d.unop).skeleton n).ι
  naturality := by
    intro d e f
    apply NatTrans.ext
    funext q x
    rfl

/-- The skeletal stages and their inclusions form the actual colimit
candidate in the outer diagram category. -/
def barSkeletalCocone (P : ReverseSimplexᵒᵖ ⥤ Type) :
    Cocone (barSkeletalDiagram P) where
  pt := barPresheaf P
  ι :=
    { app n := barSkeletonIncl P n
      naturality := by
        intro n m f
        apply NatTrans.ext
        funext d
        apply NatTrans.ext
        funext q x
        rfl }

/-- The outer-diagram skeletal filtration has the full bar as its
colimit. Pointwise colimits are reflected by evaluation; each scalar
colimit is the native complete-lattice colimit of all skeletons. -/
noncomputable def barSkeletalCocone_isColimit
    (P : ReverseSimplexᵒᵖ ⥤ Type) :
    IsColimit (barSkeletalCocone P) := by
  apply evaluationJointlyReflectsColimits _
  intro d
  let X : SSet.{0} := barValue P d.unop
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves Subcomplex.toPresheafFunctor
      ((CompleteLattice.colimitCocone
        (X.skeleton.monotone.functor)).isColimit))
    (Cocones.ext
      ((Subcomplex.isoOfEq X.iSup_skeleton) ≪≫ Subcomplex.topIso X)
      (fun _ => by rfl))

/-- Source of the proposed degree-`r` free projective attachment.
Each full nondegenerate reversal chain contributes one free outer
boundary diagram. -/
def attachingBoundary (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    ReverseSimplexᵒᵖ ⥤ SSet.{0} :=
  ∐ (fun t : NondegenerateLabel P r =>
    (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).obj (SSet.boundary r))

/-- Target of the proposed degree-`r` free projective attachment. -/
def attachingSimplex (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    ReverseSimplexᵒᵖ ⥤ SSet.{0} :=
  ∐ (fun t : NondegenerateLabel P r =>
    (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).obj Δ[r])

/-- The attaching morphism is literally the coproduct of projective
free boundary generators, retaining every full reversal-index label. -/
def attachingBoundaryMap (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    attachingBoundary P r ⟶ attachingSimplex P r :=
  Limits.Sigma.map (fun t : NondegenerateLabel P r =>
    (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).map (SSet.boundary r).ι)

/-- The distinguished nondegenerate simplex at the first vertex of a
full reversal-chain label, with the identity represented arrow. -/
def labelNondegenerate (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    (barValue P t.1.1.left).nonDegenerate r :=
  freeNondegenerateEquiv P t.1.1.left r ⟨t, 𝟙 _⟩

/-- The corresponding canonical simplex in the actual bar value. -/
def labelCell (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    Δ[r] ⟶ barValue P t.1.1.left :=
  SSet.yonedaEquiv.symm (labelNondegenerate P r t).1

/-- The labelled simplex lands in the next outer skeleton stage. -/
def labelCellSucc (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    Δ[r] ⟶ (barSkeleton P (r + 1)).obj (op t.1.1.left) :=
  SSet.yonedaEquiv.symm
    ⟨(labelNondegenerate P r t).1,
      (barValue P t.1.1.left).mem_skeleton _ (by simp)⟩

/-- The preimage of the degree-`r` skeleton under a nondegenerate
`r`-simplex is its standard boundary. This is the retained scalar
relative-cell lemma specialized to the initial inclusion. -/
theorem scalarBoundaryPreimage (X : SSet.{0}) (r : ℕ)
    (x : X.nonDegenerate r) :
    (X.skeleton r).preimage (SSet.yonedaEquiv.symm x.1) =
      SSet.boundary r := by
  let i : ((⊥ : X.Subcomplex) : SSet.{0}) ⟶ X := (⊥ : X.Subcomplex).ι
  have hrange : Subcomplex.range i = ⊥ := by
    simp [i, Subfunctor.range_ι]
  let y : SSet.relativeCellComplexOfMono.ι i r :=
    ⟨x, by rw [hrange]; simp⟩
  have h := SSet.relativeCellComplexOfMono.preimage_skeletonOfMono_eq y
  simpa [SSet.skeletonOfMono, hrange] using h

/-- The canonical labelled simplex restricts on its boundary to the
preceding outer skeleton stage. -/
def labelBoundary (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    (SSet.boundary r : SSet.{0}) ⟶
      (barSkeleton P r).obj (op t.1.1.left) :=
  Subcomplex.liftFromPreimage
    ((SSet.boundary r).ι ≫ labelCell P r t) (by
      rw [Subcomplex.preimage_preimage]
      change (((barValue P t.1.1.left).skeleton r).preimage
        (SSet.yonedaEquiv.symm (labelNondegenerate P r t).1)).preimage
          (SSet.boundary r).ι = ⊤
      rw [
        scalarBoundaryPreimage _ r (labelNondegenerate P r t),
        Subcomplex.preimage_ι])

/-- The projective free simplex map classified by the labelled
simplex in the next skeleton stage. -/
def freeLabelCellSucc (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).obj Δ[r] ⟶ barSkeleton P (r + 1) :=
  ((evaluationAdjunctionRight SSet.{0} (op t.1.1.left)).homEquiv
    Δ[r] (barSkeleton P (r + 1))).symm (labelCellSucc P r t)

/-- The projective free boundary map classified by the restriction of
the labelled simplex to the preceding skeleton. -/
def freeLabelBoundary (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
      (op t.1.1.left)).obj (SSet.boundary r) ⟶ barSkeleton P r :=
  ((evaluationAdjunctionRight SSet.{0} (op t.1.1.left)).homEquiv
    (SSet.boundary r) (barSkeleton P r)).symm (labelBoundary P r t)

/-- The proposed top attaching map, assembled over every full chain
label by the categorical coproduct universal property. -/
def attachingTop (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    attachingSimplex P r ⟶ barSkeleton P (r + 1) :=
  Sigma.desc (freeLabelCellSucc P r)

/-- The proposed left attaching map to the preceding skeleton. -/
def attachingLeft (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    attachingBoundary P r ⟶ barSkeleton P r :=
  Sigma.desc (freeLabelBoundary P r)

/-- The boundary restriction and the next-stage simplex agree after
inclusion into the next scalar skeleton. -/
theorem labelBoundary_fac (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    labelBoundary P r t ≫
        (barSkeletonMap P (Nat.le_succ r)).app (op t.1.1.left) =
      (SSet.boundary r).ι ≫ labelCellSucc P r t := by
  apply NatTrans.ext
  funext q x
  apply Subtype.ext
  rfl

/-- The square equation on a single projective free summand follows
from the naturality of the native evaluation adjunction. -/
theorem freeLabel_fac (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    freeLabelBoundary P r t ≫ barSkeletonMap P (Nat.le_succ r) =
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).map (SSet.boundary r).ι ≫
        freeLabelCellSucc P r t := by
  let adj := evaluationAdjunctionRight SSet.{0} (op t.1.1.left)
  apply (adj.homEquiv (SSet.boundary r) (barSkeleton P (r + 1))).injective
  rw [adj.homEquiv_naturality_right]
  calc
    (adj.homEquiv (SSet.boundary r) (barSkeleton P r))
          (freeLabelBoundary P r t) ≫
        ((evaluation ReverseSimplexᵒᵖ SSet.{0}).obj
          (op t.1.1.left)).map (barSkeletonMap P (Nat.le_succ r)) =
      labelBoundary P r t ≫
        (barSkeletonMap P (Nat.le_succ r)).app (op t.1.1.left) := by
          simp only [adj, freeLabelBoundary, Equiv.apply_symm_apply]
          rfl
    _ = (SSet.boundary r).ι ≫ labelCellSucc P r t :=
      labelBoundary_fac P r t
    _ = (SSet.boundary r).ι ≫
        (adj.homEquiv Δ[r] (barSkeleton P (r + 1)))
          (freeLabelCellSucc P r t) := by
          simp only [adj, freeLabelCellSucc, Equiv.apply_symm_apply]
    _ = (adj.homEquiv (SSet.boundary r) (barSkeleton P (r + 1)))
        ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
          (op t.1.1.left)).map (SSet.boundary r).ι ≫
          freeLabelCellSucc P r t) := by
      exact (adj.homEquiv_naturality_left _ _).symm

/-- The assembled free-cell attaching square commutes in the actual
outer diagram category. -/
theorem attachingSquare_comm (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    attachingLeft P r ≫ barSkeletonMap P (Nat.le_succ r) =
      attachingBoundaryMap P r ≫ attachingTop P r := by
  apply Sigma.hom_ext
  intro t
  dsimp only [attachingLeft, attachingBoundaryMap, attachingTop]
  rw [← Category.assoc, Sigma.ι_desc]
  rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_desc]
  exact freeLabel_fac P r t

/-- The initial map used to specialize the retained scalar successor
pushout to the ordinary skeleton of one simplicial set. -/
def scalarInitialInclusion (X : SSet.{0}) :
    ((⊥ : X.Subcomplex) : SSet.{0}) ⟶ X :=
  (⊥ : X.Subcomplex).ι

instance scalarInitialInclusion_mono (X : SSet.{0}) :
    Mono (scalarInitialInclusion X) := by
  dsimp [scalarInitialInclusion]
  infer_instance

/-- For the initial inclusion, the retained scalar cell index is exactly
the type of nondegenerate simplices. -/
def scalarInitialCellEquiv (X : SSet.{0}) (r : ℕ) :
    SSet.relativeCellComplexOfMono.ι (scalarInitialInclusion X) r ≃
      X.nonDegenerate r where
  toFun z := z.1
  invFun z := ⟨z, by
    simp [scalarInitialInclusion, Subfunctor.range_ι]⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := rfl

/-- Opposite-category arrows in the free evaluation are the actual
represented arrows of the manuscript bar. -/
def representedArrowEquiv (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (Σ t : NondegenerateLabel P r,
        (op t.1.1.left ⟶ op d)) ≃
      freeNondegenerateValue P d r where
  toFun z := ⟨z.1, z.2.unop⟩
  invFun z := ⟨z.1, z.2.op⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- The explicit index equivalence from the evaluated projective free
coproduct to the retained scalar cell coproduct. It includes every
reversal morphism, including automorphisms. -/
def pointwiseCellIndexEquiv (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (Σ t : NondegenerateLabel P r,
        (op t.1.1.left ⟶ op d)) ≃
      SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r :=
  (representedArrowEquiv P d r).trans
    ((freeNondegenerateEquiv P d r).trans
      (scalarInitialCellEquiv (barValue P d) r).symm)

/-- The index equivalence sends a represented full reversal-chain label
to exactly the checked nondegenerate bar simplex at that outer index. -/
theorem pointwiseCellIndexEquiv_val (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) (t : NondegenerateLabel P r)
    (h : d ⟶ t.1.1.left) :
    (pointwiseCellIndexEquiv P d r ⟨t, h.op⟩).1 =
      freeNondegenerateEquiv P d r ⟨t, h⟩ := rfl

/-- The scalar successor stage and the ordinary bar skeleton are
canonically the same subcomplex for the initial inclusion. -/
def scalarStageIso (X : SSet.{0}) (r : ℕ) :
    ((X.skeleton r : X.Subcomplex) : SSet.{0}) ≅
      SSet.skeletonOfMono (scalarInitialInclusion X) r :=
  Subcomplex.isoOfEq (by
    simp [SSet.skeletonOfMono, scalarInitialInclusion,
      Subfunctor.range_ι])

/-- Evaluation of the assembled free simplex coproduct, followed by
flattening and the explicit index equivalence, gives the exact scalar
simplex coproduct of the retained successor pushout. -/
def pointwiseAttachingSimplexIso (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (attachingSimplex P r).obj (op d) ≅
      SSet.relativeCellComplexOfMono.B
        (scalarInitialInclusion (barValue P d)) r :=
  sigmaObjIso
    (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj Δ[r]) (op d) ≪≫
    sigmaSigmaIso
      (fun t : NondegenerateLabel P r =>
        (op t.1.1.left ⟶ op d))
      (fun _ _ => Δ[r]) ≪≫
    Sigma.reindex (pointwiseCellIndexEquiv P d r)
      (fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r => Δ[r])

/-- The analogous evaluated free boundary coproduct is the exact
scalar boundary coproduct of the retained successor pushout. -/
def pointwiseAttachingBoundaryIso (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (attachingBoundary P r).obj (op d) ≅
      SSet.relativeCellComplexOfMono.A
        (scalarInitialInclusion (barValue P d)) r :=
  sigmaObjIso
    (fun t : NondegenerateLabel P r =>
      (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op t.1.1.left)).obj (SSet.boundary r)) (op d) ≪≫
    sigmaSigmaIso
      (fun t : NondegenerateLabel P r =>
        (op t.1.1.left ⟶ op d))
      (fun _ _ => (SSet.boundary r : SSet.{0})) ≪≫
    Sigma.reindex (pointwiseCellIndexEquiv P d r)
      (fun _ : SSet.relativeCellComplexOfMono.ι
        (scalarInitialInclusion (barValue P d)) r =>
        (SSet.boundary r : SSet.{0}))

/-- The retained scalar successor pushout, specialized to the initial
inclusion at one actual bar value. The remaining argument transports
this square across the preceding pointwise isomorphisms. -/
noncomputable def scalarInitialPushout (X : SSet.{0}) (r : ℕ) :
    IsPushout
      (SSet.relativeCellComplexOfMono.t (scalarInitialInclusion X) r)
      (SSet.relativeCellComplexOfMono.m (scalarInitialInclusion X) r)
      (SSet.relativeCellComplexOfMono.r (scalarInitialInclusion X) r)
      (SSet.relativeCellComplexOfMono.b (scalarInitialInclusion X) r) :=
  SSet.relativeCellComplexOfMono.isPushout (scalarInitialInclusion X) r

end

end DaggerModels.PartII.JTBarProjectiveCells
