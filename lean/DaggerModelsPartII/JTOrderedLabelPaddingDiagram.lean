import DaggerModelsPartII.JTOrderedLabelPaddingSpace
import DaggerModelsPartII.OrderedLabelElements
import DaggerModelsPartII.JTFixedLiftSpacePrecomp
import DaggerModelsPartII.JTOrderedNecklaceLabelFibrancy
import DaggerModelsPartII.JTOrderedNecklaceLabelPointFibrancy
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Contravariant padded extension spaces of actual ordered labels. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalClosed HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingDiagram

open JTOrderedLabelPaddingSpace (embedding extensionSpace square)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := NecklaceCode

private theorem embedding_natural {k k' : SimplexCategory} (v : k ⟶ k') :
    embedding k ≫ SSet.stdSimplex.map (JTPaddedTimeOperators.map v) =
      SSet.stdSimplex.map v ≫ embedding k' := by
  have h : SimplexCategory.Hom.mk (JTPaddedTimeOperators.inside k) ≫
      JTPaddedTimeOperators.map v =
        v ≫ SimplexCategory.Hom.mk (JTPaddedTimeOperators.inside k') := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact JTPaddedTimeOperators.map_inside v i
  simpa only [embedding, ← SSet.stdSimplex.map_comp] using
    congrArg SSet.stdSimplex.map h

private theorem label_restrict {Y Y' : SSet.{0}} (u : Y' ⟶ Y)
    {k k' : SimplexCategory} (v : k ⟶ k')
    (a : Y.obj (op k)) (a' : Y'.obj (op k'))
    (h : Y.map v.op (u.app (op k') a') = a) :
    SSet.stdSimplex.map v ≫ SSet.yonedaEquiv.symm a' ≫ u =
      SSet.yonedaEquiv.symm a := by
  rw [SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_map]
  exact congrArg SSet.yonedaEquiv.symm h

private def map {Y Y' : SSet.{0}} (u : Y' ⟶ Y)
    {k k' : SimplexCategory} (v : k ⟶ k')
    (a : Y.obj (op k)) (a' : Y'.obj (op k'))
    (h : Y.map v.op (u.app (op k') a') = a) :
    extensionSpace Y' k' a' ⟶ extensionSpace Y k a :=
  SSet.Subcomplex.lift
    ((SSet.ihomToPullbackFiber (square Y' k' a')).ι ≫
      (MonoidalClosed.pre (SSet.stdSimplex.map (JTPaddedTimeOperators.map v))).app Y' ≫
      (ihom (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0})).map u) (by
    apply (SSet.range_le_ihomToPullbackFiber_iff (square Y k a) _).mpr
    constructor
    · rw [Category.assoc, Category.assoc,
        ← MonoidalClosed.pre_comm_ihom_map (embedding k) u]
      rw [← Category.assoc
        ((MonoidalClosed.pre
          (SSet.stdSimplex.map (JTPaddedTimeOperators.map v))).app Y')
        ((MonoidalClosed.pre (embedding k)).app Y')
        ((ihom (Δ[k.len] : SSet.{0})).map u)]
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, embedding_natural]
      rw [MonoidalClosed.pre_map, NatTrans.comp_app]
      rw [Category.assoc
        ((MonoidalClosed.pre (embedding k')).app Y')
        ((MonoidalClosed.pre (SSet.stdSimplex.map v)).app Y')
        ((ihom (Δ[k.len] : SSet.{0})).map u)]
      rw [← Category.assoc
        (SSet.ihomToPullbackFiber (square Y' k' a')).ι
        ((MonoidalClosed.pre (embedding k')).app Y')
        (((MonoidalClosed.pre (SSet.stdSimplex.map v)).app Y') ≫
          (ihom (Δ[k.len] : SSet.{0})).map u)]
      rw [SSet.ihomToPullbackFiber_pre_app,
        SSet.const_comp]
      change SSet.const (SSet.ihom₀Equiv.symm
        (SSet.stdSimplex.map v ≫ SSet.yonedaEquiv.symm a' ≫ u)) = _
      rw [label_restrict u v a a' h]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp]
      have hc : u ≫ SSet.stdSimplex.isTerminalObj₀.from Y =
          SSet.stdSimplex.isTerminalObj₀.from Y' :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [hc]
      rw [show (MonoidalClosed.pre
          (SSet.stdSimplex.map (JTPaddedTimeOperators.map v))).app Y' ≫
          (ihom (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0})).map
            (SSet.stdSimplex.isTerminalObj₀.from Y') =
          (ihom (Δ[(JTPaddedTimeOperators.pad k').len] : SSet.{0})).map
            (SSet.stdSimplex.isTerminalObj₀.from Y') ≫
          (MonoidalClosed.pre
            (SSet.stdSimplex.map (JTPaddedTimeOperators.map v))).app
              (Δ[0] : SSet.{0}) from
        MonoidalClosed.pre_comm_ihom_map _ _]
      rw [← Category.assoc, SSet.ihomToPullbackFiber_ihom_map,
        SSet.const_comp]
      change SSet.const (SSet.ihom₀Equiv.symm
        (SSet.stdSimplex.map (JTPaddedTimeOperators.map v) ≫
          SSet.stdSimplex.isTerminalObj₀.from
            (Δ[(JTPaddedTimeOperators.pad k').len] : SSet.{0}))) = _
      rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
        (SSet.stdSimplex.map (JTPaddedTimeOperators.map v) ≫
          SSet.stdSimplex.isTerminalObj₀.from
            (Δ[(JTPaddedTimeOperators.pad k').len] : SSet.{0}))
        (SSet.stdSimplex.isTerminalObj₀.from
          (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0}))]
      rfl)

private theorem map_ι {Y Y' : SSet.{0}} (u : Y' ⟶ Y)
    {k k' : SimplexCategory} (v : k ⟶ k')
    (a : Y.obj (op k)) (a' : Y'.obj (op k'))
    (h : Y.map v.op (u.app (op k') a') = a) :
    map u v a a' h ≫ (SSet.ihomToPullbackFiber (square Y k a)).ι =
      (SSet.ihomToPullbackFiber (square Y' k' a')).ι ≫
        (MonoidalClosed.pre (SSet.stdSimplex.map (JTPaddedTimeOperators.map v))).app Y' ≫
        (ihom (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0})).map u := rfl

private theorem map_id {Y : SSet.{0}} {k : SimplexCategory}
    (a : Y.obj (op k))
    (h : Y.map (𝟙 k).op ((𝟙 Y : Y ⟶ Y).app (op k) a) = a) :
    map (𝟙 Y) (𝟙 k) a a h = 𝟙 (extensionSpace Y k a) := by
  apply (cancel_mono (SSet.ihomToPullbackFiber (square Y k a)).ι).mp
  have hpad : JTPaddedTimeOperators.map (𝟙 k) =
      𝟙 (JTPaddedTimeOperators.pad k) := JTPaddedTimeOperators.functor.map_id k
  rw [map_ι, hpad]
  rw [show (𝟙 (JTPaddedTimeOperators.pad k) :
    JTPaddedTimeOperators.pad k ⟶ JTPaddedTimeOperators.pad k) =
      SimplexCategory.Hom.mk OrderHom.id from rfl]
  rw [SSet.stdSimplex.map_id]
  rw [MonoidalClosed.pre_id, NatTrans.id_app]
  rw [show (ihom (Δ[(JTPaddedTimeOperators.pad k).len] : SSet.{0})).map (𝟙 Y) =
    𝟙 _ from (ihom _).map_id Y]
  simp

private theorem map_comp {Y₀ Y₁ Y₂ : SSet.{0}}
    (u₀₁ : Y₁ ⟶ Y₀) (u₁₂ : Y₂ ⟶ Y₁)
    {k₀ k₁ k₂ : SimplexCategory} (v₀₁ : k₀ ⟶ k₁) (v₁₂ : k₁ ⟶ k₂)
    (a₀ : Y₀.obj (op k₀)) (a₁ : Y₁.obj (op k₁)) (a₂ : Y₂.obj (op k₂))
    (h₀₁ : Y₀.map v₀₁.op (u₀₁.app (op k₁) a₁) = a₀)
    (h₁₂ : Y₁.map v₁₂.op (u₁₂.app (op k₂) a₂) = a₁)
    (h₀₂ : Y₀.map (v₀₁ ≫ v₁₂).op ((u₁₂ ≫ u₀₁).app (op k₂) a₂) = a₀) :
    map u₁₂ v₁₂ a₁ a₂ h₁₂ ≫ map u₀₁ v₀₁ a₀ a₁ h₀₁ =
      map (u₁₂ ≫ u₀₁) (v₀₁ ≫ v₁₂) a₀ a₂ h₀₂ := by
  apply (cancel_mono (SSet.ihomToPullbackFiber (square Y₀ k₀ a₀)).ι).mp
  rw [Category.assoc, map_ι, ← Category.assoc, map_ι, map_ι]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((ihom (Δ[(JTPaddedTimeOperators.pad k₁).len] : SSet.{0})).map u₁₂)
    ((MonoidalClosed.pre
      (SSet.stdSimplex.map (JTPaddedTimeOperators.map v₀₁))).app Y₁)
    ((ihom (Δ[(JTPaddedTimeOperators.pad k₀).len] : SSet.{0})).map u₀₁)]
  rw [show (ihom (Δ[(JTPaddedTimeOperators.pad k₁).len] : SSet.{0})).map u₁₂ ≫
      (MonoidalClosed.pre
        (SSet.stdSimplex.map (JTPaddedTimeOperators.map v₀₁))).app Y₁ =
      (MonoidalClosed.pre
        (SSet.stdSimplex.map (JTPaddedTimeOperators.map v₀₁))).app Y₂ ≫
        (ihom (Δ[(JTPaddedTimeOperators.pad k₀).len] : SSet.{0})).map u₁₂ from
    (MonoidalClosed.pre_comm_ihom_map _ _).symm]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((MonoidalClosed.pre
      (SSet.stdSimplex.map (JTPaddedTimeOperators.map v₁₂))).app Y₂)
    ((MonoidalClosed.pre
      (SSet.stdSimplex.map (JTPaddedTimeOperators.map v₀₁))).app Y₂)
    ((ihom (Δ[(JTPaddedTimeOperators.pad k₀).len] : SSet.{0})).map u₁₂ ≫
      (ihom (Δ[(JTPaddedTimeOperators.pad k₀).len] : SSet.{0})).map u₀₁)]
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rw [← SSet.stdSimplex.map_comp]
  have hpad : JTPaddedTimeOperators.map v₀₁ ≫ JTPaddedTimeOperators.map v₁₂ =
      JTPaddedTimeOperators.map (v₀₁ ≫ v₁₂) :=
    (JTPaddedTimeOperators.functor.map_comp v₀₁ v₁₂).symm
  rw [hpad, ← Functor.map_comp]

private abbrev labels (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W) :=
  OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b

private abbrev code (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b) := OrderedLabelElements.necklace W b i

private abbrev degree (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b) := OrderedLabelElements.degree W b i

private abbrev label (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b) := OrderedLabelElements.label W b i

/-- The literal extension space at one decorated ordered label. -/
def fiberAt (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b) : SSet.{0} :=
  extensionSpace ((labels W b).obj (op (code W b i))) (degree W b i) (label W b i)

/-- Restriction along the native necklace map and the padded coefficient operator. -/
def restriction (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    {i j : OrderedLabelElements.Index W b} (f : i ⟶ j) :
    fiberAt W b j ⟶ fiberAt W b i :=
  map ((labels W b).map ((OrderedLabelElements.projection W b).map f).1.op)
    ((OrderedLabelElements.projection W b).map f).2
    (label W b i) (label W b j) (OrderedLabelElements.label_map W b f)

@[reassoc]
theorem restriction_ι (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    {i j : OrderedLabelElements.Index W b} (f : i ⟶ j) :
    restriction W b f ≫ (SSet.ihomToPullbackFiber
      (square ((labels W b).obj (op (code W b i))) (degree W b i) (label W b i))).ι =
      (SSet.ihomToPullbackFiber
        (square ((labels W b).obj (op (code W b j))) (degree W b j) (label W b j))).ι ≫
        (MonoidalClosed.pre (SSet.stdSimplex.map
          (JTPaddedTimeOperators.map ((OrderedLabelElements.projection W b).map f).2))).app
            ((labels W b).obj (op (code W b j))) ≫
          (ihom (Δ[(JTPaddedTimeOperators.pad (degree W b i)).len] : SSet.{0})).map
            ((labels W b).map ((OrderedLabelElements.projection W b).map f).1.op) := by
  exact map_ι _ _ _ _ _

private theorem restriction_id (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b) :
    restriction W b (𝟙 i) = 𝟙 (fiberAt W b i) := by
  simp [restriction, OrderedLabelElements.projection, map_id, fiberAt]
  rfl

private theorem restriction_comp (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    {i j k : OrderedLabelElements.Index W b} (f : i ⟶ j) (g : j ⟶ k) :
    restriction W b g ≫ restriction W b f = restriction W b (f ≫ g) := by
  simp [restriction, OrderedLabelElements.projection]
  exact map_comp _ _ _ _ _ _ _ _ _ _

/-- The full padded extension spaces form a contravariant simplicial diagram
over the original decorated ordered-label category. -/
def diagram (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W) :
    (OrderedLabelElements.Index W b)ᵒᵖ ⥤ SSet.{0} where
  obj i := fiberAt W b i.unop
  map f := restriction W b f.unop
  map_id i := by
    change restriction W b (𝟙 i.unop) = 𝟙 (fiberAt W b i.unop)
    exact restriction_id W b i.unop
  map_comp f g := by
    change restriction W b (g.unop ≫ f.unop) =
      restriction W b f.unop ≫ restriction W b g.unop
    exact (restriction_comp W b g.unop f.unop).symm

/-- Pull back the padded extension diagram along any diagram of actual ordered labels. -/
def along {A : Type} [SmallCategory A] (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (L : A ⥤ OrderedLabelElements.Index W b) : Aᵒᵖ ⥤ SSet.{0} :=
  L.op ⋙ diagram W b

/-- The indexing category retains every simplex of every extension space
and both its original-label and simplex operators. -/
abbrev FullIndex {A : Type} [SmallCategory A] (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (L : A ⥤ OrderedLabelElements.Index W b) :=
  (GrothendieckTotalElements.totalDiagram (along W b L)).Elementsᵒᵖ

/-- Forget the extension and its simplex degree while keeping the actual base arrow. -/
abbrev base {A : Type} [SmallCategory A] (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (L : A ⥤ OrderedLabelElements.Index W b) : FullIndex W b L ⥤ A :=
  (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (along W b L)) ⋙
    CategoryTheory.Prod.fst Aᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The label space at each actual decorated label is Kan, including point codes. -/
theorem label_isFibrant (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (i : OrderedLabelElements.Index W b)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    IsFibrant ((labels W b).obj (op (code W b i))) := by
  let T := code W b i
  by_cases hT : T.len = 0
  · exact JTOrderedNecklaceLabelPointFibrancy.label_isFibrant W T hT b (degree W b i) (label W b i)
  · exact JTOrderedNecklaceLabelFibrancy.orderedNecklaceLabels_isFibrant W hW b T
      (Nat.pos_of_ne_zero hT)

/-- Over any original diagram of actual decorated labels, forgetting all
coherent padded extensions preserves the weak homotopy type. -/
theorem base_weak {A : Type} [SmallCategory A] (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
    (L : A ⥤ OrderedLabelElements.Index W b)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (base W b L)) := by
  have h (p : Aᵒᵖ) : GW (pointMap ((along W b L).obj p)) := by
    apply (weakEquivalence_iff_GW _).mp
    let i := L.obj p.unop
    letI := label_isFibrant W b i hW
    letI : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (fiberAt W b i)) :=
      JTOrderedLabelPaddingSpace.extensionSpace_toPoint_weak _ _ _
    let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
    have he : pointMap ((along W b L).obj p) =
        SSet.stdSimplex.isTerminalObj₀.from (fiberAt W b i) ≫ e.hom :=
      pointIsTerminal.hom_ext _ _
    rw [he]
    infer_instance
  let F := CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (along W b L)) ⋙
    CategoryTheory.Prod.fst Aᵒᵖ SimplexCategoryᵒᵖ
  have hF : WeakEquivalence (nerveMap F) :=
    SynchronizedSimplicialParameters.projection_weak (along W b L) h
  letI : WeakEquivalence (nerveMap F.op) :=
    (TotalElementsWeakComparison.nerveMap_op_iff _).mpr hF
  letI : WeakEquivalence (nerveMap (unopUnop A)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence (unopUnop A)
  change WeakEquivalence (nerveMap F.op ≫ nerveMap (unopUnop A))
  infer_instance

end

end DaggerModels.PartII.JTOrderedLabelPaddingDiagram
