import DaggerModelsPartII.CosimplicialFrameNormalization
import Mathlib.CategoryTheory.Adjunction.Opposites
import TopCatModelCategory.QuillenAdjunction

/-! Transport of the derived mapping test along mates of left Quillen functors. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

universe v u u'

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {D : Type u'} [Category.{v} D] [ModelCategory D]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]

local instance quillenFrameReedyC : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ
local instance quillenFrameReedyD : ModelCategory (SimplexCategoryᵒᵖ ⥤ Dᵒᵖ) :=
  simplicialReedyModelCategory Dᵒᵖ

variable {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D] in
private theorem op_map_fibrations [adj.IsQuillenAdjunction] {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hf : fibrations Cᵒᵖ f) : fibrations Dᵒᵖ (L.op.map f) := by
  rw [fibrations_op] at hf ⊢
  exact L.preservesCofibrations_iff.mp (Adjunction.IsQuillenAdjunction.preservesCofibrations adj)
    f.unop hf

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D] in
private theorem op_map_trivialFibrations [adj.IsQuillenAdjunction] {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hf : trivialFibrations Cᵒᵖ f) : trivialFibrations Dᵒᵖ (L.op.map f) := by
  rw [trivialFibrations_op] at hf ⊢
  letI := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations adj
  exact Functor.PreservesTrivialCofibrations.trivialCofibrations_le L f.unop hf

private theorem whiskerFrame_fibrant [adj.IsQuillenAdjunction] {A : C}
    (R : CosimplicialResolution A) : IsFibrant (R.oppositeDiagram ⋙ L.op) := by
  letI := R.fibrantOp
  letI : PreservesLimitsOfSize.{0, 0} L.op := adj.op.rightAdjoint_preservesLimits
  exact reedyFibrant_comp R.oppositeDiagram L.op (op_map_fibrations adj)

private def whiskerFrameAugmentation {A : C} (R : CosimplicialResolution A) (L : C ⥤ D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (op (L.obj A)) ⟶ R.oppositeDiagram ⋙ L.op :=
  (Functor.constComp SimplexCategoryᵒᵖ (op A) L.op).inv ≫ Functor.whiskerRight R.augmentationOp L.op

private theorem whiskerFrame_augmentation_weak [adj.IsQuillenAdjunction] {A : C}
    [IsCofibrant A] (R : CosimplicialResolution A) :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ Dᵒᵖ) (whiskerFrameAugmentation R L) := by
  letI := isFibrant_op_of_isCofibrant A
  letI := R.fibrantOp
  intro n
  letI := reedyFibrant_obj R.oppositeDiagram n
  have h : weakEquivalences Cᵒᵖ (R.augmentationOp.app n) := by
    rw [weakEquivalences_op]
    exact R.augmentation_weak n
  change weakEquivalences Dᵒᵖ (𝟙 _ ≫ L.op.map (R.augmentationOp.app n))
  rw [Category.id_comp]
  letI : IsFibrant (((Functor.const SimplexCategoryᵒᵖ).obj (op A)).obj n) :=
    isFibrant_op_of_isCofibrant A
  exact map_weak_of_trivialFibration L.op (fun p hp ↦ (op_map_trivialFibrations adj p hp).2) _ h

private def adjointMappingIso (W : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) (Z : D) :
    (CosimplicialResolution.mappingFromOppositeDiagram Z).obj (W ⋙ L.op) ≅
      (CosimplicialResolution.mappingFromOppositeDiagram (G.obj Z)).obj W :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun := fun x ↦ (adj.homEquiv (W.obj n).unop Z x.unop).op
      invFun := fun x ↦ ((adj.homEquiv (W.obj n).unop Z).symm x.unop).op
      left_inv := fun x ↦ Quiver.Hom.unop_inj (Equiv.symm_apply_apply _ x.unop)
      right_inv := fun x ↦ Quiver.Hom.unop_inj (Equiv.apply_symm_apply _ x.unop) }) (by
    intro i j f
    funext x
    change op Z ⟶ op (L.obj (W.obj i).unop) at x
    apply Quiver.Hom.unop_inj
    exact adj.homEquiv_naturality_left (W.map f).unop x.unop)

/-- The derived test on a map of left-adjoint values is the mapping-space test
on its mate between right-adjoint values. -/
theorem homotopyMappingWeakEquivalences_of_mates
    {L' : C ⥤ D} {G' : D ⥤ C} (adj' : L' ⊣ G')
    [adj.IsQuillenAdjunction] [adj'.IsQuillenAdjunction]
    (α : L ⟶ L') (β : G' ⟶ G)
    (mates : ∀ {A : C} {Z : D} (q : L'.obj A ⟶ Z),
      adj.homEquiv A Z (α.app A ≫ q) = adj'.homEquiv A Z q ≫ β.app Z)
    {A : C} [IsCofibrant A] (R : CosimplicialResolution A) (Z : D) [IsFibrant Z] :
    homotopyMappingWeakEquivalences Z (α.app A) ↔
      weakEquivalences SSet.{v} (R.mappingSSet.map (β.app Z)) := by
  let W := R.oppositeDiagram
  letI := whiskerFrame_fibrant adj R
  letI := whiskerFrame_fibrant adj' R
  let g := Functor.whiskerLeft W (NatTrans.op α)
  have h : whiskerFrameAugmentation R L' ≫ g =
      (Functor.const SimplexCategoryᵒᵖ).map (α.app A).op ≫
        whiskerFrameAugmentation R L := by
    apply NatTrans.ext
    funext n
    apply Quiver.Hom.unop_inj
    change α.app (W.obj n).unop ≫ (L'.map (R.augmentationOp.app n).unop ≫ 𝟙 _) =
      (L.map (R.augmentationOp.app n).unop ≫ 𝟙 _) ≫ α.app A
    rw [Category.comp_id, Category.comp_id]
    exact (α.naturality (R.augmentationOp.app n).unop).symm
  rw [homotopyMappingWeakEquivalences_iff_of_frames (α.app A)
    (whiskerFrameAugmentation R L) (whiskerFrameAugmentation R L')
    (whiskerFrame_augmentation_weak adj R) (whiskerFrame_augmentation_weak adj' R) g h]
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  let e := adjointMappingIso adj W Z
  let e' := adjointMappingIso adj' W Z
  have w : F.map g ≫ e.hom = e'.hom ≫ R.mappingSSet.map (β.app Z) := by
    ext n x : 2
    change op Z ⟶ op (L'.obj (W.obj n).unop) at x
    apply Quiver.Hom.unop_inj
    exact mates x.unop
  rw [← (weakEquivalences SSet.{v}).cancel_right_of_respectsIso (F.map g) e.hom,
    w, (weakEquivalences SSet.{v}).cancel_left_of_respectsIso]

/-- Derived locality against the left Quillen image of a map between cofibrant
objects is the corresponding locality test on the right-adjoint target. -/
theorem homotopyMappingWeakEquivalences_leftQuillen_iff [adj.IsQuillenAdjunction]
    {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B)
    (Z : D) [IsFibrant Z] [IsFibrant (G.obj Z)] :
    homotopyMappingWeakEquivalences Z (L.map f) ↔
      homotopyMappingWeakEquivalences (G.obj Z) f := by
  let R := cosimplicialResolution A
  let S := cosimplicialResolution B
  let g := R.comparison S f
  let gL := Functor.whiskerRight g.mapOp L.op
  letI := whiskerFrame_fibrant adj R
  letI := whiskerFrame_fibrant adj S
  have hg : whiskerFrameAugmentation S L ≫ gL =
      (Functor.const SimplexCategoryᵒᵖ).map (L.map f).op ≫
        whiskerFrameAugmentation R L := by
    apply NatTrans.ext
    funext n
    change (𝟙 _ ≫ L.op.map (S.augmentationOp.app n)) ≫ L.op.map (g.mapOp.app n) =
      L.op.map f.op ≫ (𝟙 _ ≫ L.op.map (R.augmentationOp.app n))
    simp only [Category.id_comp, ← Functor.map_comp]
    exact congrArg L.op.map (congr_app g.comm n)
  rw [homotopyMappingWeakEquivalences_iff_of_frames (L.map f)
    (whiskerFrameAugmentation R L) (whiskerFrameAugmentation S L)
    (whiskerFrame_augmentation_weak adj R) (whiskerFrame_augmentation_weak adj S) gL hg,
    homotopyMappingWeakEquivalences_iff (G.obj Z) g]
  let M := CosimplicialResolution.mappingFromOppositeDiagram Z
  let eR := adjointMappingIso adj R.oppositeDiagram Z
  let eS := adjointMappingIso adj S.oppositeDiagram Z
  have h : M.map gL ≫ eR.hom = eS.hom ≫ g.precomp (G.obj Z) := by
    ext n x : 2
    change op Z ⟶ op (L.obj (S.oppositeDiagram.obj n).unop) at x
    apply Quiver.Hom.unop_inj
    exact adj.homEquiv_naturality_left (g.mapOp.app n).unop x.unop
  rw [← (weakEquivalences SSet.{v}).cancel_right_of_respectsIso (M.map gL) eR.hom,
    h, (weakEquivalences SSet.{v}).cancel_left_of_respectsIso]

/-- The mapping simplicial sets out of an opposite cosimplicial diagram, as a functor of
the target. -/
def oppositeFrameMappingTarget (W : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ) : D ⥤ SSet.{v} :=
  opOp D ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj W

private def oppositeFrameMappingPrecomp {U V : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ} (k : U ⟶ V) :
    oppositeFrameMappingTarget U ⟶ oppositeFrameMappingTarget V where
  app Z := (CosimplicialResolution.mappingFromOppositeDiagram Z).map k
  naturality Z Z' f := by
    ext n x : 2
    exact Category.assoc f.op x (k.app n)

private theorem oppositeFrameMappingTarget_weak_iff
    {U V : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ} [IsFibrant U] [IsFibrant V] (k : U ⟶ V)
    (hk : weakEquivalences _ k) {Z Z' : D} [IsFibrant Z] [IsFibrant Z'] (f : Z ⟶ Z') :
    weakEquivalences SSet.{v} ((oppositeFrameMappingTarget U).map f) ↔
      weakEquivalences SSet.{v} ((oppositeFrameMappingTarget V).map f) := by
  let W := weakEquivalences SSet.{v}
  let t := oppositeFrameMappingPrecomp k
  have hZ : W (t.app Z) := map_weak_of_trivialFibration
    (CosimplicialResolution.mappingFromOppositeDiagram Z)
    (fun p hp ↦ (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z p hp).2)
    k hk
  have hZ' : W (t.app Z') := map_weak_of_trivialFibration
    (CosimplicialResolution.mappingFromOppositeDiagram Z')
    (fun p hp ↦ (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z' p hp).2)
    k hk
  constructor
  · intro h
    apply W.of_precomp _ _ hZ
    rw [← t.naturality f]
    exact W.comp_mem _ _ h hZ'
  · intro h
    apply W.of_postcomp _ _ hZ'
    rw [t.naturality f]
    exact W.comp_mem _ _ hZ h

/-- For a cofibrant source, a weak equivalence on right-adjoint values gives a Kan weak
equivalence on the mapping simplicial sets out of any weakly augmented Reedy fibrant
opposite frame of its left-adjoint image. -/
theorem oppositeFrameMappingTarget_weak_of_rightAdjoint_weak [adj.IsQuillenAdjunction]
    {A : C} [IsCofibrant A] {E : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ} [IsFibrant E]
    (a : (Functor.const SimplexCategoryᵒᵖ).obj (op (L.obj A)) ⟶ E)
    (ha : weakEquivalences _ a)
    {Z Z' : D} [IsFibrant Z] [IsFibrant Z'] [IsFibrant (G.obj Z)] [IsFibrant (G.obj Z')]
    (f : Z ⟶ Z') (hf : weakEquivalences C (G.map f)) :
    weakEquivalences SSet.{v} ((oppositeFrameMappingTarget E).map f) := by
  let R := cosimplicialResolution A
  let U := R.oppositeDiagram ⋙ L.op
  letI : IsFibrant U := whiskerFrame_fibrant adj R
  let b := whiskerFrameAugmentation R L
  let d := factorizationData (trivialCofibrations _) (fibrations _) b
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  letI : IsFibrant d.Z := isFibrant_of_fibration d.p
  have hp : weakEquivalences _ d.p :=
    (weakEquivalences _).of_precomp _ _ d.hi.2 (d.fac.symm ▸ whiskerFrame_augmentation_weak adj R)
  let sq : CommSq a d.i (terminal.from E) (terminal.from d.Z) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  letI : HasLiftingProperty d.i (terminal.from E) :=
    hasLiftingProperty_of_wfs _ _ d.hi (mem_fibrations _)
  have hl : weakEquivalences _ sq.lift :=
    (weakEquivalences _).of_precomp _ _ d.hi.2 (sq.fac_left.symm ▸ ha)
  have hu : weakEquivalences SSet.{v} ((oppositeFrameMappingTarget U).map f) := by
    let e := adjointMappingIso adj R.oppositeDiagram Z
    let e' := adjointMappingIso adj R.oppositeDiagram Z'
    have w : (oppositeFrameMappingTarget U).map f ≫ e'.hom =
        e.hom ≫ R.mappingSSet.map (G.map f) := by
      ext n x : 2
      change op Z ⟶ op (L.obj (R.oppositeDiagram.obj n).unop) at x
      apply Quiver.Hom.unop_inj
      exact adj.homEquiv_naturality_right x.unop f
    rw [← (weakEquivalences SSet.{v}).cancel_right_of_respectsIso _ e'.hom,
      w, (weakEquivalences SSet.{v}).cancel_left_of_respectsIso]
    exact R.mappingSSet_map_weak (G.map f) hf
  exact (oppositeFrameMappingTarget_weak_iff sq.lift hl f).mp
    ((oppositeFrameMappingTarget_weak_iff d.p hp f).mpr hu)

end

end DaggerModels.PartII
