import DaggerModelsPartII.JTDecoratedCylinderOverMapping
import DaggerModelsPartII.JTTargetIntervalOverMapping
import DaggerModelsPartII.JTDecoratedIntervalMapping
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Strict gluing of parametrized decorated lifts on varying interval diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

open JTTargetJointMarks (Joint)
open NecklaceCode (pointAt)

variable {I : Type} [SmallCategory I]
variable {U Z : SSet.{0}} (q : U ⟶ Z)
variable (K : SimplexCategory ⥤ SSet.{0}) (time : I ⥤ SimplexCategory)

private abbrev frameOverRaw :=
  Functor.uncurry.obj (JTOverParametrizedMapping.frame K U) ⋙ Over.map q

/-- Parametrize each source by its actual time and move to the original raw slice.
Both operators are used on arrows. -/
abbrev parameterize (D : I ⥤ Over U) : I ⥤ Over Z :=
  D.prod' time ⋙ frameOverRaw q K

/-- Restrict parametrized sources by a natural family of over-target arrows. -/
def parameterizeMap {D D' : I ⥤ Over U} (a : D ⟶ D') :
    parameterize q K time D ⟶ parameterize q K time D' :=
  Functor.whiskerRight (NatTrans.prod' a (𝟙 time)) (frameOverRaw q K)

theorem parameterizeMap_app {D D' : I ⥤ Over U} (a : D ⟶ D') (i : I) :
    (parameterizeMap q K time a).app i =
      (Over.map q).map (((JTOverParametrizedMapping.frame K U).map (a.app i)).app
        (time.obj i)) := by
  change (Over.map q).map
    ((((JTOverParametrizedMapping.frame K U).map (a.app i)).app (time.obj i)) ≫
      (((JTOverParametrizedMapping.frame K U).obj (D'.obj i)).map (𝟙 (time.obj i)))) = _
  rw [((JTOverParametrizedMapping.frame K U).obj (D'.obj i)).map_id, Category.comp_id]

/-- The actual underlying operator is the tensor of the native and time operators. -/
theorem parameterize_map_left (D : I ⥤ Over U) {i i' : I} (f : i ⟶ i') :
    ((parameterize q K time D).map f).left =
      (D.map f).left ⊗ₘ K.map (time.map f) := by
  change ((D.map f).left ⊗ₘ 𝟙 (K.obj (time.obj i))) ≫
    (𝟙 (D.obj i').left ⊗ₘ K.map (time.map f)) = _
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- Forget the parameter, without changing the underlying native map to the raw target. -/
def forgetParameter (D : I ⥤ Over U) :
    parameterize q K time D ⟶ D ⋙ Over.map q where
  app i := Over.homMk (fst (D.obj i).left (K.obj (time.obj i))) (by
    change fst (D.obj i).left (K.obj (time.obj i)) ≫ ((D.obj i).hom ≫ q) =
      (fst (D.obj i).left (K.obj (time.obj i)) ≫ (D.obj i).hom) ≫ q
    exact (Category.assoc _ _ _).symm)
  naturality i j f := by
    apply Over.OverMorphism.ext
    change ((parameterize q K time D).map f).left ≫
      fst (D.obj j).left (K.obj (time.obj j)) =
      fst (D.obj i).left (K.obj (time.obj i)) ≫ (D.map f).left
    rw [parameterize_map_left, tensorHom_fst]

/-- Parametrizing a diagram of pushouts keeps the pushout at each object and
on all the changing source and time operators. -/
theorem parameterize_isPushout
    {M L R P : I ⥤ Over U} {ml : M ⟶ L} {mr : M ⟶ R} {l : L ⟶ P} {r : R ⟶ P}
    (sq : ∀ i, IsPushout (ml.app i) (mr.app i) (l.app i) (r.app i)) :
    IsPushout (parameterizeMap q K time ml) (parameterizeMap q K time mr)
      (parameterizeMap q K time l) (parameterizeMap q K time r) := by
  have atObject (i : I) : IsPushout ((parameterizeMap q K time ml).app i)
      ((parameterizeMap q K time mr).app i) ((parameterizeMap q K time l).app i)
      ((parameterizeMap q K time r).app i) := by
    simp only [parameterizeMap_app]
    exact (JTOverParametrizedMapping.frameAt_isPushout K U (sq i) (time.obj i)).map
      (Over.map q)
  refine ⟨⟨NatTrans.ext (funext fun i ↦ (atObject i).w)⟩,
    ⟨evaluationJointlyReflectsColimits _ (fun i ↦ ?_)⟩⟩
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (atObject i).isColimit

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (D : I ⥤ Over Q.code) (j : Joint Q.code)

open JTTargetIntervalOverMapping (whole left right overlap overlapToLeft overlapToRight
  leftToWhole rightToWhole over_isPushout)

abbrev wholeRaw := parameterize Q.map K time (D ⋙ whole Q.code)
abbrev leftRaw := parameterize Q.map K time (D ⋙ left Q.code j)
abbrev rightRaw := parameterize Q.map K time (D ⋙ right Q.code j)
abbrev overlapRaw := parameterize Q.map K time (D ⋙ overlap Q.code j)

abbrev leftInclusion := parameterizeMap Q.map K time (Functor.whiskerLeft D (leftToWhole Q.code j))
abbrev rightInclusion :=
  parameterizeMap Q.map K time (Functor.whiskerLeft D (rightToWhole Q.code j))
abbrev overlapLeft :=
  parameterizeMap Q.map K time (Functor.whiskerLeft D (overlapToLeft Q.code j))
abbrev overlapRight :=
  parameterizeMap Q.map K time (Functor.whiskerLeft D (overlapToRight Q.code j))

/-- Gluing along the entire inverse image of the target joint is a pushout
of the actual raw diagrams, including every time and native operator. -/
theorem interval_isPushout :
    IsPushout (overlapLeft K time Q D j) (overlapRight K time Q D j)
      (leftInclusion K time Q D j) (rightInclusion K time Q D j) :=
  parameterize_isPushout Q.map K time (fun i ↦ over_isPushout Q.code j (D.obj i))

variable (labels : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)

private abbrev decorated := labels ⋙ JTDecoratedCylinderOverMapping.rawTarget W x y

/-- Side maps with the same full overlap glue to an actual natural
family of decorated lifts over the raw target. -/
def glue (l : leftRaw K time Q D j ⟶ decorated labels)
    (r : rightRaw K time Q D j ⟶ decorated labels)
    (h : overlapLeft K time Q D j ≫ l = overlapRight K time Q D j ≫ r) :
    wholeRaw K time Q D ⟶ decorated labels :=
  (interval_isPushout K time Q D j).desc l r h

theorem glue_left (l : leftRaw K time Q D j ⟶ decorated labels)
    (r : rightRaw K time Q D j ⟶ decorated labels)
    (h : overlapLeft K time Q D j ≫ l = overlapRight K time Q D j ≫ r) :
    leftInclusion K time Q D j ≫ glue K time Q D j labels l r h = l :=
  (interval_isPushout K time Q D j).inl_desc _ _ _

theorem glue_right (l : leftRaw K time Q D j ⟶ decorated labels)
    (r : rightRaw K time Q D j ⟶ decorated labels)
    (h : overlapLeft K time Q D j ≫ l = overlapRight K time Q D j ≫ r) :
    rightInclusion K time Q D j ≫ glue K time Q D j labels l r h = r :=
  (interval_isPushout K time Q D j).inr_desc _ _ _


section Postcomposition

variable {labels' : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable (u : labels ⟶ labels')

private abbrev rawOperator :=
  Functor.whiskerRight u (JTDecoratedCylinderOverMapping.rawTarget W x y)

/-- Changing decorated labels commutes with gluing when it gives the specified
change on each complete side map. -/
theorem glue_postcomp
    (l : leftRaw K time Q D j ⟶ decorated labels)
    (r : rightRaw K time Q D j ⟶ decorated labels)
    (h : overlapLeft K time Q D j ≫ l = overlapRight K time Q D j ≫ r)
    (l' : leftRaw K time Q D j ⟶ decorated labels')
    (r' : rightRaw K time Q D j ⟶ decorated labels')
    (h' : overlapLeft K time Q D j ≫ l' = overlapRight K time Q D j ≫ r')
    (hl : l ≫ rawOperator labels u = l') (hr : r ≫ rawOperator labels u = r') :
    glue K time Q D j labels l r h ≫ rawOperator labels u =
      glue K time Q D j labels' l' r' h' := by
  apply (interval_isPushout K time Q D j).hom_ext
  · rw [← Category.assoc, glue_left, glue_left]
    exact hl
  · rw [← Category.assoc, glue_right, glue_right]
    exact hr

end Postcomposition

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

private theorem endpoint_first (T : NecklaceCode) :
    SSet.boundary₁.ι₀ ≫ JTNecklaceEndpointCylinder.endpointInclusion T =
      pointAt T (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₀_desc]
  rfl

private theorem endpoint_last (T : NecklaceCode) :
    SSet.boundary₁.ι₁ ≫ JTNecklaceEndpointCylinder.endpointInclusion T =
      pointAt T (ULift.up (Fin.last T.len)) := by
  change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₁_desc]
  rfl

/-- The glued diagram retains the original ordered outer boundary. -/
theorem glue_outerBoundary
    (l : leftRaw J time Q D j ⟶ decorated labels)
    (r : rightRaw J time Q D j ⟶ decorated labels)
    (h : overlapLeft J time Q D j ≫ l = overlapRight J time Q D j ≫ r)
    (hL : ∀ p : I,
      (JTDecoratedIntervalMapping.firstLeft (D.obj p) j ⊗ₘ
        𝟙 (J.obj (time.obj p))) ≫ (l.app p).left =
        fst (Δ[0] : SSet.{0}) (J.obj (time.obj p)) ≫
          JTDecoratedIntervalMapping.cylinderFirst W x y (labels.obj p))
    (hR : ∀ p : I,
      (JTDecoratedIntervalMapping.lastRight (D.obj p) j ⊗ₘ
        𝟙 (J.obj (time.obj p))) ≫ (r.app p).left =
        fst (Δ[0] : SSet.{0}) (J.obj (time.obj p)) ≫
          JTDecoratedIntervalMapping.cylinderLast W x y (labels.obj p))
    (p : I) :
    (JTNecklaceEndpointCylinder.endpointInclusion (D.obj p).left ⊗ₘ
        𝟙 (J.obj (time.obj p))) ≫
      ((glue J time Q D j labels l r h).app p).left =
        fst B (J.obj (time.obj p)) ≫
          ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj
            (labels.obj p)).hom := by
  let X := J.obj (time.obj p)
  let S := (D.obj p).left
  let m := ((glue J time Q D j labels l r h).app p).left
  have hgl : ((leftInclusion J time Q D j).app p).left ≫ m = (l.app p).left :=
    congrArg CommaMorphism.left (NatTrans.congr_app (glue_left J time Q D j labels l r h) p)
  have hgr : ((rightInclusion J time Q D j).app p).left ≫ m = (r.app p).left :=
    congrArg CommaMorphism.left (NatTrans.congr_app (glue_right J time Q D j labels l r h) p)
  have hb0 : (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 X) ≫
      (JTNecklaceEndpointCylinder.endpointInclusion S ⊗ₘ 𝟙 X) =
      pointAt S (ULift.up 0) ⊗ₘ 𝟙 X := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, endpoint_first]
  have hb1 : (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 X) ≫
      (JTNecklaceEndpointCylinder.endpointInclusion S ⊗ₘ 𝟙 X) =
      pointAt S (ULift.up (Fin.last S.len)) ⊗ₘ 𝟙 X := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, endpoint_last]
  have hincL : ((leftInclusion J time Q D j).app p).left =
      JTTargetIntervalGluing.leftInclusion (D.obj p).hom j ⊗ₘ 𝟙 X := by
    rw [leftInclusion, parameterizeMap_app]
    rfl
  have hincR : ((rightInclusion J time Q D j).app p).left =
      JTTargetIntervalGluing.rightInclusion (D.obj p).hom j ⊗ₘ 𝟙 X := by
    rw [rightInclusion, parameterizeMap_app]
    rfl
  have hl0 : (JTDecoratedIntervalMapping.firstLeft (D.obj p) j ⊗ₘ 𝟙 X) ≫
      ((leftInclusion J time Q D j).app p).left =
      pointAt S (ULift.up 0) ⊗ₘ 𝟙 X := by
    rw [hincL]
    rw [tensorHom_comp_tensorHom, Category.id_comp,
      JTTargetIntervalOverMapping.left_first]
  have hr1 : (JTDecoratedIntervalMapping.lastRight (D.obj p) j ⊗ₘ 𝟙 X) ≫
      ((rightInclusion J time Q D j).app p).left =
      pointAt S (ULift.up (Fin.last S.len)) ⊗ₘ 𝟙 X := by
    rw [hincR]
    rw [tensorHom_comp_tensorHom, Category.id_comp,
      JTTargetIntervalOverMapping.right_last]
  apply SSet.boundary₁.hom_ext_rightTensor
  · change (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 X) ≫
        (JTNecklaceEndpointCylinder.endpointInclusion S ⊗ₘ 𝟙 X) ≫ m =
      (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 X) ≫ fst B X ≫
        ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj
          (labels.obj p)).hom
    calc
      _ = (pointAt S (ULift.up 0) ⊗ₘ 𝟙 X) ≫ m := by rw [← Category.assoc, hb0]
      _ = (JTDecoratedIntervalMapping.firstLeft (D.obj p) j ⊗ₘ 𝟙 X) ≫
          (l.app p).left := by rw [← hgl, ← Category.assoc, hl0]
      _ = fst (Δ[0] : SSet.{0}) X ≫
          JTDecoratedIntervalMapping.cylinderFirst W x y (labels.obj p) := hL p
      _ = _ := by
        change fst (Δ[0] : SSet.{0}) X ≫
          (SSet.boundary₁.ι₀ ≫ ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj
            (labels.obj p)).hom) = _
        rw [← Category.assoc (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 X) (fst B X) _]
        rw [tensorHom_fst, Category.assoc]
  · change (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 X) ≫
        (JTNecklaceEndpointCylinder.endpointInclusion S ⊗ₘ 𝟙 X) ≫ m =
      (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 X) ≫ fst B X ≫
        ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj
          (labels.obj p)).hom
    calc
      _ = (pointAt S (ULift.up (Fin.last S.len)) ⊗ₘ 𝟙 X) ≫ m := by
        rw [← Category.assoc, hb1]
      _ = (JTDecoratedIntervalMapping.lastRight (D.obj p) j ⊗ₘ 𝟙 X) ≫
          (r.app p).left := by rw [← hgr, ← Category.assoc, hr1]
      _ = fst (Δ[0] : SSet.{0}) X ≫
          JTDecoratedIntervalMapping.cylinderLast W x y (labels.obj p) := hR p
      _ = _ := by
        change fst (Δ[0] : SSet.{0}) X ≫
          (SSet.boundary₁.ι₁ ≫ ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj
            (labels.obj p)).hom) = _
        rw [← Category.assoc (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 X) (fst B X) _]
        rw [tensorHom_fst, Category.assoc]

end
end DaggerModels.PartII.JTDecoratedIntervalDiagram
