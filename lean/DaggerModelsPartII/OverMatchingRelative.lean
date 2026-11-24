import DaggerModelsPartII.ReedyMaps
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Over

/-!
# Limits of diagrams over an object and relative matching maps

The limit of a diagram in `Over B` is expressed as a pullback of the limit
of its underlying diagram against the limit of the constant diagram at `B`.
The formula includes the empty matching category in degree zero. Restricting
it to a Reedy matching category identifies the underlying matching arrow in
`Over B` with the relative matching arrow of the map to the constant diagram.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII.OverMatchingRelative

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimits C]
variable {J : Type} [SmallCategory J] (B : C)

/-- The structural maps of a diagram in `Over B`, as one natural map to the
constant diagram. -/
@[simps] def structureMap (D : J ⥤ Over B) :
    D ⋙ Over.forget B ⟶ (Functor.const J).obj B where
  app j := (D.obj j).hom
  naturality j k f := by
    change (D.map f).left ≫ (D.obj k).hom = (D.obj j).hom ≫ 𝟙 B
    simp [Over.w (D.map f)]

/-- The limit of the structural maps. -/
def limitStructureMap (D : J ⥤ Over B) :
    limit (D ⋙ Over.forget B) ⟶ limit ((Functor.const J).obj B) :=
  limMap (structureMap B D)

/-- The diagonal cone map from the fixed target to the limit of its constant
diagram. -/
def constantLimitMap : B ⟶ limit ((Functor.const J).obj B) :=
  limit.lift _ (constCone J B)

/-- The proposed underlying object of the limit in `Over B`. -/
def pullbackLimit (D : J ⥤ Over B) : C :=
  pullback (limitStructureMap B D) (constantLimitMap B)

/-- The canonical cone over `D` with pullback vertex. -/
def pullbackLimitCone (D : J ⥤ Over B) : Cone D where
  pt := Over.mk (pullback.snd (limitStructureMap B D) (constantLimitMap B))
  π :=
    { app := fun j ↦ Over.homMk
        (pullback.fst (limitStructureMap B D) (constantLimitMap B) ≫
          limit.π (D ⋙ Over.forget B) j)
        (by
          dsimp [limitStructureMap, constantLimitMap]
          calc
            (pullback.fst _ _ ≫ limit.π (D ⋙ Over.forget B) j) ≫ (D.obj j).hom =
                pullback.fst _ _ ≫ limMap (structureMap B D) ≫
                  limit.π ((Functor.const J).obj B) j := by
                    simp only [Category.assoc, limMap_π, structureMap_app]
            _ = pullback.snd _ _ ≫
                  limit.lift ((Functor.const J).obj B) (constCone J B) ≫
                  limit.π ((Functor.const J).obj B) j := by
                    have hc :
                        pullback.fst (limMap (structureMap B D))
                            (limit.lift ((Functor.const J).obj B) (constCone J B)) ≫
                          limMap (structureMap B D) =
                        pullback.snd (limMap (structureMap B D))
                            (limit.lift ((Functor.const J).obj B) (constCone J B)) ≫
                          limit.lift ((Functor.const J).obj B) (constCone J B) :=
                      pullback.condition
                    simpa only [Category.assoc] using
                      congrArg (fun f ↦ f ≫ limit.π ((Functor.const J).obj B) j)
                        hc
            _ = pullback.snd _ _ := by
                    simp [constCone])
      naturality := by
        intro j k f
        apply CostructuredArrow.hom_ext
        simpa [Category.assoc] using
          (congrArg
            (fun g ↦ pullback.fst (limitStructureMap B D) (constantLimitMap B) ≫ g)
            (limit.w (D ⋙ Over.forget B) f)).symm }

/-- The pullback cone is a limit cone, including when `J` is empty. -/
def pullbackLimitConeIsLimit (D : J ⥤ Over B) :
    IsLimit (pullbackLimitCone B D) := by
  let F := D ⋙ Over.forget B
  let a := structureMap B D
  let p := limitStructureMap B D
  let b : B ⟶ limit ((Functor.const J).obj B) := constantLimitMap B
  let Q := pullbackLimit B D
  let coneLift (s : Cone D) : s.pt.left ⟶ Q :=
    pullback.lift (limit.lift F ((Over.forget B).mapCone s)) s.pt.hom
      (by
        apply limit.hom_ext
        intro j
        simp [F, limitStructureMap, constantLimitMap,
          constCone, structureMap, Category.assoc, Over.w (s.π.app j)])
  refine
    { lift := fun s ↦ Over.homMk (coneLift s) (by
        change coneLift s ≫ pullback.snd p b = s.pt.hom
        exact pullback.lift_snd _ _ _)
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply CostructuredArrow.hom_ext
    change coneLift s ≫ pullback.fst p b ≫ limit.π F j = (s.π.app j).left
    calc
      _ = limit.lift F ((Over.forget B).mapCone s) ≫ limit.π F j := by
        rw [← Category.assoc]
        exact congrArg (fun f ↦ f ≫ limit.π F j) (pullback.lift_fst _ _ _)
      _ = (s.π.app j).left := limit.lift_π _ _
  · intro s m hm
    apply CostructuredArrow.hom_ext
    apply pullback.hom_ext
    · apply limit.hom_ext
      intro j
      have hj := congrArg CommaMorphism.left (hm j)
      change m.left ≫ pullback.fst p b ≫ limit.π F j = (s.π.app j).left at hj
      change (m.left ≫ pullback.fst p b) ≫ limit.π F j =
        (coneLift s ≫ pullback.fst p b) ≫ limit.π F j
      rw [Category.assoc, Category.assoc]
      calc
        _ = (s.π.app j).left := hj
        _ = limit.lift F ((Over.forget B).mapCone s) ≫ limit.π F j :=
          by simpa only [Functor.mapCone_π_app] using
            (limit.lift_π ((Over.forget B).mapCone s) j).symm
        _ = coneLift s ≫ pullback.fst p b ≫ limit.π F j := by
          rw [← Category.assoc]
          exact (congrArg (fun f ↦ f ≫ limit.π F j)
            (pullback.lift_fst _ _ _)).symm
    · change m.left ≫ pullback.snd p b = coneLift s ≫ pullback.snd p b
      calc
        _ = s.pt.hom := Over.w m
        _ = coneLift s ≫ pullback.snd p b := (pullback.lift_snd _ _ _).symm

/-- The underlying object of the actual limit in `Over B` is naturally
isomorphic to the pullback formula. -/
def limitPullbackIso (D : J ⥤ Over B) :
    (limit D).left ≅ pullbackLimit B D :=
  (Over.forget B).mapIso
    ((limit.isLimit D).conePointUniqueUpToIso (pullbackLimitConeIsLimit B D))

/-- The first projection of the limit iso is the universal map to the limit
of the underlying diagram. -/
theorem limitPullbackIso_fst (D : J ⥤ Over B) :
    (limitPullbackIso B D).hom ≫
        pullback.fst (limitStructureMap B D) (constantLimitMap B) =
      limit.lift (D ⋙ Over.forget B)
        ((Over.forget B).mapCone (limit.cone D)) := by
  apply limit.hom_ext
  intro j
  have hj := (limit.isLimit D).conePointUniqueUpToIso_hom_comp
    (pullbackLimitConeIsLimit B D) j
  have hj' := congrArg CommaMorphism.left hj
  simpa only [Category.assoc, limit.lift_π] using hj'

/-- The second projection of the limit iso is the structure map of the
limit object over `B`. -/
theorem limitPullbackIso_snd (D : J ⥤ Over B) :
    (limitPullbackIso B D).hom ≫
        pullback.snd (limitStructureMap B D) (constantLimitMap B) =
      (limit D).hom := by
  exact Over.w
    ((limit.isLimit D).conePointUniqueUpToIso
      (pullbackLimitConeIsLimit B D)).hom

/-- Matching in `Over B` is the relative matching pullback of the underlying
diagram's map to the constant diagram. -/
def matchingTargetIso (W : SimplexCategoryᵒᵖ ⥤ Over B) (n : ℕ) :
    ((matchingFunctor n).obj W).left ≅
      pullback ((matchingFunctor n).map (structureMap B W))
        ((matchingComparison n).app
          ((Functor.const SimplexCategoryᵒᵖ).obj B)) := by
  change (limit (matchingProjection n ⋙ W)).left ≅
    pullback (limitStructureMap B (matchingProjection n ⋙ W))
      (constantLimitMap B)
  exact limitPullbackIso B (matchingProjection n ⋙ W)

/-- The complete matching arrow, including its source, agrees with the
relative matching arrow. This applies in degree zero without an index
nonemptiness hypothesis. -/
def matchingArrowIso (W : SimplexCategoryᵒᵖ ⥤ Over B) (n : ℕ) :
    Arrow.mk (((matchingComparison n).app W).left) ≅
      Arrow.mk (relativeMatchingMap n (structureMap B W)) := by
  let e := matchingTargetIso B W n
  refine Arrow.isoMk' _ _ (Iso.refl _) e ?_
  apply pullback.hom_ext
  · apply limit.hom_ext
    intro s
    let D := matchingProjection n ⋙ W
    let F := D ⋙ Over.forget B
    have he := limitPullbackIso_fst B (matchingProjection n ⋙ W)
    have hw := congrArg CommaMorphism.left
      (limit.lift_π (matchingCone n W) s)
    have h1 :
        ((matchingComparison n).app W).left ≫ e.hom ≫
            pullback.fst (limitStructureMap B D) (constantLimitMap B) ≫
              limit.π F s = (W.map s.obj.hom).left := by
      calc
        _ = ((matchingComparison n).app W).left ≫
              limit.lift F ((Over.forget B).mapCone (limit.cone D)) ≫
                limit.π F s := by
                simpa only [Category.assoc] using
                  congrArg (fun f ↦ ((matchingComparison n).app W).left ≫ f ≫
                    limit.π F s) he
        _ = ((matchingComparison n).app W).left ≫ (limit.π D s).left := by
                simpa only [Category.assoc] using
                  congrArg (fun f ↦ ((matchingComparison n).app W).left ≫ f)
                    (limit.lift_π ((Over.forget B).mapCone (limit.cone D)) s)
        _ = (W.map s.obj.hom).left := hw
    simp only [Iso.refl_hom, Category.id_comp, relativeMatchingMap,
      pullback.lift_fst]
    calc
      _ = (W.map s.obj.hom).left := by
        exact limit.lift_π (matchingCone n (W ⋙ Over.forget B)) s
      _ = (((matchingComparison n).app W).left ≫ e.hom) ≫
            pullback.fst (limitStructureMap B D) (constantLimitMap B) ≫
              limit.π F s := by
        simpa only [Category.assoc] using h1.symm
      _ = _ := by
        dsimp [limitStructureMap, matchingFunctor, matchingComparison,
          constantLimitMap, structureMap]
        simp only [Category.assoc]
        congr 1
  · have he := limitPullbackIso_snd B (matchingProjection n ⋙ W)
    have hw := Over.w ((matchingComparison n).app W)
    have h2 :
        ((matchingComparison n).app W).left ≫ e.hom ≫
            pullback.snd (limitStructureMap B (matchingProjection n ⋙ W))
              (constantLimitMap B) = (W.obj (op ⦋n⦌)).hom := by
      calc
        _ = ((matchingComparison n).app W).left ≫ ((matchingFunctor n).obj W).hom := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ ((matchingComparison n).app W).left ≫ f) he
        _ = (W.obj (op ⦋n⦌)).hom := hw
    simp only [Iso.refl_hom, Category.id_comp, relativeMatchingMap,
      pullback.lift_snd]
    simpa only [Category.assoc, structureMap_app] using h2.symm

end

end DaggerModels.PartII.OverMatchingRelative
