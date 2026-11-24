import DaggerModelsPartII.JTTargetJointMarks

/-!
# Native pullbacks of joint-bounded target intervals

The preimage of a target interval is the source interval from the first
vertex above its initial joint to the last vertex above its final joint.
The pullback statement concerns complete simplicial maps in every degree.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetIntervalPullback

open NecklaceCode JTTargetJointMarks

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable {T U : NecklaceCode} (f : T ⟶ U)
variable (a b : Joint U) (hab : a.val ≤ b.val)

private abbrev start := (least f a).val
private abbrev finish := (greatest f b).val

include hab in
private theorem source_le : start f a ≤ finish f b :=
  (le_greatest_iff f b (start f a)).2 ((least f a).property.symm ▸ hab)

/-- The exact source interval over a joint-bounded target interval. -/
abbrev sourceInterval : NecklaceCode :=
  intervalCode T (start f a) (finish f b) (source_le f a b hab)

/-- The inclusion of the whole source interval into its original necklace. -/
def sourceInclusion : (sourceInterval f a b hab).toSSet ⟶ T.toSSet :=
  intervalι T (start f a) (finish f b) (source_le f a b hab)

private theorem vertex_orderMap (g : T.toSSet ⟶ U.toSSet)
    (x : T.toSSet.obj (op ⦋0⦌)) :
    (U.verticesEquiv (g.app (op ⦋0⦌) x)).down = orderMap g (T.verticesEquiv x).down := by
  dsimp [orderMap, mapVertices]
  rw [T.verticesEquiv.symm_apply_apply]

private theorem vertex_coordinate (N : NecklaceCode) (x : N.toSSet.obj (op ⦋0⦌)) :
    (N.verticesEquiv x).down = N.inclusion.app (op ⦋0⦌) x 0 :=
  N.verticesEquiv_down x

private theorem vertex_bounds (N : NecklaceCode) (i j : Fin (N.len + 1)) (hij : i ≤ j)
    (x : (intervalCode N i j hij).toSSet.obj (op ⦋0⦌)) :
    i ≤ (N.verticesEquiv ((intervalι N i j hij).app (op ⦋0⦌) x)).down ∧
      (N.verticesEquiv ((intervalι N i j hij).app (op ⦋0⦌) x)).down ≤ j := by
  rw [vertex_coordinate, intervalι_apply]
  exact intervalEmbedding_bounds N i j hij _

private theorem restriction_bounds (x : (sourceInterval f a b hab).toSSet.obj (op ⦋0⦌)) :
    a.val ≤ U.inclusion.app _ ((sourceInclusion f a b hab ≫ f.map).app _ x) 0 ∧
      U.inclusion.app _ ((sourceInclusion f a b hab ≫ f.map).app _ x) 0 ≤ b.val := by
  let z := (sourceInclusion f a b hab).app (op ⦋0⦌) x
  have h := vertex_bounds T (start f a) (finish f b) (source_le f a b hab) x
  change a.val ≤ U.inclusion.app _ (f.map.app _ z) 0 ∧
    U.inclusion.app _ (f.map.app _ z) 0 ≤ b.val
  simp only [← vertex_coordinate, vertex_orderMap]
  exact ⟨(least_le_iff f a _).1 h.1, (le_greatest_iff f b _).1 h.2⟩

/-- The full original map restricted to the indicated source and target intervals. -/
def restrict : (sourceInterval f a b hab).toSSet ⟶ (intervalCode U a.val b.val hab).toSSet :=
  intervalFactor U a.val b.val hab (sourceInclusion f a b hab ≫ f.map)
    (restriction_bounds f a b hab)

@[reassoc]
theorem restrict_fac :
    restrict f a b hab ≫ intervalι U a.val b.val hab = sourceInclusion f a b hab ≫ f.map :=
  intervalFactor_fac U a.val b.val hab _ _

private theorem cone_bounds (s : PullbackCone f.map (intervalι U a.val b.val hab))
    (x : s.pt.obj (op ⦋0⦌)) :
    start f a ≤ T.inclusion.app _ (s.fst.app _ x) 0 ∧
      T.inclusion.app _ (s.fst.app _ x) 0 ≤ finish f b := by
  have h := vertex_bounds U a.val b.val hab (s.snd.app (op ⦋0⦌) x)
  have e := congrFun (NatTrans.congr_app s.condition (op ⦋0⦌)) x
  change f.map.app (op ⦋0⦌) (s.fst.app (op ⦋0⦌) x) =
    (intervalι U a.val b.val hab).app (op ⦋0⦌) (s.snd.app (op ⦋0⦌) x) at e
  rw [← e, vertex_orderMap] at h
  simpa only [vertex_coordinate] using
    And.intro ((least_le_iff f a _).2 h.1) ((le_greatest_iff f b _).2 h.2)

/-- The two actual interval inclusions give the strict pullback of the original map. -/
theorem isPullback :
    IsPullback (sourceInclusion f a b hab) (restrict f a b hab)
      f.map (intervalι U a.val b.val hab) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk
    (sourceInclusion f a b hab) (restrict f a b hab) (restrict_fac f a b hab).symm)
  apply PullbackCone.isLimitAux'
  intro s
  let l := intervalFactor T (start f a) (finish f b) (source_le f a b hab)
    s.fst (cone_bounds f a b hab s)
  have hl : l ≫ sourceInclusion f a b hab = s.fst := intervalFactor_fac T _ _ _ _ _
  refine ⟨l, hl, ?_, ?_⟩
  · change l ≫ restrict f a b hab = s.snd
    apply (cancel_mono (intervalι U a.val b.val hab)).mp
    rw [Category.assoc, restrict_fac, ← Category.assoc, hl]
    exact s.condition
  · intro m hm _
    apply (cancel_mono (intervalι T (start f a) (finish f b) (source_le f a b hab))).mp
    exact hm.trans hl.symm

variable {T' T'' : NecklaceCode} {f' : T' ⟶ U} {f'' : T'' ⟶ U}

/-- A native over-target arrow restricts to the entire interval preimages. -/
def sourceMap (g : T ⟶ T') (h : g ≫ f' = f) :
    (sourceInterval f a b hab).toSSet ⟶ (sourceInterval f' a b hab).toSSet :=
  (isPullback f' a b hab).lift (sourceInclusion f a b hab ≫ g.map)
    (restrict f a b hab) (by
      have hmap : g.map ≫ f'.map = f.map := congrArg (fun k : Hom.{0} T U ↦ k.map) h
      rw [Category.assoc, hmap, restrict_fac])

@[reassoc]
theorem sourceMap_fac (g : T ⟶ T') (h : g ≫ f' = f) :
    sourceMap f a b hab g h ≫ sourceInclusion f' a b hab =
      sourceInclusion f a b hab ≫ g.map :=
  (isPullback f' a b hab).lift_fst _ _ _

@[reassoc]
theorem sourceMap_restrict (g : T ⟶ T') (h : g ≫ f' = f) :
    sourceMap f a b hab g h ≫ restrict f' a b hab = restrict f a b hab :=
  (isPullback f' a b hab).lift_snd _ _ _

theorem sourceMap_id :
    sourceMap f a b hab (𝟙 T) (Category.id_comp f) = 𝟙 _ := by
  apply (isPullback f a b hab).hom_ext
  · calc
      _ = sourceInclusion f a b hab ≫ 𝟙 T.toSSet :=
        sourceMap_fac f a b hab (𝟙 T) (Category.id_comp f)
      _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [sourceMap_restrict, Category.id_comp]

theorem sourceMap_comp (g : T ⟶ T') (h : g ≫ f' = f)
    (g' : T' ⟶ T'') (h' : g' ≫ f'' = f') :
    sourceMap f a b hab (g ≫ g') (by rw [Category.assoc, h', h]) =
      sourceMap f a b hab g h ≫ sourceMap f' a b hab g' h' := by
  apply (isPullback f'' a b hab).hom_ext
  · calc
      _ = sourceInclusion f a b hab ≫ (g.map ≫ g'.map) :=
        sourceMap_fac f a b hab (g ≫ g') (by rw [Category.assoc, h', h])
      _ = _ := by simp only [Category.assoc, sourceMap_fac, sourceMap_fac_assoc]
  · simp only [Category.assoc, sourceMap_restrict]

end

end DaggerModels.PartII.JTTargetIntervalPullback
