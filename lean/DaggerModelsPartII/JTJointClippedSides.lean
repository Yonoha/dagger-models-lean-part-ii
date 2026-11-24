import DaggerModelsPartII.JTTargetIntervalOverMapping
import ChosenNecklaceTargetJoints
import DaggerModelsPartII.JTNativeIntervalClamp

/-! The native clipped sides of a source over an actual joint of the fixed target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedSides

open NecklaceCode JTTargetJointMarks

noncomputable section

variable (U : NecklaceCode) (j : Joint U) (P : Over U)

private abbrev firstOver := (least P.hom j).val
private abbrev lastOver := (greatest P.hom j).val

/-- The left native source ends at the first vertex above the target joint. -/
def leftSourceOver : NecklacesOver U.toSSet U.first (U.verticesEquiv.symm (ULift.up j.val)) where
  code := cutLeft P.left (firstOver U j P)
  map := cutLeftι P.left (firstOver U j P) ≫ P.hom.map
  first := by
    change P.hom.map.app _ ((intervalι P.left 0 (firstOver U j P) (Fin.zero_le _)).app _
      (intervalCode P.left 0 (firstOver U j P) (Fin.zero_le _)).first) = U.first
    rw [intervalι_first]
    exact P.hom.first
  last := by
    change P.hom.map.app _ ((intervalι P.left 0 (firstOver U j P) (Fin.zero_le _)).app _
      (intervalCode P.left 0 (firstOver U j P) (Fin.zero_le _)).last) = _
    rw [intervalι_last]
    apply U.verticesEquiv.injective
    apply ULift.ext
    simpa only [Equiv.apply_symm_apply] using (least P.hom j).property

/-- The right native source starts at the last vertex above the target joint. -/
def rightSourceOver : NecklacesOver U.toSSet (U.verticesEquiv.symm (ULift.up j.val)) U.last where
  code := cutRight P.left (lastOver U j P)
  map := cutRightι P.left (lastOver U j P) ≫ P.hom.map
  first := by
    change P.hom.map.app _ ((intervalι P.left (lastOver U j P) (Fin.last P.left.len)
      (Fin.le_last _)).app _ (intervalCode P.left (lastOver U j P) (Fin.last P.left.len)
      (Fin.le_last _)).first) = _
    rw [intervalι_first]
    apply U.verticesEquiv.injective
    apply ULift.ext
    simpa only [Equiv.apply_symm_apply] using (greatest P.hom j).property
  last := by
    change P.hom.map.app _ ((intervalι P.left (lastOver U j P) (Fin.last P.left.len)
      (Fin.le_last _)).app _ (intervalCode P.left (lastOver U j P) (Fin.last P.left.len)
      (Fin.le_last _)).last) = U.last
    rw [intervalι_last]
    exact P.hom.last

/-- The left restriction preserves both endpoints into the literal left cut of the target. -/
def leftObj : Over (cutLeft U j.val) :=
  Over.mk (toInterval U 0 j.val (Fin.zero_le _) (leftSourceOver U j P)).hom

/-- The right restriction preserves both endpoints into the literal right cut of the target. -/
def rightObj : Over (cutRight U j.val) :=
  Over.mk (toInterval U j.val (Fin.last U.len) (Fin.le_last _) (rightSourceOver U j P)).hom

@[reassoc]
theorem leftObj_fac :
    (leftObj U j P).hom.map ≫ cutLeftι U j.val =
      cutLeftι P.left (firstOver U j P) ≫ P.hom.map :=
  toInterval_original U 0 j.val (Fin.zero_le _) (leftSourceOver U j P)

@[reassoc]
theorem rightObj_fac :
    (rightObj U j P).hom.map ≫ cutRightι U j.val =
      cutRightι P.left (lastOver U j P) ≫ P.hom.map :=
  toInterval_original U j.val (Fin.last U.len) (Fin.le_last _) (rightSourceOver U j P)

variable {P} {P' : Over U} (g : P ⟶ P')

private theorem over_orderMap (v : Fin (P.left.len + 1)) :
    orderMap P'.hom.map (orderMap g.left.map v) = orderMap P.hom.map v := by
  have h : g.left.map ≫ P'.hom.map = P.hom.map :=
    congrArg (fun f : P.left ⟶ U ↦ f.map) (Over.w g)
  exact (orderMap_comp_apply g.left.map P'.hom.map v).symm.trans
    (congrArg (fun m : P.left.toSSet ⟶ U.toSSet ↦ orderMap m v) h)

private theorem firstOver_le_map :
    firstOver U j P' ≤ orderMap g.left.map (firstOver U j P) := by
  apply (least_le_iff P'.hom j _).2
  rw [over_orderMap U g, (least P.hom j).property]

private theorem map_le_lastOver :
    orderMap g.left.map (lastOver U j P) ≤ lastOver U j P' := by
  apply (le_greatest_iff P'.hom j _).2
  rw [over_orderMap U g, (greatest P.hom j).property]

/-- Clipping before or after transport gives the same left vertex after the final clip. -/
theorem min_transport (v : Fin (P.left.len + 1)) :
    min (orderMap g.left.map (min v (firstOver U j P))) (firstOver U j P') =
      min (orderMap g.left.map v) (firstOver U j P') := by
  rcases le_total v (firstOver U j P) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, min_eq_right (firstOver_le_map U j g),
      min_eq_right ((firstOver_le_map U j g).trans ((orderMap g.left.map).monotone h))]

/-- Clipping before or after transport gives the same right vertex after the final clip. -/
theorem max_transport (v : Fin (P.left.len + 1)) :
    max (orderMap g.left.map (max v (lastOver U j P))) (lastOver U j P') =
      max (orderMap g.left.map v) (lastOver U j P') := by
  rcases le_total v (lastOver U j P) with h | h
  · rw [max_eq_right h, max_eq_right (map_le_lastOver U j g),
      max_eq_right (((orderMap g.left.map).monotone h).trans (map_le_lastOver U j g))]
  · rw [max_eq_left h]

/-- The left clamp keeps the original target value within the full left interval. -/
theorem min_over_target (v : Fin (P.left.len + 1)) (h : orderMap P.hom.map v ≤ j.val) :
    orderMap P.hom.map (min v (firstOver U j P)) = orderMap P.hom.map v := by
  rcases le_total v (firstOver U j P) with hv | hv
  · rw [min_eq_left hv]
  · rw [min_eq_right hv, (least P.hom j).property]
    exact le_antisymm ((least_le_iff P.hom j _).1 hv) h

/-- The right clamp keeps the original target value within the full right interval. -/
theorem max_over_target (v : Fin (P.left.len + 1)) (h : j.val ≤ orderMap P.hom.map v) :
    orderMap P.hom.map (max v (lastOver U j P)) = orderMap P.hom.map v := by
  rcases le_total v (lastOver U j P) with hv | hv
  · rw [max_eq_right hv, (greatest P.hom j).property]
    exact le_antisymm h ((le_greatest_iff P.hom j _).1 hv)
  · rw [max_eq_left hv]


open JTNativeIntervalClamp (leftClamp rightClamp leftClamp_orderMap rightClamp_orderMap)

private theorem by_orderMap {T T' : NecklaceCode} {f g : T.toSSet ⟶ T'.toSSet}
    (h : ∀ v, orderMap f v = orderMap g v) : f = g := by
  apply hom_ext_vertices
  funext v
  cases v with
  | up v => exact ULift.ext _ _ (h v)

private theorem intervalι_orderMap (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)
    (v : Fin ((intervalCode T a b hab).len + 1)) :
    orderMap (intervalι T a b hab) v = intervalEmbedding T a b hab v :=
  congrArg ULift.down (intervalι_vertices T a b hab (ULift.up v))

private theorem leftSection (P : Over U) :
    cutLeftι P.left (firstOver U j P) ≫ leftClamp P.left (firstOver U j P) = 𝟙 _ := by
  let p := firstOver U j P
  let i := cutLeftι P.left p
  let c := leftClamp P.left p
  haveI : Mono i := inferInstanceAs (Mono (intervalι P.left 0 p (Fin.zero_le _)))
  apply (cancel_mono i).mp
  rw [Category.id_comp, Category.assoc]
  apply by_orderMap (T := cutLeft P.left p) (T' := P.left)
  intro v
  have hv : orderMap i v ≤ p :=
    (intervalι_orderMap P.left 0 p (Fin.zero_le _) v).symm ▸
      (intervalEmbedding_bounds P.left 0 p (Fin.zero_le _) v).2
  exact (orderMap_comp_apply i (c ≫ i) v).trans
    ((leftClamp_orderMap _ _ _).trans (min_eq_left hv))

/-- An earlier native left clamp is absorbed after transport and the final clamp. -/
theorem leftClamp_transport :
    (leftClamp P.left (firstOver U j P) ≫ cutLeftι P.left (firstOver U j P)) ≫
      g.left.map ≫ leftClamp P'.left (firstOver U j P') =
      g.left.map ≫ leftClamp P'.left (firstOver U j P') := by
  let p := firstOver U j P
  let p' := firstOver U j P'
  let i := cutLeftι P.left p
  let i' := cutLeftι P'.left p'
  let c := leftClamp P.left p
  let c' := leftClamp P'.left p'
  haveI : Mono i' := inferInstanceAs (Mono (intervalι P'.left 0 p' (Fin.zero_le _)))
  apply (cancel_mono i').mp
  simp only [Category.assoc]
  change c ≫ i ≫ g.left.map ≫ (c' ≫ i') = g.left.map ≫ (c' ≫ i')
  rw [← Category.assoc c i]
  apply by_orderMap (T := P.left) (T' := P'.left)
  intro v
  have formula (u : Fin (P.left.len + 1)) :
      orderMap (g.left.map ≫ (c' ≫ i')) u = min (orderMap g.left.map u) p' :=
    (orderMap_comp_apply g.left.map (c' ≫ i') u).trans (leftClamp_orderMap _ _ _)
  calc
    _ = orderMap (g.left.map ≫ (c' ≫ i')) (orderMap (c ≫ i) v) :=
      orderMap_comp_apply (c ≫ i) (g.left.map ≫ (c' ≫ i')) v
    _ = min (orderMap g.left.map (min v p)) p' := by
      rw [formula, leftClamp_orderMap]
    _ = min (orderMap g.left.map v) p' := min_transport U j g v
    _ = _ := (formula v).symm

private theorem rightSection (P : Over U) :
    cutRightι P.left (lastOver U j P) ≫ rightClamp P.left (lastOver U j P) = 𝟙 _ := by
  let p := lastOver U j P
  let i := cutRightι P.left p
  let c := rightClamp P.left p
  haveI : Mono i :=
    inferInstanceAs (Mono (intervalι P.left p (Fin.last P.left.len) (Fin.le_last _)))
  apply (cancel_mono i).mp
  rw [Category.id_comp, Category.assoc]
  apply by_orderMap (T := cutRight P.left p) (T' := P.left)
  intro v
  have hv : p ≤ orderMap i v :=
    (intervalι_orderMap P.left p (Fin.last P.left.len) (Fin.le_last _) v).symm ▸
      (intervalEmbedding_bounds P.left p (Fin.last P.left.len) (Fin.le_last _) v).1
  exact (orderMap_comp_apply i (c ≫ i) v).trans
    ((rightClamp_orderMap _ _ _).trans (max_eq_left hv))

/-- An earlier native right clamp is absorbed after transport and the final clamp. -/
theorem rightClamp_transport :
    (rightClamp P.left (lastOver U j P) ≫ cutRightι P.left (lastOver U j P)) ≫
      g.left.map ≫ rightClamp P'.left (lastOver U j P') =
      g.left.map ≫ rightClamp P'.left (lastOver U j P') := by
  let p := lastOver U j P
  let p' := lastOver U j P'
  let i := cutRightι P.left p
  let i' := cutRightι P'.left p'
  let c := rightClamp P.left p
  let c' := rightClamp P'.left p'
  haveI : Mono i' :=
    inferInstanceAs (Mono (intervalι P'.left p' (Fin.last P'.left.len) (Fin.le_last _)))
  apply (cancel_mono i').mp
  simp only [Category.assoc]
  change c ≫ i ≫ g.left.map ≫ (c' ≫ i') = g.left.map ≫ (c' ≫ i')
  rw [← Category.assoc c i]
  apply by_orderMap (T := P.left) (T' := P'.left)
  intro v
  have formula (u : Fin (P.left.len + 1)) :
      orderMap (g.left.map ≫ (c' ≫ i')) u = max (orderMap g.left.map u) p' :=
    (orderMap_comp_apply g.left.map (c' ≫ i') u).trans (rightClamp_orderMap _ _ _)
  calc
    _ = orderMap (g.left.map ≫ (c' ≫ i')) (orderMap (c ≫ i) v) :=
      orderMap_comp_apply (c ≫ i) (g.left.map ≫ (c' ≫ i')) v
    _ = max (orderMap g.left.map (max v p)) p' := by
      rw [formula, rightClamp_orderMap]
    _ = max (orderMap g.left.map v) p' := max_transport U j g v
    _ = _ := (formula v).symm

private def leftArrowMap :
    (leftObj U j P).left.toSSet ⟶ (leftObj U j P').left.toSSet :=
  cutLeftι P.left (firstOver U j P) ≫ g.left.map ≫ leftClamp P'.left (firstOver U j P')

private def rightArrowMap :
    (rightObj U j P).left.toSSet ⟶ (rightObj U j P').left.toSSet :=
  cutRightι P.left (lastOver U j P) ≫ g.left.map ≫ rightClamp P'.left (lastOver U j P')

private theorem leftArrow_coord (v : Fin ((leftObj U j P).left.len + 1)) :
    orderMap (leftArrowMap U j g ≫ cutLeftι P'.left (firstOver U j P')) v =
      min (orderMap g.left.map (intervalEmbedding P.left 0 (firstOver U j P) (Fin.zero_le _) v))
        (firstOver U j P') := by
  let i := cutLeftι P.left (firstOver U j P)
  let z := leftClamp P'.left (firstOver U j P') ≫ cutLeftι P'.left (firstOver U j P')
  have e : leftArrowMap U j g ≫ cutLeftι P'.left (firstOver U j P') =
      i ≫ g.left.map ≫ z := by simp only [leftArrowMap, i, z, Category.assoc]
  rw [e]
  calc
    _ = orderMap (g.left.map ≫ z) (orderMap i v) :=
      orderMap_comp_apply i (g.left.map ≫ z) v
    _ = min (orderMap g.left.map (orderMap i v)) (firstOver U j P') :=
      (orderMap_comp_apply g.left.map z _).trans (leftClamp_orderMap _ _ _)
    _ = _ := congrArg (fun a ↦ min (orderMap g.left.map a) (firstOver U j P'))
      (intervalι_orderMap P.left 0 (firstOver U j P) (Fin.zero_le _) v)

private theorem rightArrow_coord (v : Fin ((rightObj U j P).left.len + 1)) :
    orderMap (rightArrowMap U j g ≫ cutRightι P'.left (lastOver U j P')) v =
      max (orderMap g.left.map
        (intervalEmbedding P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _) v))
        (lastOver U j P') := by
  let i := cutRightι P.left (lastOver U j P)
  let z := rightClamp P'.left (lastOver U j P') ≫ cutRightι P'.left (lastOver U j P')
  have e : rightArrowMap U j g ≫ cutRightι P'.left (lastOver U j P') =
      i ≫ g.left.map ≫ z := by simp only [rightArrowMap, i, z, Category.assoc]
  rw [e]
  calc
    _ = orderMap (g.left.map ≫ z) (orderMap i v) :=
      orderMap_comp_apply i (g.left.map ≫ z) v
    _ = max (orderMap g.left.map (orderMap i v)) (lastOver U j P') :=
      (orderMap_comp_apply g.left.map z _).trans (rightClamp_orderMap _ _ _)
    _ = _ := congrArg (fun a ↦ max (orderMap g.left.map a) (lastOver U j P'))
      (intervalι_orderMap P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _) v)

private theorem endpoint_of_orderMap {A B C : NecklaceCode}
    (f : A.toSSet ⟶ B.toSSet) (ι : B.toSSet ⟶ C.toSSet) [Mono ι]
    (a : Fin (A.len + 1)) (b : Fin (B.len + 1))
    (h : orderMap (f ≫ ι) a = orderMap ι b) :
    pointAt A (ULift.up a) ≫ f = pointAt B (ULift.up b) := by
  apply (cancel_mono ι).mp
  rw [Category.assoc, pointAt_comp, pointAt_comp]
  exact congrArg (fun v : Fin (C.len + 1) ↦ pointAt C (ULift.up v)) h

private theorem sandwich_comp {A B C D E F : SSet.{0}}
    (i : A ⟶ B) (u : B ⟶ C) (c : C ⟶ D) (k : D ⟶ C) (v : C ⟶ E) (d : E ⟶ F)
    (h : (c ≫ k) ≫ v ≫ d = v ≫ d) :
    (i ≫ u ≫ c) ≫ (k ≫ v ≫ d) = i ≫ (u ≫ v) ≫ d := by
  calc
    _ = (i ≫ u) ≫ ((c ≫ k) ≫ v ≫ d) := by simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc]

private theorem leftArrow_over :
    (leftArrowMap U j g ≫ cutLeftι P'.left (firstOver U j P')) ≫ P'.hom.map =
      cutLeftι P.left (firstOver U j P) ≫ P.hom.map := by
  apply by_orderMap (T := (leftObj U j P).left) (T' := U)
  intro v
  let x := intervalEmbedding P.left 0 (firstOver U j P) (Fin.zero_le _) v
  have hx : orderMap P'.hom.map (orderMap g.left.map x) ≤ j.val := by
    rw [over_orderMap U g]
    have hw := (orderMap P.hom.map).monotone
      (intervalEmbedding_bounds P.left 0 (firstOver U j P) (Fin.zero_le _) v).2
    simpa only [x, (least P.hom j).property] using hw
  calc
    _ = orderMap P'.hom.map
        (orderMap (leftArrowMap U j g ≫ cutLeftι P'.left (firstOver U j P')) v) :=
      orderMap_comp_apply _ P'.hom.map _
    _ = orderMap P'.hom.map (min (orderMap g.left.map x) (firstOver U j P')) :=
      congrArg (fun a ↦ orderMap P'.hom.map a) (leftArrow_coord U j g v)
    _ = orderMap P'.hom.map (orderMap g.left.map x) :=
      min_over_target U j (P := P') _ hx
    _ = orderMap P.hom.map x := over_orderMap U g x
    _ = _ := ((orderMap_comp_apply (cutLeftι P.left (firstOver U j P))
      P.hom.map v).trans (congrArg (fun a ↦ orderMap P.hom.map a)
        (intervalι_orderMap P.left 0 (firstOver U j P) (Fin.zero_le _) v))).symm

private def leftArrowHom : (leftObj U j P).left ⟶ (leftObj U j P').left where
  map := leftArrowMap U j g
  first := first_of_point _ (by
    letI : Mono (cutLeftι P'.left (firstOver U j P')) :=
      inferInstanceAs (Mono (intervalι P'.left 0 (firstOver U j P') (Fin.zero_le _)))
    apply endpoint_of_orderMap _ (cutLeftι P'.left (firstOver U j P'))
    rw [leftArrow_coord, intervalEmbedding_first, orderMap_first,
      min_eq_left (Fin.zero_le _)]
    exact ((intervalι_orderMap P'.left 0 (firstOver U j P') (Fin.zero_le _) 0).trans
      (intervalEmbedding_first P'.left 0 (firstOver U j P') (Fin.zero_le _))).symm)
  last := last_of_point _ (by
    letI : Mono (cutLeftι P'.left (firstOver U j P')) :=
      inferInstanceAs (Mono (intervalι P'.left 0 (firstOver U j P') (Fin.zero_le _)))
    apply endpoint_of_orderMap _ (cutLeftι P'.left (firstOver U j P'))
    have h : intervalEmbedding P.left 0 (firstOver U j P) (Fin.zero_le _)
        (Fin.last (leftObj U j P).left.len) = firstOver U j P :=
      intervalEmbedding_last P.left 0 (firstOver U j P) (Fin.zero_le _)
    rw [leftArrow_coord, h, min_eq_right (firstOver_le_map U j g)]
    exact ((intervalι_orderMap P'.left 0 (firstOver U j P') (Fin.zero_le _) _).trans
      (intervalEmbedding_last P'.left 0 (firstOver U j P') (Fin.zero_le _))).symm)

private def leftArrow : leftObj U j P ⟶ leftObj U j P' :=
  Over.homMk (leftArrowHom U j g) (by
    apply NecklaceCode.Hom.ext
    haveI : Mono (cutLeftι.{0} U j.val) :=
      inferInstanceAs (Mono (intervalι U 0 j.val (Fin.zero_le _)))
    apply (cancel_mono (cutLeftι U j.val)).mp
    change (leftArrowMap U j g ≫ (leftObj U j P').hom.map) ≫ cutLeftι U j.val =
      (leftObj U j P).hom.map ≫ cutLeftι U j.val
    rw [Category.assoc, leftObj_fac, leftObj_fac, ← Category.assoc]
    exact leftArrow_over U j g)

/-- The native left clip is functorial on every original over-target arrow. -/
def leftNative : Over U ⥤ Over (cutLeft U j.val) where
  obj P := leftObj U j P
  map g := leftArrow U j g
  map_id P := by
    apply Over.OverMorphism.ext
    apply NecklaceCode.Hom.ext
    change cutLeftι P.left (firstOver U j P) ≫ 𝟙 P.left.toSSet ≫
      leftClamp P.left (firstOver U j P) = 𝟙 _
    rw [Category.id_comp, leftSection U j P]
  map_comp {P P' P''} g h := by
    apply Over.OverMorphism.ext
    apply NecklaceCode.Hom.ext
    change cutLeftι P.left (firstOver U j P) ≫ (g.left.map ≫ h.left.map) ≫
        leftClamp P''.left (firstOver U j P'') =
      leftArrowMap U j g ≫ leftArrowMap U j h
    exact (sandwich_comp _ _ _ _ _ _ (leftClamp_transport U j h)).symm

private theorem rightArrow_over :
    (rightArrowMap U j g ≫ cutRightι P'.left (lastOver U j P')) ≫ P'.hom.map =
      cutRightι P.left (lastOver U j P) ≫ P.hom.map := by
  apply by_orderMap (T := (rightObj U j P).left) (T' := U)
  intro v
  let x := intervalEmbedding P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _) v
  have hx : j.val ≤ orderMap P'.hom.map (orderMap g.left.map x) := by
    rw [over_orderMap U g]
    have hw := (orderMap P.hom.map).monotone
      (intervalEmbedding_bounds P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _) v).1
    simpa only [x, (greatest P.hom j).property] using hw
  calc
    _ = orderMap P'.hom.map
        (orderMap (rightArrowMap U j g ≫ cutRightι P'.left (lastOver U j P')) v) :=
      orderMap_comp_apply _ P'.hom.map _
    _ = orderMap P'.hom.map (max (orderMap g.left.map x) (lastOver U j P')) :=
      congrArg (fun a ↦ orderMap P'.hom.map a) (rightArrow_coord U j g v)
    _ = orderMap P'.hom.map (orderMap g.left.map x) :=
      max_over_target U j (P := P') _ hx
    _ = orderMap P.hom.map x := over_orderMap U g x
    _ = _ := ((orderMap_comp_apply (cutRightι P.left (lastOver U j P))
      P.hom.map v).trans (congrArg (fun a ↦ orderMap P.hom.map a)
        (intervalι_orderMap P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _) v))).symm

private def rightArrowHom : (rightObj U j P).left ⟶ (rightObj U j P').left where
  map := rightArrowMap U j g
  first := first_of_point _ (by
    letI : Mono (cutRightι P'.left (lastOver U j P')) :=
      inferInstanceAs (Mono
        (intervalι P'.left (lastOver U j P') (Fin.last P'.left.len) (Fin.le_last _)))
    apply endpoint_of_orderMap _ (cutRightι P'.left (lastOver U j P'))
    rw [rightArrow_coord, intervalEmbedding_first, max_eq_right (map_le_lastOver U j g)]
    let p' := lastOver U j P'
    exact ((intervalι_orderMap P'.left p' (Fin.last P'.left.len) (Fin.le_last _) 0).trans
      (intervalEmbedding_first P'.left p' (Fin.last P'.left.len) (Fin.le_last _))).symm)
  last := last_of_point _ (by
    letI : Mono (cutRightι P'.left (lastOver U j P')) :=
      inferInstanceAs (Mono
        (intervalι P'.left (lastOver U j P') (Fin.last P'.left.len) (Fin.le_last _)))
    apply endpoint_of_orderMap _ (cutRightι P'.left (lastOver U j P'))
    have h : intervalEmbedding P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _)
        (Fin.last (rightObj U j P).left.len) = Fin.last P.left.len :=
      intervalEmbedding_last P.left (lastOver U j P) (Fin.last P.left.len) (Fin.le_last _)
    rw [rightArrow_coord, h, orderMap_last, max_eq_left (Fin.le_last _)]
    let p' := lastOver U j P'
    exact ((intervalι_orderMap P'.left p' (Fin.last P'.left.len) (Fin.le_last _) _).trans
      (intervalEmbedding_last P'.left p' (Fin.last P'.left.len) (Fin.le_last _))).symm)

private def rightArrow : rightObj U j P ⟶ rightObj U j P' :=
  Over.homMk (rightArrowHom U j g) (by
    apply NecklaceCode.Hom.ext
    haveI : Mono (cutRightι.{0} U j.val) :=
      inferInstanceAs (Mono (intervalι U j.val (Fin.last U.len) (Fin.le_last _)))
    apply (cancel_mono (cutRightι U j.val)).mp
    change (rightArrowMap U j g ≫ (rightObj U j P').hom.map) ≫ cutRightι U j.val =
      (rightObj U j P).hom.map ≫ cutRightι U j.val
    rw [Category.assoc, rightObj_fac, rightObj_fac, ← Category.assoc]
    exact rightArrow_over U j g)

/-- The native right clip is functorial on every original over-target arrow. -/
def rightNative : Over U ⥤ Over (cutRight U j.val) where
  obj P := rightObj U j P
  map g := rightArrow U j g
  map_id P := by
    apply Over.OverMorphism.ext
    apply NecklaceCode.Hom.ext
    change cutRightι P.left (lastOver U j P) ≫ 𝟙 P.left.toSSet ≫
      rightClamp P.left (lastOver U j P) = 𝟙 _
    rw [Category.id_comp, rightSection U j P]
  map_comp {P P' P''} g h := by
    apply Over.OverMorphism.ext
    apply NecklaceCode.Hom.ext
    change cutRightι P.left (lastOver U j P) ≫ (g.left.map ≫ h.left.map) ≫
        rightClamp P''.left (lastOver U j P'') =
      rightArrowMap U j g ≫ rightArrowMap U j h
    exact (sandwich_comp _ _ _ _ _ _ (rightClamp_transport U j h)).symm


/-- The original native arrow restricted to the left and then clipped. -/
theorem leftNative_map :
    ((leftNative U j).map g).left.map =
      cutLeftι P.left (least P.hom j).val ≫ g.left.map ≫
        leftClamp P'.left (least P'.hom j).val := rfl

/-- The original native arrow restricted to the right and then clipped. -/
theorem rightNative_map :
    ((rightNative U j).map g).left.map =
      cutRightι P.left (greatest P.hom j).val ≫ g.left.map ≫
        rightClamp P'.left (greatest P'.hom j).val := rfl

end
end DaggerModels.PartII.JTJointClippedSides
