import DaggerModelsPartII.DaggerNerveLengthFiltration
import DaggerModelsPartII.DaggerSimplexUnitImage
import DaggerModelsPartII.SegalRepresentables
import NativeStandardSpineGeometry

/-!
# The length-one stage and the literal free dagger spine

The source of the canonical map is the free dagger completion of the
standard spine subcomplex of the ordinary simplex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerNerveLengthFiltration
open DaggerModels.PartII.DaggerSimplexNerveRepresentable
open DaggerModels.PartII.DaggerSimplexNerveNaturality
open DaggerModels.PartII.SegalLocalizers

namespace DaggerModels.PartII.DaggerNerveLengthOne

noncomputable section

/-- The ordinary simplex classifying the identity functor of the free dagger
simplex, viewed as its canonical forward letter chain. -/
def canonicalSimplex (m : ℕ) :
    (Δ[m] : SSet.{0}) ⟶
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).toSSet :=
  SSet.yonedaEquiv.symm
    (pathHomChainEquiv m m (𝟙 (⟨m⟩ : DaggerSimplex)))

/-- The canonical map from the free dagger simplex to its full native nerve. -/
def canonicalDaggerMap (m : ℕ) :
    freeSimplex.{0} m ⟶
      DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m) :=
  (freeDaggerAdjunction.{0}.homEquiv
    (Δ[m] : SSet.{0})
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m))).symm (canonicalSimplex m)

/-- The literal map from the free dagger completion of the standard spine
into the full native nerve. -/
def canonicalSpineMap (m : ℕ) :
    freeDagger.obj (ordinarySpine.{0} m) ⟶
      DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m) :=
  freeDagger.map (DaggerNativeStandardSpineInner.spine.{0} m).ι ≫
    canonicalDaggerMap m

def canonicalSpinePresheafMap (m : ℕ) :
    DaggerSSet.toPresheaf.obj (freeDagger.obj (ordinarySpine.{0} m)) ⟶
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension :=
  DaggerSSet.toPresheaf.map (canonicalSpineMap m)

theorem canonicalDaggerMap_unit (m : ℕ) :
    freeDaggerAdjunction.{0}.unit.app (Δ[m] : SSet.{0}) ≫
      (canonicalDaggerMap m).hom = canonicalSimplex m := by
  change freeDaggerAdjunction.{0}.unit.app (Δ[m] : SSet.{0}) ≫
      DaggerSSet.forget.map (canonicalDaggerMap m) = canonicalSimplex m
  change (freeDaggerAdjunction.{0}.homEquiv
    (Δ[m] : SSet.{0})
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)))
    ((freeDaggerAdjunction.{0}.homEquiv
      (Δ[m] : SSet.{0})
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m))).symm (canonicalSimplex m)) = canonicalSimplex m
  exact Equiv.apply_symm_apply _ _

theorem canonicalSpineMap_unit (m : ℕ) :
    freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m) ≫
      (canonicalSpineMap m).hom =
      (DaggerNativeStandardSpineInner.spine.{0} m).ι ≫ canonicalSimplex m := by
  let incl := (DaggerNativeStandardSpineInner.spine.{0} m).ι
  have hnat : freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m) ≫
      DaggerSSet.forget.map (freeDagger.map incl) =
        incl ≫ freeDaggerAdjunction.{0}.unit.app (Δ[m] : SSet.{0}) := by
    simpa only [Functor.comp_map] using
      (freeDaggerAdjunction.unit.naturality incl).symm
  change (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m) ≫
      DaggerSSet.forget.map (freeDagger.map incl)) ≫
        (canonicalDaggerMap m).hom = _
  rw [hnat, Category.assoc, canonicalDaggerMap_unit]

/-- On an ordinary monotone simplex, the canonical map is exactly the native
chain classified by its image under `u`. -/
theorem canonicalSimplex_apply {k m : ℕ} (f : ⦋k⦌ ⟶ ⦋m⦌) :
    (canonicalSimplex m).app (op ⦋k⦌)
        (SSet.stdSimplex.objEquiv.symm f) =
      pathHomChainEquiv k m
        (u.map (ReverseSimplex.inclusion.map f)) := by
  let α : (ReverseSimplex.mk k) ⟶ (ReverseSimplex.mk m) :=
    ReverseSimplex.inclusion.map f
  have hα : Monotone α.toFun := f.toOrderHom.monotone
  have hpre := pathHomChainEquiv_precomp_monotone α hα m
    (𝟙 (⟨m⟩ : DaggerSimplex))
  have hcomp : u.map α ≫ (𝟙 (⟨m⟩ : DaggerSimplex)) = u.map α :=
    Category.comp_id _
  rw [hcomp] at hpre
  rw [hpre]
  rw [DaggerSSet.extensionMap_monotone _ α hα]
  rfl

/-- A monotone simplex whose endpoint span is at most one lies in the
literal image of the free dagger spine. -/
theorem monotone_u_map_mem_spine_range {k m : ℕ}
    (f : ⦋k⦌ ⟶ ⦋m⦌)
    (hspan : (f.toOrderHom (Fin.last k)).val ≤
      (f.toOrderHom 0).val + 1) :
    pathHomChainEquiv k m (u.map (ReverseSimplex.inclusion.map f)) ∈
      (Subfunctor.range (canonicalSpinePresheafMap m)).obj
        (op (ReverseSimplex.mk k)) := by
  let c : (Δ[m] : SSet.{0}).obj (op ⦋k⦌) :=
    SSet.stdSimplex.objEquiv.symm f
  have hc : c ∈ (DaggerNativeStandardSpineInner.spine.{0} m).obj
      (op ⦋k⦌) := by
    apply (DaggerNativeStandardSpineInner.mem_spine_iff c).2
    simpa only [SSet.stdSimplex.objEquiv_symm_apply] using hspan
  let z : (ordinarySpine.{0} m).obj (op ⦋k⦌) := ⟨c, hc⟩
  refine ⟨(freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
    (op ⦋k⦌) z, ?_⟩
  have he := congrFun (NatTrans.congr_app (canonicalSpineMap_unit m)
    (op ⦋k⦌)) z
  change (canonicalSpineMap m).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌) z) =
      (canonicalSimplex m).app (op ⦋k⦌) c at he
  change (canonicalSpineMap m).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌) z) = _
  exact he.trans (canonicalSimplex_apply f)

/-- The image of a map of dagger simplicial sets is closed under reversal. -/
theorem spine_range_reversal {k m : ℕ}
    {F : Fin (k + 1) ⥤ FreeDaggerSimplex m}
    (hF : F ∈ (Subfunctor.range (canonicalSpinePresheafMap m)).obj
      (op (ReverseSimplex.mk k))) :
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (ReverseSimplex.mk k)) F ∈
      (Subfunctor.range (canonicalSpinePresheafMap m)).obj
        (op (ReverseSimplex.mk k)) := by
  obtain ⟨z, rfl⟩ := hF
  let ρ := (ReverseSimplex.reversal (ReverseSimplex.mk k)).op
  refine ⟨((freeDagger.obj (ordinarySpine.{0} m)).extension.map ρ) z, ?_⟩
  exact congrFun ((canonicalSpinePresheafMap m).naturality ρ) z

/-- A reversal-simplex map with adjacent endpoints gives a chain in the
literal free dagger spine image, in either orientation. -/
theorem u_map_mem_spine_range {k m : ℕ}
    (α : ReverseSimplex.mk k ⟶ ReverseSimplex.mk m)
    (hspan : (α.toFun 0).val ≤ (α.toFun (Fin.last k)).val + 1 ∧
      (α.toFun (Fin.last k)).val ≤ (α.toFun 0).val + 1) :
    pathHomChainEquiv k m (u.map α) ∈
      (Subfunctor.range (canonicalSpinePresheafMap m)).obj
        (op (ReverseSimplex.mk k)) := by
  rcases α.monotone_or_antitone with hα | hα
  · let f := ReverseSimplex.monotoneHom α hα
    have hf : ReverseSimplex.inclusion.map f = α := by
      apply ReverseSimplex.Hom.ext
      intro i
      rfl
    rw [← hf]
    apply monotone_u_map_mem_spine_range f
    exact hspan.2
  · let γ : ReverseSimplex.mk k ⟶ ReverseSimplex.mk m :=
      ReverseSimplex.reversal (ReverseSimplex.mk k) ≫ α
    have hγ : Monotone γ.toFun := by
      intro i j hij
      exact hα (Fin.rev_le_rev.mpr hij)
    let f := ReverseSimplex.monotoneHom γ hγ
    have hf : ReverseSimplex.inclusion.map f = γ := by
      apply ReverseSimplex.Hom.ext
      intro i
      rfl
    have hγspan : (f.toOrderHom (Fin.last k)).val ≤
        (f.toOrderHom 0).val + 1 := by
      change (α.toFun (Fin.last k).rev).val ≤
        (α.toFun (0 : Fin (k + 1)).rev).val + 1
      simpa only [Fin.rev_last, Fin.rev_zero] using hspan.1
    have hp := monotone_u_map_mem_spine_range f hγspan
    rw [hf] at hp
    have hr := spine_range_reversal hp
    have hfac : ReverseSimplex.reversal (ReverseSimplex.mk k) ≫ γ = α := by
      apply ReverseSimplex.Hom.ext
      intro i
      change α.toFun i.rev.rev = α.toFun i
      simp only [Fin.rev_rev]
    have hpre := pathHomChainEquiv_precomp_reversal
      (ReverseSimplex.mk k) m (u.map γ)
    rw [← Functor.map_comp, hfac] at hpre
    exact hpre.symm ▸ hr

/-- A one-letter path has its unique edge as its whole path. -/
theorem path_length_one_eq_toPath {V : Type*} [Quiver V] {a b : V}
    (p : Quiver.Path a b) (hp : p.length = 1) :
    ∃ e : a ⟶ b, p = e.toPath := by
  obtain ⟨c, e, q, hq, hpeq⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p (n := 0) hp
  have hc : c = b := Quiver.Path.eq_of_length_zero q hq
  cases hc
  have hqnil : q = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero q hq
  subst q
  exact ⟨e, by simpa using hpeq⟩

/-- A word of length at most one is exactly the canonical interval word
between its endpoints. The doubled line quiver has one edge in each
available direction between adjacent vertices. -/
theorem path_length_le_one_eq_intervalWord {m : ℕ} {a b : Line m}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m)) (symmLineQuiver m) a b)
    (hp : p.length ≤ 1) : p = intervalWord m a b := by
  by_cases hz : p.length = 0
  · have hab : a = b := @Quiver.Path.eq_of_length_zero
      (Quiver.Symmetrify (Line m)) (symmLineQuiver m) a b p hz
    cases hab
    have hpnil : p = (@Quiver.Path.nil _ (symmLineQuiver m) a) :=
      Quiver.Path.eq_nil_of_length_zero p hz
    simpa only [intervalWord_self] using hpnil
  · have hone : p.length = 1 := by omega
    obtain ⟨e, rfl⟩ := path_length_one_eq_toPath p hone
    exact (intervalWord_edge m e).symm

/-- The same one-letter classification for actual morphisms of the free
dagger simplex. -/
theorem letterLength_le_one_eq_intervalWord {m : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b) (hp : letterLength p ≤ 1) :
    p = intervalWord m a.vertex b.vertex :=
  path_length_le_one_eq_intervalWord p hp

theorem forwardWord_adjacent_letterLength {m a b : ℕ}
    (ha : a ≤ m) (hb : b ≤ m) (hstep : a + 1 = b) :
    letterLength (forwardWord m a b ha hb (by omega)) = 1 := by
  subst b
  rw [forwardWord_step m a (a + 1) ha hb (by omega : a < a + 1)]
  rw [forwardWord_self, Category.comp_id]
  rfl

/-- The canonical interval word has at most one letter when its endpoints
are equal or adjacent. -/
theorem intervalWord_letterLength_le_one {m : ℕ} (a b : Line m)
    (hab : a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1) :
    letterLength (intervalWord m a b) ≤ 1 := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · have hstep : a.val + 1 = b.val := by omega
    rw [intervalWord_forward m a b h.le]
    rw [forwardWord_adjacent_letterLength
      (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt) hstep]
  · have heq : a = b := by
      cases a with
      | mk av ah =>
        cases b with
        | mk bv bh =>
          dsimp at h
          subst bv
          rfl
    subst b
    simp
  · have hstep : b.val + 1 = a.val := by omega
    rw [intervalWord_backward m a b h, letterLength_dagger,
      forwardWord_adjacent_letterLength
        (Nat.lt_succ_iff.mp b.isLt) (Nat.lt_succ_iff.mp a.isLt) hstep]

/-- Every adjacent arrow of a chain in the first stage has at most one letter. -/
theorem adjacentLength_le_one {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) (i : Fin k) :
    letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) ≤ 1 :=
  (intervalLength_le_total F (Fin.castSucc_le_succ i)).trans hF

/-- Two different adjacent arrows cannot both contain a letter when the
total length is at most one. -/
theorem unique_nonidentity_adjacent {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) {i j : Fin k}
    (hi : 0 < letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))))
    (hj : 0 < letterLength (F.map (homOfLE (Fin.castSucc_le_succ j)))) : i = j := by
  by_contra hne
  have htwo :
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) +
          letterLength (F.map (homOfLE (Fin.castSucc_le_succ j))) ≤
        totalLength k m F := by
    simpa only [totalLength] using
      (Finset.add_le_sum (s := Finset.univ)
        (f := fun a : Fin k ↦
          letterLength (F.map (homOfLE (Fin.castSucc_le_succ a))))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i) (Finset.mem_univ j) hne)
  omega

/-- The vertex coordinates of an arbitrary native chain. -/
def chainVertex {k m : ℕ} (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (i : Fin (k + 1)) : Fin (m + 1) :=
  ⟨(F.obj i).vertex.val, (F.obj i).vertex.isLt⟩

theorem chainVertex_eq_of_adjacentLength_zero {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) (i : Fin k)
    (hi : letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 0) :
    chainVertex F i.castSucc = chainVertex F i.succ := by
  apply Fin.ext
  exact congrArg Line.val
    (@Quiver.Path.eq_of_length_zero
      (Quiver.Symmetrify (Line m)) (symmLineQuiver m)
      (F.obj i.castSucc).vertex (F.obj i.succ).vertex
      (F.map (homOfLE (Fin.castSucc_le_succ i))) hi)

theorem adjacentLength_pos_of_vertex_ne {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) (i : Fin k)
    (hi : chainVertex F i.castSucc ≠ chainVertex F i.succ) :
    0 < letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) := by
  by_contra h
  have hz : letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 0 := by omega
  exact hi (chainVertex_eq_of_adjacentLength_zero F i hz)

/-- A first-stage chain changes vertex at most once, so its coordinate map
has one of the two permitted orientations. -/
theorem chainVertex_monotone_or_antitone {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    Monotone (chainVertex F) ∨ Antitone (chainVertex F) := by
  by_cases hmono : Monotone (chainVertex F)
  · exact Or.inl hmono
  · apply Or.inr
    have hnot : ¬ ∀ i : Fin k,
        chainVertex F i.castSucc ≤ chainVertex F i.succ := by
      intro h
      exact hmono (Fin.monotone_iff_le_succ.mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hdesc : chainVertex F i.succ < chainVertex F i.castSucc :=
      lt_of_not_ge hi
    have hpositive := adjacentLength_pos_of_vertex_ne F i (ne_of_gt hdesc)
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact hdesc.le
    · have hzero :
          letterLength (F.map (homOfLE (Fin.castSucc_le_succ j))) = 0 := by
        by_contra hn
        have hpositive_j :
            0 < letterLength (F.map (homOfLE (Fin.castSucc_le_succ j))) := by omega
        exact hji (unique_nonidentity_adjacent F hF hpositive_j hpositive)
      exact (chainVertex_eq_of_adjacentLength_zero F j hzero).symm.le

/-- The reversal-simplex map read off from the vertices of a first-stage
native chain. -/
def chainIndexMap {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    (ReverseSimplex.mk k) ⟶ (ReverseSimplex.mk m) :=
  ⟨chainVertex F, chainVertex_monotone_or_antitone F hF⟩

theorem chainIndexMap_obj {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) (i : Fin (k + 1)) :
    (pathHomChainEquiv k m (u.map (chainIndexMap F hF))).obj i = F.obj i := by
  change (⟨mapLine (chainIndexMap F hF) (lineAt k i.val
    (Nat.lt_succ_iff.mp i.isLt))⟩ : FreeDaggerSimplex m) = F.obj i
  congr 1

theorem pathHomChainEquiv_u_map {k m : ℕ}
    (α : (ReverseSimplex.mk k) ⟶ (ReverseSimplex.mk m))
    {i j : Fin (k + 1)} (h : i ⟶ j) :
    (pathHomChainEquiv k m (u.map α)).map h =
      intervalWord m
        (mapLine α (lineAt k i.val (Nat.lt_succ_iff.mp i.isLt)))
        (mapLine α (lineAt k j.val (Nat.lt_succ_iff.mp j.isLt))) := by
  rw [pathHomChainEquiv_map]
  change mapPath α (forwardWord k i.val j.val
    (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
    (leOfHom h)) = _
  exact mapPath_forwardWord α i.val j.val
    (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
    (leOfHom h)

theorem u_map_totalLength_le_one {k m : ℕ}
    (α : ReverseSimplex.mk k ⟶ ReverseSimplex.mk m)
    (hspan : (α.toFun 0).val ≤ (α.toFun (Fin.last k)).val + 1 ∧
      (α.toFun (Fin.last k)).val ≤ (α.toFun 0).val + 1) :
    totalLength k m (pathHomChainEquiv k m (u.map α)) ≤ 1 := by
  rw [totalLength_eq_composite]
  rw [pathHomChainEquiv_u_map]
  apply intervalWord_letterLength_le_one
  exact hspan

/-- A chain of total length at most one is the restriction of a genuine
reversal-simplex map. -/
theorem chain_eq_u_map {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    pathHomChainEquiv k m (u.map (chainIndexMap F hF)) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    exact chainIndexMap_obj F hF i
  case h_map =>
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [pathHomChainEquiv_u_map]
    have hlen : letterLength (F.map h) ≤ 1 :=
      (intervalLength_le_total F (leOfHom h)).trans hF
    rw [letterLength_le_one_eq_intervalWord (F.map h) hlen]
    congr 1

/-- The endpoints of a word of length at most one are equal or adjacent. -/
theorem path_endpoints_distance_le_one {m : ℕ} {a b : Line m}
    (p : @Quiver.Path (Quiver.Symmetrify (Line m)) (symmLineQuiver m) a b)
    (hp : p.length ≤ 1) : a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1 := by
  by_cases hz : p.length = 0
  · have hab : a = b := @Quiver.Path.eq_of_length_zero
      (Quiver.Symmetrify (Line m)) (symmLineQuiver m) a b p hz
    cases hab
    omega
  · have hone : p.length = 1 := by omega
    obtain ⟨e, rfl⟩ := path_length_one_eq_toPath p hone
    change PLift (a.val + 1 = b.val) ⊕ PLift (b.val + 1 = a.val) at e
    cases e with
    | inl h =>
        have he : a.val + 1 = b.val := h.down
        omega
    | inr h =>
        have he : b.val + 1 = a.val := h.down
        omega

/-- The first and last vertices of a length-one chain are equal or adjacent. -/
theorem chain_endpoints_distance_le_one {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    (chainVertex F 0).val ≤ (chainVertex F (Fin.last k)).val + 1 ∧
      (chainVertex F (Fin.last k)).val ≤ (chainVertex F 0).val + 1 := by
  have hpath : letterLength
      (F.map (homOfLE (Fin.zero_le (Fin.last k)))) ≤ 1 := by
    rw [← totalLength_eq_composite]
    exact hF
  exact path_endpoints_distance_le_one _ hpath

/-- The vertex image of a first-stage chain is contained in one vertex or
one adjacent pair of vertices. -/
theorem chainIndexMap_adjacent_range {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    ∃ a : Fin (m + 1), ∀ i : Fin (k + 1),
      a.val ≤ ((chainIndexMap F hF).toFun i).val ∧
        ((chainIndexMap F hF).toFun i).val ≤ a.val + 1 := by
  obtain hmono | hanti := chainVertex_monotone_or_antitone F hF
  · refine ⟨chainVertex F 0, ?_⟩
    intro i
    have hlow := hmono (Fin.zero_le i)
    have hhigh := hmono (Fin.le_last i)
    have hspan := (chain_endpoints_distance_le_one F hF).2
    change (chainVertex F 0).val ≤ (chainVertex F i).val ∧
      (chainVertex F i).val ≤ (chainVertex F 0).val + 1
    omega
  · refine ⟨chainVertex F (Fin.last k), ?_⟩
    intro i
    have hlow := hanti (Fin.le_last i)
    have hhigh := hanti (Fin.zero_le i)
    have hspan := (chain_endpoints_distance_le_one F hF).1
    change (chainVertex F (Fin.last k)).val ≤ (chainVertex F i).val ∧
      (chainVertex F i).val ≤ (chainVertex F (Fin.last k)).val + 1
    omega

/-- Every chain of total letter length at most one lies in the literal
image of the free dagger standard spine. -/
theorem length_one_mem_spine_range {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hF : totalLength k m F ≤ 1) :
    F ∈ (Subfunctor.range (canonicalSpinePresheafMap m)).obj
      (op (ReverseSimplex.mk k)) := by
  let α := chainIndexMap F hF
  have hspan : (α.toFun 0).val ≤ (α.toFun (Fin.last k)).val + 1 ∧
      (α.toFun (Fin.last k)).val ≤ (α.toFun 0).val + 1 :=
    chain_endpoints_distance_le_one F hF
  rw [← chain_eq_u_map F hF]
  exact u_map_mem_spine_range α hspan

/-- A simplex of the free dagger spine comes from either the ordinary
spine or its reversed copy. -/
theorem freeDagger_spine_cases (m k : ℕ)
    (x : (freeDagger.obj (ordinarySpine.{0} m)).toSSet.obj (op ⦋k⦌)) :
    ∃ r : SSet.opFunctor ⟶ freeDagger ⋙ DaggerSSet.forget,
      (r.app (ordinarySpine.{0} m) ≫
        (freeDagger.obj (ordinarySpine.{0} m)).dagger =
          SSet.opFunctor.map
            (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m))) ∧
      ((∃ z : (ordinarySpine.{0} m).obj (op ⦋k⦌),
        (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
          (op ⦋k⦌) z = x) ∨
      ∃ z : (SSet.opFunctor.obj (ordinarySpine.{0} m)).obj (op ⦋k⦌),
        (r.app (ordinarySpine.{0} m)).app (op ⦋k⦌) z = x) := by
  obtain ⟨r, hr⟩ := freeDagger_pushout freeDagger freeDaggerAdjunction
  refine ⟨r, (hr (ordinarySpine.{0} m)).2.2, ?_⟩
  have sq := (hr (ordinarySpine.{0} m)).1
  have sqk : IsPushout
      ((SSetVertices.inclusion (ordinarySpine.{0} m)).app (op ⦋k⦌))
      ((SSetVertices.opInclusion (ordinarySpine.{0} m)).app (op ⦋k⦌))
      ((freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌))
      ((r.app (ordinarySpine.{0} m)).app (op ⦋k⦌)) := by
    convert IsPushout.map (SSet.evaluation.obj (op ⦋k⦌)) sq using 1
  exact CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sqk x

theorem freeDagger_second_copy_dagger (m k : ℕ)
    (r : SSet.opFunctor ⟶ freeDagger ⋙ DaggerSSet.forget)
    (hr : r.app (ordinarySpine.{0} m) ≫
      (freeDagger.obj (ordinarySpine.{0} m)).dagger =
        SSet.opFunctor.map
          (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)))
    (z : (SSet.opFunctor.obj (ordinarySpine.{0} m)).obj (op ⦋k⦌)) :
    (freeDagger.obj (ordinarySpine.{0} m)).daggerSimplex
      ((r.app (ordinarySpine.{0} m)).app (op ⦋k⦌) z) =
      (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌) (SSet.opObjEquiv z) := by
  have h := congrFun (NatTrans.congr_app hr (op ⦋k⦌)) z
  exact congrArg SSet.opObjEquiv h

theorem canonicalSimplex_spine_length_le_one {k m : ℕ}
    (z : (ordinarySpine.{0} m).obj (op ⦋k⦌)) :
    totalLength k m ((canonicalSimplex m).app (op ⦋k⦌) z.val) ≤ 1 := by
  let f : ⦋k⦌ ⟶ ⦋m⦌ := SSet.stdSimplex.objEquiv z.val
  have hz : (f.toOrderHom (Fin.last k)).val ≤
      (f.toOrderHom 0).val + 1 := by
    simpa only [f] using
      (DaggerNativeStandardSpineInner.mem_spine_iff z.val).1 z.property
  have hmono : (f.toOrderHom 0).val ≤
      (f.toOrderHom (Fin.last k)).val :=
    f.toOrderHom.monotone (Fin.zero_le _)
  have hspan :
      ((ReverseSimplex.inclusion.map f).toFun 0).val ≤
        ((ReverseSimplex.inclusion.map f).toFun (Fin.last k)).val + 1 ∧
      ((ReverseSimplex.inclusion.map f).toFun (Fin.last k)).val ≤
        ((ReverseSimplex.inclusion.map f).toFun 0).val + 1 :=
    ⟨by exact (Nat.le_succ_of_le hmono), hz⟩
  have heq : SSet.stdSimplex.objEquiv.symm f = z.val :=
    SSet.stdSimplex.objEquiv.symm_apply_apply z.val
  rw [← heq]
  exact (canonicalSimplex_apply f).symm ▸
    (u_map_totalLength_le_one (ReverseSimplex.inclusion.map f) hspan)

theorem canonicalSpineMap_unit_length_le_one {k m : ℕ}
    (z : (ordinarySpine.{0} m).obj (op ⦋k⦌)) :
    totalLength k m ((canonicalSpineMap m).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌) z)) ≤ 1 := by
  have he := congrFun (NatTrans.congr_app (canonicalSpineMap_unit m)
    (op ⦋k⦌)) z
  change (canonicalSpineMap m).hom.app (op ⦋k⦌)
      ((freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
        (op ⦋k⦌) z) = (canonicalSimplex m).app (op ⦋k⦌) z.val at he
  rw [he]
  exact canonicalSimplex_spine_length_le_one z

/-- Every simplex in the literal free dagger spine image has at most one
letter in its native chain. -/
theorem spine_image_length_le_one {k m : ℕ}
    (x : (freeDagger.obj (ordinarySpine.{0} m)).toSSet.obj (op ⦋k⦌)) :
    totalLength k m ((canonicalSpineMap m).hom.app (op ⦋k⦌) x) ≤ 1 := by
  obtain ⟨r, hr, hcopy⟩ := freeDagger_spine_cases m k x
  rcases hcopy with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact canonicalSpineMap_unit_length_le_one z
  · let X := freeDagger.obj (ordinarySpine.{0} m)
    let Y := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)
    let y := (canonicalSpineMap m).hom.app (op ⦋k⦌)
      ((r.app (ordinarySpine.{0} m)).app (op ⦋k⦌) z)
    have hd : X.daggerSimplex
        ((r.app (ordinarySpine.{0} m)).app (op ⦋k⦌) z) =
        (freeDaggerAdjunction.{0}.unit.app (ordinarySpine.{0} m)).app
          (op ⦋k⦌) (SSet.opObjEquiv z) :=
      freeDagger_second_copy_dagger m k r hr z
    have hcomm := DaggerSSet.Hom.dagger_comm (canonicalSpineMap m)
      (x := (r.app (ordinarySpine.{0} m)).app (op ⦋k⦌) z)
    rw [hd] at hcomm
    have hrev : totalLength k m (Y.daggerSimplex y) ≤ 1 := by
      rw [← hcomm]
      exact canonicalSpineMap_unit_length_le_one (SSet.opObjEquiv z)
    have hlen : totalLength k m (Y.daggerSimplex y) = totalLength k m y := by
      have hreversal : Y.extensionMap
          (ReverseSimplex.reversal (ReverseSimplex.mk k)) y =
          Y.daggerSimplex y :=
        Y.extension_reversal (ReverseSimplex.mk k) y
      rw [← hreversal]
      exact totalLength_extensionMap_reversal (ReverseSimplex.mk k) m y
    rw [hlen] at hrev
    exact hrev

/-- The first total-letter-length stage is exactly the pointwise image of
the literal free dagger standard spine map. -/
theorem lengthFiltration_one_eq_spine_range (m : ℕ) :
    lengthFiltration m 1 =
      Subfunctor.range (canonicalSpinePresheafMap m) := by
  ext n F
  obtain ⟨⟨k⟩⟩ := n
  change totalLength k m F ≤ 1 ↔
    ∃ x : (freeDagger.obj (ordinarySpine.{0} m)).toSSet.obj (op ⦋k⦌),
      (canonicalSpineMap m).hom.app (op ⦋k⦌) x = F
  constructor
  · exact length_one_mem_spine_range F
  · rintro ⟨x, rfl⟩
    exact spine_image_length_le_one x

end

end DaggerModels.PartII.DaggerNerveLengthOne
