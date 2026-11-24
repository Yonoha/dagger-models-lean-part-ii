import DaggerModelsPartII.GroupoidSimplex
import DaggerModelsPartII.ReedyMaps
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Data.Finset.Sort

/-!
# The cosimplicial latching map of the JT groupoid simplex

The latching index of a cosimplicial object is the opposite of the
`MatchingIndex` used for simplicial objects.  Its objects are proper
injections into `[n]`, and its morphisms are factorizations of these
injections.  This file works with that literal index.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTParameterLatchingMono

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective

noncomputable section

/-- The actual cosimplicial proper-face diagram in degree `n`. -/
def faceDiagram (n : ℕ) : (MatchingIndex n)ᵒᵖ ⥤ SSet.{0} :=
  (matchingProjection n).leftOp ⋙ parameter

/-- The cocone of proper faces into the actual groupoid simplex. -/
def faceCocone (n : ℕ) : Cocone (faceDiagram n) where
  pt := parameter.obj ⦋n⦌
  ι :=
    { app := fun s ↦ parameter.map s.unop.obj.hom.unop
      naturality := by
        intro s t f
        change parameter.map f.unop.hom.right.unop ≫
            parameter.map t.unop.obj.hom.unop =
          parameter.map s.unop.obj.hom.unop ≫ 𝟙 _
        rw [Category.comp_id, ← parameter.map_comp]
        exact parameter.congr_map
          (congrArg Quiver.Hom.unop (StructuredArrow.w f.unop.hom)) }

/-- The actual cosimplicial latching map of `J`. -/
def faceLatchingMap (n : ℕ) : colimit (faceDiagram n) ⟶ parameter.obj ⦋n⦌ :=
  colimit.desc _ (faceCocone n)

/-- The same face diagram after the natural codiscrete identification. -/
def codiscreteFaceDiagram (n : ℕ) : (MatchingIndex n)ᵒᵖ ⥤ SSet.{0} :=
  (matchingProjection n).leftOp ⋙ vertices ⋙ codiscreteNerve

/-- The proper-face cocone into the codiscrete nerve on all vertices. -/
def codiscreteFaceCocone (n : ℕ) : Cocone (codiscreteFaceDiagram n) where
  pt := (vertices ⋙ codiscreteNerve).obj ⦋n⦌
  ι :=
    { app := fun s ↦ (vertices ⋙ codiscreteNerve).map s.unop.obj.hom.unop
      naturality := by
        intro s t f
        change (vertices ⋙ codiscreteNerve).map f.unop.hom.right.unop ≫
            (vertices ⋙ codiscreteNerve).map t.unop.obj.hom.unop =
          (vertices ⋙ codiscreteNerve).map s.unop.obj.hom.unop ≫ 𝟙 _
        rw [Category.comp_id, ← (vertices ⋙ codiscreteNerve).map_comp]
        exact (vertices ⋙ codiscreteNerve).congr_map
          (congrArg Quiver.Hom.unop (StructuredArrow.w f.unop.hom)) }

/-- The cosimplicial latching map after the codiscrete identification. -/
def codiscreteFaceLatchingMap (n : ℕ) :
    colimit (codiscreteFaceDiagram n) ⟶ (vertices ⋙ codiscreteNerve).obj ⦋n⦌ :=
  colimit.desc _ (codiscreteFaceCocone n)

/-- A monotone injection of ordinals factors through another one whenever
its vertex range is contained in the latter range. -/
private def factorThroughFace {k m n : SimplexCategory}
    (g : k ⟶ n) (f : m ⟶ n) [Mono f]
    (h : ∀ i : Fin (k.len + 1), ∃ j : Fin (m.len + 1),
      f.toOrderHom j = g.toOrderHom i) :
    k ⟶ m := by
  classical
  let ψ : Fin (k.len + 1) → Fin (m.len + 1) := fun i ↦ Classical.choose (h i)
  have hψ (i : Fin (k.len + 1)) : f.toOrderHom (ψ i) = g.toOrderHom i :=
    Classical.choose_spec (h i)
  have hf : StrictMono f.toOrderHom :=
    f.toOrderHom.monotone.strictMono_of_injective
      (SimplexCategory.mono_iff_injective.mp inferInstance)
  have hψmono : Monotone ψ := by
    intro i j hij
    by_contra hnot
    have hji : ψ j < ψ i := lt_of_not_ge hnot
    have hlt : f.toOrderHom (ψ j) < f.toOrderHom (ψ i) := hf hji
    rw [hψ j, hψ i] at hlt
    exact (not_lt_of_ge (g.toOrderHom.monotone hij)) hlt
  exact SimplexCategory.Hom.mk ⟨ψ, hψmono⟩

private theorem factorThroughFace_fac {k m n : SimplexCategory}
    (g : k ⟶ n) (f : m ⟶ n) [Mono f]
    (h : ∀ i : Fin (k.len + 1), ∃ j : Fin (m.len + 1),
      f.toOrderHom j = g.toOrderHom i) :
    factorThroughFace g f h ≫ f = g := by
  ext i
  simpa [factorThroughFace, SimplexCategory.comp_toOrderHom] using
    congrArg Fin.val (Classical.choose_spec (h i))

/-- The ordinal whose vertices are exactly a nonempty proper subset of `[n]`. -/
private def faceOfFinset {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) (hproper : S ≠ Finset.univ) : MatchingIndex n := by
  classical
  let m := S.card - 1
  have hcard : S.card = m + 1 := by
    dsimp [m]
    have hp : 0 < S.card := Finset.card_pos.mpr hS
    omega
  let f : ⦋m⦌ ⟶ ⦋n⦌ :=
    SimplexCategory.Hom.mk (S.orderEmbOfFin hcard).toOrderHom
  have hf : Mono f := SimplexCategory.mono_iff_injective.mpr
    (S.orderEmbOfFin hcard).injective
  have hm : m < n := by
    have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hproper
    have hlt : S.card < n + 1 := by simpa using Finset.card_lt_card hsub
    omega
  exact ⟨StructuredArrow.mk f.op, ⟨hm, hf⟩⟩

/-- An injective vertex map induces a degreewise injective map of
codiscrete nerves. -/
private theorem codiscreteNerve_map_mono {A B : Type} (f : A ⟶ B)
    (hf : Function.Injective f) : Mono (codiscreteNerve.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro r
  apply (mono_iff_injective _).mpr
  intro x y h
  apply ComposableArrows.ext
  · intro i j
    exact Subsingleton.elim _ _
  · intro i
    apply Codiscrete.ext
    apply hf
    exact congrArg (fun z ↦ (z.obj i).as) h

private theorem codiscrete_common_refinement (n : ℕ) (r : SimplexCategoryᵒᵖ)
    (a b : (MatchingIndex n)ᵒᵖ)
    (x : ((codiscreteFaceDiagram n).obj a).obj r)
    (y : ((codiscreteFaceDiagram n).obj b).obj r)
    (h : ((codiscreteFaceCocone n).ι.app a).app r x =
      ((codiscreteFaceCocone n).ι.app b).app r y) :
    ∃ (z : (MatchingIndex n)ᵒᵖ)
      (w : ((codiscreteFaceDiagram n).obj z).obj r)
      (p : z ⟶ a) (q : z ⟶ b),
        (((codiscreteFaceDiagram n).map p).app r) w = x ∧
        (((codiscreteFaceDiagram n).map q).app r) w = y := by
  classical
  let fa := a.unop.obj.hom.unop
  let fb := b.unop.obj.hom.unop
  letI : Mono fa := a.unop.property.2
  letI : Mono fb := b.unop.property.2
  have hlabels (i : Fin (r.unop.len + 1)) :
      fa.toOrderHom (x.obj i).as = fb.toOrderHom (y.obj i).as := by
    have hi := congrArg (fun z ↦ (z.obj i).as) h
    change fa.toOrderHom (x.obj i).as = fb.toOrderHom (y.obj i).as at hi
    exact hi
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.image (fun i : Fin (r.unop.len + 1) ↦ fa.toOrderHom (x.obj i).as)
  have hSa : ∀ v ∈ S, ∃ j, fa.toOrderHom j = v := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(x.obj i).as, rfl⟩
  have hSb : ∀ v ∈ S, ∃ j, fb.toOrderHom j = v := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(y.obj i).as, (hlabels i).symm⟩
  have hS : S.Nonempty := by
    let i : Fin (r.unop.len + 1) := ⟨0, Nat.zero_lt_succ _⟩
    exact ⟨fa.toOrderHom (x.obj i).as,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hproper : S ≠ Finset.univ := by
    intro hall
    have hsurj : Function.Surjective fa.toOrderHom := by
      intro v
      apply hSa v
      rw [hall]
      exact Finset.mem_univ v
    haveI : Epi fa := SimplexCategory.epi_iff_surjective.mpr hsurj
    have hlen : n ≤ a.unop.obj.right.unop.len :=
      SimplexCategory.len_le_of_epi fa
    exact (Nat.not_le_of_lt a.unop.property.1) hlen
  let k := S.card - 1
  have hcard : S.card = k + 1 := by
    dsimp [k]
    have hp : 0 < S.card := Finset.card_pos.mpr hS
    omega
  let e : Fin (k + 1) ≃o S := S.orderIsoOfFin hcard
  let g : ⦋k⦌ ⟶ ⦋n⦌ :=
    SimplexCategory.Hom.mk (S.orderEmbOfFin hcard).toOrderHom
  haveI hgmono : Mono g := SimplexCategory.mono_iff_injective.mpr
    (S.orderEmbOfFin hcard).injective
  have hk : k < n := by
    have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hproper
    have hlt : S.card < n + 1 := by simpa using Finset.card_lt_card hsub
    omega
  let zFace : MatchingIndex n :=
    ⟨StructuredArrow.mk g.op, ⟨hk, hgmono⟩⟩
  have hga : ∀ i : Fin (k + 1),
      ∃ j : Fin (a.unop.obj.right.unop.len + 1),
        fa.toOrderHom j = g.toOrderHom i := by
    intro i
    apply hSa (g.toOrderHom i)
    change (e i).val ∈ S
    exact (e i).property
  have hgb : ∀ i : Fin (k + 1),
      ∃ j : Fin (b.unop.obj.right.unop.len + 1),
        fb.toOrderHom j = g.toOrderHom i := by
    intro i
    apply hSb (g.toOrderHom i)
    change (e i).val ∈ S
    exact (e i).property
  let ga : ⦋k⦌ ⟶ a.unop.obj.right.unop := factorThroughFace g fa hga
  let gb : ⦋k⦌ ⟶ b.unop.obj.right.unop := factorThroughFace g fb hgb
  let pa : a.unop ⟶ zFace :=
    ⟨StructuredArrow.homMk ga.op
      (Quiver.Hom.unop_inj (factorThroughFace_fac g fa hga))⟩
  let pb : b.unop ⟶ zFace :=
    ⟨StructuredArrow.homMk gb.op
      (Quiver.Hom.unop_inj (factorThroughFace_fac g fb hgb))⟩
  let p : op zFace ⟶ a := pa.op
  let q : op zFace ⟶ b := pb.op
  let supportLabel (i : Fin (r.unop.len + 1)) : S :=
    ⟨fa.toOrderHom (x.obj i).as,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let w : ((codiscreteFaceDiagram n).obj (op zFace)).obj r :=
    Codiscrete.functor (fun i : Fin (r.unop.len + 1) ↦
      (e.symm (supportLabel i)))
  have hw : ((codiscreteFaceCocone n).ι.app (op zFace)).app r w =
      ((codiscreteFaceCocone n).ι.app a).app r x := by
    apply ComposableArrows.ext
    · intro i hi
      exact Subsingleton.elim _ _
    · intro i
      apply Codiscrete.ext
      change g.toOrderHom (e.symm (supportLabel i)) =
        fa.toOrderHom (x.obj i).as
      exact congrArg Subtype.val (e.apply_symm_apply (supportLabel i))
  have haMono : Mono ((codiscreteFaceCocone n).ι.app a) := by
    change Mono (codiscreteNerve.map (vertices.map fa))
    apply codiscreteNerve_map_mono
    change Function.Injective fa.toOrderHom
    exact SimplexCategory.mono_iff_injective.mp inferInstance
  have hbMono : Mono ((codiscreteFaceCocone n).ι.app b) := by
    change Mono (codiscreteNerve.map (vertices.map fb))
    apply codiscreteNerve_map_mono
    change Function.Injective fb.toOrderHom
    exact SimplexCategory.mono_iff_injective.mp inferInstance
  have hp : (((codiscreteFaceDiagram n).map p).app r) w = x := by
    apply (mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app ((codiscreteFaceCocone n).ι.app a)).mp haMono r)
    calc
      ((codiscreteFaceCocone n).ι.app a).app r
          (((codiscreteFaceDiagram n).map p).app r w) =
        ((codiscreteFaceCocone n).ι.app (op zFace)).app r w := by
          exact congrFun (NatTrans.congr_app ((codiscreteFaceCocone n).w p) r) w
      _ = ((codiscreteFaceCocone n).ι.app a).app r x := hw
  have hq : (((codiscreteFaceDiagram n).map q).app r) w = y := by
    apply (mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app ((codiscreteFaceCocone n).ι.app b)).mp hbMono r)
    calc
      ((codiscreteFaceCocone n).ι.app b).app r
          (((codiscreteFaceDiagram n).map q).app r w) =
        ((codiscreteFaceCocone n).ι.app (op zFace)).app r w := by
          exact congrFun (NatTrans.congr_app ((codiscreteFaceCocone n).w q) r) w
      _ = ((codiscreteFaceCocone n).ι.app b).app r y := hw.trans h
  exact ⟨op zFace, w, p, q, hp, hq⟩

private theorem desc_injective_of_common_refinement
    {I : Type} [Category I] (F : I ⥤ Type)
    (c t : Cocone F) (hc : IsColimit c)
    (bridge : ∀ (a b : I) (x : F.obj a) (y : F.obj b),
      t.ι.app a x = t.ι.app b y →
      ∃ (z : I) (w : F.obj z) (p : z ⟶ a) (q : z ⟶ b),
        F.map p w = x ∧ F.map q w = y) :
    Function.Injective (hc.desc t) := by
  intro x y h
  obtain ⟨a, x', rfl⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨b, y', rfl⟩ := Types.jointly_surjective_of_isColimit hc y
  have ht : t.ι.app a x' = t.ι.app b y' := by
    calc
      _ = hc.desc t (c.ι.app a x') := (congrFun (hc.fac t a) x').symm
      _ = hc.desc t (c.ι.app b y') := h
      _ = _ := congrFun (hc.fac t b) y'
  obtain ⟨z, w, p, q, hp, hq⟩ := bridge a b x' y' ht
  calc
    c.ι.app a x' = c.ι.app z w := by
      rw [← hp]
      exact congrFun (c.w p) w
    _ = c.ι.app b y' := by
      rw [← hq]
      exact (congrFun (c.w q) w).symm

private theorem codiscreteFaceLatchingMap_mono (n : ℕ) :
    Mono (codiscreteFaceLatchingMap n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro r
  apply (mono_iff_injective _).mpr
  let E : SSet.{0} ⥤ Type := (evaluation SimplexCategoryᵒᵖ (Type)).obj r
  let F : (MatchingIndex n)ᵒᵖ ⥤ Type := codiscreteFaceDiagram n ⋙ E
  let c : Cocone F := E.mapCocone (colimit.cocone (codiscreteFaceDiagram n))
  let t : Cocone F := E.mapCocone (codiscreteFaceCocone n)
  have hc : IsColimit c := isColimitOfPreserves E (colimit.isColimit _)
  have hbridge : ∀ (a b : (MatchingIndex n)ᵒᵖ) (x : F.obj a) (y : F.obj b),
      t.ι.app a x = t.ι.app b y →
      ∃ (z : (MatchingIndex n)ᵒᵖ) (w : F.obj z) (p : z ⟶ a) (q : z ⟶ b),
        F.map p w = x ∧ F.map q w = y := by
    intro a b x y h
    exact codiscrete_common_refinement n r a b x y h
  have hi := desc_injective_of_common_refinement F c t hc hbridge
  have heq : hc.desc t = (codiscreteFaceLatchingMap n).app r := by
    apply hc.hom_ext
    intro a
    exact (hc.fac t a).trans (by
      change t.ι.app a = c.ι.app a ≫ (codiscreteFaceLatchingMap n).app r
      exact (congrArg
        (fun f : (codiscreteFaceDiagram n).obj a ⟶
            (vertices ⋙ codiscreteNerve).obj ⦋n⦌ ↦ f.app r)
        (colimit.ι_desc (codiscreteFaceCocone n) a)).symm)
  exact heq ▸ hi

/-- The actual face diagram identified with the codiscrete face diagram. -/
private def faceDiagramIso (n : ℕ) :
    faceDiagram n ≅ codiscreteFaceDiagram n :=
  Functor.isoWhiskerLeft ((matchingProjection n).leftOp)
      parameterCodiscreteIso ≪≫
    (Functor.associator ((matchingProjection n).leftOp) vertices codiscreteNerve).symm

private theorem faceLatchingMap_comp_iso (n : ℕ) :
    faceLatchingMap n ≫ (parameterCodiscreteIso.app ⦋n⦌).hom =
      (colim.mapIso (faceDiagramIso n)).hom ≫ codiscreteFaceLatchingMap n := by
  apply colimit.hom_ext
  intro a
  have hnat := parameterCodiscreteIso.hom.naturality a.unop.obj.hom.unop
  change colimit.ι (faceDiagram n) a ≫ faceLatchingMap n ≫
      (parameterCodiscreteIso.app ⦋n⦌).hom =
    colimit.ι (faceDiagram n) a ≫ colim.map (faceDiagramIso n).hom ≫
      codiscreteFaceLatchingMap n
  calc
    _ = (faceCocone n).ι.app a ≫ (parameterCodiscreteIso.app ⦋n⦌).hom := by
      rw [faceLatchingMap, ← Category.assoc, colimit.ι_desc]
    _ = (faceDiagramIso n).hom.app a ≫ (codiscreteFaceCocone n).ι.app a := by
      change parameter.map a.unop.obj.hom.unop ≫
          (parameterCodiscreteIso.app ⦋n⦌).hom =
        (parameterCodiscreteIso.app a.unop.obj.right.unop).hom ≫
          (vertices ⋙ codiscreteNerve).map a.unop.obj.hom.unop
      exact hnat
    _ = _ := by
      rw [codiscreteFaceLatchingMap, ← Category.assoc,
        colimit.ι_map, Category.assoc, colimit.ι_desc]

/-- The actual cosimplicial latching map of `J` is monic in every degree. -/
theorem faceLatchingMap_mono (n : ℕ) : Mono (faceLatchingMap n) := by
  haveI : Mono (codiscreteFaceLatchingMap n) := codiscreteFaceLatchingMap_mono n
  have hm : Mono (faceLatchingMap n ≫ (parameterCodiscreteIso.app ⦋n⦌).hom) := by
    rw [faceLatchingMap_comp_iso]
    infer_instance
  letI : Mono (faceLatchingMap n ≫ (parameterCodiscreteIso.app ⦋n⦌).hom) := hm
  exact mono_of_mono (faceLatchingMap n) (parameterCodiscreteIso.app ⦋n⦌).hom

end

end DaggerModels.PartII.JTParameterLatchingMono
