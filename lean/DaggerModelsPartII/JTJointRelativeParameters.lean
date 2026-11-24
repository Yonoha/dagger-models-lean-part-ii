import DaggerModelsPartII.JTDecoratedIntervalDiagram
import DaggerModelsPartII.JTCodiscreteParameterPairing
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Relative groupoid parameters on the full joint interval

The inverse image of the fixed joint is preserved and reflected by the actual
native operators. A common parameter trace there thus has a natural extension
to each side, retaining the original vertex labels outside the joint.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerOriginalCodiscreteNerveInjective (mapOfVertices vertexLabels vertexLabels_natural)

namespace DaggerModels.PartII.JTJointRelativeParameters

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)
open JTCodiscreteParameterPairing (coord)

private def parameterOfVertices (X : SSet.{0}) (k : SimplexCategory)
    (φ : X.obj zero → Fin (k.len + 1)) : X ⟶ J.obj k :=
  mapOfVertices X φ ≫ (GroupoidSimplex.parameterCodiscreteIso.app k).inv

private theorem coordinate_parameterOfVertices (X : SSet.{0}) (k : SimplexCategory)
    (φ : X.obj zero → Fin (k.len + 1)) (q : SimplexCategoryᵒᵖ) (z : X.obj q)
    (v : Fin (q.unop.len + 1)) :
    coord k q ((parameterOfVertices X k φ).app q z) v =
      φ (X.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z) := by
  have h : parameterOfVertices X k φ ≫ (GroupoidSimplex.parameterCodiscreteIso.app k).hom =
      mapOfVertices X φ := by
    simp only [parameterOfVertices, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun u ↦ (u.obj v).as) (congrFun (NatTrans.congr_app h q) z)

private theorem coordinate_vertex_restriction {X : SSet.{0}} {k : SimplexCategory}
    (f : X ⟶ J.obj k) (q : SimplexCategoryᵒᵖ) (z : X.obj q) (v : Fin (q.unop.len + 1)) :
    coord k zero (f.app zero (X.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z)) 0 =
      coord k q (f.app q z) v :=
  vertexLabels_natural (f ≫ (GroupoidSimplex.parameterCodiscreteIso.app k).hom) q z v

/-- A map to the actual groupoid coefficient is determined by its vertices. -/
theorem parameter_ext {X : SSet.{0}} {k : SimplexCategory} {f g : X ⟶ J.obj k}
    (h : ∀ z, coord k zero (f.app zero z) 0 = coord k zero (g.app zero z) 0) :
    f = g := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  rw [← coordinate_vertex_restriction f, ← coordinate_vertex_restriction g]
  exact h _

section NaturalVertices

variable {I : Type} [SmallCategory I]
variable (M : I ⥤ SSet.{0}) (k : I ⥤ SimplexCategory)
variable (φ : ∀ p, (M.obj p).obj zero → Fin ((k.obj p).len + 1))
variable (hφ : ∀ {p p' : I} (a : p ⟶ p') (v : (M.obj p).obj zero),
  φ p' ((M.map a).app zero v) = (k.map a).toOrderHom (φ p v))

/-- A vertex assignment commuting with the diagram's operators determines
an actual natural transformation into the groupoid parameters. -/
def parameterOfNaturalVertices : M ⟶ k ⋙ J where
  app p := parameterOfVertices (M.obj p) (k.obj p) (φ p)
  naturality {p p'} a := by
    apply parameter_ext
    intro v
    change coord (k.obj p') zero
        ((parameterOfVertices (M.obj p') (k.obj p') (φ p')).app zero
          ((M.map a).app zero v)) 0 =
      coord (k.obj p') zero
        ((J.map (k.map a)).app zero
          ((parameterOfVertices (M.obj p) (k.obj p) (φ p)).app zero v)) 0
    rw [JTCodiscreteParameterPairing.coord_map]
    simp only [coordinate_parameterOfVertices, SimplexCategory.const_eq_id, op_id,
      FunctorToTypes.map_id_apply]
    exact hφ a v

/-- The natural parameter has exactly the prescribed vertices. -/
theorem parameterOfNaturalVertices_coord (p : I) (v : (M.obj p).obj zero) :
    coord (k.obj p) zero ((parameterOfNaturalVertices M k φ hφ).app p |>.app zero v) 0 =
      φ p v := by
  change coord (k.obj p) zero ((parameterOfVertices (M.obj p) (k.obj p) (φ p)).app zero v) 0 =
    φ p v
  simp only [coordinate_parameterOfVertices, SimplexCategory.const_eq_id, op_id,
    FunctorToTypes.map_id_apply]

end NaturalVertices

section Extension

variable {I : Type} [SmallCategory I] {M L : I ⥤ SSet.{0}}
variable (a : M ⟶ L) {k : I ⥤ SimplexCategory}
variable (trace : M ⟶ k ⋙ J) (original : L ⟶ k ⋙ J)

private def patchedLabel (p : I) : (L.obj p).obj zero → Fin ((k.obj p).len + 1) :=
  Function.extend ((a.app p).app zero)
    (fun u ↦ coord (k.obj p) zero ((trace.app p).app zero u) 0)
    (fun u ↦ coord (k.obj p) zero ((original.app p).app zero u) 0)

variable (injective : ∀ p, Function.Injective ((a.app p).app zero))
variable (reflects : ∀ {p p' : I} (f : p ⟶ p') (v : (L.obj p).obj zero),
  (L.map f).app zero v ∈ Set.range ((a.app p').app zero) →
    v ∈ Set.range ((a.app p).app zero))

include injective in
private theorem patches_at_vertex (p : I) (v : (M.obj p).obj zero) :
    patchedLabel a trace original p ((a.app p).app zero v) =
      coord (k.obj p) zero ((trace.app p).app zero v) 0 :=
  (injective p).extend_apply _ _ _

private theorem patches_away_from_vertex (p : I) (v : (L.obj p).obj zero)
    (hv : v ∉ Set.range ((a.app p).app zero)) :
    patchedLabel a trace original p v =
      coord (k.obj p) zero ((original.app p).app zero v) 0 :=
  Function.extend_apply' _ _ _ hv

include injective reflects in
private theorem patchedLabel_natural {p p' : I} (f : p ⟶ p') (v : (L.obj p).obj zero) :
    patchedLabel a trace original p' ((L.map f).app zero v) =
      (k.map f).toOrderHom (patchedLabel a trace original p v) := by
  by_cases hv : v ∈ Set.range ((a.app p).app zero)
  · obtain ⟨u, rfl⟩ := hv
    have ha := congrFun (NatTrans.congr_app (a.naturality f) zero) u
    change (a.app p').app zero ((M.map f).app zero u) =
      (L.map f).app zero ((a.app p).app zero u) at ha
    rw [← ha, patches_at_vertex a trace original injective,
      patches_at_vertex a trace original injective]
    have ht := congrFun (NatTrans.congr_app (trace.naturality f) zero) u
    change (trace.app p').app zero ((M.map f).app zero u) =
      (J.map (k.map f)).app zero ((trace.app p).app zero u) at ht
    rw [ht, JTCodiscreteParameterPairing.coord_map]
  · have h' : (L.map f).app zero v ∉ Set.range ((a.app p').app zero) :=
      fun h ↦ hv (reflects f v h)
    rw [patches_away_from_vertex a trace original p' _ h',
      patches_away_from_vertex a trace original p _ hv]
    have ht := congrFun (NatTrans.congr_app (original.naturality f) zero) v
    change (original.app p').app zero ((L.map f).app zero v) =
      (J.map (k.map f)).app zero ((original.app p).app zero v) at ht
    rw [ht, JTCodiscreteParameterPairing.coord_map]

include injective reflects in
/-- Extend a natural trace across a varying vertex subset when arrows reflect
membership in the subset. Use the original parameters on the complement. -/
def extend : L ⟶ k ⋙ J where
  app p := parameterOfVertices (L.obj p) (k.obj p) (patchedLabel a trace original p)
  naturality {p p'} f := by
    apply parameter_ext
    intro v
    change coord (k.obj p') zero
        ((parameterOfVertices _ _ (patchedLabel a trace original p')).app zero
          ((L.map f).app zero v)) 0 =
      coord (k.obj p') zero
        ((J.map (k.map f)).app zero
          ((parameterOfVertices _ _ (patchedLabel a trace original p)).app zero v)) 0
    rw [JTCodiscreteParameterPairing.coord_map, coordinate_parameterOfVertices,
      coordinate_parameterOfVertices, SimplexCategory.const_eq_id, op_id]
    simp only [FunctorToTypes.map_id_apply]
    exact patchedLabel_natural a trace original injective reflects f v

/-- The extension realizes the prescribed trace on all overlap simplices. -/
theorem restrict_extend : a ≫ extend a trace original injective reflects = trace := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro v
  change coord (k.obj p) zero
      ((parameterOfVertices _ _ (patchedLabel a trace original p)).app zero
        ((a.app p).app zero v)) 0 = _
  rw [coordinate_parameterOfVertices, SimplexCategory.const_eq_id, op_id,
    FunctorToTypes.map_id_apply]
  exact patches_at_vertex a trace original injective p v

/-- The parameters are unchanged on every vertex outside the overlap. -/
theorem extend_away (p : I) (v : (L.obj p).obj zero)
    (hv : v ∉ Set.range ((a.app p).app zero)) :
    coord (k.obj p) zero ((extend a trace original injective reflects).app p |>.app zero v)
      0 = coord (k.obj p) zero ((original.app p).app zero v) 0 := by
  change coord (k.obj p) zero
      ((parameterOfVertices _ _ (patchedLabel a trace original p)).app zero v) 0 = _
  rw [coordinate_parameterOfVertices, SimplexCategory.const_eq_id, op_id,
    FunctorToTypes.map_id_apply]
  exact patches_away_from_vertex a trace original p v hv

/-- Extending the restriction of the original map recovers that map exactly. -/
theorem extend_eq_of_restriction (h : a ≫ original = trace) :
    extend a trace original injective reflects = original := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro v
  by_cases hv : v ∈ Set.range ((a.app p).app zero)
  · obtain ⟨u, rfl⟩ := hv
    have he := NatTrans.congr_app (restrict_extend a trace original injective reflects) p
    have ho := NatTrans.congr_app h p
    have hh := congrFun (NatTrans.congr_app (he.trans ho.symm) zero) u
    exact congrArg (fun z ↦ coord (k.obj p) zero z 0) hh
  · exact extend_away a trace original injective reflects p v hv

/-- On an arbitrary source chart, compare only the part of the trace that
survives the chart's coefficient operator. -/
def TraceMatches {X Y A : SSet.{0}} {k m : SimplexCategory}
    (a : X ⟶ Y) (trace : X ⟶ J.obj k) (original : Y ⟶ J.obj k)
    (u : A ⟶ Y) (b : k ⟶ m) : Prop :=
  ∀ (x : X.obj zero) (z : A.obj zero), a.app zero x = u.app zero z →
    coord m zero ((trace ≫ J.map b).app zero x) 0 =
      coord m zero ((original ≫ J.map b).app zero (u.app zero z)) 0

/-- A chart constrains exactly the overlap vertices in the image of that chart. -/
theorem traceMatches_iff {X Y A : SSet.{0}} {k m : SimplexCategory}
    (a : X ⟶ Y) (trace : X ⟶ J.obj k) (original : Y ⟶ J.obj k)
    (u : A ⟶ Y) (b : k ⟶ m) :
    TraceMatches a trace original u b ↔
      ∀ x, a.app zero x ∈ Set.range (u.app zero) →
        b.toOrderHom (coord k zero (trace.app zero x) 0) =
          b.toOrderHom (coord k zero (original.app zero (a.app zero x)) 0) := by
  unfold TraceMatches
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := hx
    have h' := h x z hz.symm
    change coord m zero ((J.map b).app zero (trace.app zero x)) 0 =
      coord m zero ((J.map b).app zero (original.app zero (u.app zero z))) 0 at h'
    rw [JTCodiscreteParameterPairing.coord_map, JTCodiscreteParameterPairing.coord_map, hz] at h'
    exact h'
  · intro h x z hx
    change coord m zero ((J.map b).app zero (trace.app zero x)) 0 =
      coord m zero ((J.map b).app zero (original.app zero (u.app zero z))) 0
    rw [JTCodiscreteParameterPairing.coord_map, JTCodiscreteParameterPairing.coord_map, ← hx]
    exact h x ⟨z, hx.symm⟩

/-- Equality after a coefficient operator on the joint vertices of a chart
gives equality after that operator on the complete extended chart. -/
theorem extend_project_on (p : I) {A : SSet.{0}} (u : A ⟶ L.obj p)
    {m : SimplexCategory} (b : k.obj p ⟶ m)
    (h : TraceMatches (a.app p) (trace.app p) (original.app p) u b) :
    u ≫ (extend a trace original injective reflects).app p ≫ J.map b =
      u ≫ (original.app p) ≫ J.map b := by
  apply parameter_ext
  intro z
  let v := u.app zero z
  by_cases hv : v ∈ Set.range ((a.app p).app zero)
  · obtain ⟨x, hx⟩ := hv
    have he := NatTrans.congr_app (restrict_extend a trace original injective reflects) p
    change a.app p ≫ (extend a trace original injective reflects).app p =
      trace.app p at he
    have he' := congrFun (NatTrans.congr_app he zero) x
    change ((extend a trace original injective reflects).app p).app zero
      ((a.app p).app zero x) = (trace.app p).app zero x at he'
    rw [hx] at he'
    change coord m zero ((J.map b).app zero
        (((extend a trace original injective reflects).app p).app zero v)) 0 = _
    rw [he']
    exact h x z hx
  · change coord m zero ((J.map b).app zero
        (((extend a trace original injective reflects).app p).app zero v)) 0 =
      coord m zero ((J.map b).app zero ((original.app p).app zero v)) 0
    rw [JTCodiscreteParameterPairing.coord_map, JTCodiscreteParameterPairing.coord_map,
      extend_away a trace original injective reflects p v hv]

end Extension

section NativeSides

open JTTargetJointMarks (Joint)
open JTTargetIntervalOverMapping (overlap left right whole overlapToLeft overlapToRight
  leftToWhole rightToWhole)
open JTDecoratedIntervalDiagram (parameterize parameterizeMap parameterizeMap_app
  parameterize_map_left)
open JTTargetIntervalGluing (middleInclusion middlePB)
open NecklaceCode (pointAt)

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable {I : Type} [SmallCategory I] {U : NecklaceCode} {Z : SSet.{0}}
variable (q : U.toSSet ⟶ Z) (K : SimplexCategory ⥤ SSet.{0}) (time : I ⥤ SimplexCategory)
variable (D : I ⥤ Over U) (j : Joint U)

private abbrev jointVertex : U.toSSet.obj zero :=
  (pointAt U (ULift.up j.val)).app zero (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))

private theorem native_vertex_range (P : Over U) {V : Over U.toSSet}
    (a : (overlap U j).obj P ⟶ V) (b : V ⟶ (whole U).obj P) [Mono b.left]
    (hab : a.left ≫ b.left = middleInclusion P.hom j) (v : V.left.obj zero) :
    v ∈ Set.range (a.left.app zero) ↔ V.hom.app zero v = jointVertex j := by
  let t := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))
  let sq := (middlePB P.hom j).map ((evaluation _ _).obj zero)
  have hb : Function.Injective (b.left.app zero) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  have hfac (u : ((overlap U j).obj P).left.obj zero) :
      b.left.app zero (a.left.app zero u) = (middleInclusion P.hom j).app zero u :=
    congrFun (NatTrans.congr_app hab zero) u
  have hw (u : V.left.obj zero) :
      P.hom.map.app zero (b.left.app zero u) = V.hom.app zero u :=
    congrFun (NatTrans.congr_app (Over.w b) zero) u
  constructor
  · rintro ⟨u, rfl⟩
    rw [← hw, hfac]
    have hm : (JTTargetIntervalGluing.middlePoint P.hom j).app zero u = t :=
      Subsingleton.elim _ _
    exact (congrFun (NatTrans.congr_app (middlePB P.hom j).w zero) u).trans
      (congrArg ((pointAt U (ULift.up j.val)).app zero) hm)
  · intro hv
    have h : P.hom.map.app zero (b.left.app zero v) =
        (pointAt U (ULift.up j.val)).app zero t := (hw v).trans hv
    obtain ⟨u, hu, _⟩ := Types.exists_of_isPullback sq (b.left.app zero v) t h
    exact ⟨u, hb ((hfac u).trans hu)⟩

/-- The actual interval diagram with its independent simplicial time. -/
abbrev withTime (F : Over U ⥤ Over U.toSSet) : I ⥤ SSet.{0} :=
  parameterize q K time (D ⋙ F) ⋙ Over.forget Z

/-- The actual full source inclusion, tensored with the entire time simplex. -/
abbrev withTimeMap {F G : Over U ⥤ Over U.toSSet} (a : F ⟶ G) :
    withTime q K time D F ⟶ withTime q K time D G :=
  Functor.whiskerRight (parameterizeMap q K time (Functor.whiskerLeft D a)) (Over.forget Z)

/-- The inclusion uses the original horizontal map and the whole time identity. -/
theorem withTimeMap_app {F G : Over U ⥤ Over U.toSSet} (a : F ⟶ G) (p : I) :
    (withTimeMap q K time D a).app p =
      (a.app (D.obj p)).left ⊗ₘ 𝟙 (K.obj (time.obj p)) := by
  change ((parameterizeMap q K time (Functor.whiskerLeft D a)).app p).left = _
  rw [parameterizeMap_app]
  rfl

variable {L : Over U ⥤ Over U.toSSet} (a : overlap U j ⟶ L) (b : L ⟶ whole U)
variable (monoSide : ∀ P, Mono (b.app P).left)
variable (fac : ∀ P, (a.app P).left ≫ (b.app P).left = middleInclusion P.hom j)

include monoSide fac in
private theorem time_vertex_range (p : I) (v : (withTime q K time D L).obj p |>.obj zero) :
    v ∈ Set.range (((withTimeMap q K time D a).app p).app zero) ↔
      ((L.obj (D.obj p)).hom.app zero v.1) = jointVertex j := by
  letI := monoSide (D.obj p)
  rw [withTimeMap_app]
  have h := native_vertex_range j (D.obj p) (a.app (D.obj p)) (b.app (D.obj p))
    (fac (D.obj p)) v.1
  constructor
  · rintro ⟨u, rfl⟩
    exact (native_vertex_range j (D.obj p) (a.app (D.obj p)) (b.app (D.obj p))
      (fac (D.obj p)) _).mp ⟨u.1, rfl⟩
  · intro hv
    obtain ⟨u, hu⟩ := h.mpr hv
    refine ⟨(u, v.2), ?_⟩
    change ((a.app (D.obj p)).left.app zero u, v.2) = v
    exact Prod.ext hu rfl

include fac in
private theorem time_vertex_injective (p : I) :
    Function.Injective (((withTimeMap q K time D a).app p).app zero) := by
  let P := D.obj p
  letI : Mono (middleInclusion P.hom j) := by
    unfold middleInclusion JTTargetIntervalPullback.sourceInclusion
    infer_instance
  letI : Mono (a.app P).left := mono_of_mono_fac (fac P)
  have ha : Function.Injective ((a.app P).left.app zero) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  rw [withTimeMap_app]
  intro v v' h
  change ((a.app P).left.app zero v.1, v.2) =
    ((a.app P).left.app zero v'.1, v'.2) at h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  exact Prod.ext (ha hfirst) hsecond

include monoSide fac in
private theorem time_vertex_reflects {p p' : I} (f : p ⟶ p')
    (v : (withTime q K time D L).obj p |>.obj zero)
    (h : ((withTime q K time D L).map f).app zero v ∈
      Set.range (((withTimeMap q K time D a).app p').app zero)) :
    v ∈ Set.range (((withTimeMap q K time D a).app p).app zero) := by
  rw [time_vertex_range q K time D j a b monoSide fac p]
  rw [time_vertex_range q K time D j a b monoSide fac p'] at h
  have hmap := parameterize_map_left q K time (D ⋙ L) f
  have hfirst :
      (((withTime q K time D L).map f).app zero v).1 =
        ((L.map (D.map f)).left.app zero v.1) :=
    congrArg Prod.fst (congrFun (NatTrans.congr_app hmap zero) v)
  rw [hfirst] at h
  exact (congrFun (NatTrans.congr_app (Over.w (L.map (D.map f))) zero) v.1).symm.trans h

variable {k : I ⥤ SimplexCategory}
variable (trace : withTime q K time D (overlap U j) ⟶ k ⋙ J)
variable (original : withTime q K time D L ⟶ k ⋙ J)

/-- Extend the shared coefficient trace along a native side with its actual time operators. -/
abbrev extendSide :=
  extend (withTimeMap q K time D a) trace original
    (time_vertex_injective q K time D j a b fac)
    (time_vertex_reflects q K time D j a b monoSide fac)

private theorem left_mono (P : Over U) : Mono ((leftToWhole U j).app P).left := by
  change Mono (JTTargetIntervalGluing.leftInclusion P.hom j)
  unfold JTTargetIntervalGluing.leftInclusion JTTargetIntervalPullback.sourceInclusion
  infer_instance

private theorem right_mono (P : Over U) : Mono ((rightToWhole U j).app P).left := by
  change Mono (JTTargetIntervalGluing.rightInclusion P.hom j)
  unfold JTTargetIntervalGluing.rightInclusion JTTargetIntervalPullback.sourceInclusion
  infer_instance

/-- The full joint preimage embeds in the left time-parameterized interval. -/
theorem overlapToLeft_vertices_injective (p : I) :
    Function.Injective (((withTimeMap q K time D (overlapToLeft U j)).app p).app zero) :=
  time_vertex_injective q K time D j (overlapToLeft U j) (leftToWhole U j)
    (fun P ↦ JTTargetIntervalGluing.middleLeft_fac P.hom j) p

/-- The full joint preimage embeds in the right time-parameterized interval. -/
theorem overlapToRight_vertices_injective (p : I) :
    Function.Injective (((withTimeMap q K time D (overlapToRight U j)).app p).app zero) :=
  time_vertex_injective q K time D j (overlapToRight U j) (rightToWhole U j)
    (fun P ↦ JTTargetIntervalGluing.middleRight_fac P.hom j) p

/-- Operators of the left interval reflect membership in the full joint preimage. -/
theorem overlapToLeft_vertices_reflects {p p' : I} (f : p ⟶ p')
    (v : (withTime q K time D (left U j)).obj p |>.obj zero)
    (h : ((withTime q K time D (left U j)).map f).app zero v ∈
      Set.range (((withTimeMap q K time D (overlapToLeft U j)).app p').app zero)) :
    v ∈ Set.range (((withTimeMap q K time D (overlapToLeft U j)).app p).app zero) :=
  time_vertex_reflects q K time D j (overlapToLeft U j) (leftToWhole U j) (left_mono j)
    (fun P ↦ JTTargetIntervalGluing.middleLeft_fac P.hom j) f v h

/-- Operators of the right interval reflect membership in the full joint preimage. -/
theorem overlapToRight_vertices_reflects {p p' : I} (f : p ⟶ p')
    (v : (withTime q K time D (right U j)).obj p |>.obj zero)
    (h : ((withTime q K time D (right U j)).map f).app zero v ∈
      Set.range (((withTimeMap q K time D (overlapToRight U j)).app p').app zero)) :
    v ∈ Set.range (((withTimeMap q K time D (overlapToRight U j)).app p).app zero) :=
  time_vertex_reflects q K time D j (overlapToRight U j) (rightToWhole U j) (right_mono j)
    (fun P ↦ JTTargetIntervalGluing.middleRight_fac P.hom j) f v h

/-- Replace the left coefficient map on the entire inverse image of the joint. -/
abbrev extendLeft (s : withTime q K time D (left U j) ⟶ k ⋙ J) :=
  extendSide q K time D j (overlapToLeft U j) (leftToWhole U j) (left_mono j)
    (fun P ↦ JTTargetIntervalGluing.middleLeft_fac P.hom j) trace s

/-- Replace the right coefficient map on the entire inverse image of the joint. -/
abbrev extendRight (t : withTime q K time D (right U j) ⟶ k ⋙ J) :=
  extendSide q K time D j (overlapToRight U j) (rightToWhole U j) (right_mono j)
    (fun P ↦ JTTargetIntervalGluing.middleRight_fac P.hom j) trace t

/-- The two independently extended parameters agree on the full joint
interval in every dimension and along every source, time, and coefficient operator. -/
theorem extended_sides_agree (s : withTime q K time D (left U j) ⟶ k ⋙ J)
    (t : withTime q K time D (right U j) ⟶ k ⋙ J) :
    withTimeMap q K time D (overlapToLeft U j) ≫ extendLeft q K time D j trace s =
      withTimeMap q K time D (overlapToRight U j) ≫ extendRight q K time D j trace t := by
  rw [extendLeft, extendRight, extendSide, extendSide, restrict_extend, restrict_extend]

/-- The projected left parameter is unchanged on each chart whose
joint vertices satisfy the chart's coefficient restriction. -/
theorem extendLeft_project_on
    (s : withTime q K time D (left U j) ⟶ k ⋙ J)
    (p : I) {A : SSet.{0}} (u : A ⟶ (withTime q K time D (left U j)).obj p)
    {m : SimplexCategory} (b : k.obj p ⟶ m)
    (h : TraceMatches ((withTimeMap q K time D (overlapToLeft U j)).app p)
      (trace.app p) (s.app p) u b) :
    u ≫ (extendLeft q K time D j trace s).app p ≫ J.map b = u ≫ s.app p ≫ J.map b :=
  extend_project_on (withTimeMap q K time D (overlapToLeft U j)) trace s
    (time_vertex_injective q K time D j (overlapToLeft U j) (leftToWhole U j)
      (fun P ↦ JTTargetIntervalGluing.middleLeft_fac P.hom j))
    (time_vertex_reflects q K time D j (overlapToLeft U j) (leftToWhole U j) (left_mono j)
      (fun P ↦ JTTargetIntervalGluing.middleLeft_fac P.hom j)) p u b h

/-- The projected right parameter is unchanged on each chart whose
joint vertices satisfy the chart's coefficient restriction. -/
theorem extendRight_project_on
    (t : withTime q K time D (right U j) ⟶ k ⋙ J)
    (p : I) {A : SSet.{0}} (u : A ⟶ (withTime q K time D (right U j)).obj p)
    {m : SimplexCategory} (b : k.obj p ⟶ m)
    (h : TraceMatches ((withTimeMap q K time D (overlapToRight U j)).app p)
      (trace.app p) (t.app p) u b) :
    u ≫ (extendRight q K time D j trace t).app p ≫ J.map b = u ≫ t.app p ≫ J.map b :=
  extend_project_on (withTimeMap q K time D (overlapToRight U j)) trace t
    (time_vertex_injective q K time D j (overlapToRight U j) (rightToWhole U j)
      (fun P ↦ JTTargetIntervalGluing.middleRight_fac P.hom j))
    (time_vertex_reflects q K time D j (overlapToRight U j) (rightToWhole U j) (right_mono j)
      (fun P ↦ JTTargetIntervalGluing.middleRight_fac P.hom j)) p u b h

/-- Parametrization preserves composition of two native maps. -/
theorem withTimeMap_comp {G H T : Over U ⥤ Over U.toSSet}
    (a : G ⟶ H) (b : H ⟶ T) :
    withTimeMap q K time D (a ≫ b) = withTimeMap q K time D a ≫ withTimeMap q K time D b := by
  apply NatTrans.ext
  funext p
  change (withTimeMap q K time D (a ≫ b)).app p =
    (withTimeMap q K time D a).app p ≫ (withTimeMap q K time D b).app p
  rw [withTimeMap_app, withTimeMap_app, withTimeMap_app, tensorHom_comp_tensorHom, Category.id_comp]
  rfl

private theorem injective_withTimeMap {G H : Over U ⥤ Over U.toSSet}
    (a : G ⟶ H) (p : I) [Mono (a.app (D.obj p)).left] :
    Function.Injective (((withTimeMap q K time D a).app p).app zero) := by
  let a₀ := (a.app (D.obj p)).left.app zero
  have hinj : Function.Injective a₀ := (mono_iff_injective _).mp inferInstance
  rw [withTimeMap_app]
  intro v v' he
  change (a₀ v.1, v.2) = (a₀ v'.1, v'.2) at he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  exact Prod.ext (hinj h₁) h₂

theorem left_vertices_injective (p : I) :
    Function.Injective (((withTimeMap q K time D (leftToWhole U j)).app p).app zero) := by
  letI := left_mono j (D.obj p)
  exact injective_withTimeMap q K time D _ p

theorem right_vertices_injective (p : I) :
    Function.Injective (((withTimeMap q K time D (rightToWhole U j)).app p).app zero) := by
  letI := right_mono j (D.obj p)
  exact injective_withTimeMap q K time D _ p

/-- The actual inclusion of the full joint preimage in the whole source diagram. -/
abbrev jointToWhole :=
  JTTargetIntervalOverMapping.inclusion U j j le_rfl

/-- The whole-source joint inclusion factors through the original left interval. -/
theorem jointToWhole_left :
    overlapToLeft U j ≫ leftToWhole U j = jointToWhole j := by
  apply NatTrans.ext
  funext P
  apply Over.OverMorphism.ext
  exact JTTargetIntervalGluing.middleLeft_fac P.hom j

/-- The whole-source joint inclusion factors through the original right interval. -/
theorem jointToWhole_right :
    overlapToRight U j ≫ rightToWhole U j = jointToWhole j := by
  apply NatTrans.ext
  funext P
  apply Over.OverMorphism.ext
  exact JTTargetIntervalGluing.middleRight_fac P.hom j

private theorem joint_fac (P : Over U) :
    ((jointToWhole j).app P).left ≫ (NatTrans.app (𝟙 (whole U)) P).left = middleInclusion P.hom j := by
  change middleInclusion P.hom j ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem joint_vertices_injective (p : I) :
    Function.Injective (((withTimeMap q K time D (jointToWhole j)).app p).app zero) :=
  time_vertex_injective q K time D j (jointToWhole j) (𝟙 (whole U)) (joint_fac j) p

private theorem identity_mono (P : Over U) : Mono ((NatTrans.app (𝟙 (whole U)) P).left) := by
  change Mono (𝟙 _ : P.left.toSSet ⟶ P.left.toSSet)
  infer_instance

/-- The full joint preimage is reflected by every original operator of the whole diagram. -/
theorem joint_vertices_reflects {p p' : I} (f : p ⟶ p')
    (v : ((withTime q K time D (whole U)).obj p).obj zero) :
    ((withTime q K time D (whole U)).map f).app zero v ∈
      Set.range (((withTimeMap q K time D (jointToWhole j)).app p').app zero) →
    v ∈ Set.range (((withTimeMap q K time D (jointToWhole j)).app p).app zero) :=
  time_vertex_reflects q K time D j (jointToWhole j) (𝟙 (whole U))
    identity_mono (joint_fac j) f v

/-- A vertex of the entire product belongs to the joint preimage exactly when
its original horizontal coordinate has the prescribed native image. -/
theorem joint_vertex_range_iff (p : I) (v : ((withTime q K time D (whole U)).obj p).obj zero) :
    v ∈ Set.range (((withTimeMap q K time D (jointToWhole j)).app p).app zero) ↔
      ((D.obj p).hom.map.app zero v.1) = jointVertex j :=
  time_vertex_range q K time D j (jointToWhole j) (𝟙 (whole U))
    identity_mono (joint_fac j) p v

/-- Away from the whole overlap, left extension retains the original coefficient. -/
theorem extendLeft_away (s : withTime q K time D (left U j) ⟶ k ⋙ J)
    (p : I) (v : ((withTime q K time D (left U j)).obj p).obj zero)
    (hv : v ∉ Set.range (((withTimeMap q K time D (overlapToLeft U j)).app p).app zero)) :
    coord (k.obj p) zero (((extendLeft q K time D j trace s).app p).app zero v) 0 =
      coord (k.obj p) zero ((s.app p).app zero v) 0 :=
  extend_away (withTimeMap q K time D (overlapToLeft U j)) trace s _ _ p v hv

/-- Away from the whole overlap, right extension retains the original coefficient. -/
theorem extendRight_away (t : withTime q K time D (right U j) ⟶ k ⋙ J)
    (p : I) (v : ((withTime q K time D (right U j)).obj p).obj zero)
    (hv : v ∉ Set.range (((withTimeMap q K time D (overlapToRight U j)).app p).app zero)) :
    coord (k.obj p) zero (((extendRight q K time D j trace t).app p).app zero v) 0 =
      coord (k.obj p) zero ((t.app p).app zero v) 0 :=
  extend_away (withTimeMap q K time D (overlapToRight U j)) trace t _ _ p v hv

end NativeSides

section Assembly

open JTTargetJointMarks (Joint)
open JTTargetIntervalOverMapping (left right overlap whole overlapToLeft overlapToRight
  leftToWhole rightToWhole)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source}
variable {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (K : SimplexCategory ⥤ SSet.{0}) (time : I ⥤ SimplexCategory) (D : I ⥤ Over Q.code)
variable (j : Joint Q.code)

private abbrev leftLeg := withTimeMap Q.map K time D (leftToWhole Q.code j)
private abbrev rightLeg := withTimeMap Q.map K time D (rightToWhole Q.code j)
private abbrev middleLeft := withTimeMap Q.map K time D (overlapToLeft Q.code j)
private abbrev middleRight := withTimeMap Q.map K time D (overlapToRight Q.code j)

/-- The complete parametrized source is also the pushout of the underlying
simplicial-set diagrams. -/
theorem underlying_isPushout :
    IsPushout (middleLeft Q K time D j) (middleRight Q K time D j)
      (leftLeg Q K time D j) (rightLeg Q K time D j) :=
  (JTDecoratedIntervalDiagram.interval_isPushout K time Q D j).map
    ((Functor.whiskeringRight I (Over (Raw W)) SSet.{0}).obj (Over.forget (Raw W)))

variable {k : I ⥤ SimplexCategory}
variable (trace : withTime Q.map K time D (overlap Q.code j) ⟶ k ⋙ J)
variable (s : withTime Q.map K time D (left Q.code j) ⟶ k ⋙ J)
variable (t : withTime Q.map K time D (right Q.code j) ⟶ k ⋙ J)

/-- The two independently supplied coefficient maps, with the same prescribed
full joint trace, define a single natural map on the actual native time diagram. -/
def assemble : withTime Q.map K time D (whole Q.code) ⟶ k ⋙ J :=
  (underlying_isPushout Q K time D j).desc
    (extendLeft Q.map K time D j trace s) (extendRight Q.map K time D j trace t)
    (extended_sides_agree Q.map K time D j trace s t)

@[reassoc]
theorem assemble_left :
    leftLeg Q K time D j ≫ assemble Q K time D j trace s t =
      extendLeft Q.map K time D j trace s :=
  (underlying_isPushout Q K time D j).inl_desc _ _ _

@[reassoc]
theorem assemble_right :
    rightLeg Q K time D j ≫ assemble Q K time D j trace s t =
      extendRight Q.map K time D j trace t :=
  (underlying_isPushout Q K time D j).inr_desc _ _ _

/-- The assembled parameter has the exact common trace at the joint. -/
theorem assemble_trace :
    middleLeft Q K time D j ≫ leftLeg Q K time D j ≫ assemble Q K time D j trace s t =
      trace := by
  rw [assemble_left, extendLeft, extendSide, restrict_extend]

/-- The relative assembly of the restrictions of a complete coefficient map
recovers the original map on the whole time-parametrized diagram. -/
theorem assemble_of_restrictions
    (p : withTime Q.map K time D (whole Q.code) ⟶ k ⋙ J) :
    assemble Q K time D j (middleLeft Q K time D j ≫ leftLeg Q K time D j ≫ p)
      (leftLeg Q K time D j ≫ p) (rightLeg Q K time D j ≫ p) = p := by
  let h := underlying_isPushout Q K time D j
  apply h.hom_ext
  · rw [assemble_left, extendLeft, extendSide, extend_eq_of_restriction]
    rfl
  · rw [assemble_right, extendRight, extendSide, extend_eq_of_restriction]
    rw [← Category.assoc, ← Category.assoc, h.w]

end Assembly

end

end DaggerModels.PartII.JTJointRelativeParameters
