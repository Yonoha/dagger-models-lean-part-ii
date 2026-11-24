import DaggerModelsPartII.TimePrismChain
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort

/-! Carry ordered chains along actual coefficient and time arrows, allowing larger target chains. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.TimePrismChainDiagram

open TimePrismChain (Chain Vertex)

noncomputable section

private def VertexIn {k n : ℕ} (C : Chain k n) : Type := ↥C.vertices

private abbrev VertexIn.val {k n : ℕ} {C : Chain k n} (v : VertexIn C) : Vertex k n :=
  (show C.vertices from v).val

private theorem VertexIn.property {k n : ℕ} {C : Chain k n} (v : VertexIn C) :
    v.val ∈ C.vertices := (show C.vertices from v).property

section Enumerate

variable {k n : ℕ} (C : Chain k n)

private instance : LinearOrder (VertexIn C) :=
  LinearOrder.lift' (fun v : VertexIn C ↦ toLex v.val)
    (fun _ _ h ↦ Subtype.ext (congrArg ofLex h))

private instance : Fintype (VertexIn C) :=
  @Fintype.ofFinite (VertexIn C) (inferInstanceAs (Finite C.vertices))

private instance : Nonempty (VertexIn C) := by
  obtain ⟨j, hj⟩ := C.covers 0
  exact ⟨⟨(0, j), hj⟩⟩

private theorem ordered_iff (a b : VertexIn C) : a ≤ b ↔ a.val ≤ b.val := by
  change toLex a.val ≤ toLex b.val ↔ a.val ≤ b.val
  refine ⟨?_, fun h ↦ Prod.Lex.toLex_mono h⟩
  intro h
  by_cases he : a.val = b.val
  · exact he.le
  · rcases C.chain a.property b.property he with h' | h'
    · exact h'
    · exact (he (congrArg ofLex (le_antisymm h (Prod.Lex.toLex_mono h')))).elim

/-- The simplex that enumerates the actual vertices of the chosen chain. -/
def ordinal : SimplexCategory := ⦋Fintype.card (VertexIn C) - 1⦌

private theorem card_eq : Fintype.card (VertexIn C) = (ordinal C).len + 1 := by
  change Fintype.card (VertexIn C) = Fintype.card (VertexIn C) - 1 + 1
  have h := Fintype.card_pos (α := VertexIn C)
  omega

/-- Enumeration in the original coordinatewise order on the chain. -/
def enumerate : Fin ((ordinal C).len + 1) ≃o VertexIn C :=
  Fintype.orderIsoFinOfCardEq _ (card_eq C)

/-- Projection of the actual chain to its original coefficient. -/
def coefficient : ordinal C ⟶ ⦋k⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ ((enumerate C) i).val.1,
    fun _ _ h ↦ ((ordered_iff C _ _).mp ((enumerate C).monotone h)).1⟩

/-- Projection of the actual chain to its original time. -/
def time : ordinal C ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ ((enumerate C) i).val.2,
    fun _ _ h ↦ ((ordered_iff C _ _).mp ((enumerate C).monotone h)).2⟩

/-- A chosen chain retains all coefficient vertices. -/
theorem coefficient_surjective : Function.Surjective (coefficient C).toOrderHom := by
  intro i
  obtain ⟨j, hj⟩ := C.covers i
  obtain ⟨q, hq⟩ := (enumerate C).surjective ⟨(i, j), hj⟩
  exact ⟨q, congrArg (fun v : VertexIn C ↦ v.val.1) hq⟩

end Enumerate

section Total

variable {I : Type} [SmallCategory I]
variable (K N : I ⥤ SimplexCategory)

/-- A base object and one chain through its literal coefficient-time prism. -/
structure Index where
  base : I
  chain : Chain (K.obj base).len (N.obj base).len

/-- The original coefficient and time maps on prism vertices. -/
def imageVertex {i j : I} (f : i ⟶ j)
    (v : Vertex (K.obj i).len (N.obj i).len) : Vertex (K.obj j).len (N.obj j).len :=
  ((K.map f).toOrderHom v.1, (N.map f).toOrderHom v.2)

/-- The same original arrow, provided it carries the source chain into the target chain. -/
structure Hom (p q : Index K N) where
  base : p.base ⟶ q.base
  mapsTo : Set.MapsTo (imageVertex K N base) p.chain.vertices q.chain.vertices

theorem hom_ext {p q : Index K N} {f g : Hom K N p q} (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem imageVertex_id (i : I) (v : Vertex (K.obj i).len (N.obj i).len) :
    imageVertex K N (𝟙 i) v = v := by
  simp [imageVertex]

private theorem imageVertex_comp {i j l : I} (f : i ⟶ j) (g : j ⟶ l)
    (v : Vertex (K.obj i).len (N.obj i).len) :
    imageVertex K N (f ≫ g) v = imageVertex K N g (imageVertex K N f v) := by
  simp [imageVertex, K.map_comp, N.map_comp]

instance : SmallCategory (Index K N) where
  Hom := Hom K N
  id p := ⟨𝟙 p.base, by intro v hv; rw [imageVertex_id]; exact hv⟩
  comp f g := ⟨f.base ≫ g.base, by intro v hv; rw [imageVertex_comp]; exact g.mapsTo (f.mapsTo hv)⟩
  id_comp f := hom_ext K N (Category.id_comp f.base)
  comp_id f := hom_ext K N (Category.comp_id f.base)
  assoc f g l := hom_ext K N (Category.assoc f.base g.base l.base)

/-- Forget the chain and retain both original projection functors. -/
def base : Index K N ⥤ I where
  obj p := p.base
  map f := f.base

private def imageOnChain {p q : Index K N} (f : p ⟶ q) :
    VertexIn p.chain →o VertexIn q.chain where
  toFun v := ⟨imageVertex K N f.base v.val, f.mapsTo v.property⟩
  monotone' a b h := by
    have h' := (ordered_iff p.chain a b).mp h
    apply (ordered_iff q.chain _ _).mpr
    exact ⟨(K.map f.base).toOrderHom.monotone h'.1, (N.map f.base).toOrderHom.monotone h'.2⟩

private def ordinalMap {p q : Index K N} (f : p ⟶ q) :
    ordinal p.chain ⟶ ordinal q.chain :=
  SimplexCategory.Hom.mk ⟨
    fun v ↦ (enumerate q.chain).symm (imageOnChain K N f (enumerate p.chain v)),
    fun _ _ h ↦ (enumerate q.chain).symm.monotone
      ((imageOnChain K N f).monotone ((enumerate p.chain).monotone h))⟩

private theorem ordinalMap_vertex {p q : Index K N} (f : p ⟶ q)
    (v : Fin ((ordinal p.chain).len + 1)) :
    enumerate q.chain ((ordinalMap K N f).toOrderHom v) =
      imageOnChain K N f (enumerate p.chain v) :=
  (enumerate q.chain).apply_symm_apply _

/-- The literal chain ordinals form a diagram even when the arrows enlarge their chains. -/
def ordinals : Index K N ⥤ SimplexCategory where
  obj p := ordinal p.chain
  map f := ordinalMap K N f
  map_id p := by
    ext v : 3
    apply (enumerate p.chain).injective
    rw [ordinalMap_vertex]
    apply Subtype.ext
    exact imageVertex_id K N p.base _
  map_comp f g := by
    ext v : 3
    apply (enumerate _).injective
    change enumerate _ ((ordinalMap K N (f ≫ g)).toOrderHom v) =
      enumerate _ ((ordinalMap K N g).toOrderHom ((ordinalMap K N f).toOrderHom v))
    rw [ordinalMap_vertex, ordinalMap_vertex, ordinalMap_vertex]
    apply Subtype.ext
    exact imageVertex_comp K N f.base g.base _

/-- Recover the exact original coefficient operator on every chain. -/
def coeffProjection : ordinals K N ⟶ base K N ⋙ K where
  app p := coefficient p.chain
  naturality {p q} f := by
    ext v : 3
    change (enumerate q.chain ((ordinalMap K N f).toOrderHom v)).val.1 = _
    rw [ordinalMap_vertex]
    rfl

/-- Recover the exact original time operator on every chain. -/
def timeProjection : ordinals K N ⟶ base K N ⋙ N where
  app p := time p.chain
  naturality {p q} f := by
    ext v : 3
    change (enumerate q.chain ((ordinalMap K N f).toOrderHom v)).val.2 = _
    rw [ordinalMap_vertex]
    rfl

theorem coeffProjection_surjective (p : Index K N) :
    Function.Surjective ((coeffProjection K N).app p).toOrderHom :=
  coefficient_surjective p.chain

end Total

end
end DaggerModels.PartII.TimePrismChainDiagram
