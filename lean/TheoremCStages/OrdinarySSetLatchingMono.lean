import DaggerModelsPartII.ReedyMaps
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Ordinary simplicial-set latching objects

The actual Reedy latching object is the colimit over proper epimorphisms out of
`[n]`. A representative is moved along its Eilenberg–Zilber decomposition to
one whose simplex is nondegenerate. Uniqueness of that decomposition proves
that the comparison embeds the colimit as the degenerate `n`-simplices.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySSetLatchingMono

noncomputable section

private def index {n : ℕ} {d : SimplexCategory}
    (f : ⦋n⦌ ⟶ d) (hd : d.len < n) (hf : Epi f) : LatchingIndex n :=
  ⟨CostructuredArrow.mk f.op, hd, hf⟩

private def corePoint (X : SSet.{0}) {n k : ℕ}
    (g : ⦋n⦌ ⟶ ⦋k⦌) (hk : k < n) (hg : Epi g)
    (y : X.obj (op ⦋k⦌)) :
    (latchingProjection n ⋙ X).obj (index g hk hg) := by
  change X.obj (op ⦋k⦌)
  exact y

private theorem comparison_on_ι (X : SSet.{0}) {n : ℕ}
    (s : LatchingIndex n) (x : X.obj s.obj.left) :
    ((latchingComparison n).app X)
        (colimit.ι (latchingProjection n ⋙ X) s x) = X.map s.obj.hom x := by
  change colimit.desc (latchingProjection n ⋙ X) (latchingCocone n X)
    (colimit.ι (latchingProjection n ⋙ X) s x) = X.map s.obj.hom x
  exact Types.Colimit.ι_desc_apply (latchingProjection n ⋙ X)
    (latchingCocone n X) s x

private theorem normalize_index (X : SSet.{0}) {n : ℕ} {d : SimplexCategory}
    (f : ⦋n⦌ ⟶ d) (hd : d.len < n) (hf : Epi f)
    (x : X.obj (op d)) :
    ∃ (k : ℕ) (hk : k < n) (g : ⦋n⦌ ⟶ ⦋k⦌) (hg : Epi g)
      (y : X.nonDegenerate k),
      colimit.ι (latchingProjection n ⋙ X) (index f hd hf) x =
        colimit.ι (latchingProjection n ⋙ X) (index g hk hg)
          (corePoint X g hk hg y) ∧
      X.map f.op x = X.map g.op y := by
  induction d using SimplexCategory.rec with
  | _ m =>
    obtain ⟨k, e, he, y, hy⟩ := X.exists_nonDegenerate x
    letI : Epi e := he
    let g : ⦋n⦌ ⟶ ⦋k⦌ := f ≫ e
    have hk : k < n := lt_of_le_of_lt (SimplexCategory.len_le_of_epi e) hd
    have hg : Epi g := by
      letI : Epi f := hf
      letI : Epi e := he
      infer_instance
    let j : index g hk hg ⟶ index f hd hf :=
      ⟨CostructuredArrow.homMk e.op (by
        change e.op ≫ f.op = g.op
        rw [op_comp])⟩
    have hj : (latchingProjection n ⋙ X).map j (corePoint X g hk hg y) = x := by
      change X.map e.op y = x
      exact hy.symm
    refine ⟨k, hk, g, hg, y, ?_, ?_⟩
    · exact (Types.colimit_sound j hj).symm
    · rw [hy]
      change X.map f.op (X.map e.op y) = X.map (f ≫ e).op y
      rw [op_comp, FunctorToTypes.map_comp_apply]

private theorem normalize (X : SSet.{0}) {n : ℕ} (s : LatchingIndex n)
    (x : X.obj s.obj.left) :
    ∃ (k : ℕ) (hk : k < n) (g : ⦋n⦌ ⟶ ⦋k⦌) (hg : Epi g)
      (y : X.nonDegenerate k),
      colimit.ι (latchingProjection n ⋙ X) s x =
        colimit.ι (latchingProjection n ⋙ X) (index g hk hg)
          (corePoint X g hk hg y) ∧
      X.map s.obj.hom x = X.map g.op y := by
  letI : Epi s.obj.hom.unop := s.property.2
  obtain ⟨k, hk, g, hg, y, hι, hmap⟩ :=
    normalize_index X s.obj.hom.unop s.property.1 s.property.2 x
  let j : index s.obj.hom.unop s.property.1 s.property.2 ⟶ s :=
    ⟨CostructuredArrow.homMk (𝟙 s.obj.left) (by
      change (𝟙 s.obj.left) ≫ s.obj.hom = s.obj.hom
      simp only [Category.id_comp])⟩
  have hj : (latchingProjection n ⋙ X).map j x = x := by
    change X.map (𝟙 s.obj.left) x = x
    have hx : X.map (𝟙 s.obj.left) = 𝟙 (X.obj s.obj.left) := X.map_id s.obj.left
    exact congrFun hx x
  have hι' : colimit.ι (latchingProjection n ⋙ X) s x =
      colimit.ι (latchingProjection n ⋙ X) (index g hk hg)
        (corePoint X g hk hg y) := by
    calc
      colimit.ι (latchingProjection n ⋙ X) s x =
          colimit.ι (latchingProjection n ⋙ X)
            (index s.obj.hom.unop s.property.1 s.property.2) x :=
        (Types.colimit_sound j hj).symm
      _ = _ := hι
  exact ⟨k, hk, g, hg, y, hι', hmap⟩

/-- The image of the actual latching comparison is exactly the degenerate
`n`-simplices. -/
theorem latchingComparison_range (X : SSet.{0}) (n : ℕ) :
    Set.range ((latchingComparison n).app X) = X.degenerate n := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨s, y, rfl⟩ :=
      Types.jointly_surjective' (F := latchingProjection n ⋙ X) z
    obtain ⟨k, hk, g, hg, a, _, hmap⟩ := normalize X s y
    rw [SSet.mem_degenerate_iff]
    refine ⟨k, hk, g, hg, a, ?_⟩
    change X.map g.op a =
      ((latchingComparison n).app X)
        (colimit.ι (latchingProjection n ⋙ X) s y)
    rw [comparison_on_ι]
    exact hmap.symm
  · intro hx
    obtain ⟨k, hk, g, hg, y, hy⟩ := (X.mem_degenerate_iff x).mp hx
    refine ⟨colimit.ι (latchingProjection n ⋙ X) (index g hk hg)
      (corePoint X g hk hg y), ?_⟩
    rw [comparison_on_ι]
    exact hy

/-- For every simplicial set, its actual Reedy latching comparison is a
monomorphism of types. -/
theorem latchingComparison_mono (X : SSet.{0}) (n : ℕ) :
    Mono ((latchingComparison n).app X) := by
  rw [mono_iff_injective]
  intro a b hab
  obtain ⟨s, x, rfl⟩ :=
    Types.jointly_surjective' (F := latchingProjection n ⋙ X) a
  obtain ⟨t, y, rfl⟩ :=
    Types.jointly_surjective' (F := latchingProjection n ⋙ X) b
  obtain ⟨k, hk, g, hg, u, hs, hsmap⟩ := normalize X s x
  obtain ⟨l, hl, h, hh, v, ht, htmap⟩ := normalize X t y
  letI : Epi g := hg
  letI : Epi h := hh
  change ((latchingComparison n).app X)
      (colimit.ι (latchingProjection n ⋙ X) s x) =
    ((latchingComparison n).app X)
      (colimit.ι (latchingProjection n ⋙ X) t y) at hab
  rw [comparison_on_ι, comparison_on_ι] at hab
  have heval : X.map g.op u = X.map h.op v := by
    calc
      X.map g.op u = X.map s.obj.hom x := hsmap.symm
      _ = X.map t.obj.hom y := hab
      _ = X.map h.op v := htmap
  have hkl : k = l :=
    X.unique_nonDegenerate_dim (X.map g.op u) g u rfl h v heval
  cases hkl
  have huv : u = v :=
    X.unique_nonDegenerate_simplex (X.map g.op u) g u rfl h v heval
  have hgh : g = h :=
    X.unique_nonDegenerate_map (X.map g.op u) g u rfl h v heval
  cases hgh
  cases huv
  calc
    colimit.ι (latchingProjection n ⋙ X) s x =
        colimit.ι (latchingProjection n ⋙ X) (index g hk hg)
          (corePoint X g hk hg u) := hs
    _ = colimit.ι (latchingProjection n ⋙ X) t y := ht.symm

#print axioms latchingComparison_range
#print axioms latchingComparison_mono

end

end DaggerModels.PartII.OrdinarySSetLatchingMono
