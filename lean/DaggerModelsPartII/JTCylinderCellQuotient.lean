import DaggerModelsPartII.JTCylinderBlockQuotient
import DaggerModelsPartII.JTCylinderStaircase
import DaggerModelsPartII.JTCylinderStaircaseFaces
import DaggerModelsPartII.JTCylinderFrame
import TopCatModelCategory.ColimitsType
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Lean.Elab.Tactic.Omega

/-!
# The literal staircase cell in the reduced cylinder

The source of a cell is the independently constructed two-block quotient.
The target is the actual reduced-cylinder value.  The literal staircase
map descends through both block collapses.  Its descended map is mono,
its range is the staircase cell, and its augmentation is the block
projection.  All positions and degrees, including the end cases, are
included.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCylinderCellQuotient

noncomputable section

open JTCylinderBlockQuotient JTCylinderStaircase
  JTCylinderStaircaseFaces JTCylinderFrame

/-- Every standard simplex maps epimorphically to the terminal standard
simplex: the zero vertex gives a section, including in dimension zero. -/
private theorem simplex_terminal_epi (n : ℕ) :
    Epi (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{0})) := by
  haveI : IsSplitEpi
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{0})) :=
    IsSplitEpi.mk' {
      section_ :=
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
      id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
  infer_instance

/-- Both successive literal block collapses are epimorphic.  This will
identify the image of the cell with the image of its staircase simplex. -/
theorem simplexToBlock_epi (a b : ℕ) :
    Epi (simplexToBlock a b) := by
  letI := simplex_terminal_epi a
  haveI : Epi (simplexToFirst a b) := by
    change Epi (pushout.inl (firstBlock a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})))
    infer_instance
  letI := simplex_terminal_epi b
  haveI : Epi (pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0}))) := by
    infer_instance
  change Epi (simplexToFirst a b ≫
    pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})))
  infer_instance

/-- An ordinal simplex supported on the first block factors through
the literal first-block inclusion. This remains valid for `a=0`. -/
private def factorFirstHom (a b n : ℕ)
    (f : ⦋n⦌ ⟶ ⦋(code a b).len⦌)
    (hf : ∀ i : Fin (n + 1), (f.toOrderHom i).val ≤ a) :
    ⦋n⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨(f.toOrderHom i).val, Nat.lt_succ_of_le (hf i)⟩,
      by
        intro i j hij
        apply Fin.le_iff_val_le_val.mpr
        exact Fin.le_iff_val_le_val.mp (f.toOrderHom.monotone hij)⟩

private theorem factorFirstHom_comp (a b n : ℕ)
    (f : ⦋n⦌ ⟶ ⦋(code a b).len⦌)
    (hf : ∀ i : Fin (n + 1), (f.toOrderHom i).val ≤ a) :
    factorFirstHom a b n f hf ≫ firstHom a b = f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [firstHom_apply]
  rfl

/-- An ordinal simplex supported on the last block factors through
the literal last-block inclusion, including `b=0`. -/
private def factorLastHom (a b n : ℕ)
    (f : ⦋n⦌ ⟶ ⦋(code a b).len⦌)
    (hf : ∀ i : Fin (n + 1), a + 1 ≤ (f.toOrderHom i).val) :
    ⦋n⦌ ⟶ ⦋b⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨(f.toOrderHom i).val - (a + 1), by
        have hi := (f.toOrderHom i).isLt
        change (f.toOrderHom i).val < (code a b).len + 1 at hi
        dsimp [code, wedge, single] at hi
        have hge := hf i
        change (f.toOrderHom i).val - (a + 1) < b + 1
        omega⟩,
      by
        intro i j hij
        apply Fin.le_iff_val_le_val.mpr
        have hmono := f.toOrderHom.monotone hij
        change (f.toOrderHom i).val ≤ (f.toOrderHom j).val at hmono
        change (f.toOrderHom i).val - (a + 1) ≤
          (f.toOrderHom j).val - (a + 1)
        omega⟩

private theorem factorLastHom_comp (a b n : ℕ)
    (f : ⦋n⦌ ⟶ ⦋(code a b).len⦌)
    (hf : ∀ i : Fin (n + 1), a + 1 ≤ (f.toOrderHom i).val) :
    factorLastHom a b n f hf ≫ lastHom a b = f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [lastHom_apply]
  have hi := hf i
  dsimp only [factorLastHom, SimplexCategory.Hom.toOrderHom_mk]
  change a + 1 + ((f.toOrderHom i).val - (a + 1)) =
    (f.toOrderHom i).val
  omega

/-- Every simplex of the original source simplex whose vertices lie in
the first full block is the image of the actual `firstBlock` map. -/
private theorem firstBlock_factor_obj (a b n : ℕ)
    (z : (simplex a b).obj (Opposite.op ⦋n⦌))
    (hz : ∀ i : Fin (n + 1),
      ((SSet.stdSimplex.objEquiv z).toOrderHom i).val ≤ a) :
    ∃ w : (Δ[a] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (firstBlock a b).app (Opposite.op ⦋n⦌) w = z := by
  let f := SSet.stdSimplex.objEquiv z
  let g := factorFirstHom a b n f hz
  refine ⟨SSet.stdSimplex.objEquiv.symm g, ?_⟩
  rw [firstBlock_eq_map]
  change SSet.stdSimplex.objEquiv.symm (g ≫ firstHom a b) = z
  rw [factorFirstHom_comp a b n f hz]
  exact Equiv.symm_apply_apply SSet.stdSimplex.objEquiv z

/-- Every simplex supported on the last full block is the image of
the actual `lastBlock` map, including the terminal-block vertex. -/
private theorem lastBlock_factor_obj (a b n : ℕ)
    (z : (simplex a b).obj (Opposite.op ⦋n⦌))
    (hz : ∀ i : Fin (n + 1),
      a + 1 ≤ ((SSet.stdSimplex.objEquiv z).toOrderHom i).val) :
    ∃ w : (Δ[b] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (lastBlock a b).app (Opposite.op ⦋n⦌) w = z := by
  let f := SSet.stdSimplex.objEquiv z
  let g := factorLastHom a b n f hz
  refine ⟨SSet.stdSimplex.objEquiv.symm g, ?_⟩
  rw [lastBlock_eq_map]
  change SSet.stdSimplex.objEquiv.symm (g ≫ lastHom a b) = z
  rw [factorLastHom_comp a b n f hz]
  exact Equiv.symm_apply_apply SSet.stdSimplex.objEquiv z

private theorem block_length (k : ℕ) (t : Fin (k + 1)) :
    (code t.val (k - t.val)).len = k + 1 := by
  have ht := t.isLt
  dsimp [code, wedge, single]
  omega

/-- The literal three-bead code has the dimension of the `t`th maximal
simplex, with the first collapsed block `0,…,t` and the last one
`t+1,…,k+1`. -/
def blockSimplexIso (k : ℕ) (t : Fin (k + 1)) :
    simplex t.val (k - t.val) ≅ (Δ[k + 1] : SSet.{0}) :=
  SSet.stdSimplex.mapIso
    (eqToIso (congrArg (fun n : ℕ => (⦋n⦌ : SimplexCategory))
      (block_length k t)))

/-- The actual staircase simplex followed by the literal cylinder leg.
Its descent along `simplexToBlock` is the remaining cell construction. -/
def blockSimplexToCylinder (k : ℕ) (t : Fin (k + 1)) :
    simplex t.val (k - t.val) ⟶ JTCylinderFrame.value.obj ⦋k⦌ :=
  (blockSimplexIso k t).hom ≫
    staircaseSimplex k t ≫ JTCylinderFrame.cylinder ⦋k⦌

private def rawPrism (k : ℕ) (t : Fin (k + 1)) :
    simplex t.val (k - t.val) ⟶
      JTXiEndpointCollapse.interval ⊗ Δ[k] :=
  (blockSimplexIso k t).hom ≫ staircaseSimplex k t

/-- The interval projection of the chosen raw staircase is precisely
the independently defined block-height map. -/
private theorem blockSimplex_height (k : ℕ) (t : Fin (k + 1)) :
    (blockSimplexIso k t).hom ≫ staircaseSimplex k t ≫
        CartesianMonoidalCategory.fst (Δ[1] : SSet.{0}) Δ[k] =
      height t.val (k - t.val) := by
  let e : ⦋(code t.val (k - t.val)).len⦌ ≅ ⦋k + 1⦌ :=
    eqToIso (congrArg (fun n : ℕ => (⦋n⦌ : SimplexCategory))
      (block_length k t))
  have he : e.hom ≫ cutHom k t = heightHom t.val (k - t.val) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    have hcast : (e.hom.toOrderHom i).val = i.val := by
      change ((eqToHom (congrArg
        (fun n : ℕ => (⦋n⦌ : SimplexCategory))
        (block_length k t))).toOrderHom i).val = i.val
      simp only [SimplexCategory.eqToHom_toOrderHom,
        OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
        Fin.castOrderIso_apply]
      rfl
    dsimp only [cutHom, heightHom, SimplexCategory.mkHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.fst]
    simp only [OrderHom.coe_mk]
    change (staircaseOrder k t (e.hom.toOrderHom i)).1.val =
      (if i.val ≤ t.val then (0 : Fin 2) else 1).val
    by_cases hi : i.val ≤ t.val
    · have hei : (e.hom.toOrderHom i).val ≤ t.val := by
        simpa only [hcast] using hi
      have hfirst := (staircaseOrder_first_iff k t
        (e.hom.toOrderHom i)).2 hei
      rw [hfirst, if_pos hi]
    · have hei : t.val < (e.hom.toOrderHom i).val := by
        omega
      have hsecond := (staircaseOrder_second_iff k t
        (e.hom.toOrderHom i)).2 hei
      rw [hsecond, if_neg hi]
  calc
    (blockSimplexIso k t).hom ≫ staircaseSimplex k t ≫
        CartesianMonoidalCategory.fst (Δ[1] : SSet.{0}) Δ[k] =
      (blockSimplexIso k t).hom ≫
        SSet.stdSimplex.map (cutHom k t) := by
          rw [staircaseSimplex_fst]
    _ = SSet.stdSimplex.map (e.hom ≫ cutHom k t) := by
      change SSet.stdSimplex.map e.hom ≫
        SSet.stdSimplex.map (cutHom k t) = _
      rw [← SSet.stdSimplex.map_comp]
    _ = height t.val (k - t.val) := by
      rw [he]
      rfl

private theorem rawPrism_fst (k : ℕ) (t : Fin (k + 1)) :
    rawPrism k t ≫ CartesianMonoidalCategory.fst
      JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
        height t.val (k - t.val) :=
  blockSimplex_height k t

private theorem rawPrism_mono (k : ℕ) (t : Fin (k + 1)) :
    Mono (rawPrism k t) := by
  dsimp only [rawPrism]
  haveI : Mono (staircaseSimplex k t) := staircaseSimplex_mono k t
  infer_instance

private theorem blockSimplex_augmentation (k : ℕ) (t : Fin (k + 1)) :
    blockSimplexToCylinder k t ≫
      JTCylinderFrame.augmentation.app ⦋k⦌ =
        height t.val (k - t.val) := by
  calc
    blockSimplexToCylinder k t ≫
        JTCylinderFrame.augmentation.app ⦋k⦌ =
      rawPrism k t ≫
        (JTCylinderFrame.cylinder ⦋k⦌ ≫
          JTCylinderFrame.augmentation.app ⦋k⦌) := by
            simp only [blockSimplexToCylinder, rawPrism, Category.assoc]
    _ = rawPrism k t ≫ CartesianMonoidalCategory.fst
        JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) := by
          rw [JTCylinderFrame.cylinder_augmentation]
    _ = height t.val (k - t.val) := rawPrism_fst k t

/-- A simplex in a pure interval row becomes its corresponding fixed
boundary point in the actual reduced-cylinder pushout. This applies to
either row, and imposes no condition on the simplex coordinate. -/
private theorem pureRow_cylinder {X : SSet.{0}} (k : ℕ)
    (u : X ⟶ JTXiEndpointCollapse.interval ⊗ Δ[k])
    (p : X ⟶ (Δ[0] : SSet.{0}))
    (β : (Δ[0] : SSet.{0}) ⟶ JTXiEndpointCollapse.boundary)
    (hfst : u ≫ CartesianMonoidalCategory.fst
      JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
        (p ≫ β) ≫ JTCylinderFrame.j) :
    u ≫ JTCylinderFrame.cylinder ⦋k⦌ =
      (p ≫ β) ≫ JTCylinderFrame.boundary.app ⦋k⦌ := by
  let v : X ⟶ JTXiEndpointCollapse.boundary ⊗ Δ[k] :=
    CartesianMonoidalCategory.lift (p ≫ β)
      (u ≫ CartesianMonoidalCategory.snd
        JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}))
  have hv : v ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0})) = u := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (v ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0}))) ≫
            CartesianMonoidalCategory.fst
              JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
          v ≫ (CartesianMonoidalCategory.fst
            JTXiEndpointCollapse.boundary (Δ[k] : SSet.{0}) ≫
              JTCylinderFrame.j) := by
            rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst]
        _ = (p ≫ β) ≫ JTCylinderFrame.j := by
          rw [← Category.assoc]
          exact congrArg (fun f ↦ f ≫ JTCylinderFrame.j)
            (CartesianMonoidalCategory.lift_fst _ _)
        _ = u ≫ CartesianMonoidalCategory.fst
          JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) := hfst.symm
    · calc
        (v ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0}))) ≫
            CartesianMonoidalCategory.snd
              JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
          v ≫ (CartesianMonoidalCategory.snd
            JTXiEndpointCollapse.boundary (Δ[k] : SSet.{0}) ≫
              (𝟙 (Δ[k] : SSet.{0}))) := by
            rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
        _ = u ≫ CartesianMonoidalCategory.snd
            JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) := by
          simp only [Category.comp_id]
          exact CartesianMonoidalCategory.lift_snd _ _
  calc
    u ≫ JTCylinderFrame.cylinder ⦋k⦌ =
        (v ≫ (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0}))) ≫
          JTCylinderFrame.cylinder ⦋k⦌ := by rw [hv]
    _ = v ≫ (CartesianMonoidalCategory.fst
          JTXiEndpointCollapse.boundary (Δ[k] : SSet.{0}) ≫
            JTCylinderFrame.boundary.app ⦋k⦌) := by
          rw [Category.assoc]
          exact congrArg (fun f ↦ v ≫ f)
            (JTCylinderFrame.isPushout ⦋k⦌).w
    _ = (p ≫ β) ≫ JTCylinderFrame.boundary.app ⦋k⦌ := by
      rw [← Category.assoc]
      exact congrArg
        (fun f ↦ f ≫ JTCylinderFrame.boundary.app ⦋k⦌)
        (CartesianMonoidalCategory.lift_fst _ _)

private def endpointZero (k : ℕ) :
    (Δ[0] : SSet.{0}) ⟶ JTCylinderFrame.value.obj ⦋k⦌ :=
  SSet.boundary₁.ι₀ ≫ JTCylinderFrame.boundary.app ⦋k⦌

private def endpointOne (k : ℕ) :
    (Δ[0] : SSet.{0}) ⟶ JTCylinderFrame.value.obj ⦋k⦌ :=
  SSet.boundary₁.ι₁ ≫ JTCylinderFrame.boundary.app ⦋k⦌

private theorem zeroVertex_j :
    SSet.boundary₁.ι₀ ≫ JTCylinderFrame.j = edgeZero := by
  dsimp only [JTCylinderFrame.j, edgeZero]
  rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
  rfl

private theorem oneVertex_j :
    SSet.boundary₁.ι₁ ≫ JTCylinderFrame.j = edgeOne := by
  dsimp only [JTCylinderFrame.j, edgeOne]
  rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
  rfl

private theorem firstBlock_raw_cylinder (k : ℕ) (t : Fin (k + 1)) :
    firstBlock t.val (k - t.val) ≫ blockSimplexToCylinder k t =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[t.val] : SSet.{0}) ≫
        endpointZero k := by
  let u : (Δ[t.val] : SSet.{0}) ⟶
      JTXiEndpointCollapse.interval ⊗ Δ[k] :=
    firstBlock t.val (k - t.val) ≫
      (blockSimplexIso k t).hom ≫ staircaseSimplex k t
  have hu : u ≫ CartesianMonoidalCategory.fst
        JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
      (SSet.stdSimplex.isTerminalObj₀.from
        (Δ[t.val] : SSet.{0}) ≫ SSet.boundary₁.ι₀) ≫
          JTCylinderFrame.j := by
    calc
      u ≫ CartesianMonoidalCategory.fst
          JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
        firstBlock t.val (k - t.val) ≫
          ((blockSimplexIso k t).hom ≫ staircaseSimplex k t ≫
            CartesianMonoidalCategory.fst
              JTXiEndpointCollapse.interval (Δ[k] : SSet.{0})) := by
            simp only [u, Category.assoc]
      _ = firstBlock t.val (k - t.val) ≫
          height t.val (k - t.val) :=
            congrArg (fun f ↦ firstBlock t.val (k - t.val) ≫ f)
              (blockSimplex_height k t)
      _ = SSet.stdSimplex.isTerminalObj₀.from
          (Δ[t.val] : SSet.{0}) ≫ edgeZero :=
            firstBlock_height_point _ _
      _ = (SSet.stdSimplex.isTerminalObj₀.from
          (Δ[t.val] : SSet.{0}) ≫ SSet.boundary₁.ι₀) ≫
            JTCylinderFrame.j := by
          simp only [Category.assoc, zeroVertex_j]
  have h := pureRow_cylinder k u
    (SSet.stdSimplex.isTerminalObj₀.from (Δ[t.val] : SSet.{0}))
    SSet.boundary₁.ι₀ hu
  simpa only [u, blockSimplexToCylinder, endpointZero,
    Category.assoc] using h

private theorem lastBlock_raw_cylinder (k : ℕ) (t : Fin (k + 1)) :
    lastBlock t.val (k - t.val) ≫ blockSimplexToCylinder k t =
      SSet.stdSimplex.isTerminalObj₀.from
        (Δ[k - t.val] : SSet.{0}) ≫ endpointOne k := by
  let u : (Δ[k - t.val] : SSet.{0}) ⟶
      JTXiEndpointCollapse.interval ⊗ Δ[k] :=
    lastBlock t.val (k - t.val) ≫
      (blockSimplexIso k t).hom ≫ staircaseSimplex k t
  have hu : u ≫ CartesianMonoidalCategory.fst
        JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
      (SSet.stdSimplex.isTerminalObj₀.from
        (Δ[k - t.val] : SSet.{0}) ≫ SSet.boundary₁.ι₁) ≫
          JTCylinderFrame.j := by
    calc
      u ≫ CartesianMonoidalCategory.fst
          JTXiEndpointCollapse.interval (Δ[k] : SSet.{0}) =
        lastBlock t.val (k - t.val) ≫
          ((blockSimplexIso k t).hom ≫ staircaseSimplex k t ≫
            CartesianMonoidalCategory.fst
              JTXiEndpointCollapse.interval (Δ[k] : SSet.{0})) := by
            simp only [u, Category.assoc]
      _ = lastBlock t.val (k - t.val) ≫
          height t.val (k - t.val) :=
            congrArg (fun f ↦ lastBlock t.val (k - t.val) ≫ f)
              (blockSimplex_height k t)
      _ = SSet.stdSimplex.isTerminalObj₀.from
          (Δ[k - t.val] : SSet.{0}) ≫ edgeOne :=
            lastBlock_height_point _ _
      _ = (SSet.stdSimplex.isTerminalObj₀.from
          (Δ[k - t.val] : SSet.{0}) ≫ SSet.boundary₁.ι₁) ≫
            JTCylinderFrame.j := by
          simp only [Category.assoc, oneVertex_j]
  have h := pureRow_cylinder k u
    (SSet.stdSimplex.isTerminalObj₀.from
      (Δ[k - t.val] : SSet.{0})) SSet.boundary₁.ι₁ hu
  simpa only [u, blockSimplexToCylinder, endpointOne,
    Category.assoc] using h

/-- Private universal-property assembly.  The two hypotheses are the
literal pure-row equations to be proved from the staircase coordinates
and the reduced-cylinder pushout.  No public cell map is inferred from
unproved equations. -/
private def descendOfBlockEquations (k : ℕ) (t : Fin (k + 1))
    (h₀ : firstBlock t.val (k - t.val) ≫
      blockSimplexToCylinder k t =
        SSet.stdSimplex.isTerminalObj₀.from
          (Δ[t.val] : SSet.{0}) ≫ endpointZero k)
    (h₁ : lastBlock t.val (k - t.val) ≫
      blockSimplexToCylinder k t =
        SSet.stdSimplex.isTerminalObj₀.from
          (Δ[k - t.val] : SSet.{0}) ≫ endpointOne k) :
    blockQuotient t.val (k - t.val) ⟶
      JTCylinderFrame.value.obj ⦋k⦌ := by
  let firstDesc : firstQuotient t.val (k - t.val) ⟶
      JTCylinderFrame.value.obj ⦋k⦌ :=
    pushout.desc (blockSimplexToCylinder k t) (endpointZero k) h₀
  have firstDesc_simplex :
      simplexToFirst t.val (k - t.val) ≫ firstDesc =
        blockSimplexToCylinder k t :=
    pushout.inl_desc _ _ _
  have hLast :
      (lastBlock t.val (k - t.val) ≫
        simplexToFirst t.val (k - t.val)) ≫ firstDesc =
        SSet.stdSimplex.isTerminalObj₀.from
          (Δ[k - t.val] : SSet.{0}) ≫ endpointOne k := by
    calc
      _ = lastBlock t.val (k - t.val) ≫
          (simplexToFirst t.val (k - t.val) ≫ firstDesc) :=
            Category.assoc _ _ _
      _ = lastBlock t.val (k - t.val) ≫
          blockSimplexToCylinder k t := by rw [firstDesc_simplex]
      _ = _ := h₁
  exact pushout.desc firstDesc (endpointOne k) hLast

private theorem simplex_descendOfBlockEquations (k : ℕ)
    (t : Fin (k + 1))
    (h₀ : firstBlock t.val (k - t.val) ≫
      blockSimplexToCylinder k t =
        SSet.stdSimplex.isTerminalObj₀.from
          (Δ[t.val] : SSet.{0}) ≫ endpointZero k)
    (h₁ : lastBlock t.val (k - t.val) ≫
      blockSimplexToCylinder k t =
        SSet.stdSimplex.isTerminalObj₀.from
          (Δ[k - t.val] : SSet.{0}) ≫ endpointOne k) :
    simplexToBlock t.val (k - t.val) ≫
      descendOfBlockEquations k t h₀ h₁ =
        blockSimplexToCylinder k t := by
  dsimp only [simplexToBlock, descendOfBlockEquations]
  rw [Category.assoc, pushout.inl_desc]
  change pushout.inl (firstBlock t.val (k - t.val))
      (SSet.stdSimplex.isTerminalObj₀.from
        (Δ[t.val] : SSet.{0})) ≫
        pushout.desc (blockSimplexToCylinder k t) (endpointZero k) h₀ =
      blockSimplexToCylinder k t
  exact pushout.inl_desc _ _ _

/-- The literal two-block quotient maps to the actual reduced cylinder.
Both collapsed source blocks land at their original ordered boundary
points; no substitute cell object is used. -/
def cellToCylinder (k : ℕ) (t : Fin (k + 1)) :
    blockQuotient t.val (k - t.val) ⟶
      JTCylinderFrame.value.obj ⦋k⦌ :=
  descendOfBlockEquations k t
    (firstBlock_raw_cylinder k t) (lastBlock_raw_cylinder k t)

theorem simplexToBlock_cellToCylinder (k : ℕ) (t : Fin (k + 1)) :
    simplexToBlock t.val (k - t.val) ≫ cellToCylinder k t =
      blockSimplexToCylinder k t :=
  simplex_descendOfBlockEquations k t
    (firstBlock_raw_cylinder k t) (lastBlock_raw_cylinder k t)

/-- The cylinder augmentation on the cell is precisely the independently
constructed block projection to the original interval. -/
theorem cellToCylinder_augmentation (k : ℕ) (t : Fin (k + 1)) :
    cellToCylinder k t ≫ JTCylinderFrame.augmentation.app ⦋k⦌ =
      blockProjection t.val (k - t.val) := by
  haveI : Epi (simplexToBlock t.val (k - t.val)) :=
    simplexToBlock_epi _ _
  apply (cancel_epi (simplexToBlock t.val (k - t.val))).mp
  calc
    simplexToBlock t.val (k - t.val) ≫
        (cellToCylinder k t ≫
          JTCylinderFrame.augmentation.app ⦋k⦌) =
      blockSimplexToCylinder k t ≫
        JTCylinderFrame.augmentation.app ⦋k⦌ := by
          rw [← Category.assoc, simplexToBlock_cellToCylinder]
    _ = height t.val (k - t.val) := by
      exact blockSimplex_augmentation k t
    _ = simplexToBlock t.val (k - t.val) ≫
        blockProjection t.val (k - t.val) :=
          (simplexToBlock_projection _ _).symm

/-- The cell has exactly the image of the chosen staircase simplex in
the actual reduced cylinder, not a larger union of prism simplices. -/
theorem cellToCylinder_range (k : ℕ) (t : Fin (k + 1)) :
    SSet.Subcomplex.range (cellToCylinder k t) =
      SSet.Subcomplex.range (blockSimplexToCylinder k t) := by
  haveI : Epi (simplexToBlock t.val (k - t.val)) :=
    simplexToBlock_epi _ _
  have hr : SSet.Subcomplex.range
      (simplexToBlock t.val (k - t.val)) = ⊤ :=
    SSet.Subcomplex.range_eq_top (simplexToBlock t.val (k - t.val))
  calc
    SSet.Subcomplex.range (cellToCylinder k t) =
      (⊤ : (blockQuotient t.val (k - t.val)).Subcomplex).image
        (cellToCylinder k t) := by rw [SSet.Subcomplex.image_top]
    _ = (SSet.Subcomplex.range
        (simplexToBlock t.val (k - t.val))).image
          (cellToCylinder k t) := by rw [hr]
    _ = SSet.Subcomplex.range
        (simplexToBlock t.val (k - t.val) ≫ cellToCylinder k t) :=
          (SSet.Subcomplex.range_comp _ _).symm
    _ = SSet.Subcomplex.range (blockSimplexToCylinder k t) := by
      rw [simplexToBlock_cellToCylinder]

/-- Pointwise equality of raw representatives descends to monicity of
the cell map once the literal quotient projection is epi. -/
private theorem mono_of_raw_relation {A Q P : SSet.{0}}
    (q : A ⟶ Q) (g : Q ⟶ P) (hq : Epi q)
    (hraw : ∀ n : ℕ,
      ∀ x y : A.obj (Opposite.op ⦋n⦌),
        (q ≫ g).app (Opposite.op ⦋n⦌) x =
          (q ≫ g).app (Opposite.op ⦋n⦌) y →
            q.app (Opposite.op ⦋n⦌) x =
              q.app (Opposite.op ⦋n⦌) y) :
    Mono g := by
  haveI : Epi q := hq
  haveI : ∀ c : SimplexCategoryᵒᵖ, Mono (g.app c) := by
    intro c
    induction c using Opposite.rec with | op c =>
      induction c using SimplexCategory.rec with | h n =>
        apply (mono_iff_injective _).2
        intro x y hxy
        have hqPoint : Epi (q.app (Opposite.op ⦋n⦌)) :=
          (NatTrans.epi_iff_epi_app q).1 hq (Opposite.op ⦋n⦌)
        obtain ⟨x', rfl⟩ := (epi_iff_surjective _).1 hqPoint x
        obtain ⟨y', rfl⟩ := (epi_iff_surjective _).1 hqPoint y
        exact hraw n x' y' hxy
  exact NatTrans.mono_of_mono_app g

/-- In every simplex degree the ordered boundary of `Δ[1]` consists
of the two original constant-vertex simplices. -/
private theorem boundary_point_cases (n : ℕ)
    (z : JTXiEndpointCollapse.boundary.obj (Opposite.op ⦋n⦌)) :
    (∃ w : (Δ[0] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      SSet.boundary₁.ι₀.app (Opposite.op ⦋n⦌) w = z) ∨
    (∃ w : (Δ[0] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      SSet.boundary₁.ι₁.app (Opposite.op ⦋n⦌) w = z) := by
  have sq := (SSet.boundary₁.isPushout.{0}).map
    (SSet.evaluation.obj (Opposite.op ⦋n⦌))
  exact Types.eq_or_eq_of_isPushout sq z

/-- The two constant simplices of the interval are distinct in every
degree, since they disagree at the first vertex. -/
private theorem edgeZero_ne_edgeOne (n : ℕ)
    (x y : (Δ[0] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    edgeZero.app (Opposite.op ⦋n⦌) x ≠
      edgeOne.app (Opposite.op ⦋n⦌) y := by
  intro h
  have hv := congrArg
    (fun z : (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) =>
      (SSet.stdSimplex.objEquiv z).toOrderHom (0 : Fin (n + 1))) h
  change (0 : Fin 2) = 1 at hv
  exact (by decide : (0 : Fin 2) ≠ 1) hv

private theorem height_zero_indices (a b n : ℕ)
    (x : (simplex a b).obj (Opposite.op ⦋n⦌))
    (w : (Δ[0] : SSet.{0}).obj (Opposite.op ⦋n⦌))
    (h : (height a b).app (Opposite.op ⦋n⦌) x =
      edgeZero.app (Opposite.op ⦋n⦌) w) :
    ∀ i : Fin (n + 1),
      ((SSet.stdSimplex.objEquiv x).toOrderHom i).val ≤ a := by
  intro i
  have hv := congrArg
    (fun z : (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) => z i) h
  change (if ((SSet.stdSimplex.objEquiv x).toOrderHom i).val ≤ a then
    (0 : Fin 2) else 1) = 0 at hv
  by_cases hle : ((SSet.stdSimplex.objEquiv x).toOrderHom i).val ≤ a
  · exact hle
  · rw [if_neg hle] at hv
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hv)

private theorem height_one_indices (a b n : ℕ)
    (x : (simplex a b).obj (Opposite.op ⦋n⦌))
    (w : (Δ[0] : SSet.{0}).obj (Opposite.op ⦋n⦌))
    (h : (height a b).app (Opposite.op ⦋n⦌) x =
      edgeOne.app (Opposite.op ⦋n⦌) w) :
    ∀ i : Fin (n + 1),
      a + 1 ≤ ((SSet.stdSimplex.objEquiv x).toOrderHom i).val := by
  intro i
  have hv := congrArg
    (fun z : (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) => z i) h
  change (if ((SSet.stdSimplex.objEquiv x).toOrderHom i).val ≤ a then
    (0 : Fin 2) else 1) = 1 at hv
  by_cases hle : ((SSet.stdSimplex.objEquiv x).toOrderHom i).val ≤ a
  · rw [if_pos hle] at hv
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hv)
  · omega

/-- A raw staircase simplex lying in the reduced-cylinder seam comes
from exactly one of the two full source blocks.  This is a statement
about actual simplices, including degeneracies, not just vertices. -/
private theorem seam_source_block (k : ℕ) (t : Fin (k + 1)) (n : ℕ)
    (x : (simplex t.val (k - t.val)).obj (Opposite.op ⦋n⦌))
    (h : ∃ z : (JTXiEndpointCollapse.boundary ⊗ Δ[k]).obj
        (Opposite.op ⦋n⦌),
      (rawPrism k t).app (Opposite.op ⦋n⦌) x =
        (JTCylinderFrame.j ⊗ₘ 𝟙 (Δ[k] : SSet.{0})).app
          (Opposite.op ⦋n⦌) z) :
    (∃ w : (Δ[t.val] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (firstBlock t.val (k - t.val)).app (Opposite.op ⦋n⦌) w = x) ∨
    (∃ w : (Δ[k - t.val] : SSet.{0}).obj (Opposite.op ⦋n⦌),
      (lastBlock t.val (k - t.val)).app (Opposite.op ⦋n⦌) w = x) := by
  obtain ⟨z, hz⟩ := h
  have hheight : (height t.val (k - t.val)).app
      (Opposite.op ⦋n⦌) x =
        JTCylinderFrame.j.app (Opposite.op ⦋n⦌) z.1 := by
    have hfst := congrArg Prod.fst hz
    change ((rawPrism k t ≫ CartesianMonoidalCategory.fst
      JTXiEndpointCollapse.interval (Δ[k] : SSet.{0})).app
        (Opposite.op ⦋n⦌) x) =
      JTCylinderFrame.j.app (Opposite.op ⦋n⦌) z.1 at hfst
    rw [rawPrism_fst] at hfst
    exact hfst
  rcases boundary_point_cases n z.1 with ⟨w, hw⟩ | ⟨w, hw⟩
  · have hzero : (height t.val (k - t.val)).app
        (Opposite.op ⦋n⦌) x =
          edgeZero.app (Opposite.op ⦋n⦌) w := by
      calc
        _ = JTCylinderFrame.j.app (Opposite.op ⦋n⦌) z.1 := hheight
        _ = (SSet.boundary₁.ι₀ ≫ JTCylinderFrame.j).app
          (Opposite.op ⦋n⦌) w := by rw [← hw]; rfl
        _ = edgeZero.app (Opposite.op ⦋n⦌) w := by rw [zeroVertex_j]
    exact Or.inl (firstBlock_factor_obj _ _ n x
      (height_zero_indices _ _ n x w hzero))
  · have hone : (height t.val (k - t.val)).app
        (Opposite.op ⦋n⦌) x =
          edgeOne.app (Opposite.op ⦋n⦌) w := by
      calc
        _ = JTCylinderFrame.j.app (Opposite.op ⦋n⦌) z.1 := hheight
        _ = (SSet.boundary₁.ι₁ ≫ JTCylinderFrame.j).app
          (Opposite.op ⦋n⦌) w := by rw [← hw]; rfl
        _ = edgeOne.app (Opposite.op ⦋n⦌) w := by rw [oneVertex_j]
    exact Or.inr (lastBlock_factor_obj _ _ n x
      (height_one_indices _ _ n x w hone))

private theorem firstBlock_quotient_constant (a b n : ℕ)
    (x y : (Δ[a] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (simplexToBlock a b).app (Opposite.op ⦋n⦌)
        ((firstBlock a b).app (Opposite.op ⦋n⦌) x) =
      (simplexToBlock a b).app (Opposite.op ⦋n⦌)
        ((firstBlock a b).app (Opposite.op ⦋n⦌) y) := by
  have hpoint :
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})).app
        (Opposite.op ⦋n⦌) x =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})).app
        (Opposite.op ⦋n⦌) y := Subsingleton.elim _ _
  have hx := congrFun (NatTrans.congr_app (firstCollapse a b)
    (Opposite.op ⦋n⦌)) x
  have hy := congrFun (NatTrans.congr_app (firstCollapse a b)
    (Opposite.op ⦋n⦌)) y
  simpa only [NatTrans.comp_app] using
    hx.trans ((congrArg ((firstVertex a b).app (Opposite.op ⦋n⦌))
      hpoint).trans hy.symm)

private theorem lastBlock_quotient_constant (a b n : ℕ)
    (x y : (Δ[b] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (simplexToBlock a b).app (Opposite.op ⦋n⦌)
        ((lastBlock a b).app (Opposite.op ⦋n⦌) x) =
      (simplexToBlock a b).app (Opposite.op ⦋n⦌)
        ((lastBlock a b).app (Opposite.op ⦋n⦌) y) := by
  have hpoint :
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})).app
        (Opposite.op ⦋n⦌) x =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})).app
        (Opposite.op ⦋n⦌) y := Subsingleton.elim _ _
  have hx := congrFun (NatTrans.congr_app (lastCollapse a b)
    (Opposite.op ⦋n⦌)) x
  have hy := congrFun (NatTrans.congr_app (lastCollapse a b)
    (Opposite.op ⦋n⦌)) y
  simpa only [NatTrans.comp_app] using
    hx.trans ((congrArg ((lastVertex a b).app (Opposite.op ⦋n⦌))
      hpoint).trans hy.symm)

private theorem height_firstBlock_obj (a b n : ℕ)
    (w : (Δ[a] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (height a b).app (Opposite.op ⦋n⦌)
        ((firstBlock a b).app (Opposite.op ⦋n⦌) w) =
      edgeZero.app (Opposite.op ⦋n⦌)
        ((SSet.stdSimplex.isTerminalObj₀.from
          (Δ[a] : SSet.{0})).app (Opposite.op ⦋n⦌) w) := by
  have h := congrFun (NatTrans.congr_app
    (firstBlock_height_point a b) (Opposite.op ⦋n⦌)) w
  simpa only [NatTrans.comp_app] using h

private theorem height_lastBlock_obj (a b n : ℕ)
    (w : (Δ[b] : SSet.{0}).obj (Opposite.op ⦋n⦌)) :
    (height a b).app (Opposite.op ⦋n⦌)
        ((lastBlock a b).app (Opposite.op ⦋n⦌) w) =
      edgeOne.app (Opposite.op ⦋n⦌)
        ((SSet.stdSimplex.isTerminalObj₀.from
          (Δ[b] : SSet.{0})).app (Opposite.op ⦋n⦌) w) := by
  have h := congrFun (NatTrans.congr_app
    (lastBlock_height_point a b) (Opposite.op ⦋n⦌)) w
  simpa only [NatTrans.comp_app] using h

/-- The actual cylinder quotient makes no additional identifications
inside one staircase simplex beyond the two full blocks already
collapsed by `simplexToBlock`. -/
private theorem raw_relation (k : ℕ) (t : Fin (k + 1)) (n : ℕ)
    (x y : (simplex t.val (k - t.val)).obj (Opposite.op ⦋n⦌))
    (h : (blockSimplexToCylinder k t).app (Opposite.op ⦋n⦌) x =
      (blockSimplexToCylinder k t).app (Opposite.op ⦋n⦌) y) :
    (simplexToBlock t.val (k - t.val)).app (Opposite.op ⦋n⦌) x =
      (simplexToBlock t.val (k - t.val)).app (Opposite.op ⦋n⦌) y := by
  let q := Opposite.op ⦋n⦌
  have hJMono : Mono JTCylinderFrame.j := inferInstance
  have hJApp : Mono (JTCylinderFrame.j.app q) :=
    (NatTrans.mono_iff_mono_app JTCylinderFrame.j).1 hJMono q
  have hJ : Function.Injective (JTCylinderFrame.j.app q) :=
    (mono_iff_injective _).1 hJApp
  have hLeft : Function.Injective
      (((ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
        (Δ[k] : SSet.{0})).app q) := by
    intro z z' hz
    change (JTCylinderFrame.j.app q z.1, z.2) =
      (JTCylinderFrame.j.app q z'.1, z'.2) at hz
    exact Prod.ext (hJ (congrArg Prod.fst hz))
      (congrArg
        (fun p : JTXiEndpointCollapse.interval.obj q ×
          (Δ[k] : SSet.{0}).obj q ↦ p.2) hz)
  let sq := (JTCylinderFrame.isPushout ⦋k⦌).map
    (SSet.evaluation.obj q)
  have hCylinder :
      (JTCylinderFrame.cylinder ⦋k⦌).app q
          ((rawPrism k t).app q x) =
        (JTCylinderFrame.cylinder ⦋k⦌).app q
          ((rawPrism k t).app q y) := by
    simpa only [blockSimplexToCylinder, rawPrism,
      NatTrans.comp_app] using h
  obtain hsame | ⟨zx, zy, hx, hy, _⟩ :=
    (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
      sq.isColimit hLeft
      ((rawPrism k t).app q x) ((rawPrism k t).app q y)).1
        hCylinder
  · have hMono : Mono (rawPrism k t) := rawPrism_mono k t
    have hInj : Function.Injective ((rawPrism k t).app q) :=
      (mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app (rawPrism k t)).1 hMono q)
    have hxy := hInj hsame
    rw [hxy]
  · have hHeight : (height t.val (k - t.val)).app q x =
        (height t.val (k - t.val)).app q y := by
      have hAug := congrArg
        ((JTCylinderFrame.augmentation.app ⦋k⦌).app q) h
      have hxAug := congrFun (NatTrans.congr_app
        (blockSimplex_augmentation k t) q) x
      have hyAug := congrFun (NatTrans.congr_app
        (blockSimplex_augmentation k t) q) y
      calc
        (height t.val (k - t.val)).app q x =
          ((blockSimplexToCylinder k t ≫
            JTCylinderFrame.augmentation.app ⦋k⦌).app q) x :=
              hxAug.symm
        _ = (JTCylinderFrame.augmentation.app ⦋k⦌).app q
            ((blockSimplexToCylinder k t).app q x) := rfl
        _ = (JTCylinderFrame.augmentation.app ⦋k⦌).app q
            ((blockSimplexToCylinder k t).app q y) := hAug
        _ = ((blockSimplexToCylinder k t ≫
            JTCylinderFrame.augmentation.app ⦋k⦌).app q) y := rfl
        _ = (height t.val (k - t.val)).app q y := hyAug
    rcases seam_source_block k t n x ⟨zx, hx⟩ with
      ⟨wx, hwx⟩ | ⟨wx, hwx⟩
    · rcases seam_source_block k t n y ⟨zy, hy⟩ with
        ⟨wy, hwy⟩ | ⟨wy, hwy⟩
      · rw [← hwx, ← hwy]
        exact firstBlock_quotient_constant _ _ n wx wy
      · have h0 := height_firstBlock_obj t.val (k - t.val) n wx
        have h1 := height_lastBlock_obj t.val (k - t.val) n wy
        rw [← hwx, ← hwy] at hHeight
        exact False.elim ((edgeZero_ne_edgeOne n _ _)
          (h0.symm.trans (hHeight.trans h1)))
    · rcases seam_source_block k t n y ⟨zy, hy⟩ with
        ⟨wy, hwy⟩ | ⟨wy, hwy⟩
      · have h1 := height_lastBlock_obj t.val (k - t.val) n wx
        have h0 := height_firstBlock_obj t.val (k - t.val) n wy
        rw [← hwx, ← hwy] at hHeight
        exact False.elim ((edgeZero_ne_edgeOne n _ _)
          (h0.symm.trans (hHeight.symm.trans h1)))
      · rw [← hwx, ← hwy]
        exact lastBlock_quotient_constant _ _ n wx wy

/-- Each literal two-block quotient is embedded as its own staircase
cell in the actual reduced cylinder, uniformly for all positions. -/
theorem cellToCylinder_mono (k : ℕ) (t : Fin (k + 1)) :
    Mono (cellToCylinder k t) := by
  apply mono_of_raw_relation
    (simplexToBlock t.val (k - t.val)) (cellToCylinder k t)
    (simplexToBlock_epi _ _)
  intro n x y h
  apply raw_relation k t n x y
  simpa only [simplexToBlock_cellToCylinder] using h

/-- The original block quotient is the actual image subcomplex of its
cell map. This iso is the native range factorization of the proved mono. -/
def cellRangeIso (k : ℕ) (t : Fin (k + 1)) :
    blockQuotient t.val (k - t.val) ≅
      SSet.Subcomplex.range (cellToCylinder k t) := by
  letI : Mono (cellToCylinder k t) := cellToCylinder_mono k t
  exact asIso (SSet.Subcomplex.toRange (cellToCylinder k t))

theorem cellRangeIso_hom_ι (k : ℕ) (t : Fin (k + 1)) :
    (cellRangeIso k t).hom ≫
      (SSet.Subcomplex.range (cellToCylinder k t)).ι =
        cellToCylinder k t := by
  change SSet.Subcomplex.toRange (cellToCylinder k t) ≫
      (SSet.Subcomplex.range (cellToCylinder k t)).ι =
        cellToCylinder k t
  exact SSet.Subcomplex.toRange_ι _

theorem cellRangeIso_augmentation (k : ℕ) (t : Fin (k + 1)) :
    (cellRangeIso k t).hom ≫
      (SSet.Subcomplex.range (cellToCylinder k t)).ι ≫
        JTCylinderFrame.augmentation.app ⦋k⦌ =
          blockProjection t.val (k - t.val) := by
  rw [← Category.assoc, cellRangeIso_hom_ι,
    cellToCylinder_augmentation]

/-- The augmentation restricted to each actual staircase cell is weak
in the original ordinary Joyal class. -/
theorem cellRange_augmentation_weak (k : ℕ) (t : Fin (k + 1)) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      ((SSet.Subcomplex.range (cellToCylinder k t)).ι ≫
        JTCylinderFrame.augmentation.app ⦋k⦌) := by
  have hIso : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (cellRangeIso k t).hom := MorphismProperty.of_isIso _ _
  apply DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.of_precomp
    (cellRangeIso k t).hom _ hIso
  rw [cellRangeIso_augmentation]
  exact blockProjection_weak t.val (k - t.val)

end

end DaggerModels.PartII.JTCylinderCellQuotient
