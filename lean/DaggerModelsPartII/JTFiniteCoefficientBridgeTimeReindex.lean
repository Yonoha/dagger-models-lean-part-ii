import DaggerModelsPartII.JTFiniteCoefficientBridgeTime

/-!
# Reindexing the finite family and time simplex simultaneously
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeTimeReindex

open JTFiniteCoefficientBridgeTime

noncomputable section

/-- Reindex whole time faces, allowing a degenerate map in the time coordinate. -/
def map {m m' : ℕ} {n n' : SimplexCategory}
    (e : ⦋m⦌ ⟶ ⦋m'⦌) (he : Function.Injective e.toOrderHom) (j : n ⟶ n') :
    time m n ⟶ time m' n' :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    let x := (timeVertexEquiv m n).symm v
    timeVertexEquiv m' n' (e.toOrderHom x.1, j.toOrderHom x.2), by
    intro v w hvw
    obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
    obtain ⟨y, rfl⟩ := (timeVertexEquiv m n).surjective w
    simp only [Equiv.symm_apply_apply]
    rcases lt_or_eq_of_le (le_copy m n hvw) with h | h
    · exact cross_copy_le n'
        (e.toOrderHom.monotone.strictMono_of_injective he h)
        (j.toOrderHom x.2) (j.toOrderHom y.2)
    · exact (JTHigherInterleavedParameter.prismOrder ⦋m'⦌ n').monotone
        ⟨e.toOrderHom.monotone h.le,
          j.toOrderHom.monotone (le_time_of_copy_eq m n h hvw)⟩⟩

theorem map_vertex {m m' : ℕ} {n n' : SimplexCategory}
    (e : ⦋m⦌ ⟶ ⦋m'⦌) (he : Function.Injective e.toOrderHom) (j : n ⟶ n')
    (x : Fin (m + 1) × Fin (n.len + 1)) :
    (map e he j).toOrderHom (timeVertexEquiv m n x) =
      timeVertexEquiv m' n' (e.toOrderHom x.1, j.toOrderHom x.2) := by
  simp [map]

theorem timeSide_map {m m' : ℕ} {n n' : SimplexCategory}
    (e : ⦋m⦌ ⟶ ⦋m'⦌) (he : Function.Injective e.toOrderHom) (j : n ⟶ n')
    (a : Fin (m + 1)) :
    timeSide n a ≫ map e he j = j ≫ timeSide n' (e.toOrderHom a) := by
  ext t : 3
  exact map_vertex e he j (a, t)

theorem map_id (m : ℕ) (n : SimplexCategory) :
    map (𝟙 ⦋m⦌) (fun _ _ h ↦ h) (𝟙 n) = 𝟙 (time m n) := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
  rw [map_vertex]
  rfl

theorem map_comp {m m' m'' : ℕ} {n n' n'' : SimplexCategory}
    (e : ⦋m⦌ ⟶ ⦋m'⦌) (he : Function.Injective e.toOrderHom)
    (e' : ⦋m'⦌ ⟶ ⦋m''⦌) (he' : Function.Injective e'.toOrderHom)
    (j : n ⟶ n') (j' : n' ⟶ n'') :
    map (e ≫ e') (he'.comp he) (j ≫ j') =
      map e he j ≫ map e' he' j' := by
  ext v : 3
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
  change (map (e ≫ e') (he'.comp he) (j ≫ j')).toOrderHom (timeVertexEquiv m n x) =
    (map e' he' j').toOrderHom
      ((map e he j).toOrderHom (timeVertexEquiv m n x))
  rw [map_vertex, map_vertex, map_vertex]
  rfl

theorem map_injective {m m' : ℕ} {n n' : SimplexCategory}
    (e : ⦋m⦌ ⟶ ⦋m'⦌) (he : Function.Injective e.toOrderHom) (j : n ⟶ n')
    (hj : Function.Injective j.toOrderHom) :
    Function.Injective (map e he j).toOrderHom := by
  intro v w hvw
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
  obtain ⟨y, rfl⟩ := (timeVertexEquiv m n).surjective w
  rw [map_vertex, map_vertex] at hvw
  have hxy := (timeVertexEquiv m' n').injective hvw
  exact congrArg (timeVertexEquiv m n) (Prod.ext (he (congrArg Prod.fst hxy))
    (hj (congrArg Prod.snd hxy)))

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeTimeReindex
