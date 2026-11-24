import DaggerModelsPartII.PresheafMonoGenerationZorn

set_option autoImplicit false
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

/-- The free simplex map classified by one simplex of a diagram. -/
def freeSimplexMapOfElement (G : C ⥤ SSet.{u}) (c : C) (n : ℕ)
    (x : (G.obj c).obj (Opposite.op ⦋n⦌)) :
    freeSimplexDiagram C c n ⟶ G :=
  ((evaluationAdjunctionRight SSet.{u} c).homEquiv Δ[n] G).symm
    (SSet.yonedaEquiv.symm x)

/-- The distinguished simplex of the free simplex diagram. -/
def freeSimplexGeneric (c : C) (n : ℕ) :
    ((freeSimplexDiagram C c n).obj c).obj (Opposite.op ⦋n⦌) :=
  (Sigma.ι (fun _ : c ⟶ c => Δ[n]) (𝟙 c)).app (Opposite.op ⦋n⦌)
    (SSet.yonedaEquiv (𝟙 Δ[n]))

theorem freeSimplexMapOfElement_generic (G : C ⥤ SSet.{u}) (c : C) (n : ℕ)
    (x : (G.obj c).obj (Opposite.op ⦋n⦌)) :
    ((freeSimplexMapOfElement C G c n x).app c).app (Opposite.op ⦋n⦌)
      (freeSimplexGeneric C c n) = x := by
  let f := freeSimplexMapOfElement C G c n x
  let ι : Δ[n] ⟶ (freeSimplexDiagram C c n).obj c :=
    Sigma.ι (fun _ : c ⟶ c => Δ[n]) (𝟙 c)
  have hmap : ι ≫ f.app c = SSet.yonedaEquiv.symm x := by
    change (Sigma.ι (fun _ : c ⟶ c => Δ[n]) (𝟙 c)) ≫
      (freeSimplexMapOfElement C G c n x).app c = SSet.yonedaEquiv.symm x
    exact ((evaluationAdjunctionRight SSet.{u} c).homEquiv Δ[n] G).apply_symm_apply
      (SSet.yonedaEquiv.symm x)
  change (f.app c).app (Opposite.op ⦋n⦌)
    (ι.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 Δ[n]))) = x
  calc
    (f.app c).app (Opposite.op ⦋n⦌)
      (ι.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 Δ[n]))) =
      (ι ≫ f.app c).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv (𝟙 Δ[n])) := rfl
    _ = (SSet.yonedaEquiv.symm x).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (𝟙 Δ[n])) := by rw [hmap]
    _ = x := by simp [SSet.yonedaEquiv, uliftYonedaEquiv]


/-- The cyclic subfunctor of a simplex is a regular-epi quotient of the free
simplex diagram. -/
theorem cyclicSubfunctor_regularEpi (G : C ⥤ SSet.{u}) (c : C) (n : ℕ)
    (x : (Functor.uncurry.obj G).obj (c, Opposite.op ⦋n⦌)) :
    ∃ e : freeSimplexDiagram C c n ⟶
        Functor.curry.obj (PresheafMonoGeneration.cyclicSubfunctor
          (Functor.uncurry.obj G) x).toFunctor,
      IsRegularEpi e := by
  let B := Functor.uncurry.obj G
  let T := PresheafMonoGeneration.cyclicSubfunctor B x
  let Q : C ⥤ SSet.{u} := Functor.curry.obj T.toFunctor
  let xT : (Q.obj c).obj (Opposite.op ⦋n⦌) :=
    ⟨x, PresheafMonoGeneration.mem_cyclicSubfunctor B x⟩
  let e : freeSimplexDiagram C c n ⟶ Q := freeSimplexMapOfElement C Q c n xT
  have hsurj : ∀ d : C × SimplexCategoryᵒᵖ,
      Function.Surjective ((Functor.uncurry.map e).app d) := by
    rintro ⟨c', m'⟩ ⟨y, hy⟩
    obtain ⟨h, hh⟩ := hy
    let R := freeSimplexDiagram C c n
    let z₀ := freeSimplexGeneric C c n
    let z := (Functor.uncurry.obj R).map h z₀
    refine ⟨z, ?_⟩
    have hnat := FunctorToTypes.naturality (Functor.uncurry.obj R)
      (Functor.uncurry.obj Q) (Functor.uncurry.map e) h z₀
    have hgen : ((Functor.uncurry.map e).app (c, Opposite.op ⦋n⦌) z₀) = xT :=
      freeSimplexMapOfElement_generic C Q c n xT
    apply Subtype.ext
    calc
      (((Functor.uncurry.map e).app (c', m')) z).val =
          (((Functor.uncurry.obj Q).map h)
            ((Functor.uncurry.map e).app (c, Opposite.op ⦋n⦌) z₀)).val := by
              exact congrArg Subtype.val hnat
      _ = (((Functor.uncurry.obj Q).map h) xT).val := by rw [hgen]
      _ = B.map h x := by
        simp only [Q, T, Functor.uncurry, Functor.curry, Functor.curryObj,
          Subfunctor.toFunctor] at *
        change B.map (Prod.mkHom (𝟙 c') h.2)
            (B.map (Prod.mkHom h.1 (𝟙 (Opposite.op ⦋n⦌))) x) = B.map h x
        rw [← FunctorToTypes.map_comp_apply]
        have hh : Prod.mkHom h.1 (𝟙 (Opposite.op ⦋n⦌)) ≫
            Prod.mkHom (𝟙 c') h.2 = h := by
          ext <;> simp
        rw [hh]
      _ = y := hh
  haveI : Epi (Functor.uncurry.map e) := by
    rw [NatTrans.epi_iff_epi_app]
    intro d
    exact (epi_iff_surjective _).mpr (hsurj d)
  haveI : Epi e := Functor.uncurry.epi_of_epi_map inferInstance
  haveI : IsRegularEpiCategory (C ⥤ SSet.{u}) := inferInstance
  exact ⟨e, IsRegularEpiCategory.regularEpiOfEpi e⟩

end
end DaggerModels.PartII.InjectiveKanDiagram
