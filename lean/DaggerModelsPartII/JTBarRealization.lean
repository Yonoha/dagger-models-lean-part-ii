import DaggerModelsPartII.JTBarChainSSet
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Literal coend realization of the explicit bar chains

For each outer reversal index and each test simplex, the manuscript's
representable-coproduct realization is the actual Mathlib coend of the
bifunctor `(q, r) ↦ B_q × Δ[r]_n`. The inverse is the generator at `q = n`
with the identity simplex. The coend relation for a simplex operator gives
the other inverse. The chain simplicial set is already isomorphic to the
installed bar row, so this isolates the genuine coend bridge.

Projective cofibrancy and the derived density comparison are separate.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarRealization

noncomputable section

open JTProjectiveBar JTBarChains JTBarChainSSet

/-- The pointwise coend kernel for the simplicial copower of `X` by
standard simplices. Its diagonal at `q` is `X_q × Δ[q]_n`. -/
def realizationKernel (X : SSet.{0}) (n : SimplexCategoryᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ SimplexCategory ⥤ Type where
  obj q :=
    { obj r := X.obj q × (SSet.stdSimplex.obj r).obj n
      map {r s} f := fun z => (z.1, (SSet.stdSimplex.map f).app n z.2)
      map_id r := by
        funext z
        simp
      map_comp f g := by
        funext z
        simp [Functor.map_comp] }
  map {q q'} f :=
    { app r := fun z => (X.map f z.1, z.2)
      naturality := by
        intro r s g
        funext z
        rfl }
  map_id q := by
    apply NatTrans.ext
    funext r z
    simp
  map_comp f g := by
    apply NatTrans.ext
    funext r z
    simp

/-- Evaluate a coend generator `(x, σ : [n] ⟶ [q])` by restricting `x`
along the simplex operator `σ`. -/
def evaluationLeg (X : SSet.{0}) (n : SimplexCategoryᵒᵖ)
    (q : SimplexCategory) :
    ((realizationKernel X n).obj (op q)).obj q ⟶ X.obj n :=
  fun z => X.map (SSet.stdSimplex.objEquiv z.2).op z.1

/-- The evaluation legs satisfy the literal coend relation. -/
theorem evaluationLeg_condition (X : SSet.{0})
    (n : SimplexCategoryᵒᵖ) {i j : SimplexCategory} (f : i ⟶ j) :
    ((realizationKernel X n).map f.op).app i ≫ evaluationLeg X n i =
      ((realizationKernel X n).obj (op j)).map f ≫ evaluationLeg X n j := by
  funext z
  rcases z with ⟨x, σ⟩
  change X.map (SSet.stdSimplex.objEquiv σ).op (X.map f.op x) =
    X.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map f).app n σ)).op x
  rw [← FunctorToTypes.map_comp_apply]
  rw [← op_comp]
  rfl

/-- Evaluation descends from the literal abstract coend. -/
def coendEvaluation (X : SSet.{0}) (n : SimplexCategoryᵒᵖ) :
    coend (realizationKernel X n) ⟶ X.obj n :=
  coend.desc (evaluationLeg X n) (fun _ _ f => evaluationLeg_condition X n f)

theorem coendEvaluation_generator (X : SSet.{0}) (n : SimplexCategoryᵒᵖ)
    (q : SimplexCategory)
    (z : ((realizationKernel X n).obj (op q)).obj q) :
    coendEvaluation X n ((coend.ι (realizationKernel X n) q) z) =
      evaluationLeg X n q z := by
  change (coend.ι (realizationKernel X n) q ≫ coendEvaluation X n) z = _
  rw [coendEvaluation, coend.ι_desc]

/-- Insert a simplex as the coend generator at its own degree with the
identity standard simplex. -/
def identityGenerator (X : SSet.{0}) (n : SimplexCategoryᵒᵖ)
    (x : X.obj n) : coend (realizationKernel X n) :=
  (coend.ι (realizationKernel X n) n.unop)
    (x, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))

/-- Evaluating the identity generator returns its simplex. -/
theorem coendEvaluation_identityGenerator (X : SSet.{0})
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    coendEvaluation X n (identityGenerator X n x) = x := by
  change (coend.ι (realizationKernel X n) n.unop ≫
    coendEvaluation X n) (x, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)) = x
  simp only [coendEvaluation, coend.ι_desc]
  simp [evaluationLeg]

/-- Every literal coend generator is equivalent, by its own simplex
operator, to the identity generator at the test degree. -/
theorem identityGenerator_coendEvaluation_generator (X : SSet.{0})
    (n : SimplexCategoryᵒᵖ) (q : SimplexCategory)
    (z : ((realizationKernel X n).obj (op q)).obj q) :
    identityGenerator X n
      (coendEvaluation X n ((coend.ι (realizationKernel X n) q) z)) =
      (coend.ι (realizationKernel X n) q) z := by
  rcases z with ⟨x, σ⟩
  let θ : n.unop ⟶ q := SSet.stdSimplex.objEquiv σ
  have h := coend.condition (F := realizationKernel X n) θ
  have hz := congrFun h (x, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
  change (coend.ι (realizationKernel X n) n.unop)
      (coendEvaluation X n ((coend.ι (realizationKernel X n) q) (x, σ)),
        SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)) =
      (coend.ι (realizationKernel X n) q) (x, σ)
  rw [coendEvaluation_generator]
  have hs : (SSet.stdSimplex.map θ).app n
      (SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)) = σ := by
    calc
      _ = SSet.stdSimplex.objEquiv.symm ((𝟙 n.unop) ≫ θ) :=
        (SSet.stdSimplex.objEquiv_symm_comp (𝟙 n.unop) θ).symm
      _ = σ := by simp [θ]
  simpa [evaluationLeg, θ, realizationKernel, hs] using hz

/-- Pointwise co-Yoneda for the actual Mathlib coend of standard-simplex
copowers, with explicit inverse on generators. -/
def coendEquiv (X : SSet.{0}) (n : SimplexCategoryᵒᵖ) :
    coend (realizationKernel X n) ≃ X.obj n where
  toFun := coendEvaluation X n
  invFun := identityGenerator X n
  left_inv y := by
    have h : coendEvaluation X n ≫ identityGenerator X n = 𝟙 _ := by
      apply coend.hom_ext
      intro q
      funext z
      exact identityGenerator_coendEvaluation_generator X n q z
    exact congrFun h y
  right_inv x := coendEvaluation_identityGenerator X n x

/-- Changing the test simplex degree acts on the standard-simplex factor
of the coend kernel, leaving the bar coefficient unchanged. -/
def realizationKernelDegreeMap (X : SSet.{0})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    realizationKernel X n ⟶ realizationKernel X m where
  app q :=
    { app r := fun z => (z.1, (SSet.stdSimplex.obj r).map f z.2)
      naturality := by
        intro r s g
        funext z
        apply Prod.ext
        · rfl
        · exact congrFun ((SSet.stdSimplex.map g).naturality f).symm z.2 }
  naturality := by
    intro q q' g
    apply NatTrans.ext
    funext r z
    rfl

theorem coendDegreeMap_generator (X : SSet.{0})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (q : SimplexCategory)
    (z : ((realizationKernel X n).obj (op q)).obj q) :
    coend.map (realizationKernelDegreeMap X f)
        ((coend.ι (realizationKernel X n) q) z) =
      (coend.ι (realizationKernel X m) q)
        (((realizationKernelDegreeMap X f).app (op q)).app q z) := by
  change (coend.ι (realizationKernel X n) q ≫
    coend.map (realizationKernelDegreeMap X f)) z = _
  rw [coend.ι_map]
  rfl

private theorem realizationKernelDegreeMap_id (X : SSet.{0})
    (n : SimplexCategoryᵒᵖ) :
    realizationKernelDegreeMap X (𝟙 n) = 𝟙 (realizationKernel X n) := by
  apply NatTrans.ext
  funext q
  apply NatTrans.ext
  funext r z
  simp [realizationKernelDegreeMap]

private theorem realizationKernelDegreeMap_comp (X : SSet.{0})
    {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) :
    realizationKernelDegreeMap X (f ≫ g) =
      realizationKernelDegreeMap X f ≫ realizationKernelDegreeMap X g := by
  apply NatTrans.ext
  funext q
  apply NatTrans.ext
  funext r z
  simp [realizationKernelDegreeMap]

/-- The literal pointwise abstract coends assemble into a simplicial set.
Its `n`-simplices are `∫^q X_q × Δ[q]_n`. -/
def coendRealization (X : SSet.{0}) : SSet.{0} where
  obj n := coend (realizationKernel X n)
  map f := coend.map (realizationKernelDegreeMap X f)
  map_id n := by
    change coend.map (realizationKernelDegreeMap X (𝟙 n)) = 𝟙 _
    rw [realizationKernelDegreeMap_id]
    exact coend.map_id
  map_comp f g := by
    change coend.map (realizationKernelDegreeMap X (f ≫ g)) =
      coend.map (realizationKernelDegreeMap X f) ≫
        coend.map (realizationKernelDegreeMap X g)
    rw [realizationKernelDegreeMap_comp]
    exact (coend.map_comp _ _).symm

/-- The pointwise co-Yoneda equivalences respect every test-simplex
operator, giving a genuine simplicial-set isomorphism. -/
def coendRealizationIso (X : SSet.{0}) : coendRealization X ≅ X :=
  NatIso.ofComponents (fun n => (coendEquiv X n).toIso) (by
    intro n m f
    apply coend.hom_ext
    intro q
    funext z
    rcases z with ⟨x, σ⟩
    change coendEvaluation X m
        (coend.map (realizationKernelDegreeMap X f)
          ((coend.ι (realizationKernel X n) q) (x, σ))) =
      X.map f (coendEvaluation X n
        ((coend.ι (realizationKernel X n) q) (x, σ)))
    rw [coendDegreeMap_generator, coendEvaluation_generator,
      coendEvaluation_generator]
    change X.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj q).map f σ)).op x =
      X.map f (X.map (SSet.stdSimplex.objEquiv σ).op x)
    rw [← FunctorToTypes.map_comp_apply]
    rw [SSet.stdSimplex.map_apply]
    rfl)

/-- Transporting a simplicial map across coend evaluation acts on a raw
coend generator by applying the map to its chain coefficient. -/
theorem coendTransport_generator {X Y : SSet.{0}} (α : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (q : SimplexCategory)
    (a : X.obj (op q)) (σ : (SSet.stdSimplex.obj q).obj n) :
    ((coendRealizationIso X).hom ≫ α ≫ (coendRealizationIso Y).inv).app n
        ((coend.ι (realizationKernel X n) q) (a, σ)) =
      (coend.ι (realizationKernel Y n) q) (α.app (op q) a, σ) := by
  apply (coendEquiv Y n).injective
  change coendEvaluation Y n
      (((coendRealizationIso X).hom ≫ α ≫
        (coendRealizationIso Y).inv).app n
        ((coend.ι (realizationKernel X n) q) (a, σ))) =
    coendEvaluation Y n
      ((coend.ι (realizationKernel Y n) q) (α.app (op q) a, σ))
  simpa [coendRealizationIso, coendEquiv, coendEvaluation_generator,
    coendEvaluation_identityGenerator, evaluationLeg]
    using congrFun (α.naturality (SSet.stdSimplex.objEquiv σ).op) a

/-- The literal coend at test degree `n` gives the installed bar row's
simplices, via the actual chain-simplicial-set isomorphism. -/
def coendBarDegreeIso (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (n : SimplexCategoryᵒᵖ) :
    coend (realizationKernel (chainSSet P d) n) ≅
      (barValue P d).obj n :=
  (coendEquiv (chainSSet P d) n).toIso ≪≫
    ((barValueChainIso P d).app n).symm

/-- The entire actual bar row is the coend realization of the literal
representable-coproduct chain diagram, not only a degreewise equivalent set. -/
def coendBarIso (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    coendRealization (chainSSet P d) ≅ barValue P d :=
  coendRealizationIso (chainSSet P d) ≪≫ (barValueChainIso P d).symm

/-- The outer reversal-index diagram of literal coend realizations. Its
action is transported from the already constructed actual bar diagram through
the explicit coend evaluation and chain isomorphisms. -/
def coendBarPresheaf (P : ReverseSimplexᵒᵖ ⥤ Type) :
    SegalLocalizers.ReverseDaggerSpace.{0} where
  obj d := coendRealization (chainSSet P d.unop)
  map {d e} f :=
    (coendBarIso P d.unop).hom ≫ (barPresheaf P).map f ≫
      (coendBarIso P e.unop).inv
  map_id d := by
    change (coendBarIso P d.unop).hom ≫
      (barPresheaf P).map (𝟙 d) ≫ (coendBarIso P d.unop).inv = 𝟙 _
    rw [(barPresheaf P).map_id d]
    exact (coendBarIso P d.unop).hom_inv_id
  map_comp f g := by
    simp [Category.assoc]

/-- The coend realization is naturally the installed bar diagram in every
outer reversal index. -/
def coendBarPresheafIso (P : ReverseSimplexᵒᵖ ⥤ Type) :
    coendBarPresheaf P ≅ barPresheaf P :=
  NatIso.ofComponents (fun d => coendBarIso P d.unop) (by
    intro d e f
    simp [coendBarPresheaf, Category.assoc])

/-- A map of coefficient presheaves acts on the actual coend-resolution
diagram by its already checked action on the literal bar chain. -/
def coendBarPresheafMap {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) : coendBarPresheaf P ⟶ coendBarPresheaf Q where
  app d := (coendBarIso P d.unop).hom ≫
    (barPresheafMap α).app d ≫ (coendBarIso Q d.unop).inv
  naturality := by
    intro d e f
    simp [coendBarPresheaf, Category.assoc]

/-- The literal coend-resolution diagrams are functorial in every input
reversal presheaf, with no new coefficient action assumed. -/
def coendBarFunctor :
    (ReverseSimplexᵒᵖ ⥤ Type) ⥤ SegalLocalizers.ReverseDaggerSpace.{0} where
  obj := coendBarPresheaf
  map := coendBarPresheafMap
  map_id P := by
    apply NatTrans.ext
    funext d
    change (coendBarIso P d.unop).hom ≫
      (barPresheafMap (𝟙 P)).app d ≫ (coendBarIso P d.unop).inv = 𝟙 _
    have h := congrArg (fun η : barPresheaf P ⟶ barPresheaf P => η.app d)
      (barFunctor.map_id P)
    change (barPresheafMap (𝟙 P)).app d = 𝟙 _ at h
    rw [h]
    exact (coendBarIso P d.unop).hom_inv_id
  map_comp α β := by
    apply NatTrans.ext
    funext d
    change (coendBarIso _ d.unop).hom ≫
        (barPresheafMap (α ≫ β)).app d ≫ (coendBarIso _ d.unop).inv =
      ((coendBarIso _ d.unop).hom ≫ (barPresheafMap α).app d ≫
        (coendBarIso _ d.unop).inv) ≫
      ((coendBarIso _ d.unop).hom ≫ (barPresheafMap β).app d ≫
        (coendBarIso _ d.unop).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have h := congrArg (fun η : barPresheaf _ ⟶ barPresheaf _ => η.app d)
      (barFunctor.map_comp α β)
    simpa only [NatTrans.comp_app] using congrArg
      (fun k => (coendBarIso _ d.unop).hom ≫ k ≫ (coendBarIso _ d.unop).inv) h

/-- The manuscript's explicit bar coend realization agrees naturally with
the installed bar functor in both the outer index and the coefficient input. -/
def coendBarFunctorIso : coendBarFunctor ≅ barFunctor :=
  NatIso.ofComponents coendBarPresheafIso (by
    intro P Q α
    apply NatTrans.ext
    funext d
    change ((coendBarIso P d.unop).hom ≫
      (barPresheafMap α).app d ≫ (coendBarIso Q d.unop).inv) ≫
      (coendBarIso Q d.unop).hom =
      (coendBarIso P d.unop).hom ≫ (barPresheafMap α).app d
    simp [Category.assoc])


/-- The checked outer map, expressed as a map of chain simplicial sets. -/
def chainOuterNat (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) :
    chainSSet P e ⟶ chainSSet P d :=
  (barValueChainIso P e).inv ≫ barOuterMap P f ≫
    (barValueChainIso P d).hom

/-- The checked coefficient map, expressed as a map of chain simplicial sets. -/
def chainCoefficientNat {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) (d : ReverseSimplex) :
    chainSSet P d ⟶ chainSSet Q d :=
  (barValueChainIso P d).inv ≫ barWeightMap α d ≫
    (barValueChainIso Q d).hom

theorem chainOuterNat_apply (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e)
    (n : SimplexCategoryᵒᵖ) (a : (chainSSet P e).obj n) :
    (chainOuterNat P f).app n a = chainOuterMap P f n.unop.len a := by
  let γ := (barValueChainIso P e).inv.app n a
  have hγ : (barValueChainIso P e).hom.app n γ = a := by
    simp [γ]
  change (barValueChainIso P d).hom.app n ((barOuterMap P f).app n γ) = _
  rw [barValueChainIso_outer, hγ]

theorem chainCoefficientNat_apply {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) (d : ReverseSimplex)
    (n : SimplexCategoryᵒᵖ) (a : (chainSSet P d).obj n) :
    (chainCoefficientNat α d).app n a =
      chainCoefficientMap α d n.unop.len a := by
  let γ := (barValueChainIso P d).inv.app n a
  have hγ : (barValueChainIso P d).hom.app n γ = a := by
    simp [γ]
  change (barValueChainIso Q d).hom.app n ((barWeightMap α d).app n γ) = _
  rw [barValueChainIso_coefficient, hγ]

/-- On a literal coend generator, an outer reversal map changes exactly
the first represented arrow of the full chain and leaves `σ` unchanged. -/
theorem coendBar_outer_generator (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e)
    (n : SimplexCategoryᵒᵖ) (q : SimplexCategory)
    (a : (chainSSet P e).obj (op q))
    (σ : (SSet.stdSimplex.obj q).obj n) :
    ((coendBarPresheaf P).map f.op).app n
        ((coend.ι (realizationKernel (chainSSet P e) n) q) (a, σ)) =
      (coend.ι (realizationKernel (chainSSet P d) n) q)
        (chainOuterMap P f q.len a, σ) := by
  change ((coendRealizationIso (chainSSet P e)).hom ≫
      chainOuterNat P f ≫
      (coendRealizationIso (chainSSet P d)).inv).app n
      ((coend.ι (realizationKernel (chainSSet P e) n) q) (a, σ)) = _
  rw [coendTransport_generator]
  rw [chainOuterNat_apply]

/-- On a literal coend generator, a coefficient map changes exactly the
terminal presheaf element of the full chain and leaves `σ` unchanged. -/
theorem coendBar_coefficient_generator
    {P Q : ReverseSimplexᵒᵖ ⥤ Type} (α : P ⟶ Q)
    (d : ReverseSimplex) (n : SimplexCategoryᵒᵖ) (q : SimplexCategory)
    (a : (chainSSet P d).obj (op q))
    (σ : (SSet.stdSimplex.obj q).obj n) :
    ((coendBarPresheafMap α).app (op d)).app n
        ((coend.ι (realizationKernel (chainSSet P d) n) q) (a, σ)) =
      (coend.ι (realizationKernel (chainSSet Q d) n) q)
        (chainCoefficientMap α d q.len a, σ) := by
  change ((coendRealizationIso (chainSSet P d)).hom ≫
      chainCoefficientNat α d ≫
      (coendRealizationIso (chainSSet Q d)).inv).app n
      ((coend.ι (realizationKernel (chainSSet P d) n) q) (a, σ)) = _
  rw [coendTransport_generator]
  rw [chainCoefficientNat_apply]

end

end DaggerModels.PartII.JTBarRealization
