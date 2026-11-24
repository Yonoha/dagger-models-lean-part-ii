import DaggerModelsPartII.JTProjectiveBar

/-!
# Explicit chain presentation of the projective bar rows

This module identifies the degree-`r` nerve row of `JTProjectiveBar.barValue`
with a chain of full reversal-simplex morphisms, a represented simplex at the
first index, and one presheaf element at the terminal index. The intermediate
presheaf elements are pulled back from the terminal one.

This comparison concerns simplices only. It does not assert projective
cofibrancy, a coend realization comparison, or the derived density map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarChains

noncomputable section

open JTProjectiveBar

/-- Literal degree-`r` bar summands: a full reversal-index chain, a
represented simplex at its first index, and a coefficient at its last. -/
def ChainData (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) : Type :=
  Σ c : ComposableArrows ReverseSimplex r,
    (d ⟶ c.left) × P.obj (op c.right)

/-- Projection of a structured-arrow nerve simplex to all its reversal
indices, its first represented simplex, and its terminal coefficient. -/
def extract (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ)
    (γ : ComposableArrows (barCategory P d) r) : ChainData P d r :=
  ⟨γ ⋙ StructuredArrow.proj d (elementIndex P) ⋙ elementIndex P,
    (γ.obj 0).hom, (γ.obj (Fin.last r)).right.unop.2⟩

/-- The coefficient forced at vertex `i` by a terminal coefficient. -/
def coefficientAt (P : ReverseSimplexᵒᵖ ⥤ Type)
    {r : ℕ} (c : ComposableArrows ReverseSimplex r)
    (x : P.obj (op c.right)) (i : Fin (r + 1)) :
    P.obj (op (c.obj i)) :=
  P.map (c.map (homOfLE (Fin.le_last i))).op x

/-- Every edge of an index chain acts between the pulled-back coefficients.
This retains all reversal morphisms, including automorphisms. -/
private theorem coefficientAt_map (P : ReverseSimplexᵒᵖ ⥤ Type)
    {r : ℕ} (c : ComposableArrows ReverseSimplex r)
    (x : P.obj (op c.right)) {i j : Fin (r + 1)} (f : i ⟶ j) :
    P.map (c.map f).op (coefficientAt P c x j) =
      coefficientAt P c x i := by
  unfold coefficientAt
  calc
    P.map (c.map f).op
        (P.map (c.map (homOfLE (Fin.le_last j))).op x) =
        P.map ((c.map (homOfLE (Fin.le_last j))).op ≫
          (c.map f).op) x := by rw [FunctorToTypes.map_comp_apply]
    _ = P.map (c.map (homOfLE (Fin.le_last i))).op x := by
      rw [← op_comp, ← c.map_comp]
      rfl

/-- The unique category-of-elements object over each index of a chain. -/
def elementAt (P : ReverseSimplexᵒᵖ ⥤ Type)
    {r : ℕ} (c : ComposableArrows ReverseSimplex r)
    (x : P.obj (op c.right)) (i : Fin (r + 1)) : P.Elementsᵒᵖ :=
  op (P.elementsMk (op (c.obj i)) (coefficientAt P c x i))

/-- The category-of-elements lift of an index-chain arrow. -/
def elementArrow (P : ReverseSimplexᵒᵖ ⥤ Type)
    {r : ℕ} (c : ComposableArrows ReverseSimplex r)
    (x : P.obj (op c.right)) {i j : Fin (r + 1)} (f : i ⟶ j) :
    elementAt P c x i ⟶ elementAt P c x j :=
  (CategoryOfElements.homMk (unop (elementAt P c x j))
    (unop (elementAt P c x i)) (c.map f).op
      (coefficientAt_map P c x f)).op

/-- The first represented simplex propagates along the index chain. -/
def representedAt {r : ℕ} (c : ComposableArrows ReverseSimplex r)
    {d : ReverseSimplex} (h : d ⟶ c.left) (i : Fin (r + 1)) :
    d ⟶ c.obj i :=
  h ≫ c.map (homOfLE (Fin.zero_le i))

private theorem elementIndex_map_eqToHom
    (P : ReverseSimplexᵒᵖ ⥤ Type)
    {s t : P.Elementsᵒᵖ} (h : s = t) :
    (elementIndex P).map (eqToHom h) =
      eqToHom (congrArg (elementIndex P).obj h) := by
  cases h
  rfl

/-- Lift the terminal-coefficient data to a full chain of structured arrows.
Every earlier element and every structured-arrow triangle is forced. -/
def lift (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) (a : ChainData P d r) :
    ComposableArrows (barCategory P d) r where
  obj i := StructuredArrow.mk
    (show d ⟶ (elementIndex P).obj (elementAt P a.1 a.2.2 i) from
      representedAt a.1 a.2.1 i)
  map {i j} f := StructuredArrow.homMk
    (elementArrow P a.1 a.2.2 f) (by
      dsimp [representedAt, elementArrow, elementIndex]
      rw [Category.assoc, ← a.1.map_comp]
      rfl)
  map_id i := by
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simp [elementArrow]
    rfl
  map_comp f g := by
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simp [elementArrow]

/-- A structured-arrow chain is determined by its index chain, its first
represented simplex, and the terminal coefficient. -/
def chainEquiv (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    ComposableArrows (barCategory P d) r ≃ ChainData P d r where
  toFun := extract P d r
  invFun := lift P d r
  left_inv γ := by
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      have hr : elementAt P (extract P d r γ).1
          (extract P d r γ).2.2 i = (γ.obj i).right := by
        apply congrArg op
        refine Functor.Elements.ext _ _ rfl ?_
        simpa only [eqToHom_refl, FunctorToTypes.map_id_apply,
          extract, coefficientAt, elementIndex] using
          (γ.map (homOfLE (Fin.le_last i))).right.unop.property
      apply StructuredArrow.obj_ext _ _ hr
      have hmap : (elementIndex P).map (eqToHom hr) = 𝟙 _ := by
        rw [elementIndex_map_eqToHom]
        rfl
      rw [hmap]
      change representedAt (extract P d r γ).1
        (extract P d r γ).2.1 i ≫ 𝟙 _ = (γ.obj i).hom
      rw [Category.comp_id]
      simp [extract, representedAt]
    case h_map =>
      intro i j f
      apply StructuredArrow.hom_ext
      letI : (elementIndex P).Faithful := by
        dsimp [elementIndex]
        infer_instance
      apply (elementIndex P).map_injective
      simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right,
        Functor.map_comp, elementIndex_map_eqToHom]
      change (extract P d r γ).1.map f =
        𝟙 _ ≫ (extract P d r γ).1.map f ≫ 𝟙 _
      simp
  right_inv a := by
    rcases a with ⟨c, h, x⟩
    apply Sigma.ext
    · apply CategoryTheory.Functor.ext
      case h_obj =>
        intro i
        rfl
      case h_map =>
        intro i j f
        rfl
    · simp [extract, lift, representedAt]
      constructor
      · exact Category.comp_id h
      · change P.map (c.map (𝟙 (Fin.last r))).op x = x
        simp

/-- The degree-`r` row of the installed bar is the literal chain coproduct
with every reversal morphism present. -/
def barDegreeEquiv (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    (barValue P d).obj (op ⦋r⦌) ≃ ChainData P d r :=
  chainEquiv P d r

/-- Outer reversal-index action on the literal chain presentation. -/
def chainOuterMap (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) (r : ℕ) :
    ChainData P e r → ChainData P d r :=
  fun a => ⟨a.1, f ≫ a.2.1, a.2.2⟩

/-- Changing the coefficient presheaf changes only the terminal element. -/
def chainCoefficientMap {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) (d : ReverseSimplex) (r : ℕ) :
    ChainData P d r → ChainData Q d r :=
  fun a => ⟨a.1, a.2.1, α.app (op a.1.right) a.2.2⟩

/-- The outer action of the installed bar agrees with precomposition of
the represented first simplex under the chain presentation. -/
theorem extract_outer (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) (r : ℕ)
    (γ : ComposableArrows (barCategory P e) r) :
    extract P d r
      ((Functor.mapComposableArrows
        (StructuredArrow.map f : barCategory P e ⥤ barCategory P d) r).obj γ) =
      chainOuterMap P f r (extract P e r γ) := by
  rfl

/-- The installed coefficient action agrees with the terminal-element
action under the chain presentation. -/
theorem extract_coefficient {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) (d : ReverseSimplex) (r : ℕ)
    (γ : ComposableArrows (barCategory P d) r) :
    extract Q d r
      ((Functor.mapComposableArrows
        (StructuredArrow.pre d (CategoryOfElements.map α).op
          (elementIndex Q)) r).obj γ) =
      chainCoefficientMap α d r (extract P d r γ) := by
  rfl

end

end DaggerModels.PartII.JTBarChains
