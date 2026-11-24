import DaggerModelsPartII.JTGraphSimplexLastVertex

/-! The standard-simplex resolution compares to the original last-vertex chain. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.SimplexResolutionSwitch

variable {m n : SimplexCategory}

/-- A pointwise comparison of two ordinal maps gives the ordinal map
which chooses the first at time zero and the second at time one. -/
def switch (f g : m ⟶ n) (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) (t : m ⟶ ⦋1⦌) :
    m ⟶ n :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ if t.toOrderHom i = 0 then f.toOrderHom i else g.toOrderHom i
      monotone' := by
        intro i j hij
        by_cases ht : t.toOrderHom j = 0
        · have hi : t.toOrderHom i = 0 :=
            Fin.le_zero_iff.mp (ht ▸ t.toOrderHom.monotone hij)
          simp only [hi, ht, if_true]
          exact f.toOrderHom.monotone hij
        · simp only [ht, if_false]
          split
          · exact (f.toOrderHom.monotone hij).trans (h j)
          · exact g.toOrderHom.monotone hij }

theorem switch_zero (f g : m ⟶ n) (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) :
    switch f g h (m.const ⦋1⦌ 0) = f := by
  ext i : 3
  rfl

theorem switch_one (f g : m ⟶ n) (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) :
    switch f g h (m.const ⦋1⦌ 1) = g := by
  ext i : 3
  rfl

/-- Switching commutes with simultaneous restriction along any simplex operator. -/
theorem precomp_switch {k : SimplexCategory} (a : k ⟶ m) (f g : m ⟶ n)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) (t : m ⟶ ⦋1⦌) :
    a ≫ switch f g h t = switch (a ≫ f) (a ≫ g) (fun i ↦ h (a.toOrderHom i)) (a ≫ t) := by
  ext i : 3
  rfl

/-- Switching commutes with postcomposition by any monotone ordinal map. -/
theorem switch_postcomp {k : SimplexCategory} (f g : m ⟶ n)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) (t : m ⟶ ⦋1⦌) (a : n ⟶ k) :
    switch f g h t ≫ a =
      switch (f ≫ a) (g ≫ a) (fun i ↦ a.toOrderHom.monotone (h i)) t := by
  ext i : 3
  change a.toOrderHom (if t.toOrderHom i = 0 then f.toOrderHom i else g.toOrderHom i) =
    if t.toOrderHom i = 0 then a.toOrderHom (f.toOrderHom i) else a.toOrderHom (g.toOrderHom i)
  split <;> rfl

end DaggerModels.PartII.SimplexResolutionSwitch

open Opposite

namespace DaggerModels.PartII.SimplexResolutionLastOrdinal

open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)

variable {D : Type} [SmallCategory D] (d : D ⥤ SimplexCategory)
variable {q r : SimplexCategoryᵒᵖ}

private abbrev tailArrow (F : (nerve D).obj q) (i : Fin (q.unop.len + 1)) :
    F.obj i ⟶ last F :=
  F.map (homOfLE (Fin.le_last i))

/-- The last vertex of each simplex, transported by its suffix to the common last simplex. -/
def lastOrdinal (F : (nerve D).obj q) : q.unop ⟶ d.obj (last F) :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ (d.map (tailArrow F i)).toOrderHom (Fin.last (d.obj (F.obj i)).len)
      monotone' := by
        intro i j h
        have hf : tailArrow F i = F.map (homOfLE h) ≫ tailArrow F j := by
          rw [← F.map_comp]
          rfl
        change (d.map (tailArrow F i)).toOrderHom (Fin.last (d.obj (F.obj i)).len) ≤
          (d.map (tailArrow F j)).toOrderHom (Fin.last (d.obj (F.obj j)).len)
        rw [hf, d.map_comp]
        exact (d.map (tailArrow F j)).toOrderHom.monotone (Fin.le_last _) }

/-- The last vertex of the first simplex is bounded by the last-vertex chain. -/
theorem first_le_lastOrdinal (F : (nerve D).obj q) (f : q.unop ⟶ d.obj (first F))
    (i : Fin (q.unop.len + 1)) :
    (f ≫ d.map (tailArrow F 0)).toOrderHom i ≤ (lastOrdinal d F).toOrderHom i := by
  change (d.map (tailArrow F 0)).toOrderHom (f.toOrderHom i) ≤
    (d.map (tailArrow F i)).toOrderHom (Fin.last (d.obj (F.obj i)).len)
  have hf : tailArrow F 0 = F.map (homOfLE (Fin.zero_le i)) ≫ tailArrow F i := by
    rw [← F.map_comp]
    rfl
  rw [hf, d.map_comp]
  exact (d.map (tailArrow F i)).toOrderHom.monotone (Fin.le_last _)

/-- Face and degeneracy operators retain the last-vertex chain via the actual suffix. -/
theorem lastOrdinal_natural (F : (nerve D).obj q) (α : q ⟶ r) :
    lastOrdinal d ((nerve D).map α F) ≫ d.map (lastArrow α F) =
      α.unop ≫ lastOrdinal d F := by
  ext i : 3
  let u := α.unop.toOrderHom i
  let j := α.unop.toOrderHom (Fin.last r.unop.len)
  have hf : tailArrow F u =
      tailArrow ((nerve D).map α F) i ≫ lastArrow α F := by
    change F.map (homOfLE (Fin.le_last u)) =
      F.map (homOfLE (α.unop.toOrderHom.monotone (Fin.le_last i))) ≫
        F.map (homOfLE (Fin.le_last j))
    rw [← F.map_comp]
    rfl
  change (d.map (lastArrow α F)).toOrderHom
    ((d.map (tailArrow ((nerve D).map α F) i)).toOrderHom (Fin.last (d.obj (F.obj u)).len)) =
      (d.map (tailArrow F u)).toOrderHom (Fin.last (d.obj (F.obj u)).len)
  rw [hf, d.map_comp]
  rfl

end DaggerModels.PartII.SimplexResolutionLastOrdinal

namespace DaggerModels.PartII.NerveSimplexResolutionHomotopy

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerNativeSimplicialReplacementCells (first initialArrow horizontal vertical)
open DaggerNativeDualTheoremACells (last lastArrow)
open DaggerNativeSimplicialReplacement (replacement diagonalProjection)
open JTGraphCylinderSimplexSpan (Simplices degree)
open JTGraphSimplexLastVertex (lastVertex)
open SimplexResolutionLastOrdinal (lastOrdinal first_le_lastOrdinal lastOrdinal_natural)
open SimplexResolutionSwitch (switch switch_zero switch_one precomp_switch switch_postcomp)

noncomputable section

variable (C : Type) [SmallCategory C]

private abbrev simplexDegree : Simplices C ⥤ SimplexCategory := degree C

private def weight : Simplices C ⥤ SSet.{0} := simplexDegree C ⋙ SSet.stdSimplex

private abbrev Res := DaggerBisimplicialDiagonal.diag (replacement (weight C))

private abbrev chain {q : SimplexCategoryᵒᵖ} (F : (nerve (Simplices C)).obj q) :=
  (last F).unop.snd

private abbrev suffix {C : Type} [SmallCategory C] {q : SimplexCategoryᵒᵖ}
    (F : (nerve (Simplices C)).obj q) :=
  F.map (homOfLE (Fin.zero_le (Fin.last q.unop.len)))

private def atFirst {q : SimplexCategoryᵒᵖ} (F : (nerve (Simplices C)).obj q)
    (t : ((weight C).obj (first F)).obj q) : q.unop ⟶ (simplexDegree C).obj (last F) :=
  SSet.stdSimplex.objEquiv t ≫ (simplexDegree C).map (suffix F)

private def atLast {q : SimplexCategoryᵒᵖ} (F : (nerve (Simplices C)).obj q) :
    q.unop ⟶ (simplexDegree C).obj (last F) := lastOrdinal (simplexDegree C) F

private theorem first_le_last {q : SimplexCategoryᵒᵖ} (F : (nerve (Simplices C)).obj q)
    (t : ((weight C).obj (first F)).obj q) (i : Fin (q.unop.len + 1)) :
    (atFirst C F t).toOrderHom i ≤ (atLast C F).toOrderHom i :=
  first_le_lastOrdinal (simplexDegree C) F (SSet.stdSimplex.objEquiv t) i

private theorem triangle {q r : SimplexCategoryᵒᵖ}
    (F : (nerve (Simplices C)).obj q) (α : q ⟶ r) :
    suffix F =
      initialArrow α F ≫ suffix ((nerve (Simplices C)).map α F) ≫ lastArrow α F := by
  change F.map (homOfLE _) = F.map (homOfLE _) ≫ F.map (homOfLE _) ≫ F.map (homOfLE _)
  rw [← F.map_comp, ← F.map_comp]
  rfl

private theorem first_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (Res C).obj q) :
    atFirst C ((Res C).map α s).1 ((Res C).map α s).2 ≫ (simplexDegree C).map (lastArrow α s.1) =
      α.unop ≫ atFirst C s.1 s.2 := by
  rcases s with ⟨F, t⟩
  change (α.unop ≫ SSet.stdSimplex.objEquiv t ≫ (simplexDegree C).map (initialArrow α F)) ≫
      (simplexDegree C).map (suffix ((nerve (Simplices C)).map α F)) ≫
        (simplexDegree C).map (lastArrow α F) =
    α.unop ≫ (SSet.stdSimplex.objEquiv t ≫ (simplexDegree C).map (suffix F))
  rw [triangle C F α, (simplexDegree C).map_comp, (simplexDegree C).map_comp]
  simp only [Category.assoc]

private theorem chain_natural {q r : SimplexCategoryᵒᵖ}
    (F : (nerve (Simplices C)).obj q) (α : q ⟶ r) :
    (nerve C).map ((simplexDegree C).map (lastArrow α F)).op (chain C F) =
      chain C ((nerve (Simplices C)).map α F) :=
  (lastArrow α F).unop.property

private def timeOrdinal {q : SimplexCategoryᵒᵖ} (s : (Res C).obj q)
    (t : (Δ[1] : SSet.{0}).obj q) : q.unop ⟶ (simplexDegree C).obj (last s.1) :=
  switch (atFirst C s.1 s.2) (atLast C s.1) (first_le_last C s.1 s.2)
    (SSet.stdSimplex.objEquiv t)

private theorem time_natural {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (Res C).obj q) (t : (Δ[1] : SSet.{0}).obj q) :
    timeOrdinal C ((Res C).map α s) ((Δ[1] : SSet.{0}).map α t) ≫
        (simplexDegree C).map (lastArrow α s.1) = α.unop ≫ timeOrdinal C s t := by
  unfold timeOrdinal
  rw [switch_postcomp, precomp_switch]
  have h₀ := first_natural C α s
  have h₁ := lastOrdinal_natural (simplexDegree C) s.1 α
  have ht : SSet.stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map α t) =
      α.unop ≫ SSet.stdSimplex.objEquiv t := rfl
  have h₁' : atLast C ((Res C).map α s).1 ≫ (simplexDegree C).map (lastArrow α s.1) =
      α.unop ≫ atLast C s.1 := h₁
  exact congrArg (fun t : r.unop ⟶ ⦋1⦌ ↦ switch _ _ _ t) ht |>.trans
    (by
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      funext i
      simp only [switch, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
      rw [h₀, h₁'])

/-- Interpolate between evaluation of the entire parameter and the last-vertex chain. -/
def comparisonMap : Res C ⊗ Δ[1] ⟶ nerve C where
  app _ s := (nerve C).map (timeOrdinal C s.1 s.2).op (chain C s.1.1)
  naturality {q r} α := by
    funext s
    change (nerve C).map (timeOrdinal C ((Res C).map α s.1) ((Δ[1] : SSet.{0}).map α s.2)).op
        (chain C ((nerve (Simplices C)).map α s.1.1)) =
      (nerve C).map α ((nerve C).map (timeOrdinal C s.1 s.2).op (chain C s.1.1))
    rw [← chain_natural C s.1.1 α]
    simp only [← FunctorToTypes.map_comp_apply]
    exact congrArg (fun k : r.unop ⟶ (simplexDegree C).obj (last s.1.1) ↦
      (nerve C).map k.op (chain C s.1.1)) (time_natural C α s.1 s.2)

private def evaluation : weight C ⟶ (Functor.const (Simplices C)).obj (nerve C) where
  app P := SSet.yonedaEquiv.symm P.unop.snd
  naturality {P P'} f := by
    change SSet.stdSimplex.map ((simplexDegree C).map f) ≫ SSet.yonedaEquiv.symm P'.unop.snd =
      SSet.yonedaEquiv.symm P.unop.snd ≫ 𝟙 (nerve C)
    rw [Category.comp_id]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_map_comp]
    exact f.unop.property

/-- Evaluate the entire standard-simplex parameter in the original nerve. -/
def evaluationMap : Res C ⟶ nerve C :=
  DaggerNativeSimplicialReplacement.diagonalAugmentation (weight C) (evaluation C)

private theorem comparison_zero :
    SSet.ι₀ ≫ comparisonMap C = evaluationMap C := by
  apply NatTrans.ext
  funext q s
  change (nerve C).map (switch (atFirst C s.1 s.2) (atLast C s.1)
    (first_le_last C s.1 s.2) (q.unop.const ⦋1⦌ 0)).op (chain C s.1) =
      (SSet.yonedaEquiv.symm (first s.1).unop.snd).app q s.2
  have hs := switch_zero (atFirst C s.1 s.2) (atLast C s.1) (first_le_last C s.1 s.2)
  refine (congrArg (fun j : q.unop ⟶ (simplexDegree C).obj (last s.1) ↦
    (nerve C).map j.op (chain C s.1)) hs).trans ?_
  change (nerve C).map ((SSet.stdSimplex.objEquiv s.2 ≫
    (simplexDegree C).map (suffix s.1)).op) (chain C s.1) = _
  change (nerve C).map (SSet.stdSimplex.objEquiv s.2).op
    ((nerve C).map ((simplexDegree C).map (suffix s.1)).op (chain C s.1)) = _
  rw [show (nerve C).map ((simplexDegree C).map (suffix s.1)).op (chain C s.1) =
      (first s.1).unop.snd from (suffix s.1).unop.property]
  exact (SSet.yonedaEquiv_symm_app_apply _ _).symm

private theorem last_obj_transport {P P' : Simplices C} (f : P ⟶ P') :
    P'.unop.snd.obj (((simplexDegree C).map f).toOrderHom (Fin.last P.unop.fst.unop.len)) =
      (lastVertex C).obj P := by
  have e := f.unop.property
  change (nerve C).map ((simplexDegree C).map f).op P'.unop.snd = P.unop.snd at e
  exact congrArg (fun A : (nerve C).obj P.unop.fst ↦ last A) e

private theorem transported_ordinal_arrow {D : Type} [SmallCategory D]
    (F : D ⥤ C) {i j i' j' : D} (hi : i = i') (hj : j = j') (f : i ⟶ j) (g : i' ⟶ j')
    [Subsingleton (i ⟶ j)] :
    HEq (F.map f) (F.map g) := by
  subst i'
  subst j'
  exact heq_of_eq (congrArg F.map (Subsingleton.elim f g))

private theorem last_map_transport_on_chains {p p' p'' : SimplexCategoryᵒᵖ}
    (α : p' ⟶ p) (β : p'' ⟶ p') (u'' : (nerve C).obj p'')
    (u' : (nerve C).obj p') (u : (nerve C).obj p)
    (hβ : (nerve C).map β u'' = u') (hα : (nerve C).map α u' = u) :
    HEq (u''.map (homOfLE (β.unop.toOrderHom.monotone
      (Fin.le_last (α.unop.toOrderHom (Fin.last p.unop.len))))))
      ((lastVertex C).map
        (CategoryOfElements.homMk (F := nerve C) ⟨p', u'⟩ ⟨p, u⟩ α hα).op) := by
  subst u'
  subst u
  apply heq_of_eq
  change u''.map _ = eqToHom rfl ≫ lastArrow α ((nerve C).map β u'')
  rw [eqToHom_refl, Category.id_comp]
  rfl

private theorem last_map_transport {P P' P'' : Simplices C} (g : P ⟶ P') (t : P' ⟶ P'') :
    HEq (P''.unop.snd.map (homOfLE
      (((simplexDegree C).map t).toOrderHom.monotone
        (Fin.le_last (((simplexDegree C).map g).toOrderHom (Fin.last P.unop.fst.unop.len))))))
      ((lastVertex C).map g) :=
  last_map_transport_on_chains C g.unop.val t.unop.val P''.unop.snd P'.unop.snd P.unop.snd
    t.unop.property g.unop.property

private theorem comparison_one :
    SSet.ι₁ ≫ comparisonMap C = diagonalProjection (weight C) ≫ nerveMap (lastVertex C) := by
  apply NatTrans.ext
  funext q s
  change (nerve C).map (switch (atFirst C s.1 s.2) (atLast C s.1)
    (first_le_last C s.1 s.2) (q.unop.const ⦋1⦌ 1)).op (chain C s.1) =
    s.1 ⋙ lastVertex C
  have hs := switch_one (atFirst C s.1 s.2) (atLast C s.1) (first_le_last C s.1 s.2)
  refine (congrArg (fun j : q.unop ⟶ (simplexDegree C).obj (last s.1) ↦
    (nerve C).map j.op (chain C s.1)) hs).trans ?_
  refine CategoryTheory.Functor.ext (fun i ↦ last_obj_transport C
    (s.1.map (homOfLE (Fin.le_last i)))) ?_
  intro i j f
  let g := s.1.map f
  let t := s.1.map (homOfLE (Fin.le_last j))
  have h : s.1.map (homOfLE (Fin.le_last i)) = g ≫ t := by
    rw [← s.1.map_comp]
    rfl
  have hi : (atLast C s.1).toOrderHom i =
      ((simplexDegree C).map t).toOrderHom (((simplexDegree C).map g).toOrderHom
        (Fin.last ((s.1.obj i).unop.fst.unop.len))) := by
    change ((simplexDegree C).map (s.1.map (homOfLE (Fin.le_last i)))).toOrderHom _ = _
    rw [h, (simplexDegree C).map_comp]
    rfl
  have hj : (atLast C s.1).toOrderHom j =
      ((simplexDegree C).map t).toOrderHom (Fin.last (s.1.obj j).unop.fst.unop.len) := rfl
  have hf : HEq (((nerve C).map (atLast C s.1).op (chain C s.1)).map f)
      ((lastVertex C).map g) := by
    refine HEq.trans ?_ (last_map_transport C g t)
    change HEq ((chain C s.1).map
      (homOfLE ((atLast C s.1).toOrderHom.monotone (leOfHom f)))) _
    exact transported_ordinal_arrow C (chain C s.1) hi hj _ _
  exact (conj_eqToHom_iff_heq _ _
    (last_obj_transport C (s.1.map (homOfLE (Fin.le_last i))))
    (last_obj_transport C t)).mpr hf

/-- The exact evaluation of the standard-simplex parameter is homotopic to
the nerve of the last-vertex functor after forgetting the parameter. -/
def comparison : SSet.Homotopy (evaluationMap C)
    (diagonalProjection (weight C) ≫ nerveMap (lastVertex C)) :=
  SSet.Homotopy.mk (comparisonMap C) (comparison_zero C) (comparison_one C)

variable (A : (nerve C).Subcomplex)

/-- The same last-vertex functor restricted to the actual simplices of A. -/
def lastVertexOnSubcomplex : A.toSSet.Elementsᵒᵖ ⥤ C :=
  (CategoryOfElements.map A.ι).op ⋙ lastVertex C

private abbrev toSimplices : A.toSSet.Elementsᵒᵖ ⥤ Simplices C :=
  (CategoryOfElements.map A.ι).op

private def liftElements (X : SSet.{0}) : DaggerNativeSimplexIndexResolution.LiftedIndex X ⥤
    X.Elementsᵒᵖ :=
  ULiftHom.down ⋙ (CategoryOfElements.costructuredArrowULiftYonedaEquivalence X).inverse

private def intoNerveResolution :
    SimplicialResolutionFunctor.resolutionFunctor.obj A.toSSet ⟶ Res C :=
  DaggerNativeSimplicialReplacementReindex.diagonalReindex
    (liftElements A.toSSet ⋙ toSimplices C A) (weight C)

private theorem into_projection :
    intoNerveResolution C A ≫ diagonalProjection (weight C) ≫ nerveMap (lastVertex C) =
      SimplicialResolutionFunctor.elementsProjection.app A.toSSet ≫
        nerveMap (lastVertexOnSubcomplex C A) := by
  let F := liftElements A.toSSet
  let G := toSimplices C A
  let L := lastVertex C
  have h := DaggerNativeSimplicialReplacementReindex.projection_square (F ⋙ G) (weight C)
  change intoNerveResolution C A ≫ diagonalProjection (weight C) =
    DaggerNativeSimplexIndexResolution.toLiftedNerve A.toSSet ≫ nerveMap (F ⋙ G) at h
  rw [← Category.assoc, h, Category.assoc]
  change DaggerNativeSimplexIndexResolution.toLiftedNerve A.toSSet ≫
      nerveMap (F ⋙ G) ≫ nerveMap L =
    (DaggerNativeSimplexIndexResolution.toLiftedNerve A.toSSet ≫ nerveMap F) ≫
      nerveMap (G ⋙ L)
  rw [Category.assoc]
  rfl

private theorem into_evaluation :
    intoNerveResolution C A ≫ evaluationMap C =
      SimplicialResolutionFunctor.augmentation.app A.toSSet ≫ A.ι := by
  apply NatTrans.ext
  funext q s
  change (SSet.yonedaEquiv.symm
      (A.ι.app _ (SSet.yonedaEquiv
        (ULiftHom.down.obj (first s.1)).hom))).app q s.2 =
    A.ι.app q ((ULiftHom.down.obj (first s.1)).hom.app q s.2)
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply]
  rfl

/-- The weak standard-simplex resolution of a subcomplex compares its literal
inclusion to the last vertices of the original simplices it contains. -/
def comparisonOnSubcomplex : SSet.Homotopy
    (SimplicialResolutionFunctor.augmentation.app A.toSSet ≫ A.ι)
    (SimplicialResolutionFunctor.elementsProjection.app A.toSSet ≫
      nerveMap (lastVertexOnSubcomplex C A)) :=
  ((comparison C).precomp (intoNerveResolution C A)).congr
    (into_evaluation C A) (Category.assoc _ _ _ |>.trans (into_projection C A))

end
end DaggerModels.PartII.NerveSimplexResolutionHomotopy
