import DaggerModels.Presentable
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# External tensor and evaluation for simplicial dagger simplicial sets

The ordinary simplex direction is the outer direction of Part II,
`cs.not.SS`. The external tensor and mapping simplicial set use the Mathlib
copower--coyoneda adjunction. No model structure on the diagram category
is assumed here.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

/-- The category in Part II, `cs.not.SS`. -/
abbrev ResolutionDiagram := SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}

local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- For fixed `A`, the external tensor sends `K` to the diagram of copowers by `K_k`. -/
def externalTensor (A : DaggerSSet.{u}) : SSet.{u} ⥤ ResolutionDiagram.{u} :=
  (Functor.whiskeringRight _ _ _).obj (sigmaConst.obj A)

/-- The simplicial set with `k`-simplices the morphisms from `A` to `W_k`. -/
def mappingSimplicialSet (A : DaggerSSet.{u}) : ResolutionDiagram.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringRight _ _ _).obj (coyoneda.obj (op A))

/-- Part II, `cs.lem.adjunction`: the external tensor is adjoint to the mapping functor. -/
def externalTensorAdjunction (A : DaggerSSet.{u}) :
    externalTensor A ⊣ mappingSimplicialSet A :=
  (sigmaConstAdj A).whiskerRight _

/-- The summand indexed by a simplex of the tensor parameter. -/
def externalTensorInclusion (A : DaggerSSet.{u}) (K : SSet.{u})
    (k : SimplexCategoryᵒᵖ) (x : K.obj k) :
    A ⟶ ((externalTensor A).obj K).obj k :=
  Sigma.ι (fun _ : K.obj k ↦ A) x

/-- The bijection sends a map to its restrictions to the individual summands. -/
theorem externalTensorAdjunction_homEquiv_apply
    (A : DaggerSSet.{u}) (K : SSet.{u}) (W : ResolutionDiagram.{u})
    (f : (externalTensor A).obj K ⟶ W) (k : SimplexCategoryᵒᵖ) (x : K.obj k) :
    ((externalTensorAdjunction A).homEquiv K W f).app k x =
      externalTensorInclusion A K k x ≫ f.app k := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The external tensor with a fixed simplicial set, functorial in the dagger input. -/
def externalTensorWith (K : SSet.{u}) : DaggerSSet.{u} ⥤ ResolutionDiagram.{u} :=
  sigmaConst ⋙ (Functor.whiskeringLeft _ _ _).obj K

/-- Functoriality in the dagger input acts by the same map on each summand. -/
theorem externalTensorWith_map_inclusion {A B : DaggerSSet.{u}} (f : A ⟶ B)
    (K : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : K.obj k) :
    externalTensorInclusion A K k x ≫ ((externalTensorWith K).map f).app k =
      f ≫ externalTensorInclusion B K k x := by
  simp [externalTensorWith, externalTensorInclusion, sigmaConst]

/-- Naturality in `A` of the bijection of Part II, `cs.lem.adjunction`. -/
theorem externalTensorAdjunction_natural_in_dagger {A B : DaggerSSet.{u}} (f : A ⟶ B)
    (K : SSet.{u}) (W : ResolutionDiagram.{u}) (g : (externalTensor B).obj K ⟶ W)
    (k : SimplexCategoryᵒᵖ) (x : K.obj k) :
    ((externalTensorAdjunction A).homEquiv K W ((externalTensorWith K).map f ≫ g)).app k x =
      f ≫ ((externalTensorAdjunction B).homEquiv K W g).app k x := by
  rw [externalTensorAdjunction_homEquiv_apply, externalTensorAdjunction_homEquiv_apply,
    NatTrans.comp_app, ← Category.assoc, externalTensorWith_map_inclusion, Category.assoc]

/-- Evaluation at `[k]` in the ordinary simplex direction. -/
def evaluationAt (k : ℕ) : ResolutionDiagram.{u} ⥤ DaggerSSet.{u} :=
  (evaluation _ _).obj (op ⦋k⦌)

/-- The bijection for the representable parameter `Δ[k]`. -/
def evaluationHomEquiv (k : ℕ) (A : DaggerSSet.{u}) (W : ResolutionDiagram.{u}) :
    ((externalTensorWith (Δ[k] : SSet.{u})).obj A ⟶ W) ≃
      (A ⟶ (evaluationAt k).obj W) :=
  ((externalTensorAdjunction A).homEquiv (Δ[k] : SSet.{u}) W).trans SSet.yonedaEquiv

/-- On morphisms the evaluation bijection restricts to the identity simplex. -/
theorem evaluationHomEquiv_apply (k : ℕ) (A : DaggerSSet.{u})
    (W : ResolutionDiagram.{u}) (f : (externalTensorWith (Δ[k] : SSet.{u})).obj A ⟶ W) :
    evaluationHomEquiv k A W f =
      externalTensorInclusion A (Δ[k] : SSet.{u}) (op ⦋k⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) ≫ f.app (op ⦋k⦌) :=
  externalTensorAdjunction_homEquiv_apply A _ W f _ _

/-- Part II, `cs.cor.evk`: external tensor with `Δ[k]` is left adjoint to evaluation. -/
def evaluationAdjunction (k : ℕ) :
    externalTensorWith (Δ[k] : SSet.{u}) ⊣ evaluationAt k :=
  Adjunction.mkOfHomEquiv
    { homEquiv := evaluationHomEquiv k
      homEquiv_naturality_left_symm := by
        intro A B W f g
        apply (evaluationHomEquiv k A W).injective
        rw [Equiv.apply_symm_apply, evaluationHomEquiv_apply, NatTrans.comp_app,
          ← Category.assoc]
        rw [externalTensorWith_map_inclusion, Category.assoc, ← evaluationHomEquiv_apply,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro A W V f g
        rw [evaluationHomEquiv_apply, evaluationHomEquiv_apply, NatTrans.comp_app,
          Category.assoc]
        rfl }

/-- The unique map from the ordinary simplex `k` to `[0]`. -/
def simplexCollapse (k : SimplexCategoryᵒᵖ) : k.unop ⟶ ⦋0⦌ :=
  SimplexCategory.isTerminalZero.from k.unop

@[simp] theorem simplexCollapse_zero_op :
    (simplexCollapse (op ⦋0⦌)).op = 𝟙 (op ⦋0⦌) :=
  Quiver.Hom.unop_inj (SimplexCategory.isTerminalZero.hom_ext _ _)

/-- Compatibility of the collapse with every ordinary simplicial operator. -/
theorem simplexCollapse_op_comp {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (simplexCollapse i).op ≫ f = (simplexCollapse j).op :=
  Quiver.Hom.unop_inj (SimplexCategory.isTerminalZero.hom_ext _ _)

/-- The strictly constant simplicial diagram. -/
def constantDiagram : DaggerSSet.{u} ⥤ ResolutionDiagram.{u} :=
  Functor.const _

/-- The map `ℓ_W` in Part II, `cs.thm.resolution`. -/
def resolutionCounit (W : ResolutionDiagram.{u}) :
    constantDiagram.obj ((evaluationAt 0).obj W) ⟶ W where
  app k := W.map (simplexCollapse k).op
  naturality i j f := by
    change 𝟙 _ ≫ W.map (simplexCollapse j).op =
      W.map (simplexCollapse i).op ≫ W.map f
    rw [Category.id_comp, ← W.map_comp, simplexCollapse_op_comp]

/-- The strictly constant diagram is left adjoint to evaluation at `[0]`. -/
def constantEvaluationAdjunction :
    constantDiagram.{u} ⊣ evaluationAt 0 where
  unit := 𝟙 _
  counit :=
    { app := resolutionCounit
      naturality W V f := by
        ext k
        exact (f.naturality (simplexCollapse k).op).symm }
  left_triangle_components A := by
    ext k
    change 𝟙 A ≫ 𝟙 A = 𝟙 A
    exact Category.id_comp _
  right_triangle_components W := by
    change 𝟙 _ ≫ W.map (simplexCollapse (op ⦋0⦌)).op = 𝟙 _
    rw [simplexCollapse_zero_op, W.map_id, Category.id_comp]

/-- The paper's `(-) ⊠ Δ[0]` is naturally isomorphic to the constant diagram functor. -/
def constantDiagramIsoExternalTensorZero :
    constantDiagram.{u} ≅ externalTensorWith (Δ[0] : SSet.{u}) :=
  constantEvaluationAdjunction.leftAdjointUniq (evaluationAdjunction 0)

/-- Part II, `cs.thm.resolution`: the collapse maps detect all structure maps.

The statement applies to the weak-equivalence property of the Part I model,
but does not require or assert the existence of the Part II localization.
-/
theorem resolutionCounit_levelwise_iff
    (P : MorphismProperty DaggerSSet.{u}) [P.HasTwoOutOfThreeProperty]
    (W : ResolutionDiagram.{u}) :
    (∀ k, P ((resolutionCounit W).app k)) ↔
      (∀ (i j : SimplexCategoryᵒᵖ) (f : i ⟶ j), P (W.map f)) := by
  constructor
  · intro h i j f
    apply P.of_precomp (W.map (simplexCollapse i).op) (W.map f) (h i)
    rw [← W.map_comp, simplexCollapse_op_comp]
    exact h j
  · intro h k
    exact h _ _ _

end

end DaggerModels.PartII
