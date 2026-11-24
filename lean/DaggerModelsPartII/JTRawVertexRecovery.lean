import DaggerModelsPartII.JTRealizationGraphGenerator
import DaggerModelsPartII.JTParameterVertexKan

/-!
# Recovering the original zero row from the vertices of JT realization
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTRawVertexRecovery

open OrdinaryJTRealization JTRealizationGenerators GroupoidSimplex
open JTGtildeOrderedFiberAction (zeroTensorVertex)
open JTCylinderCEComparison (simplexUnit)

noncomputable section

private abbrev zeroIndex : Index := (⦋0⦌, ⦋0⦌)
private abbrev zeroDegree := op (⦋0⦌ : SimplexCategory)

private def baseVertex : (tFunctor.obj zeroIndex).obj zeroDegree :=
  SSet.yonedaEquiv zeroTensorVertex

/-- The vertex of the original box selected by the two operators out of zero. -/
def boxVertex {p : Index} (a : zeroIndex ⟶ p) : (tFunctor.obj p).obj zeroDegree :=
  (tFunctor.map a).app zeroDegree baseVertex

theorem boxVertex_formula {p : Index} (a : zeroIndex ⟶ p) :
    boxVertex a =
      (SSet.stdSimplex.objEquiv.symm a.1,
        SSet.yonedaEquiv (SSet.stdSimplex.map a.2 ≫ simplexUnit.app p.2)) := by
  have hz : zeroTensorVertex =
      lift (𝟙 (Δ[0] : SSet.{0})) (simplexUnit.app ⦋0⦌) := by
    unfold zeroTensorVertex
    rw [JTParameterZero.parameterZeroIsTerminal.hom_ext
      JTParameterZero.parameterZeroIso.inv (simplexUnit.app ⦋0⦌)]
  have h := SSet.yonedaEquiv_comp zeroTensorVertex (tFunctor.map a)
  change SSet.yonedaEquiv (zeroTensorVertex ≫ tFunctor.map a) = boxVertex a at h
  rw [← h]
  change SSet.yonedaEquiv (zeroTensorVertex ≫
    (SSet.stdSimplex.map a.1 ⊗ₘ parameter.map a.2)) = _
  rw [hz]
  have hh : lift (𝟙 (Δ[0] : SSet.{0})) (simplexUnit.app ⦋0⦌) ≫
      (SSet.stdSimplex.map a.1 ⊗ₘ parameter.map a.2) =
        lift (SSet.stdSimplex.map a.1) (SSet.stdSimplex.map a.2 ≫ simplexUnit.app p.2) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst, Category.id_comp,
        lift_fst]
    · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd,
        lift_snd, simplexUnit.naturality]
  rw [hh]
  change (SSet.yonedaEquiv (SSet.stdSimplex.map a.1),
    SSet.yonedaEquiv (SSet.stdSimplex.map a.2 ≫ simplexUnit.app p.2)) = _
  rw [SSet.stdSimplex.yonedaEquiv_map]

/-- The object of the completed simplex selected by a parameter vertex. -/
def parameterIndex (k : SimplexCategory) (u : (Δ[0] : SSet.{0}) ⟶ parameter.obj k) :
    Fin (k.len + 1) := ((SSet.yonedaEquiv u).obj 0).as.as

theorem parameterIndex_vertex (k : SimplexCategory)
    (u : (Δ[0] : SSet.{0}) ⟶ parameter.obj k) :
    u = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k (parameterIndex k u)) ≫
      simplexUnit.app k := by
  letI : Quiver.IsThin (completion k) :=
    DaggerOriginalInitialCategoryCompletionThin.completionIsThin
      (0 : Fin (k.len + 1)) (Fin.isInitialZero _)
  apply SSet.yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  have hi : i = 0 := @Subsingleton.elim (Fin 1) inferInstance i 0
  subst i
  rfl

private def vertexOperator {p : Index} (b : (tFunctor.obj p).obj zeroDegree) :
    zeroIndex ⟶ p :=
  (SSet.stdSimplex.objEquiv b.1, SimplexCategory.const ⦋0⦌ p.2 (b.2.obj 0).as.as)

private theorem vertexOperator_boxVertex {p : Index} (a : zeroIndex ⟶ p) :
    vertexOperator (boxVertex a) = a := by
  rw [boxVertex_formula]
  apply Prod.ext
  · exact Equiv.apply_symm_apply _ _
  · change SimplexCategory.const ⦋0⦌ p.2 (a.2.toOrderHom 0) = a.2
    ext i
    have hi : i = 0 := @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl

private theorem boxVertex_vertexOperator {p : Index}
    (b : (tFunctor.obj p).obj zeroDegree) : boxVertex (vertexOperator b) = b := by
  rw [boxVertex_formula]
  apply Prod.ext
  · exact Equiv.symm_apply_apply _ _
  · letI : Quiver.IsThin (completion p.2) :=
      DaggerOriginalInitialCategoryCompletionThin.completionIsThin
        (0 : Fin (p.2.len + 1)) (Fin.isInitialZero _)
    apply nerve.ext_of_isThin
    funext i
    have hi : i = 0 := @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl

private theorem vertexOperator_natural {p q : Index} (a : p ⟶ q)
    (b : (tFunctor.obj p).obj zeroDegree) :
    vertexOperator ((tFunctor.map a).app zeroDegree b) = vertexOperator b ≫ a := by
  have h : boxVertex (vertexOperator b ≫ a) = (tFunctor.map a).app zeroDegree b := by
    unfold boxVertex
    rw [tFunctor.map_comp]
    change (tFunctor.map a).app zeroDegree (boxVertex (vertexOperator b)) = _
    rw [boxVertex_vertexOperator]
  rw [← h, vertexOperator_boxVertex]

private abbrev evalZero : SSet.{0} ⥤ Type := (evaluation _ _).obj zeroDegree

private def vertexCocone (W : BiPresheaf) :
    Cocone (simplexDiagram W ⋙ evalZero) where
  pt := W.obj (op zeroIndex)
  ι :=
    { app σ := ↾fun b ↦ W.map (vertexOperator b).op (uliftYonedaEquiv.{0} σ.hom)
      naturality := by
        intro σ τ f
        funext b
        change W.map (vertexOperator ((tFunctor.map f.left).app zeroDegree b)).op
            (uliftYonedaEquiv.{0} τ.hom) =
          W.map (vertexOperator b).op (uliftYonedaEquiv.{0} σ.hom)
        rw [vertexOperator_natural, op_comp, W.map_comp]
        change W.map (vertexOperator b).op (W.map f.left.op (uliftYonedaEquiv.{0} τ.hom)) = _
        rw [uliftYonedaEquiv_naturality]
        change W.map (vertexOperator b).op
            (uliftYonedaEquiv.{0} (uliftYoneda.map f.left ≫ τ.hom)) = _
        rw [CostructuredArrow.w f] }

/-- Read the original coefficient vertex, by descent over the actual realization. -/
def recover (W : BiPresheaf) : (realization.obj W).obj zeroDegree ⟶ W.obj (op zeroIndex) :=
  (isColimitOfPreserves evalZero (simplexCoconeIsColimit W)).desc (vertexCocone W)

theorem recover_generator (W : BiPresheaf) (p : Index) (w : W.obj (op p))
    (a : zeroIndex ⟶ p) :
    recover W ((generator W p w).app zeroDegree (boxVertex a)) = W.map a.op w := by
  have h := congrFun ((isColimitOfPreserves evalZero (simplexCoconeIsColimit W)).fac
    (vertexCocone W) (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w))) (boxVertex a)
  change recover W ((generator W p w).app zeroDegree (boxVertex a)) =
    W.map (vertexOperator (boxVertex a)).op (uliftYonedaEquiv.{0}
      (uliftYonedaEquiv.{0}.symm w)) at h
  simpa only [vertexOperator_boxVertex, Equiv.apply_symm_apply] using h

/-- The actual raw zero generator, with the original section. -/
def zeroVertex (W : BiPresheaf) (w : W.obj (op zeroIndex)) :
    (realization.obj W).obj zeroDegree :=
  SSet.yonedaEquiv (zeroTensorVertex ≫ generator W zeroIndex w)

theorem recover_zeroVertex (W : BiPresheaf) (w : W.obj (op zeroIndex)) :
    recover W (zeroVertex W w) = w := by
  have h := recover_generator W zeroIndex w (𝟙 zeroIndex)
  simpa only [zeroVertex, SSet.yonedaEquiv_comp, baseVertex, boxVertex,
    tFunctor.map_id, NatTrans.id_app, types_id_apply, op_id, W.map_id] using h

theorem generator_vertex (W : BiPresheaf) (p : Index) (w : W.obj (op p))
    (a : zeroIndex ⟶ p) :
    (generator W p w).app zeroDegree (boxVertex a) = zeroVertex W (W.map a.op w) := by
  have h := congrArg (fun q : tFunctor.obj zeroIndex ⟶ realization.obj W ↦
    q.app zeroDegree baseVertex) (generator_relation W a w)
  simpa only [zeroVertex, SSet.yonedaEquiv_comp, baseVertex, boxVertex] using h

theorem zeroVertex_recover (W : BiPresheaf) (b : (realization.obj W).obj zeroDegree) :
    zeroVertex W (recover W b) = b := by
  obtain ⟨p, w, s, hs⟩ := exists_generator W zeroDegree b
  rw [← hs, ← boxVertex_vertexOperator s, recover_generator, generator_vertex]

/-- The literal realization vertices identify with the original zero row. -/
def zeroVertexEquiv (W : BiPresheaf) :
    W.obj (op zeroIndex) ≃ (realization.obj W).obj zeroDegree :=
  ⟨zeroVertex W, recover W, recover_zeroVertex W, zeroVertex_recover W⟩

theorem rawZeroGeneratorVertex_injective (W : SegalLocalizers.ReverseDaggerSpace.{0}) :
    Function.Injective (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W) :=
  (zeroVertexEquiv (JTReversalInput.ordinaryInput.obj W)).injective

end

end DaggerModels.PartII.JTRawVertexRecovery
