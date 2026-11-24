import DaggerModelsPartII.JTParameterReversal
import DaggerModelsPartII.JTSimplexReversal
import DaggerModelsPartII.JTRealizationGenerators
import DaggerModelsPartII.JTRealizationVertices

/-!
# Dagger on the actual Joyal--Tierney realization

The underlying functor is the previously fixed ordinary realization applied
to the literal restriction of a reversal simplicial space. Its colimit
universal property implements the manuscript's formula on generators.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.DaggerJTRealization

open SegalLocalizers OrdinaryJTRealization JTReversalInput JTReversalIndex
open JTParameterReversal JTSimplexReversal JTRealizationGenerators

noncomputable section

/-- Keep the actual ordinary realization as the underlying simplicial set. -/
def underlyingRealization : ReverseDaggerSpace.{0} ⥤ SSet.{0} :=
  ordinaryInput ⋙ realization

/-- The reversed leg sends the represented element through horizontal reversal. -/
def reversalLeg (W : ReverseDaggerSpace.{0})
    (σ : SimplexIndex (ordinaryInput.obj W)) :
    tFunctor.obj σ.left ⟶ (underlyingRealization.obj W).op :=
  tReversalIso.hom.app σ.left ≫ SSet.opFunctor.map
    (generator (ordinaryInput.obj W) (indexReversal.obj σ.left)
      ((horizontalIso W).hom.app (op σ.left) (uliftYonedaEquiv.{0} σ.hom)))

/-- The reversed legs obey the literal coend relation. -/
def reversalCocone (W : ReverseDaggerSpace.{0}) :
    Cocone (simplexDiagram (ordinaryInput.obj W)) where
  pt := (underlyingRealization.obj W).op
  ι := {
    app := reversalLeg W
    naturality := by
      intro σ τ f
      change tFunctor.map f.left ≫ reversalLeg W τ = reversalLeg W σ
      have hw : uliftYonedaEquiv.{0} σ.hom =
          (ordinaryInput.obj W).map f.left.op (uliftYonedaEquiv.{0} τ.hom) :=
        ((uliftYonedaEquiv_naturality τ.hom f.left.op).trans
          (congrArg uliftYonedaEquiv.{0} (CostructuredArrow.w f))).symm
      have hc : (horizontalIso W).hom.app (op σ.left) (uliftYonedaEquiv.{0} σ.hom) =
          (ordinaryInput.obj W).map (indexReversal.map f.left).op
            ((horizontalIso W).hom.app (op τ.left) (uliftYonedaEquiv.{0} τ.hom)) := by
        exact (congrArg ((horizontalIso W).hom.app (op σ.left)) hw).trans
          (congrFun ((horizontalIso W).hom.naturality f.left.op)
            (uliftYonedaEquiv.{0} τ.hom))
      have ht : tFunctor.map f.left ≫ tReversalIso.hom.app τ.left =
          tReversalIso.hom.app σ.left ≫
            SSet.opFunctor.map (tFunctor.map (indexReversal.map f.left)) :=
        tReversalIso.hom.naturality f.left
      unfold reversalLeg
      rw [← Category.assoc, ht, Category.assoc, ← SSet.opFunctor.map_comp,
        generator_relation, ← hc] }

/-- The actual coend-induced simplicial reversal, without replacing the underlying object. -/
def toOpposite (W : ReverseDaggerSpace.{0}) :
    underlyingRealization.obj W ⟶ (underlyingRealization.obj W).op :=
  (simplexCoconeIsColimit (ordinaryInput.obj W)).desc (reversalCocone W)

/-- The induced map has exactly the prescribed formula on coend generators. -/
theorem generator_toOpposite (W : ReverseDaggerSpace.{0})
    (p : Index) (w : (ordinaryInput.obj W).obj (op p)) :
    generator (ordinaryInput.obj W) p w ≫ toOpposite W =
      tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj W) (indexReversal.obj p)
          ((horizontalIso W).hom.app (op p) w)) := by
  have h := (simplexCoconeIsColimit (ordinaryInput.obj W)).fac (reversalCocone W)
    (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w))
  change generator (ordinaryInput.obj W) p w ≫ toOpposite W =
    tReversalIso.hom.app p ≫ SSet.opFunctor.map
      (generator (ordinaryInput.obj W) (indexReversal.obj p)
        ((horizontalIso W).hom.app (op p)
          (uliftYonedaEquiv.{0} (uliftYonedaEquiv.{0}.symm w)))) at h
  simpa only [Equiv.apply_symm_apply] using h

private theorem generator_hom_ext (W : BiPresheaf) {X : SSet.{0}}
    {f g : realization.obj W ⟶ X}
    (h : ∀ (p : Index) (w : W.obj (op p)), generator W p w ≫ f = generator W p w ≫ g) :
    f = g := by
  apply (simplexCoconeIsColimit W).hom_ext
  intro σ
  simpa only [simplexCocone_leg, generator, Equiv.symm_apply_apply] using
    h σ.left (uliftYonedaEquiv.{0} σ.hom)



/-- The manuscript's formula on an arbitrary actual coend generator. -/
theorem toOpposite_generator_app (W : ReverseDaggerSpace.{0})
    (m k n : SimplexCategory) (w : (ordinaryInput.obj W).obj (op (m, k)))
    (α : (SSet.stdSimplex.obj m).obj (op n))
    (ξ : (GroupoidSimplex.parameter.obj k).obj (op n)) :
    SSet.opObjEquiv ((toOpposite W).app (op n)
      ((generator (ordinaryInput.obj W) (m, k) w).app (op n) (α, ξ))) =
      (generator (ordinaryInput.obj W) (m, k)
        (JTRealizationVertices.horizontalReversalCoefficient W m k w)).app (op n)
        (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α)),
          (GroupoidSimplexReversal.daggerParameter.obj k).daggerSimplex (n := n.len) ξ) := by
  have h := congrFun (NatTrans.congr_app
    (generator_toOpposite W (m, k) w) (op n)) (α, ξ)
  change (toOpposite W).app (op n)
      ((generator (ordinaryInput.obj W) (m, k) w).app (op n) (α, ξ)) =
    (generator (ordinaryInput.obj W) (m, k)
      ((horizontalIso W).hom.app (op (m, k)) w)).app (op n)
      (SSet.opObjEquiv ((tReversalIso.hom.app (m, k)).app (op n) (α, ξ))) at h
  have ht := tReversal_app (m, k) n α ξ
  have hg := congrArg
    (fun s : (tFunctor.obj (m, k)).obj (op n) ↦
      (generator (ordinaryInput.obj W) (m, k)
        ((horizontalIso W).hom.app (op (m, k)) w)).app (op n) s) ht
  simpa only [horizontalIso_hom_app,
    JTRealizationVertices.horizontalReversalCoefficient, parameter_underlying] using h.trans hg


/-- The actual realization reversal squares to the canonical double-opposite map. -/
theorem toOpposite_twice (W : ReverseDaggerSpace.{0}) :
    toOpposite W ≫ SSet.opFunctor.map (toOpposite W) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W) =
        𝟙 (underlyingRealization.obj W) := by
  apply generator_hom_ext (ordinaryInput.obj W)
  intro p w
  have hh := horizontal_twice W p.1 p.2 w
  calc
    _ = (generator (ordinaryInput.obj W) p w ≫ toOpposite W) ≫
        SSet.opFunctor.map (toOpposite W) ≫
          SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W) := by
      simp only [Category.assoc]
    _ = tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj W) (indexReversal.obj p)
          ((horizontalIso W).hom.app (op p) w) ≫ toOpposite W) ≫
          SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W) := by
      rw [Functor.map_comp, generator_toOpposite]
      simp only [Category.assoc]
    _ = tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (tReversalIso.hom.app (indexReversal.obj p) ≫ SSet.opFunctor.map
          (generator (ordinaryInput.obj W) p w)) ≫
          SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W) := by
      rw [generator_toOpposite]
      exact congrArg (fun x : (ordinaryInput.obj W).obj (op p) ↦
        tReversalIso.hom.app p ≫ SSet.opFunctor.map
          (tReversalIso.hom.app (indexReversal.obj p) ≫ SSet.opFunctor.map
            (generator (ordinaryInput.obj W) p x)) ≫
          SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W)) hh
    _ = (tReversalIso.hom.app p ≫
          SSet.opFunctor.map (tReversalIso.hom.app (indexReversal.obj p))) ≫
        (SSet.opFunctor.map (SSet.opFunctor.map
          (generator (ordinaryInput.obj W) p w)) ≫
            SSet.opFunctorCompOpFunctorIso.hom.app (underlyingRealization.obj W)) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (tReversalIso.hom.app p ≫
          SSet.opFunctor.map (tReversalIso.hom.app (indexReversal.obj p))) ≫
        (SSet.opFunctorCompOpFunctorIso.hom.app (tFunctor.obj p) ≫
          generator (ordinaryInput.obj W) p w) := by
      exact congrArg (fun h ↦ (tReversalIso.hom.app p ≫
        SSet.opFunctor.map (tReversalIso.hom.app (indexReversal.obj p))) ≫ h)
          (SSet.opFunctorCompOpFunctorIso.hom.naturality
            (generator (ordinaryInput.obj W) p w))
    _ = _ := by
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun h ↦ h ≫ generator (ordinaryInput.obj W) p w)
          (tReversal_twice p)

/-- Reversal commutes with the actual realization of every input morphism. -/
theorem toOpposite_naturality {W V : ReverseDaggerSpace.{0}} (f : W ⟶ V) :
    underlyingRealization.map f ≫ toOpposite V =
      toOpposite W ≫ SSet.opFunctor.map (underlyingRealization.map f) := by
  apply generator_hom_ext (ordinaryInput.obj W)
  intro p w
  change generator (ordinaryInput.obj W) p w ≫
      (realization.map (ordinaryInput.map f) ≫ toOpposite V) =
    generator (ordinaryInput.obj W) p w ≫
      (toOpposite W ≫ SSet.opFunctor.map (realization.map (ordinaryInput.map f)))
  calc
    _ = generator (ordinaryInput.obj V) p
        ((ordinaryInput.map f).app (op p) w) ≫ toOpposite V := by
      rw [← Category.assoc, generator_naturality]
    _ = tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj V) p
          ((horizontalIso V).hom.app (op p)
            ((ordinaryInput.map f).app (op p) w))) :=
      generator_toOpposite V p ((ordinaryInput.map f).app (op p) w)
    _ = tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj V) p
          ((ordinaryInput.map f).app (op p)
            ((horizontalIso W).hom.app (op p) w))) :=
      congrArg (fun x ↦ tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj V) p x))
          (horizontal_naturality_input f p.1 p.2 w)
    _ = tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj W) p ((horizontalIso W).hom.app (op p) w) ≫
          realization.map (ordinaryInput.map f)) := by
      rw [generator_naturality]
    _ = (tReversalIso.hom.app p ≫ SSet.opFunctor.map
        (generator (ordinaryInput.obj W) p ((horizontalIso W).hom.app (op p) w))) ≫
          SSet.opFunctor.map (realization.map (ordinaryInput.map f)) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (generator (ordinaryInput.obj W) p w ≫ toOpposite W) ≫
          SSet.opFunctor.map (realization.map (ordinaryInput.map f)) :=
      congrArg (fun h ↦ h ≫ SSet.opFunctor.map (realization.map (ordinaryInput.map f)))
        (generator_toOpposite W p w).symm
    _ = _ := Category.assoc _ _ _



/-- The horizontal coend relation fixes every vertex of the actual realization. -/
theorem toOpposite_fixedVertices (W : ReverseDaggerSpace.{0})
    (x : (underlyingRealization.obj W).obj (op ⦋0⦌)) :
    SSet.opObjEquiv ((toOpposite W).app (op ⦋0⦌) x) = x := by
  obtain ⟨⟨m, k⟩, w, ⟨α, ξ⟩, hx⟩ :=
    exists_generator (ordinaryInput.obj W) (op ⦋0⦌) x
  rw [← hx]
  calc
    _ = (generator (ordinaryInput.obj W) (m, k)
        (JTRealizationVertices.horizontalReversalCoefficient W m k w)).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv α)),
          (GroupoidSimplexReversal.daggerParameter.obj k).daggerSimplex (n := 0) ξ) :=
      toOpposite_generator_app W m k ⦋0⦌ w α ξ
    _ = _ := by
      simpa only [DaggerSSet.daggerSimplex, Equiv.symm_apply_apply] using
        JTRealizationVertices.reversed_generator_vertex W m k
          (SSet.stdSimplex.objEquiv α) ξ w

/-- The actual ordinary realization, with the coend dagger constructed above. -/
def daggerObject (W : ReverseDaggerSpace.{0}) : DaggerSSet.{0} where
  toSSet := underlyingRealization.obj W
  dagger := toOpposite W
  involutive n x := by
    exact congrFun (NatTrans.congr_app (toOpposite_twice W) (op ⦋n⦌)) x
  fixedVertices := toOpposite_fixedVertices W

/-- The manuscript's dagger realization, retaining the fixed ordinary underlying functor. -/
def daggerRealization : ReverseDaggerSpace.{0} ⥤ DaggerSSet.{0} where
  obj := daggerObject
  map f := { hom := underlyingRealization.map f, comm := toOpposite_naturality f }
  map_id W := by
    apply DaggerSSet.Hom.ext
    exact underlyingRealization.map_id W
  map_comp f g := by
    apply DaggerSSet.Hom.ext
    exact underlyingRealization.map_comp f g

/-- Forgetting the dagger gives literally the original ordinary JT realization. -/
theorem daggerRealization_underlying :
    daggerRealization ⋙ DaggerSSet.forget = ordinaryInput ⋙ realization := rfl


end

end DaggerModels.PartII.DaggerJTRealization
