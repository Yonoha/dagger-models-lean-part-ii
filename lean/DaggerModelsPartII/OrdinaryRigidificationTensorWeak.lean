import OriginalProductHomComparisonReconciledRecovered
import OriginalSimplicialPiZeroLaxMonoidal
import DaggerModelsPartII.OrdinaryDwyerKanCore
import DaggerModels.RigidificationVertices
import SSetProductGeometric
import OriginalOrdinaryMovingHomDiagramReconciled

/-!
# Product stability of a rigidified ordinary DK equivalence

The original product Hom comparison, with its actual projection equations
and endpoint transports, proves local weak preservation under tensor with
an arbitrary simplicial set. Fixed-vertex insertion transports the original
component essential-surjectivity witness. No ordinary model structure or
categorical-weak reflection theorem is assumed.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryDwyerKanCore
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalSimplicialPiZeroLaxMonoidal
open DaggerOriginalSimplicialPiZeroCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.OrdinaryRigidificationTensorWeak

noncomputable section

private theorem fst_projection_naturality
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B) :
    (K ◁ f) ≫ fst K B = fst K A := by
  ext n x
  rfl

private theorem snd_projection_naturality
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B) :
    (K ◁ f) ≫ snd K B = snd K A ≫ f := by
  ext n x
  rfl

/-- The fixed-vertex insertion is natural in the second simplicial factor.
The zero-simplex calculation is already the native
`leftVertexInclusion_zero`. -/
private theorem leftVertexInclusion_naturality
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (k : K.obj (op ⦋0⦌)) :
    leftVertexInclusion K A k ≫ K ◁ f =
      f ≫ leftVertexInclusion K B k := by
  -- Both maps send `a` to the pair of the constant simplex at `k`
  -- and `f(a)`; this is pointwise naturality of the cartesian tensor.
  ext n a
  · rfl
  · change f.app n a = f.app n a
    rfl

private theorem fst_obj_eq
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (z : (rigidification.obj (K ⊗ A)).Obj) :
    (rigidification.map (fst K B)).obj ((rigidification.map (K ◁ f)).obj z) =
      (rigidification.map (fst K A)).obj z := by
  have hfun : rigidification.map (K ◁ f) ≫ rigidification.map (fst K B) =
      rigidification.map (fst K A) := by
    rw [← rigidification.map_comp, fst_projection_naturality]
  exact congrArg (fun g : rigidification.obj (K ⊗ A) ⟶ rigidification.obj K ↦
    g.obj z) hfun

private theorem snd_obj_eq
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (z : (rigidification.obj (K ⊗ A)).Obj) :
    (rigidification.map (snd K B)).obj ((rigidification.map (K ◁ f)).obj z) =
      (rigidification.map f).obj ((rigidification.map (snd K A)).obj z) := by
  have hfun : rigidification.map (K ◁ f) ≫ rigidification.map (snd K B) =
      rigidification.map (snd K A) ≫ rigidification.map f := by
    rw [← rigidification.map_comp, ← rigidification.map_comp,
      snd_projection_naturality]
  exact congrArg (fun g : rigidification.obj (K ⊗ A) ⟶ rigidification.obj B ↦
    g.obj z) hfun

/-- The original `sigma` comparison is natural in the second factor.
After projecting to each Hom factor, the equality is functoriality of
`rigidification.map` plus `sigma_fst` and `sigma_snd`. -/
private theorem sigma_naturality_second
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (z w : (rigidification.obj (K ⊗ A)).Obj) :
    DaggerOriginalProductProjection.sigma K A z w ≫
      ((𝟙 (((rigidification.map (fst K A)).obj z) ⟶[SSet.{u}]
          ((rigidification.map (fst K A)).obj w))) ⊗ₘ
        ((rigidification.map f).map
          ((rigidification.map (snd K A)).obj z)
          ((rigidification.map (snd K A)).obj w))) =
      ((rigidification.map (K ◁ f)).map z w) ≫
        DaggerOriginalProductProjection.sigma K B
          ((rigidification.map (K ◁ f)).obj z)
          ((rigidification.map (K ◁ f)).obj w) ≫
        ((DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj K) (fst_obj_eq K f z) (fst_obj_eq K f w)) ⊗ₘ
          (DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj B) (snd_obj_eq K f z) (snd_obj_eq K f w))) := by
  -- The two projections are the original `sigma_fst` and `sigma_snd`.
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      Category.comp_id]
    rw [← Category.assoc (DaggerOriginalProductProjection.sigma K B _ _)
      (fst _ _) _, DaggerOriginalProductProjection.sigma_fst]
    have hfun : rigidification.map (K ◁ f) ≫ rigidification.map (fst K B) =
        rigidification.map (fst K A) := by
      rw [← rigidification.map_comp, fst_projection_naturality]
    rw [DaggerOriginalProductProjection.sigma_fst]
    simp only [← Category.assoc]
    rw [← SimplicialCat.comp_map]
    exact (DaggerModels.OriginalOrdinaryEndpointTransport.map_of_eq hfun z w).symm
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
    rw [← Category.assoc (DaggerOriginalProductProjection.sigma K A z w)
      (snd _ _) _, DaggerOriginalProductProjection.sigma_snd]
    rw [← Category.assoc (DaggerOriginalProductProjection.sigma K B _ _)
      (snd _ _) _, DaggerOriginalProductProjection.sigma_snd]
    have hfun : rigidification.map (K ◁ f) ≫ rigidification.map (snd K B) =
        rigidification.map (snd K A) ≫ rigidification.map f := by
      rw [← rigidification.map_comp, ← rigidification.map_comp,
        snd_projection_naturality]
    simp only [← Category.assoc]
    rw [← SimplicialCat.comp_map, ← SimplicialCat.comp_map]
    exact (DaggerModels.OriginalOrdinaryEndpointTransport.map_of_eq hfun z w).symm

/-- Actual ordinary DK weakness after tensoring the original simplicial
map with an arbitrary left factor. -/
theorem rigidification_whiskerLeft_W
    (K : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B)
    (hf : W (rigidification.map f)) :
    W (rigidification.map (K ◁ f)) := by
  constructor
  · apply (localGeometric_iff_native _).2
    intro z w
    let hK : SSet.{u} :=
      ((rigidification.map (fst K A)).obj z) ⟶[SSet.{u}]
        ((rigidification.map (fst K A)).obj w)
    let hA : SSet.{u} :=
      ((rigidification.map (snd K A)).obj z) ⟶[SSet.{u}]
        ((rigidification.map (snd K A)).obj w)
    let hB : SSet.{u} :=
      ((rigidification.map f).obj ((rigidification.map (snd K A)).obj z))
        ⟶[SSet.{u}]
      ((rigidification.map f).obj ((rigidification.map (snd K A)).obj w))
    let hmap : hA ⟶ hB :=
      (rigidification.map f).map
        ((rigidification.map (snd K A)).obj z)
        ((rigidification.map (snd K A)).obj w)
    have hwmap : WeakEquivalence hmap :=
      (localGeometric_iff_native (rigidification.map f)).1 hf.1 _ _
    have hσA : WeakEquivalence (DaggerOriginalProductProjection.sigma K A z w) :=
      (DaggerSSetGluing.weakEquivalence_iff_GW _).2
        (DaggerOriginalProductProjection.sigma_GW K A z w)
    have hσB : WeakEquivalence (DaggerOriginalProductProjection.sigma K B
        ((rigidification.map (K ◁ f)).obj z)
        ((rigidification.map (K ◁ f)).obj w)) :=
      (DaggerSSetGluing.weakEquivalence_iff_GW _).2
        (DaggerOriginalProductProjection.sigma_GW K B _ _)
    have hprod : WeakEquivalence ((𝟙 hK) ⊗ₘ hmap) :=
      (DaggerSSetGluing.weakEquivalence_iff_GW _).2
        (DaggerSSetProductGeometric.tensorMap_geometric
          (𝟙 hK) hmap
          (DaggerSSetProductGeometric.identity_geometric hK)
          ((DaggerSSetGluing.weakEquivalence_iff_GW _).1 hwmap))
    have hcomp : WeakEquivalence
        (DaggerOriginalProductProjection.sigma K A z w ≫
          ((𝟙 hK) ⊗ₘ hmap)) := by
      infer_instance
    have htransport : WeakEquivalence
        ((DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj K) (fst_obj_eq K f z) (fst_obj_eq K f w)) ⊗ₘ
          (DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj B) (snd_obj_eq K f z) (snd_obj_eq K f w))) := by
      have hfirst : WeakEquivalence
          (DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj K) (fst_obj_eq K f z) (fst_obj_eq K f w)) := by
        unfold DaggerModels.OriginalOrdinaryEndpointTransport.transport
        infer_instance
      have hsecond : WeakEquivalence
          (DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj B) (snd_obj_eq K f z) (snd_obj_eq K f w)) := by
        unfold DaggerModels.OriginalOrdinaryEndpointTransport.transport
        infer_instance
      exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
        (DaggerSSetProductGeometric.tensorMap_geometric _ _
          ((DaggerSSetGluing.weakEquivalence_iff_GW _).1 hfirst)
          ((DaggerSSetGluing.weakEquivalence_iff_GW _).1 hsecond))
    have hpost : WeakEquivalence
        (DaggerOriginalProductProjection.sigma K B
          ((rigidification.map (K ◁ f)).obj z)
          ((rigidification.map (K ◁ f)).obj w) ≫
          ((DaggerModels.OriginalOrdinaryEndpointTransport.transport
              (rigidification.obj K) (fst_obj_eq K f z) (fst_obj_eq K f w)) ⊗ₘ
            (DaggerModels.OriginalOrdinaryEndpointTransport.transport
              (rigidification.obj B) (snd_obj_eq K f z) (snd_obj_eq K f w)))) := by
      infer_instance
    have heq := sigma_naturality_second K f z w
    rw [heq] at hcomp
    exact weakEquivalence_of_postcomp
      ((rigidification.map (K ◁ f)).map z w)
      (DaggerOriginalProductProjection.sigma K B
        ((rigidification.map (K ◁ f)).obj z)
        ((rigidification.map (K ◁ f)).obj w) ≫
        ((DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj K) (fst_obj_eq K f z) (fst_obj_eq K f w)) ⊗ₘ
          (DaggerModels.OriginalOrdinaryEndpointTransport.transport
            (rigidification.obj B) (snd_obj_eq K f z) (snd_obj_eq K f w))))
  · constructor
    intro q
    let v := (vertexEquiv (K ⊗ B)).symm q
    let k : K.obj (op ⦋0⦌) := v.1
    let b : B.obj (op ⦋0⦌) := v.2
    obtain ⟨a, ⟨e⟩⟩ := hf.2.mem_essImage (vertexEquiv B b)
    let a₀ : A.obj (op ⦋0⦌) := (vertexEquiv A).symm a
    let src : (rigidification.obj (K ⊗ A)).Obj := vertexEquiv (K ⊗ A) (k, a₀)
    let incA : A ⟶ K ⊗ A := leftVertexInclusion K A k
    let incB : B ⟶ K ⊗ B := leftVertexInclusion K B k
    have hsrc₀ : (rigidification.map incA).obj a = src := by
      have ha : vertexEquiv A a₀ = a := (vertexEquiv A).apply_symm_apply a
      rw [← ha]
      simpa only [src, incA, leftVertexInclusion_zero] using
        vertexEquiv_naturality incA a₀
    have hfun : rigidification.map incA ≫ rigidification.map (K ◁ f) =
        rigidification.map f ≫ rigidification.map incB := by
      rw [← rigidification.map_comp, ← rigidification.map_comp,
        leftVertexInclusion_naturality]
    have hsrc :
        (componentFunctor (rigidification.map (K ◁ f))).obj src =
          (componentFunctor (rigidification.map incB)).obj
            ((componentFunctor (rigidification.map f)).obj a) := by
      change (rigidification.map (K ◁ f)).obj src =
        (rigidification.map incB).obj ((rigidification.map f).obj a)
      rw [← hsrc₀]
      exact congrArg (fun g : rigidification.obj A ⟶ rigidification.obj (K ⊗ B) ↦
        g.obj a) hfun
    have hq :
        (componentFunctor (rigidification.map incB)).obj (vertexEquiv B b) = q := by
      change (rigidification.map incB).obj (vertexEquiv B b) = q
      have hv₀ : incB.app (op ⦋0⦌) b = v := by
        change (leftVertexInclusion K B k).app (op ⦋0⦌) b = v
        rw [leftVertexInclusion_zero]
        change (v.1, v.2) = v
        cases v
        rfl
      have hv : vertexEquiv (K ⊗ B) v = q :=
        (vertexEquiv (K ⊗ B)).apply_symm_apply q
      have hn := vertexEquiv_naturality incB b
      rw [hv₀] at hn
      exact hn.trans hv
    exact ⟨src, ⟨eqToIso hsrc ≪≫
      (componentFunctor (rigidification.map incB)).mapIso e ≪≫ eqToIso hq⟩⟩

end

end DaggerModels.PartII.OrdinaryRigidificationTensorWeak
