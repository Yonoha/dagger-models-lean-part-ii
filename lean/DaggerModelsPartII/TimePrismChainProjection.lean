import DaggerModelsPartII.TimePrismChainDiagram
import DaggerModelsPartII.TimePrismChainRelative
import DaggerModelsPartII.TotalElementsWeakComparison
import NativeDualTheoremA

/-! Identify the literal comma categories governing the moving-chain projection. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TimePrismChainProjection

open TimePrismChain (Chain)
open TimePrismChainDiagram (Index base Hom imageVertex imageVertex_id hom_ext)

noncomputable section

variable {I : Type} [SmallCategory I]
variable (K N : I ⥤ SimplexCategory) (q : I)

private abbrev Fiber := Chain (K.obj q).len (N.obj q).len
private abbrev Comma := CostructuredArrow (base K N) q

/-- Embed the entire chain fiber over the identity of the fixed base object. -/
def inFiber : Fiber K N q ⥤ Comma K N q where
  obj C := CostructuredArrow.mk (Y := (⟨q, C⟩ : Index K N)) (𝟙 q)
  map {C D} f := by
    let a : (⟨q, C⟩ : Index K N) ⟶ ⟨q, D⟩ :=
      ⟨𝟙 q, fun v hv ↦ (imageVertex_id K N q v).symm ▸ leOfHom f hv⟩
    exact CostructuredArrow.homMk a (Category.id_comp (𝟙 q))
  map_id C := by
    apply CostructuredArrow.hom_ext
    apply hom_ext K N
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply hom_ext K N
    exact (Category.id_comp (𝟙 q)).symm

variable (U : Comma K N q)

/-- All complete chains containing the image of the original source chain. -/
abbrev Relative :=
  {C : Fiber K N q // Set.MapsTo (imageVertex K N U.hom) U.left.chain.vertices C.vertices}

private def toFiber (C : Relative K N q U) : U ⟶ (inFiber K N q).obj C.val := by
  let f : U.left ⟶ (⟨q, C.val⟩ : Index K N) := ⟨U.hom, C.property⟩
  exact CostructuredArrow.homMk f (Category.comp_id U.hom)

/-- The literal inclusion of prescribed-chain extensions in the under-category. -/
def relativeFunctor : Relative K N q U ⥤ StructuredArrow U (inFiber K N q) where
  obj C := StructuredArrow.mk (toFiber K N q U C)
  map f := StructuredArrow.homMk (homOfLE (leOfHom f)) (by
    apply CostructuredArrow.hom_ext
    apply hom_ext K N
    exact Category.comp_id U.hom)
  map_id C := by
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim
  map_comp f g := by
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim

private theorem under_left (P : StructuredArrow U (inFiber K N q)) :
    P.hom.left.base = U.hom := by
  have h := CostructuredArrow.w P.hom
  change P.hom.left.base ≫ 𝟙 q = U.hom at h
  exact (Category.comp_id _).symm.trans h

private def fromUnder (P : StructuredArrow U (inFiber K N q)) : Relative K N q U :=
  ⟨P.right, by
    rw [← under_left K N q U P]
    exact P.hom.left.mapsTo⟩

private theorem relative_eq (P : StructuredArrow U (inFiber K N q)) :
    (relativeFunctor K N q U).obj (fromUnder K N q U P) = P := by
  refine StructuredArrow.obj_ext _ _ rfl ?_
  rw [eqToHom_refl, (inFiber K N q).map_id, Category.comp_id]
  apply CostructuredArrow.hom_ext
  apply hom_ext K N
  exact (under_left K N q U P).symm

local instance : (relativeFunctor K N q U).Full where
  map_surjective f := ⟨homOfLE (leOfHom f.right), by
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim⟩

local instance : (relativeFunctor K N q U).Faithful where
  map_injective _ := Subsingleton.elim _ _

local instance : (relativeFunctor K N q U).EssSurj :=
  ⟨fun p ↦ ⟨fromUnder K N q U p, ⟨eqToIso (relative_eq K N q U p)⟩⟩⟩

local instance : (relativeFunctor K N q U).IsEquivalence where

/-- The exact under-category is equivalent to the relative poset of chain extensions. -/
def relativeEquivalence : Relative K N q U ≌ StructuredArrow U (inFiber K N q) :=
  (relativeFunctor K N q U).asEquivalence

end

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

/-- Contractible relative chain extensions suffice for weakness of the
whole projection, including arrows with non-surjective coefficient operators. -/
theorem projection_weak_of {I : Type} [SmallCategory I] (K N : I ⥤ SimplexCategory)
    (h : ∀ (q : I) (U : CostructuredArrow (base K N) q),
      GW (pointMap (nerve (Relative K N q U)))) :
    WeakEquivalence (nerveMap (base K N)) := by
  apply (weakEquivalence_iff_GW _).mpr
  apply DaggerNerveTheoremA.nerveMap_GW
  intro q
  let j := inFiber K N q
  have hj : GW (nerveMap j) := DaggerNativeDualTheoremA.nerveMap_GW j (fun P ↦ by
    let i := (relativeEquivalence K N q P).functor
    letI : WeakEquivalence (nerveMap i) :=
      DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence i
    apply (weakEquivalence_iff_GW _).mp
    apply (weakEquivalence_precomp_iff (nerveMap i) _).mp
    rw [pointIsTerminal.hom_ext (nerveMap i ≫ pointMap _) (pointMap _)]
    exact (weakEquivalence_iff_GW _).mpr (h q P))
  letI : WeakEquivalence (nerveMap j) := (weakEquivalence_iff_GW _).mpr hj
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (nerveMap j) _).mp
  rw [pointIsTerminal.hom_ext (nerveMap j ≫ pointMap _) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr (TimePrismChain.point_GW _ _)

noncomputable section

variable {I : Type} [SmallCategory I] (K N : I ⥤ SimplexCategory) (q : I)
variable (U : CostructuredArrow (base K N) q)

private abbrev image := imageVertex K N U.hom '' U.left.chain.vertices

private def relativeOrderIso : Relative K N q U ≃o
    TimePrismChainRelative.Chain (K.obj q).len (N.obj q).len
      (image K N q U) (Fin.last (N.obj q).len) where
  toFun C := ⟨C.val, Set.image_subset_iff.mpr C.property, fun _ _ ↦ Fin.le_last _⟩
  invFun C := ⟨C.toChain, Set.image_subset_iff.mp C.contains⟩
  left_inv C := by cases C; rfl
  right_inv C := by cases C; rfl
  map_rel_iff' := Iff.rfl

private theorem image_chain : IsChain (· ≤ ·) (image K N q U) :=
  IsChain.image (· ≤ ·) (· ≤ ·) (imageVertex K N U.hom)
    (by
      intro a b h
      exact ⟨(K.map U.hom).toOrderHom.monotone h.1,
        (N.map U.hom).toOrderHom.monotone h.2⟩)
    U.left.chain.chain

private theorem relative_point_GW : GW (pointMap (nerve (Relative K N q U))) := by
  let i := (relativeOrderIso K N q U).equivalence.functor
  letI : WeakEquivalence (nerveMap i) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence i
  have h : GW (pointMap (nerve
      (TimePrismChainRelative.Chain (K.obj q).len (N.obj q).len
        (image K N q U) (Fin.last (N.obj q).len)))) :=
    TimePrismChainRelative.point_GW _ _ _ _ (image_chain K N q U) (fun _ _ ↦ Fin.le_last _)
  letI : WeakEquivalence (pointMap (nerve
      (TimePrismChainRelative.Chain (K.obj q).len (N.obj q).len
        (image K N q U) (Fin.last (N.obj q).len)))) := (weakEquivalence_iff_GW _).mpr h
  rw [← pointIsTerminal.hom_ext (nerveMap i ≫ pointMap _) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- The actual category of all coefficient-covering chains projects by a nerve weak equivalence. -/
theorem projection_weak : WeakEquivalence (nerveMap (base K N)) :=
  projection_weak_of K N (fun q U ↦ relative_point_GW K N q U)

end

end DaggerModels.PartII.TimePrismChainProjection
