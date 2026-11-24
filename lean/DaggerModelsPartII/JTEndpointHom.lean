import DaggerModelsPartII.JTOrderedFrameMate
import DaggerModelsPartII.JTEndpointObjects
import DaggerModelsPartII.EndpointCobaseHom
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The literal endpoint cobase represents the ordered Hom simplicial set

The boundary object is the original rigidification of the free dagger
one-boundary. Its selected map to C is classified by the actual ordered
pair x,y. Pushout restriction identifies maps under that boundary with
the original Xi/Gamma ordered endpoint equations, naturally in degree.
-/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointHom

open JTZeroObjects JTEndpointObjects JTOrderedFrameMate
open JTRelativeReedyFrame JTActualCosimplicialFrame

noncomputable section

private local instance : HomotopicalAlgebra.ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The specified map from the literal two-endpoint boundary. -/
def boundaryTarget (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : Bdagger ⟶ C :=
  (boundaryPairEquiv C).symm (x, y)

@[simp] theorem endpointMap_boundaryTarget_zero (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) : endpointMap 0 ≫ boundaryTarget C x y = objectMap C x := by
  apply (zeroHomEquiv C).injective
  have h := (boundaryPairEquiv C).apply_symm_apply (x, y)
  rw [boundaryPairEquiv_apply] at h
  simpa only [zeroHomEquiv_objectMap] using congrArg Prod.fst h

@[simp] theorem endpointMap_boundaryTarget_one (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) : endpointMap 1 ≫ boundaryTarget C x y = objectMap C y := by
  apply (zeroHomEquiv C).injective
  have h := (boundaryPairEquiv C).apply_symm_apply (x, y)
  rw [boundaryPairEquiv_apply] at h
  simpa only [zeroHomEquiv_objectMap] using congrArg Prod.snd h

/-- The two actual outer-zero source frames in each cosimplicial degree. -/
def endpointSource (F : SimplexCategory ⥤ OuterDiagram) :
    SimplexCategory ⥤ Coefficient where
  obj k := (F.obj k).obj zeroIndex ⨿ (F.obj k).obj zeroIndex
  map θ := coprod.map ((F.map θ).app zeroIndex) ((F.map θ).app zeroIndex)
  map_id k := by simp only [F.map_id, NatTrans.id_app, coprod.map_id_id]
  map_comp θ ψ := by
    simp only [F.map_comp, NatTrans.comp_app, coprod.map_map]

/-- The two ordered outer vertex maps, as an actual cosimplicial arrow. -/
def endpointFaces (F : SimplexCategory ⥤ OuterDiagram) :
    endpointSource F ⟶ F ⋙ (evaluation ReverseSimplex Coefficient).obj oneIndex where
  app k := coprod.desc ((F.obj k).map (vertex 0)) ((F.obj k).map (vertex 1))
  naturality {j k} θ := by
    apply coprod.hom_ext
    · simpa only [endpointSource, coprod.inl_map_assoc, coprod.inl_desc,
        coprod.inl_desc_assoc] using ((F.map θ).naturality (vertex 0)).symm
    · simpa only [endpointSource, coprod.inr_map_assoc, coprod.inr_desc,
        coprod.inr_desc_assoc] using ((F.map θ).naturality (vertex 1)).symm

private theorem augmentation_vertical {F : SimplexCategory ⥤ OuterDiagram}
    (a : F ⟶ constantA) {j k : SimplexCategory} (θ : j ⟶ k) :
    (F.map θ).app zeroIndex ≫ (a.app k).app zeroIndex = (a.app j).app zeroIndex := by
  have h := congrArg (fun t ↦ t.app zeroIndex) (a.naturality θ)
  have hc : (constantA.map θ).app zeroIndex = 𝟙 _ := by simp [constantA]
  simpa only [NatTrans.comp_app, hc, Category.comp_id] using h

/-- Collapse both endpoint frames to their original ordered boundary vertices. -/
def endpointCollapse {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA) :
    endpointSource F ⟶ (Functor.const SimplexCategory).obj Bdagger where
  app k := coprod.desc ((a.app k).app zeroIndex ≫ endpointMap 0)
    ((a.app k).app zeroIndex ≫ endpointMap 1)
  naturality {j k} θ := by
    apply coprod.hom_ext
    · simp only [endpointSource, coprod.inl_map_assoc, coprod.inl_desc,
        coprod.inl_desc_assoc, Functor.const_obj_map]
      rw [← Category.assoc, augmentation_vertical a θ]
      exact (Category.comp_id _).symm
    · simp only [endpointSource, coprod.inr_map_assoc, coprod.inr_desc,
        coprod.inr_desc_assoc, Functor.const_obj_map]
      rw [← Category.assoc, augmentation_vertical a θ]
      exact (Category.comp_id _).symm

/-- The actual B-first endpoint pushout of the outer-one augmented frame. -/
def collapsedFrame {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA) :
    SimplexCategory ⥤ Coefficient :=
  JTEndpointCobase.endpointCobase (endpointFaces F) Bdagger (endpointCollapse a)

/-- The same actual collapsed frame as a diagram under the fixed literal boundary. -/
def collapsedUnder {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA) :
    SimplexCategory ⥤ Under Bdagger :=
  Under.lift (collapsedFrame a)
    (JTEndpointCobase.endpointCobase_inl (endpointFaces F) Bdagger (endpointCollapse a))

/-- The original target object with its specified ordered endpoints. -/
def targetUnder (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : Under Bdagger :=
  Under.mk (boundaryTarget C x y)

private def evaluatedCobaseIso {F : SimplexCategory ⥤ OuterDiagram}
    (a : F ⟶ constantA) (k : SimplexCategory) :
    (collapsedUnder a).obj k ≅
      Under.mk (pushout.inl ((endpointCollapse a).app k) ((endpointFaces F).app k)) :=
  let h := JTEndpointCobase.endpointCobase_isPushout_at
    (endpointFaces F) Bdagger (endpointCollapse a) k
  Under.isoMk h.isoPushout h.inl_isoPushout_hom

private def spanOrderedEquiv {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) (k : SimplexCategory) :
    {f : (F.obj k).obj oneIndex ⟶ C //
      (endpointFaces F).app k ≫ f = (endpointCollapse a).app k ≫ boundaryTarget C x y} ≃
      OrderedHom F a C x y k where
  toFun f := ⟨f.val, by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · have h := congrArg (fun t ↦ coprod.inl ≫ t) f.property
      simpa only [endpointFaces, endpointCollapse, coprod.inl_desc_assoc,
        Category.assoc, endpointMap_boundaryTarget_zero, endpointObject_zero] using h
    · have h := congrArg (fun t ↦ coprod.inr ≫ t) f.property
      simpa only [endpointFaces, endpointCollapse, coprod.inr_desc_assoc,
        Category.assoc, endpointMap_boundaryTarget_one, endpointObject_one] using h⟩
  invFun f := ⟨f.val, by
    apply coprod.hom_ext
    · simpa only [endpointFaces, endpointCollapse, coprod.inl_desc_assoc,
        Category.assoc, endpointMap_boundaryTarget_zero, endpointObject_zero] using f.property 0
    · simpa only [endpointFaces, endpointCollapse, coprod.inr_desc_assoc,
        Category.assoc, endpointMap_boundaryTarget_one, endpointObject_one] using f.property 1⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- Maps under the literal boundary are exactly the original ordered Hom maps. -/
def orderedHomEquiv {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) (k : SimplexCategory) :
    ((collapsedUnder a).obj k ⟶ targetUnder C x y) ≃ OrderedHom F a C x y k :=
  (Iso.homCongr (evaluatedCobaseIso a k) (Iso.refl (targetUnder C x y))).trans
    ((EndpointCobaseHom.cobaseHomEquiv ((endpointFaces F).app k)
      ((endpointCollapse a).app k) (boundaryTarget C x y)).trans
        (spanOrderedEquiv a C x y k))

/-- The equivalence is literal restriction along the actual frame coprojection. -/
theorem orderedHomEquiv_val {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) (k : SimplexCategory)
    (f : (collapsedUnder a).obj k ⟶ targetUnder C x y) :
    (orderedHomEquiv a C x y k f).val =
      (JTEndpointCobase.endpointCobase_inr (endpointFaces F) Bdagger
        (endpointCollapse a)).app k ≫ f.right := by
  change (EndpointCobaseHom.cobaseHomEquiv ((endpointFaces F).app k)
    ((endpointCollapse a).app k) (boundaryTarget C x y)
      ((evaluatedCobaseIso a k).inv ≫ f)).val = _
  rw [EndpointCobaseHom.cobaseHomEquiv_val, Under.comp_right]
  rw [← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f.right)
    (JTEndpointCobase.endpointCobase_isPushout_at
      (endpointFaces F) Bdagger (endpointCollapse a) k).inr_isoPushout_inv

/-- The actual Hom simplicial set of the endpoint-collapsed under-diagram. -/
def underHomSSet {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : SSet.{0} :=
  (collapsedUnder a).op ⋙ yoneda.obj (targetUnder C x y)

/-- The pointwise pushout identifications form an isomorphism of simplicial sets. -/
def orderedHomSSetIso {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    underHomSSet a C x y ≅ orderedHomSSet F a C x y :=
  NatIso.ofComponents (fun k ↦ (orderedHomEquiv a C x y k.unop).toIso) (by
    intro k l θ
    funext f
    apply Subtype.ext
    change (orderedHomEquiv a C x y l.unop
        ((collapsedUnder a).map θ.unop ≫ f)).val =
      (F.map θ.unop).app oneIndex ≫ (orderedHomEquiv a C x y k.unop f).val
    rw [orderedHomEquiv_val, orderedHomEquiv_val]
    have h := (JTEndpointCobase.endpointCobase_inr
      (endpointFaces F) Bdagger (endpointCollapse a)).naturality θ.unop
    simpa only [Category.assoc] using (congrArg (fun t ↦ t ≫ f.right) h).symm)

end

end DaggerModels.PartII.JTEndpointHom
