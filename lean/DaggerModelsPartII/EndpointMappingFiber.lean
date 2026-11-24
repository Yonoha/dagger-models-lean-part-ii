import DaggerModelsPartII.EndpointCobaseHom
import TopCatModelCategory.SSet.Fiber

/-!
# Strict endpoint fibers of Hom from a cosimplicial cobase

The specified source augmentation and boundary map determine a literal point
of the source Hom simplicial set. Hom under the boundary from the actual
endpoint cobase is canonically the pullback of the original mapping arrow
over that point. This is a strict categorical identification; its use as a
homotopy fiber additionally requires a fibration or a verified replacement.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.EndpointMappingFiber

noncomputable section

variable {C : Type u} [Category.{0} C]
variable {S T : SimplexCategory ⥤ C} (i : S ⟶ T)
  {B Z : C} (a : S ⟶ (Functor.const SimplexCategory).obj B) (b : B ⟶ Z)

/-- The literal Hom simplicial set of a cosimplicial coefficient diagram. -/
def mapping (F : SimplexCategory ⥤ C) : SSet.{0} := F.op ⋙ yoneda.obj Z

/-- Precomposition with the actual endpoint-face arrow. -/
def precomp : mapping (Z := Z) T ⟶ mapping (Z := Z) S :=
  Functor.whiskerRight (NatTrans.op i) (yoneda.obj Z)

/-- The constant endpoint point induced by the given augmentation and boundary. -/
def endpointPoint : (Δ[0] : SSet.{0}) ⟶ mapping (Z := Z) S where
  app k _ := a.app k.unop ≫ b
  naturality {k l} θ := by
    funext z
    change a.app l.unop ≫ b = S.map θ.unop ≫ (a.app k.unop ≫ b)
    have h : S.map θ.unop ≫ a.app k.unop = a.app l.unop := by
      exact (a.naturality θ.unop).trans (Category.comp_id (a.app l.unop))
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ b) h.symm

/-- An actual augmentation-preserving map carries the specified endpoint
point to the point of the replacement source. -/
theorem endpointPoint_precomp {S' : SimplexCategory ⥤ C} (h : S' ⟶ S)
    (a' : S' ⟶ (Functor.const SimplexCategory).obj B) (ha : h ≫ a = a') :
    endpointPoint a b ≫ precomp (Z := Z) h = endpointPoint a' b := by
  apply NatTrans.ext
  funext k z
  change h.app k.unop ≫ (a.app k.unop ≫ b) = a'.app k.unop ≫ b
  rw [← Category.assoc]
  exact congrArg (fun t ↦ t ≫ b) (NatTrans.congr_app ha k.unop)

/-- Maps from the target with exactly the specified constant endpoint equation. -/
def span : SSet.{0} where
  obj k := {f : T.obj k.unop ⟶ Z // i.app k.unop ≫ f = a.app k.unop ≫ b}
  map {k l} θ f := ⟨T.map θ.unop ≫ f.val, by
    rw [← Category.assoc, ← i.naturality θ.unop, Category.assoc, f.property]
    have h : S.map θ.unop ≫ a.app k.unop = a.app l.unop := by
      exact (a.naturality θ.unop).trans (Category.comp_id (a.app l.unop))
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ b) h⟩
  map_id _ := by funext f; apply Subtype.ext; simp
  map_comp _ _ := by funext f; apply Subtype.ext; simp [Category.assoc]

/-- Forgetting the endpoint equation retains the actual map from the target. -/
def spanRestriction : span i a b ⟶ mapping (Z := Z) T where
  app _ f := f.val
  naturality {_ _} _ := rfl

/-- The span's endpoint equation is precisely the pullback square equation. -/
theorem span_square :
    spanRestriction i a b ≫ precomp i =
      SSet.stdSimplex.objZeroIsTerminal.from (span i a b) ≫ endpointPoint a b := by
  apply NatTrans.ext
  funext k f
  exact f.property

/-- The actual endpoint span is the strict fiber of the mapping arrow. -/
theorem span_isPullback :
    IsPullback (spanRestriction i a b)
      (SSet.stdSimplex.objZeroIsTerminal.from (span i a b))
      (precomp i) (endpointPoint a b) where
  w := span_square i a b
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ {
      app k z := ⟨s.fst.app k z, by
        exact congrFun (NatTrans.congr_app s.condition k) z⟩
      naturality {k l} θ := by
        funext z
        apply Subtype.ext
        exact congrFun (s.fst.naturality θ) z })
    (fun _ ↦ rfl)
    (fun _ ↦ SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _)
    (fun s m hm _ ↦ by
      apply NatTrans.ext
      funext k z
      apply Subtype.ext
      exact congrFun (NatTrans.congr_app hm k) z)⟩

/-- The canonical fiber isomorphism has the literal restriction as first leg. -/
def spanFiberIso : span i a b ≅ pullback (precomp i) (endpointPoint a b) :=
  (span_isPullback i a b).isoPullback

variable [HasColimitsOfSize.{0, 0} C]

/-- The actual B-first cobase, considered under the fixed boundary. -/
def cobaseUnder : SimplexCategory ⥤ Under B :=
  Under.lift (pushout a i) (pushout.inl a i)

/-- Hom under the original boundary into its specified target. -/
def underMapping : SSet.{0} := (cobaseUnder i a).op ⋙ yoneda.obj (Under.mk b)

private def evaluatedCobaseIso (k : SimplexCategory) :
    (cobaseUnder i a).obj k ≅ Under.mk (pushout.inl (a.app k) (i.app k)) :=
  let h := (IsPushout.of_hasPushout a i).map ((evaluation SimplexCategory C).obj k)
  Under.isoMk h.isoPushout h.inl_isoPushout_hom

private def underSpanEquiv (k : SimplexCategory) :
    ((cobaseUnder i a).obj k ⟶ Under.mk b) ≃ (span i a b).obj (op k) :=
  (Iso.homCongr (evaluatedCobaseIso i a k) (Iso.refl (Under.mk b))).trans
    (EndpointCobaseHom.cobaseHomEquiv (i.app k) (a.app k) b)

private theorem underSpanEquiv_val (k : SimplexCategory)
    (f : (cobaseUnder i a).obj k ⟶ Under.mk b) :
    (underSpanEquiv i a b k f).val = (pushout.inr a i).app k ≫ f.right := by
  dsimp only [underSpanEquiv, Equiv.trans_apply]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  have h := EndpointCobaseHom.cobaseHomEquiv_val (i.app k) (a.app k) b
    ((evaluatedCobaseIso i a k).inv ≫ f)
  apply h.trans
  rw [Under.comp_right, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f.right)
    ((IsPushout.of_hasPushout a i).map
      ((evaluation SimplexCategory C).obj k)).inr_isoPushout_inv

/-- The pushout Hom equivalences are natural in the actual simplicial degree. -/
def underSpanIso : underMapping i a b ≅ span i a b :=
  NatIso.ofComponents (fun k ↦ (underSpanEquiv i a b k.unop).toIso) (by
    intro k l θ
    funext f
    apply Subtype.ext
    change (underSpanEquiv i a b l.unop ((cobaseUnder i a).map θ.unop ≫ f)).val =
      T.map θ.unop ≫ (underSpanEquiv i a b k.unop f).val
    rw [underSpanEquiv_val, underSpanEquiv_val]
    have h := (pushout.inr a i).naturality θ.unop
    simpa only [Category.assoc] using (congrArg (fun t ↦ t ≫ f.right) h).symm)

/-- The literal under-boundary Hom is the strict ordered mapping fiber. -/
def underFiberIso : underMapping i a b ≅ pullback (precomp i) (endpointPoint a b) :=
  underSpanIso i a b ≪≫ spanFiberIso i a b

/-- The first projection of the strict ordered fiber is restriction to the
target coprojection of the actual endpoint cobase. -/
theorem underFiberIso_hom_fst_app (k : SimplexCategory)
    (f : (cobaseUnder i a).obj k ⟶ Under.mk b) :
    (((underFiberIso i a b).hom ≫
      pullback.fst (precomp (Z := Z) i) (endpointPoint a b)).app (op k)) f =
      (pushout.inr a i).app k ≫ f.right := by
  simp only [underFiberIso, Iso.trans_hom, Category.assoc, spanFiberIso,
    (span_isPullback i a b).isoPullback_hom_fst]
  exact underSpanEquiv_val i a b k f

end

end DaggerModels.PartII.EndpointMappingFiber
