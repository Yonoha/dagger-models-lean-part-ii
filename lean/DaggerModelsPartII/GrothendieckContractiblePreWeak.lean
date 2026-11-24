import DaggerModelsPartII.GrothendieckContractibleFibers

/-! Weakness of Grothendieck reindexing along a weak base functor. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.GrothendieckContractiblePreWeak

noncomputable section

variable {C D : Type} [SmallCategory C] [SmallCategory D]
variable (F : C ⥤ Cat.{0, 0}) (G : D ⥤ C)

/-- Reindexing a diagram with weakly contractible fiber nerves along a
weak base functor gives a weak functor of full Grothendieck constructions. -/
theorem pre_weak
    (hF : ∀ c : C, GW (pointMap (nerve (F.obj c))))
    (hG : WeakEquivalence (nerveMap G)) :
    WeakEquivalence (nerveMap (Grothendieck.pre F G)) := by
  have hFG : WeakEquivalence
      (nerveMap (Grothendieck.forget (G ⋙ F))) :=
    GrothendieckContractibleFibers.projection_weak (G ⋙ F)
      (fun d ↦ hF (G.obj d))
  have hF' : WeakEquivalence (nerveMap (Grothendieck.forget F)) :=
    GrothendieckContractibleFibers.projection_weak F hF
  have hbase : Grothendieck.pre F G ⋙ Grothendieck.forget F =
      Grothendieck.forget (G ⋙ F) ⋙ G := rfl
  have hcomm : nerveMap (Grothendieck.pre F G) ≫
      nerveMap (Grothendieck.forget F) =
      nerveMap (Grothendieck.forget (G ⋙ F)) ≫ nerveMap G := by
    have h := congrArg nerveMap hbase
    simpa only [nerveFunctor.map_comp] using h
  haveI := hFG
  haveI := hF'
  haveI := hG
  exact weakEquivalence_of_postcomp_of_fac hcomm

end
end DaggerModels.PartII.GrothendieckContractiblePreWeak
