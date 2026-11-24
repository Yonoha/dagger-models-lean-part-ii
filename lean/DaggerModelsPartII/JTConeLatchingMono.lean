import DaggerModelsPartII.JTConeReedy
import DaggerModelsPartII.JTCylinderConeComparison
import DaggerModelsPartII.UnderColimitCoverage
import DaggerModelsPartII.UnderReedyCriterion
import DaggerModelsPartII.JTCylinderReedy
import OriginalCounitRightConeQCommonConeImageReconciled
import OriginalCounitRightConeQZeroFaceIntersectionReconciled

/-!
# Monicity of the literal right-cone latching maps

The source is the actual under-boundary face colimit, including its fixed
base at degrees zero and one. Scalar cone coface intersections are taken
from the original pushout geometry, not from rigidified Hom objects.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
  HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.JTConeLatchingMono

noncomputable section

open JTCylinderConeComparison JTConeReedy
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonBoundaryOverlap
open DaggerOriginalCounitRightConeQCommonConeImage
open DaggerOriginalCounitRightConeQZeroFaceIntersection

/-- The two actual endpoints remain distinct in every cone degree. This
follows from the already checked projection of the original cone to the
standard interval and needs no low-degree case split. -/
theorem coneBoundary_mono (k : SimplexCategory) : Mono (coneBoundary k) := by
  have h := coneBoundary_projection k
  change coneBoundary k ≫
    DaggerActualRightConeFinalEdgeMaps.projection k.len =
      (SSet.boundary.{0} 1).ι at h
  have hm : Mono (coneBoundary k ≫
      DaggerActualRightConeFinalEdgeMaps.projection k.len) := by
    rw [h]
    infer_instance
  letI : Mono (coneBoundary k ≫
      DaggerActualRightConeFinalEdgeMaps.projection k.len) := hm
  exact mono_of_mono (coneBoundary k)
    (DaggerActualRightConeFinalEdgeMaps.projection k.len)

/-- The maximal proper face omitting one vertex. -/
private def maximalFace (n : ℕ) (j : Fin (n + 2)) : MatchingIndex (n + 1) :=
  ⟨StructuredArrow.mk (SimplexCategory.δ j).op,
    ⟨Nat.lt_succ_self n, by
      change Mono (SimplexCategory.δ j)
      infer_instance⟩⟩

/-- Any proper face factors through a maximal coface. In the opposite
face diagram, this gives a map from the arbitrary face to a top face. -/
private theorem face_factors_maximal (n : ℕ) (s : MatchingIndex (n + 1)) :
    ∃ j : Fin (n + 2), Nonempty (maximalFace n j ⟶ s) := by
  classical
  let f : ⦋s.obj.right.unop.len⦌ ⟶ ⦋n + 1⦌ := s.obj.hom.unop
  have hnepi : ¬ Epi f := by
    intro hf
    letI : Epi f := hf
    exact (not_le_of_gt s.property.1) (SimplexCategory.len_le_of_epi f)
  have hns : ¬ Function.Surjective f.toOrderHom := by
    intro hf
    exact hnepi (SimplexCategory.epi_iff_surjective.mpr hf)
  change ¬ ∀ j, ∃ k, f.toOrderHom k = j at hns
  push_neg at hns
  obtain ⟨j, hj⟩ := hns
  let g := SimplexCategory.factor_δ f j
  have hg : g ≫ SimplexCategory.δ j = f :=
    SimplexCategory.factor_δ_spec f j hj
  refine ⟨j, ⟨?_⟩⟩
  exact ⟨StructuredArrow.homMk g.op (Quiver.Hom.unop_inj hg)⟩

/-- Every simplex from an arbitrary proper face has a representative in
a maximal face inside the literal under-boundary colimit. -/
private theorem face_to_maximal (n : ℕ) (s : MatchingIndex (n + 1))
    (q : SimplexCategoryᵒᵖ)
    (x : ((faceDiagram (n + 1)).obj (op s)).right.obj q) :
    ∃ (i : Fin (n + 2))
      (y : (DaggerOriginalCounitRightCone.cone.{0} n).obj q),
      ((colimit.ι (faceDiagram (n + 1)) (op s)).right).app q x =
        ((colimit.ι (faceDiagram (n + 1))
          (op (maximalFace n i))).right).app q y := by
  obtain ⟨i, ⟨p⟩⟩ := face_factors_maximal n s
  let y := (((faceDiagram (n + 1)).map p.op).right).app q x
  refine ⟨i, y, ?_⟩
  have hw := congrArg (fun f ↦ f.right)
    (colimit.w (faceDiagram (n + 1)) p.op)
  exact (congrFun (NatTrans.congr_app hw q) x).symm

/-- The actual latching descent sends its fixed-base image to the
original cone boundary. -/
private theorem latching_base (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (b : JTXiEndpointCollapse.boundary.obj q) :
    (faceLatchingMap n).right.app q
        ((colimit (faceDiagram n)).hom.app q b) =
      (coneBoundary ⦋n⦌).app q b := by
  have h := Under.w (faceLatchingMap n)
  exact congrFun (NatTrans.congr_app h q) b

/-- On each proper face, the same descent is the original cone map. -/
private theorem latching_leg (n : ℕ) (s : MatchingIndex n)
    (q : SimplexCategoryᵒᵖ)
    (y : ((faceDiagram n).obj (op s)).right.obj q) :
    (faceLatchingMap n).right.app q
        (((colimit.ι (faceDiagram n) (op s)).right).app q y) =
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        s.obj.hom.unop).app q) y := by
  have h := congrArg (fun f ↦ f.right)
    (colimit.ι_desc (faceCocone n) (op s))
  exact congrFun (NatTrans.congr_app h q) y

/-- The actual common proper face underlying two different maximal
faces of the ordinary cone. -/
private def commonFace (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    MatchingIndex (n + 2) :=
  ⟨StructuredArrow.mk (commonBaseHom n i j hij).op,
    ⟨by
      change n < n + 2
      omega, by
      apply SimplexCategory.mono_iff_injective.mpr
      intro x y h
      apply (commonBaseOrderIso n i j hij).injective
      apply Subtype.ext
      exact h⟩⟩

private def maximalToCommonI (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    maximalFace (n + 1) i ⟶ commonFace n i j hij :=
  ⟨StructuredArrow.homMk (factorI n i j hij).op
    (Quiver.Hom.unop_inj (factorI_spec n i j hij))⟩

private def maximalToCommonJ (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    maximalFace (n + 1) j ⟶ commonFace n i j hij :=
  ⟨StructuredArrow.homMk (factorJ n i j hij).op
    (Quiver.Hom.unop_inj (factorJ_spec n i j hij))⟩

/-- If a maximal face meets the fixed boundary in the target cone, its
preimage is the very same boundary simplex in the source cone. The
undercategory colimit identifies those two representatives. -/
private theorem maximal_base_overlap (n : ℕ) (i : Fin (n + 2))
    (q : SimplexCategoryᵒᵖ) (b : JTXiEndpointCollapse.boundary.obj q)
    (y : (DaggerOriginalCounitRightCone.cone.{0} n).obj q)
    (h : (coneBoundary ⦋n + 1⦌).app q b =
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ i)).app q) y) :
    (colimit (faceDiagram (n + 1))).hom.app q b =
      ((colimit.ι (faceDiagram (n + 1))
        (op (maximalFace n i))).right).app q y := by
  have hnat := coneBoundary_naturality (SimplexCategory.δ i)
  have hsource :
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ i)).app q)
        ((coneBoundary ⦋n⦌).app q b) =
      (coneBoundary ⦋n + 1⦌).app q b := by
    exact congrFun (NatTrans.congr_app hnat q) b
  have hmono : Function.Injective
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ i)).app q) :=
    (mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp (coneCoface_mono n i) q)
  have hy : y = (coneBoundary ⦋n⦌).app q b :=
    (hmono (hsource.trans h)).symm
  rw [hy]
  have hw := Under.w (colimit.ι (faceDiagram (n + 1))
    (op (maximalFace n i)))
  exact (congrFun (NatTrans.congr_app hw q) b).symm

/-- In degree at least two, equal simplices in two actual maximal cone
faces have one representative in their literal common cone face. The
proper-face cocone then identifies the representatives. -/
private theorem positive_maximal_overlap (n : ℕ) (i j : Fin (n + 3))
    (q : SimplexCategoryᵒᵖ)
    (x y : (DaggerOriginalCounitRightCone.cone.{0} (n + 1)).obj q)
    (h : ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
      (SimplexCategory.δ i)).app q) x =
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ j)).app q) y) :
    ((colimit.ι (faceDiagram (n + 2))
      (op (maximalFace (n + 1) i))).right).app q x =
    ((colimit.ι (faceDiagram (n + 2))
      (op (maximalFace (n + 1) j))).right).app q y := by
  by_cases hij : i = j
  · subst j
    have hmono : Function.Injective
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (SimplexCategory.δ i)).app q) :=
      (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app _).mp (coneCoface_mono (n + 1) i) q)
    exact congrArg _ (hmono h)
  · obtain ⟨z, hz⟩ :=
      (commonConeMap_pointwise_range_iff n i j hij q
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (SimplexCategory.δ i)).app q x)).2
        ⟨⟨x, rfl⟩, ⟨y, h.symm⟩⟩
    have hfi :
        DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (factorI n i j hij) ≫
          DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i) =
          DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (commonBaseHom n i j hij) := by
      rw [← DaggerOriginalCounitRightConeFunctor.coneFunctor.map_comp,
        factorI_spec]
    have hfj :
        DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (factorJ n i j hij) ≫
          DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ j) =
          DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (commonBaseHom n i j hij) := by
      rw [← DaggerOriginalCounitRightConeFunctor.coneFunctor.map_comp,
        factorJ_spec]
    have hxi :
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (factorI n i j hij)).app q) z = x := by
      apply (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app _).mp
          (coneCoface_mono (n + 1) i) q)
      exact (congrFun (NatTrans.congr_app hfi q) z).trans hz
    have hyj :
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (factorJ n i j hij)).app q) z = y := by
      apply (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app _).mp
          (coneCoface_mono (n + 1) j) q)
      exact (congrFun (NatTrans.congr_app hfj q) z).trans (hz.trans h)
    have hlegI := congrArg (fun f ↦ f.right)
      (colimit.w (faceDiagram (n + 2))
        (maximalToCommonI n i j hij).op)
    have hlegJ := congrArg (fun f ↦ f.right)
      (colimit.w (faceDiagram (n + 2))
        (maximalToCommonJ n i j hij).op)
    calc
      ((colimit.ι (faceDiagram (n + 2))
          (op (maximalFace (n + 1) i))).right).app q x =
          ((colimit.ι (faceDiagram (n + 2))
            (op (commonFace n i j hij))).right).app q z := by
              rw [← hxi]
              exact congrFun (NatTrans.congr_app hlegI q) z
      _ = ((colimit.ι (faceDiagram (n + 2))
          (op (maximalFace (n + 1) j))).right).app q y := by
              rw [← hyj]
              exact (congrFun (NatTrans.congr_app hlegJ q) z).symm

/-- In degree one, the two maximal cone faces meet in the *fixed ordered
boundary*, which is already amalgamated in the undercategory coproduct. -/
private theorem one_maximal_overlap (i j : Fin 2)
    (q : SimplexCategoryᵒᵖ)
    (x y : (DaggerOriginalCounitRightCone.cone.{0} 0).obj q)
    (h : ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
      (SimplexCategory.δ i)).app q) x =
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ j)).app q) y) :
    ((colimit.ι (faceDiagram 1) (op (maximalFace 0 i))).right).app q x =
      ((colimit.ι (faceDiagram 1) (op (maximalFace 0 j))).right).app q y := by
  by_cases hij : i = j
  · subst j
    have hmono : Function.Injective
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (SimplexCategory.δ i)).app q) :=
      (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app _).mp (coneCoface_mono 0 i) q)
    exact congrArg _ (hmono h)
  · have hcommon :
        ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
          (SimplexCategory.δ i)).app q x) ∈
            Set.range ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
              (SimplexCategory.δ i)).app q) ∧
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i)).app q x) ∈
            Set.range ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
              (SimplexCategory.δ j)).app q) :=
        ⟨⟨x, rfl⟩, ⟨y, h.symm⟩⟩
    have hb := (zero_coface_pointwise_common_image_iff i j hij q _).1 hcommon
    rcases hb with ⟨z, hz⟩ | ⟨z, hz⟩
    · let b : JTXiEndpointCollapse.boundary.obj q :=
        (SSet.boundary₁.ι₀).app q z
      have hboundary : (coneBoundary ⦋1⦌).app q b =
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i)).app q) x := by
        change (coneBoundary ⦋1⦌).app q ((SSet.boundary₁.ι₀).app q z) = _
        exact (congrFun (NatTrans.congr_app (coneBoundary_zero ⦋1⦌) q) z).trans hz
      exact (maximal_base_overlap 0 i q b x hboundary).symm.trans
        (maximal_base_overlap 0 j q b y (hboundary.trans h))
    · let b : JTXiEndpointCollapse.boundary.obj q :=
        (SSet.boundary₁.ι₁).app q z
      have hboundary : (coneBoundary ⦋1⦌).app q b =
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i)).app q) x := by
        change (coneBoundary ⦋1⦌).app q ((SSet.boundary₁.ι₁).app q z) = _
        exact (congrFun (NatTrans.congr_app (coneBoundary_one ⦋1⦌) q) z).trans hz
      exact (maximal_base_overlap 0 i q b x hboundary).symm.trans
        (maximal_base_overlap 0 j q b y (hboundary.trans h))

/-- All positive target degrees have compatible representatives in
maximal actual cone faces. The degree-one case uses the fixed boundary;
higher degrees use the literal common cone. -/
private theorem maximal_overlap (n : ℕ) (i j : Fin (n + 2))
    (q : SimplexCategoryᵒᵖ)
    (x y : (DaggerOriginalCounitRightCone.cone.{0} n).obj q)
    (h : ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
      (SimplexCategory.δ i)).app q) x =
      ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
        (SimplexCategory.δ j)).app q) y) :
    ((colimit.ι (faceDiagram (n + 1))
      (op (maximalFace n i))).right).app q x =
    ((colimit.ι (faceDiagram (n + 1))
      (op (maximalFace n j))).right).app q y := by
  cases n with
  | zero => exact one_maximal_overlap i j q x y h
  | succ k => exact positive_maximal_overlap k i j q x y h

/-- Every positive-degree literal latching arrow is monic on its
underlying ordinary simplicial set. The proof uses the fixed base plus
actual-face coverage of the undercategory colimit. -/
theorem positive_faceLatchingMap_right_mono (n : ℕ) :
    Mono (faceLatchingMap (n + 1)).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y h
  rcases UnderColimitCoverage.jointly_surjective (faceDiagram (n + 1)) q x with
    ⟨bx, rfl⟩ | ⟨sx, xx, rfl⟩
  · rcases UnderColimitCoverage.jointly_surjective (faceDiagram (n + 1)) q y with
      ⟨b_y, rfl⟩ | ⟨sy, yy, rfl⟩
    · have hb : (coneBoundary ⦋n + 1⦌).app q bx =
          (coneBoundary ⦋n + 1⦌).app q b_y := by
        simpa only [latching_base] using h
      have hinj : Function.Injective ((coneBoundary ⦋n + 1⦌).app q) :=
        (mono_iff_injective _).mp
          ((NatTrans.mono_iff_mono_app _).mp
            (coneBoundary_mono ⦋n + 1⦌) q)
      exact congrArg _ (hinj hb)
    · obtain ⟨j, z, hz⟩ := face_to_maximal n sy.unop q yy
      rw [hz] at h ⊢
      have hb : (coneBoundary ⦋n + 1⦌).app q bx =
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ j)).app q) z := by
        simpa only [latching_base, latching_leg] using h
      exact maximal_base_overlap n j q bx z hb
  · rcases UnderColimitCoverage.jointly_surjective (faceDiagram (n + 1)) q y with
      ⟨b_y, rfl⟩ | ⟨sy, yy, rfl⟩
    · obtain ⟨i, z, hz⟩ := face_to_maximal n sx.unop q xx
      rw [hz] at h ⊢
      have hb : (coneBoundary ⦋n + 1⦌).app q b_y =
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i)).app q) z := by
        simpa only [latching_base, latching_leg] using h.symm
      exact (maximal_base_overlap n i q b_y z hb).symm
    · obtain ⟨i, zx, hzx⟩ := face_to_maximal n sx.unop q xx
      obtain ⟨j, zy, hzy⟩ := face_to_maximal n sy.unop q yy
      rw [hzx, hzy] at h ⊢
      have hf :
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ i)).app q) zx =
          ((DaggerOriginalCounitRightConeFunctor.coneFunctor.{0}.map
            (SimplexCategory.δ j)).app q) zy := by
        simpa only [latching_leg] using h
      exact maximal_overlap n i j q zx zy hf

/-- The empty degree-zero proper-face category contributes only the
fixed base to the undercategory colimit. -/
theorem zero_faceLatchingMap_right_mono :
    Mono (faceLatchingMap 0).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y h
  rcases UnderColimitCoverage.jointly_surjective (faceDiagram 0) q x with
    ⟨bx, rfl⟩ | ⟨s, _, _⟩
  · rcases UnderColimitCoverage.jointly_surjective (faceDiagram 0) q y with
      ⟨b_y, rfl⟩ | ⟨s, _, _⟩
    · have hb : (coneBoundary ⦋0⦌).app q bx =
          (coneBoundary ⦋0⦌).app q b_y := by
        simpa only [latching_base] using h
      have hinj : Function.Injective ((coneBoundary ⦋0⦌).app q) :=
        (mono_iff_injective _).mp
          ((NatTrans.mono_iff_mono_app _).mp
            (coneBoundary_mono ⦋0⦌) q)
      exact congrArg _ (hinj hb)
    · exact isEmptyElim s.unop
  · exact isEmptyElim s.unop

/-- The literal under-boundary latching map has monic underlying
simplicial-set map in every degree, including degree zero. -/
theorem faceLatchingMap_right_mono (n : ℕ) :
    Mono (faceLatchingMap n).right := by
  cases n with
  | zero => exact zero_faceLatchingMap_right_mono
  | succ k => exact positive_faceLatchingMap_right_mono k

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : ModelCategory (Under JTXiEndpointCollapse.boundary) :=
  JTEndpointCobase.underModel JTXiEndpointCollapse.boundary
private local instance : ModelCategory (Under JTXiEndpointCollapse.boundary)ᵒᵖ :=
  inferInstance
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under JTXiEndpointCollapse.boundary)ᵒᵖ) :=
  simplicialReedyModelCategory (Under JTXiEndpointCollapse.boundary)ᵒᵖ

/-- Every literal right-cone latching arrow is a cofibration in the
original ordinary Joyal model under the ordered boundary. -/
theorem faceLatchingMap_cofibration (n : ℕ) :
    cofibrations (Under JTXiEndpointCollapse.boundary)
      (faceLatchingMap n) := by
  change cofibrations SSet.{0} (faceLatchingMap n).right
  change
    DaggerNativeOriginalJoyalSmithModelData.modelData.model.categoryWithCofibrations.cofibrations _
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact faceLatchingMap_right_mono n

/-- The original ordinary right-cone diagram is Reedy cofibrant under
its fixed ordered boundary in the unchanged Joyal under-model. -/
theorem coneUnder_op_isFibrant : IsFibrant JTCylinderConeComparison.coneUnder.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations (Under JTXiEndpointCollapse.boundary)ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app coneUnder.op) (coneMatchingIso n).hom).mp
  rw [coneMatchingIso_comp, fibrations_op]
  exact faceLatchingMap_cofibration n

end

end DaggerModels.PartII.JTConeLatchingMono
