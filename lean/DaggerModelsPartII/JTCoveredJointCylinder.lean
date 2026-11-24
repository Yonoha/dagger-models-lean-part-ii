import DaggerModelsPartII.JTJointRelativeGraphFamily
import DaggerModelsPartII.JTEndpointReducedCover
import DaggerModelsPartII.JTEndpointCoveredPrism
import DaggerModelsPartII.JTEndpointCoverRigidification
import DaggerModelsPartII.NecklaceCylinderHomSpan
import DaggerModelsPartII.JTDecoratedIntervalCylinder
import DaggerModelsPartII.JTNecklaceCylinderConnector

/-! Collapse the lifted endpoints and retain the exact two fixed-target projections. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open EnrichedCategory DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalCounitRightConeRelativeHomotopy (timeSlice)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTCoveredJointCylinder

open JTJointRelativeGraphFamily
open JTJointRelativeParameters (withTime)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (whole left right)
open JTTargetJointMarks (Joint)
open JTNecklaceEndpointCylinder (endpointInclusion cylinder value nativeMap nativeMap_cylinder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (hfirst : j.val ≠ 0) (hlast : j.val ≠ Fin.last Q.code.len)

private abbrev code (p : I) := (codes L).obj p
private abbrev cylinders (v : I ⥤ SimplexCategory) :=
  JTDecoratedIntervalCylinder.reduced Q (native F) v

private abbrev boundaryCollapse :=
  Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection

private def cylinderLeg (v : I ⥤ SimplexCategory) :
    withTime Q.map J v (native F) (whole Q.code) ⟶ cylinders F v ⋙ Under.forget B where
  app p := (cylinder (code (L := L) p)).app (v.obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (native F) v f).symm

private theorem cylinder_boundary :
    productBoundary F ≫ cylinderLeg F time =
      boundaryCollapse (time := time) ≫ JTEndpointReducedCover.boundary (cylinders F time) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p)).w

/-- Collapse both lifted endpoint lines to the original ordered boundary. -/
abbrev reduced : I ⥤ Under B :=
  JTEndpointReducedCover.reduced (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time))

/-- The covered reduced cylinder projects to the original native and time cylinder. -/
def projection : reduced F j s t hfirst hlast ⟶ cylinders F time :=
  JTEndpointReducedCover.projection (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time) (fullCoverProjection F j s t)
    (productBoundary F) (cylinderLeg F time) (coveredBoundary_projection F j s t hfirst hlast)
    (cylinder_boundary F)

/-- Projection also acts on every internal necklace and arrow of the original
presentation, using the identity on the indexing category. -/
abbrev presentationProjection :
    BoundaryNecklaceComma.Presentation (reduced F j s t hfirst hlast) ⥤
      BoundaryNecklaceComma.Presentation (cylinders F time) :=
  JTBoundaryNecklacePresentationCone.mapPresentation (cylinders F time)
    (reduced F j s t hfirst hlast) (𝟭 I) (projection F j s t hfirst hlast)


include hfirst in
private theorem productBoundary_mono (p : I) : Mono ((productBoundary F).app p) := by
  have hj : (j.val : ℕ) ≠ 0 := fun h ↦ hfirst (Fin.ext h)
  have hj' := j.val.isLt
  have hpos : 0 < Q.code.len := by omega
  haveI : Mono (endpointInclusion Q.code) :=
    NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos Q.code hpos
  have hn : endpointInclusion (code (L := L) p) ≫ (F.collapse.app p).map =
      endpointInclusion Q.code :=
    JTNecklaceEndpointCylinder.endpointInclusion_natural (F.collapse.app p)
  haveI : Mono (endpointInclusion (code (L := L) p)) := mono_of_mono_fac hn
  change Mono (endpointInclusion (code (L := L) p) ⊗ₘ 𝟙 (J.obj (time.obj p)))
  rw [tensorHom_id]
  exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono _ _

/-- The projection across endpoint collapse keeps the weak type of each original cylinder
as soon as the pulled-back left and right coefficient tests can be solved together. -/
theorem projection_weak (h : CrossAgreementAlongOperators F j s t) (p : I) :
    WeakEquivalence ((projection F j s t hfirst hlast).app p).right := by
  letI := productBoundary_mono F j hfirst p
  letI : WeakEquivalence (C := SSet.{0}) ((fullCoverProjection F j s t).app p) :=
    ⟨(fullCover_trivialFibration F j s t h p).2⟩
  exact JTEndpointReducedCover.projection_weak (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time) (fullCoverProjection F j s t)
    (productBoundary F) (cylinderLeg F time) (coveredBoundary_projection F j s t hfirst hlast)
    (cylinder_boundary F) p
    (JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p))

/-- Each original reduced cylinder is a retract of the covered one under
its original two endpoint vertices. -/
theorem exists_section (h : CrossAgreementAlongOperators F j s t) (p : I) :
    ∃ r : (cylinders F time).obj p ⟶ (reduced F j s t hfirst hlast).obj p,
      r ≫ (projection F j s t hfirst hlast).app p = 𝟙 _ := by
  letI := productBoundary_mono F j hfirst p
  have hf := fullCover_trivialFibration F j s t h p
  letI : Fibration (C := SSet.{0}) ((fullCoverProjection F j s t).app p) := ⟨hf.1⟩
  letI : WeakEquivalence (C := SSet.{0}) ((fullCoverProjection F j s t).app p) := ⟨hf.2⟩
  obtain ⟨_, _, _, r, _, hr⟩ := JTEndpointReducedCover.exists_relative_section
    (coveredBoundary F j s t hfirst hlast) (boundaryCollapse (time := time))
    (cylinders F time) (fullCoverProjection F j s t) (productBoundary F) (cylinderLeg F time)
    (coveredBoundary_projection F j s t hfirst hlast) (cylinder_boundary F) p
    (JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p))
  exact ⟨r, hr⟩

private def coveredGraph : fullCover F j s t ⟶
    withTime Q.map J (coefficient (L := L)) (native F) (whole Q.code) where
  app p := lift ((fullCoverProjection F j s t).app p ≫
    fst (code (L := L) p).toSSet (J.obj (time.obj p))) ((fullCoverParameter F j s t).app p)
  naturality {p p'} f := by
    let π := fullCoverProjection F j s t
    let θ := fullCoverParameter F j s t
    let U := (fullCover F j s t).map f
    let a := ((native F).map f).left.map
    let g := J.map ((coefficient (L := L)).map f)
    change _ = _ ≫ ((JTDecoratedIntervalDiagram.parameterize Q.map J (coefficient (L := L))
      (native F ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    apply NatTrans.ext
    funext q z
    change (((π.app p').app q (U.app q z)).1, (θ.app p').app q (U.app q z)) =
      (a.app q ((π.app p).app q z).1, g.app q ((θ.app p).app q z))
    apply Prod.ext
    · have e := congrFun (NatTrans.congr_app (π.naturality f) q) z
      have e' := congrArg Prod.fst e
      exact e'
    · exact congrFun (NatTrans.congr_app (θ.naturality f) q) z

private abbrev graphLeg :
    fullCover F j s t ⟶ L ⋙ underDiagram W x y ⋙ Under.forget B :=
  coveredGraph F j s t ≫ cylinderLeg F (coefficient (L := L))

private theorem graph_boundary :
    coveredBoundary F j s t hfirst hlast ≫ graphLeg F j s t =
      boundaryCollapse (time := time) ≫
        JTEndpointReducedCover.boundary (L ⋙ underDiagram W x y) := by
  apply NatTrans.ext
  funext p
  let u := (coveredBoundary F j s t hfirst hlast).app p
  let k := (coefficient (L := L)).obj p
  let T := code (L := L) p
  let e := (boundaryCollapse (time := time)).app p
  let θ := (fullCoverParameter F j s t).app p
  have h := NatTrans.congr_app (coveredBoundary_projection F j s t hfirst hlast) p
  change u ≫ (fullCoverProjection F j s t).app p = (productBoundary F).app p at h
  change u ≫ lift ((fullCoverProjection F j s t).app p ≫ fst T.toSSet (J.obj (time.obj p))) θ ≫
    (cylinder T).app k = e ≫ (JTNecklaceEndpointCylinder.boundary T).app k
  rw [← Category.assoc, comp_lift, ← Category.assoc u, h]
  change lift ((endpointInclusion T ⊗ₘ 𝟙 _) ≫ fst _ _) (u ≫ θ) ≫
      (cylinder T).app k = _
  rw [tensorHom_fst]
  exact JTNecklaceCylinderConnector.boundary_collapse T k e (u ≫ θ)

/-- The chosen graph parameters map the covered reduced cylinder to the original
decorated label, with both collapsed endpoints retained. -/
def decorated :
    reduced F j s t hfirst hlast ⟶ L ⋙ underDiagram W x y :=
  JTEndpointReducedCover.descend (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time)) (L ⋙ underDiagram W x y) (graphLeg F j s t)
    (graph_boundary F j s t hfirst hlast)

private abbrev nativeTarget := BoundaryNecklaceComma.necklaceUnder.obj Q.code

/-- The covered native map is the original exact collapse to the specified target. -/
def nativeProjection :
    reduced F j s t hfirst hlast ⟶ (Functor.const I).obj (nativeTarget (Q := Q)) :=
  projection F j s t hfirst hlast ≫ JTDecoratedIntervalCylinder.native Q (native F) time

private abbrev coveredCylinderLeg :=
  pushout.inl (coveredBoundary F j s t hfirst hlast) (boundaryCollapse (time := time))

private theorem projection_cylinder (p : I) :
    (coveredCylinderLeg F j s t hfirst hlast).app p ≫
      ((projection F j s t hfirst hlast).app p).right =
        (fullCoverProjection F j s t).app p ≫ (cylinderLeg F time).app p :=
  JTEndpointReducedCover.descend_cylinder (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time)
    (fullCoverProjection F j s t ≫ cylinderLeg F time) _ p

private theorem decorated_cylinder (p : I) :
    (coveredCylinderLeg F j s t hfirst hlast).app p ≫
      ((decorated F j s t hfirst hlast).app p).right = (graphLeg F j s t).app p :=
  JTEndpointReducedCover.descend_cylinder (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time)) (L ⋙ underDiagram W x y) (graphLeg F j s t)
    (graph_boundary F j s t hfirst hlast) p

private theorem covered_isPushout (p : I) :
    IsPushout ((coveredBoundary F j s t hfirst hlast).app p)
      ((boundaryCollapse (time := time)).app p)
      ((coveredCylinderLeg F j s t hfirst hlast).app p)
      ((reduced F j s t hfirst hlast).obj p).hom :=
  (IsPushout.of_hasPushout (coveredBoundary F j s t hfirst hlast)
    (boundaryCollapse (time := time))).map ((evaluation I SSet.{0}).obj p)

private theorem cylinderHom_point_GW (T : NecklaceCode) (n : SimplexCategory) :
    GW (pointMap (NecklaceCylinderHomSpan.cylinderHom T n)) := by
  letI := NecklaceCylinderHomSpan.leftMap_weak T n
  letI : WeakEquivalence (C := SSet.{0}) (pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
    (weakEquivalence_iff_GW _).mpr (DecoratedNecklaceHomBar.necklaceHom_point_GW T)
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (NecklaceCylinderHomSpan.leftMap T n ≫ pointMap _) (pointMap _)]
  infer_instance

private theorem exists_relative_deformation (h : CrossAgreementAlongOperators F j s t) (p : I) :
    let c := (reduced F j s t hfirst hlast).obj p
    let Y := (cylinders F time).obj p
    let ρ := (projection F j s t hfirst hlast).app p
    ∃ (r : Y ⟶ c) (K : c.right ⊗ (Δ[1] : SSet.{0}) ⟶ c.right),
      r ≫ ρ = 𝟙 Y ∧ timeSlice c.right 0 ≫ K = 𝟙 c.right ∧
        timeSlice c.right 1 ≫ K = ρ.right ≫ r.right ∧
        (c.hom ▷ (Δ[1] : SSet.{0})) ≫ K = fst B (Δ[1] : SSet.{0}) ≫ c.hom := by
  letI := productBoundary_mono F j hfirst p
  let ρ := (projection F j s t hfirst hlast).app p
  let π := (fullCoverProjection F j s t).app p
  let d := (productBoundary F).app p
  let u := (coveredBoundary F j s t hfirst hlast).app p
  let l := (coveredCylinderLeg F j s t hfirst hlast).app p
  have hf := fullCover_trivialFibration F j s t h p
  letI : Fibration (C := SSet.{0}) π := ⟨hf.1⟩
  letI : WeakEquivalence (C := SSet.{0}) π := ⟨hf.2⟩
  obtain ⟨σ, hσ, hπ, r, hr, hr'⟩ := JTEndpointReducedCover.exists_relative_section
    (coveredBoundary F j s t hfirst hlast) (boundaryCollapse (time := time))
    (cylinders F time) (fullCoverProjection F j s t) (productBoundary F) (cylinderLeg F time)
    (coveredBoundary_projection F j s t hfirst hlast) (cylinder_boundary F) p
    (JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p))
  have hu : u ≫ π = d :=
    NatTrans.congr_app (coveredBoundary_projection F j s t hfirst hlast) p
  have hp : l ≫ (ρ.right ≫ r.right) = (π ≫ σ) ≫ l := by
    rw [← Category.assoc, show l ≫ ρ.right = π ≫ (cylinderLeg F time).app p from
      projection_cylinder F j s t hfirst hlast p, Category.assoc, hr, ← Category.assoc]
  have hb : ((reduced F j s t hfirst hlast).obj p).hom ≫ (ρ.right ≫ r.right) =
      ((reduced F j s t hfirst hlast).obj p).hom := Under.w (ρ ≫ r)
  obtain ⟨K, h₀, h₁, hB⟩ := JTEndpointCoveredPrism.exists_collapsed_prism
    u d π σ hu hσ hπ _ _ _ (covered_isPushout F j s t hfirst hlast p) _ hp hb
  exact ⟨r, K, hr', h₀, h₁, hB⟩

/-- Every complete covered internal-necklace fiber has weakly contractible nerve. -/
theorem fiber_point_GW (h : CrossAgreementAlongOperators F j s t) (p : I) :
    GW (pointMap (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder
      ((reduced F j s t hfirst hlast).obj p)))) := by
  obtain ⟨r, K, hr, h₀, h₁, hB⟩ := exists_relative_deformation F j s t hfirst hlast h p
  apply JTEndpointCoverRigidification.fiber_point_GW
    ((projection F j s t hfirst hlast).app p) r hr K h₀ h₁ hB
  rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
  exact cylinderHom_point_GW (code (L := L) p) (time.obj p)

/-- The covered internal-necklace presentation retains the weak type of its index. -/
theorem forget_weak (h : CrossAgreementAlongOperators F j s t) :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j s t hfirst hlast)))) :=
  GrothendieckContractibleFibers.projection_weak _ (fiber_point_GW F j s t hfirst hlast h)


/-- The full comparison on nerves is weak, with the same index and all
of the old internal necklaces and arrows retained in the target. -/
theorem presentationProjection_weak (h : CrossAgreementAlongOperators F j s t) :
    WeakEquivalence (nerveMap (presentationProjection F j s t hfirst hlast)) := by
  let p := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (cylinders F time))
  let q := Grothendieck.forget
    (BoundaryNecklaceComma.fiberDiagram (reduced F j s t hfirst hlast))
  let f := presentationProjection F j s t hfirst hlast
  have hb : f ⋙ p = q := rfl
  have he : nerveMap f ≫ nerveMap p = nerveMap q :=
    (nerveFunctor.map_comp f.toCatHom p.toCatHom).symm.trans (congrArg nerveMap hb)
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap q) := forget_weak F j s t hfirst hlast h
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap p) :=
    JTParametrizedTargetFamilies.projection_weak
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap f ≫ nerveMap p) := by
    rw [he]
    infer_instance
  exact weakEquivalence_of_postcomp (nerveMap f) (nerveMap p)

/-- A weakly contractible indexing category gives a weakly contractible
covered evaluation domain. -/
theorem presentation_point_GW (h : CrossAgreementAlongOperators F j s t)
    (hI : GW (pointMap (nerve I))) :
    GW (pointMap (nerve (BoundaryNecklaceComma.Presentation (reduced F j s t hfirst hlast)))) := by
  let p := Grothendieck.forget
    (BoundaryNecklaceComma.fiberDiagram (reduced F j s t hfirst hlast))
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap p) := forget_weak F j s t hfirst hlast h
  letI : WeakEquivalence (C := SSet.{0}) (pointMap (nerve I)) := (weakEquivalence_iff_GW _).mpr hI
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (nerveMap p ≫ pointMap _) (pointMap _)]
  infer_instance

variable (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t)

include hs ht in
/-- The covered decorated and native maps commute over the literal raw target. -/
theorem pair_square (p : I) :
    (decorated F j s t hfirst hlast).app p ≫ (underCocone W x y).app (L.obj p) =
      (nativeProjection F j s t hfirst hlast).app p ≫
        JTTargetCommaPullback.targetMap W x y Q := by
  let u := (decorated F j s t hfirst hlast).app p ≫ (underCocone W x y).app (L.obj p)
  let v := (nativeProjection F j s t hfirst hlast).app p ≫
    JTTargetCommaPullback.targetMap W x y Q
  change u = v
  apply Under.UnderMorphism.ext
  apply (covered_isPushout F j s t hfirst hlast p).hom_ext
  · let i := (coveredCylinderLeg F j s t hfirst hlast).app p
    change i ≫ (((decorated F j s t hfirst hlast).app p).right ≫
      ((underCocone W x y).app (L.obj p)).right) =
        i ≫ (((projection F j s t hfirst hlast).app p).right ≫
          ((JTDecoratedIntervalCylinder.native Q (native F) time).app p).right) ≫ Q.map
    rw [← Category.assoc i, decorated_cylinder, ← Category.assoc i,
      ← Category.assoc i, projection_cylinder]
    let T := code (L := L) p
    let n := time.obj p
    let k := (coefficient (L := L)).obj p
    change (((coveredGraph F j s t).app p ≫ (cylinder T).app k) ≫
        ((underCocone W x y).app (L.obj p)).right) =
      (((fullCoverProjection F j s t).app p ≫ (cylinder T).app n) ≫
        (NecklaceCylinderAugmentation.augmentation T n ≫ (F.collapse.app p).map)) ≫ Q.map
    simp only [Category.assoc]
    rw [← Category.assoc ((cylinder T).app n) (NecklaceCylinderAugmentation.augmentation T n),
      NecklaceCylinderAugmentation.augmentation_cylinder]
    exact fullCover_raw F j s t hs ht p
  · exact (Under.w u).trans (Under.w v).symm

/-- Evaluation retains all internal necklaces of the covered reduced cylinder
and lands in the original fixed-target comma category. -/
def evaluate : BoundaryNecklaceComma.Presentation (reduced F j s t hfirst hlast) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTDecoratedIntervalCylinder.evaluateFromProjections Q L _ (decorated F j s t hfirst hlast)
    (nativeProjection F j s t hfirst hlast) (pair_square F j s t hfirst hlast hs ht)

/-- The decorated projection is the given internal necklace followed by the lifted graph. -/
theorem evaluate_decorated (P : BoundaryNecklaceComma.Presentation
    (reduced F j s t hfirst hlast)) :
    ((evaluate F j s t hfirst hlast hs ht).obj P).left.fiber.hom =
      P.fiber.hom ≫ (decorated F j s t hfirst hlast).app P.base :=
  JTDecoratedIntervalCylinder.evaluateFromProjections_decorated Q L _ _ _ _ P

/-- The native projection factors through the original native and time cylinder. -/
theorem evaluate_native (P : BoundaryNecklaceComma.Presentation (reduced F j s t hfirst hlast)) :
    BoundaryNecklaceComma.necklaceUnder.map
        ((evaluate F j s t hfirst hlast hs ht).obj P).hom.hom =
      P.fiber.hom ≫ (nativeProjection F j s t hfirst hlast).app P.base :=
  JTDecoratedIntervalCylinder.evaluateFromProjections_native Q L _ _ _ _ P

section OriginalSection

private abbrev originalReduced :=
  reduced F j (originalLeft F j) (originalRight F j) hfirst hlast

private abbrev originalProjection :=
  projection F j (originalLeft F j) (originalRight F j) hfirst hlast

private abbrev originalDecorated :=
  decorated F j (originalLeft F j) (originalRight F j) hfirst hlast

private abbrev originalNative :=
  nativeProjection F j (originalLeft F j) (originalRight F j) hfirst hlast

private abbrev originalPushout (p : I) :=
  JTNecklaceEndpointCylinder.isPushout (code (L := L) p) (time.obj p)

/-- The original parameter gives a natural section under the original ordered boundary. -/
def originalSection : cylinders F time ⟶ originalReduced F j hfirst hlast :=
  JTEndpointReducedCover.naturalRelativeSection
    (coveredBoundary F j (originalLeft F j) (originalRight F j) hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time)
    (productBoundary F) (cylinderLeg F time) (originalCoverSection F j)
    (originalCoverSection_boundary F j hfirst hlast) (originalPushout (L := L) (time := time))

theorem originalSection_projection :
    originalSection F j hfirst hlast ≫ originalProjection F j hfirst hlast = 𝟙 _ :=
  JTEndpointReducedCover.naturalRelativeSection_projection
    (coveredBoundary F j (originalLeft F j) (originalRight F j) hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time)
    (fullCoverProjection F j (originalLeft F j) (originalRight F j))
    (productBoundary F) (cylinderLeg F time)
    (coveredBoundary_projection F j (originalLeft F j) (originalRight F j) hfirst hlast)
    (cylinder_boundary F) (originalCoverSection F j)
    (originalCoverSection_boundary F j hfirst hlast) (originalPushout (L := L) (time := time))
    (originalCoverSection_projection F j)

private theorem originalSection_cylinder (p : I) :
    (cylinderLeg F time).app p ≫ ((originalSection F j hfirst hlast).app p).right =
      (originalCoverSection F j).app p ≫
        (coveredCylinderLeg F j (originalLeft F j) (originalRight F j) hfirst hlast).app p :=
  JTEndpointReducedCover.naturalRelativeSection_cylinder
    (coveredBoundary F j (originalLeft F j) (originalRight F j) hfirst hlast)
    (boundaryCollapse (time := time)) (cylinders F time)
    (productBoundary F) (cylinderLeg F time) (originalCoverSection F j)
    (originalCoverSection_boundary F j hfirst hlast) (originalPushout (L := L) (time := time)) p

private theorem originalSection_graph (p : I) :
    (originalCoverSection F j).app p ≫
      (coveredGraph F j (originalLeft F j) (originalRight F j)).app p =
        lift (fst (code (L := L) p).toSSet (J.obj (time.obj p))) (F.parameter p) := by
  let q := (originalCoverSection F j).app p
  let π := (fullCoverProjection F j (originalLeft F j) (originalRight F j)).app p
  let θ := (fullCoverParameter F j (originalLeft F j) (originalRight F j)).app p
  let a := fst (code (L := L) p).toSSet (J.obj (time.obj p))
  have hπ : q ≫ π = 𝟙 _ := NatTrans.congr_app (originalCoverSection_projection F j) p
  have hθ : q ≫ θ = F.parameter p :=
    NatTrans.congr_app (originalCoverSection_parameter F j) p
  change q ≫ lift (π ≫ a) θ = lift a (F.parameter p)
  rw [comp_lift, ← Category.assoc q, hπ, Category.id_comp, hθ]

private theorem originalSection_decorated (p : I) :
    (originalSection F j hfirst hlast).app p ≫ (originalDecorated F j hfirst hlast).app p =
      JTParametrizedTargetLiftTransport.graph (F.parameter p) := by
  let u := (originalSection F j hfirst hlast).app p ≫ (originalDecorated F j hfirst hlast).app p
  let v := JTParametrizedTargetLiftTransport.graph (F.parameter p)
  change u = v
  apply Under.UnderMorphism.ext
  apply (originalPushout (L := L) (time := time) p).hom_ext
  · change (cylinderLeg F time).app p ≫ ((originalSection F j hfirst hlast).app p).right ≫
      ((originalDecorated F j hfirst hlast).app p).right =
        (cylinderLeg F time).app p ≫ v.right
    rw [← Category.assoc, originalSection_cylinder, Category.assoc, decorated_cylinder]
    change (originalCoverSection F j).app p ≫
        (coveredGraph F j (originalLeft F j) (originalRight F j)).app p ≫
          (cylinder (code (L := L) p)).app ((coefficient (L := L)).obj p) =
      (cylinder (code (L := L) p)).app (time.obj p) ≫
        JTInterpolatedReducedCylinder.cylinderMap (code (L := L) p) (F.parameter p)
    rw [← Category.assoc, originalSection_graph,
      JTInterpolatedReducedCylinder.cylinderMap_cylinder]
    rfl
  · exact (Under.w u).trans (Under.w v).symm

private abbrev originalPair (p : I) :=
  pair_square F j (originalLeft F j) (originalRight F j) hfirst hlast
    (original_rawOn F (leftLeg F j)) (original_rawOn F (rightLeg F j)) p

private abbrev originalCoveredLift :=
  JTDecoratedIntervalCylinder.liftFromProjections Q L (originalReduced F j hfirst hlast)
    (originalDecorated F j hfirst hlast) (originalNative F j hfirst hlast)
    (originalPair F j hfirst hlast)

private theorem originalSection_lift :
    originalSection F j hfirst hlast ≫ originalCoveredLift F j hfirst hlast =
      JTParametrizedTargetFamilies.liftNatural F := by
  apply NatTrans.ext
  funext p
  apply pullback.hom_ext (f := (underCocone W x y).app (L.obj p))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change ((originalSection F j hfirst hlast).app p ≫ _) ≫
      JTTargetCommaPullback.fst W x y Q (L.obj p) = _
    rw [Category.assoc]
    change (originalSection F j hfirst hlast).app p ≫
        ((originalCoveredLift F j hfirst hlast).app p ≫
          JTTargetCommaPullback.fst W x y Q (L.obj p)) = _
    rw [JTDecoratedIntervalCylinder.liftFromProjections_fst]
    exact (originalSection_decorated F j hfirst hlast p).trans
      (JTCylinderOverTarget.lift_decorated W x y Q (L.obj p) (code (L := L) p)
        (time.obj p) (JTParametrizedTargetLiftTransport.graph (F.parameter p))
        (F.collapse.app p) (F.raw p)).symm
  · change ((originalSection F j hfirst hlast).app p ≫ _) ≫
      JTTargetCommaPullback.snd W x y Q (L.obj p) = _
    rw [Category.assoc]
    change (originalSection F j hfirst hlast).app p ≫
        ((originalCoveredLift F j hfirst hlast).app p ≫
          JTTargetCommaPullback.snd W x y Q (L.obj p)) = _
    rw [JTDecoratedIntervalCylinder.liftFromProjections_snd]
    have hOld := JTCylinderOverTarget.lift_native W x y Q (L.obj p) (code (L := L) p)
      (time.obj p) (JTParametrizedTargetLiftTransport.graph (F.parameter p))
      (F.collapse.app p) (F.raw p)
    refine Eq.trans ?_ hOld.symm
    have h : (originalSection F j hfirst hlast).app p ≫
        (originalProjection F j hfirst hlast).app p = 𝟙 _ :=
      NatTrans.congr_app (originalSection_projection F j hfirst hlast) p
    change (originalSection F j hfirst hlast).app p ≫
      (originalProjection F j hfirst hlast).app p ≫
        (JTDecoratedIntervalCylinder.native Q (native F) time).app p = _
    rw [← Category.assoc, h, Category.id_comp]
    apply Under.UnderMorphism.ext
    rfl

/-- The section retains each internal necklace and its original base. -/
def originalPresentationSection :
    JTParametrizedTargetFamilies.Presentation (L := L) (time := time) ⥤
      BoundaryNecklaceComma.Presentation (originalReduced F j hfirst hlast) :=
  Grothendieck.map (Functor.whiskerRight (originalSection F j hfirst hlast)
    BoundaryNecklaceComma.diagram)

/-- Evaluating after the section recovers the exact original functor. -/
theorem evaluate_originalSection :
    originalPresentationSection F j hfirst hlast ⋙
        evaluate F j (originalLeft F j) (originalRight F j) hfirst hlast
          (original_rawOn F (leftLeg F j)) (original_rawOn F (rightLeg F j)) =
      JTParametrizedTargetFamilies.evaluate F := by
  unfold originalPresentationSection evaluate JTDecoratedIntervalCylinder.evaluateFromProjections
    JTParametrizedTargetFamilies.evaluate JTBoundaryNecklacePresentationCone.mapPresentation
  simp only [← Functor.assoc]
  rw [← Grothendieck.map_comp_eq, ← Functor.whiskerRight_comp]
  rw [originalSection_lift F j hfirst hlast]

/-- The section is a strict section of the old presentation on all arrows. -/
theorem originalPresentationSection_projection :
    originalPresentationSection F j hfirst hlast ⋙
        presentationProjection F j (originalLeft F j) (originalRight F j) hfirst hlast = 𝟭 _ := by
  unfold originalPresentationSection presentationProjection
    JTBoundaryNecklacePresentationCone.mapPresentation
  change Grothendieck.map (Functor.whiskerRight (originalSection F j hfirst hlast)
      BoundaryNecklaceComma.diagram) ⋙ Grothendieck.map
      (Functor.whiskerRight (originalProjection F j hfirst hlast)
        BoundaryNecklaceComma.diagram) = _
  rw [← Grothendieck.map_comp_eq, ← Functor.whiskerRight_comp]
  change Grothendieck.map
      (Functor.whiskerRight (originalSection F j hfirst hlast ≫
        originalProjection F j hfirst hlast) BoundaryNecklaceComma.diagram) = _
  rw [originalSection_projection]
  have he : Functor.whiskerRight (𝟙 (cylinders F time)) BoundaryNecklaceComma.diagram =
      𝟙 (BoundaryNecklaceComma.fiberDiagram (cylinders F time)) :=
    Functor.whiskerRight_id _
  rw [he]
  exact Grothendieck.map_id_eq (F := BoundaryNecklaceComma.fiberDiagram (cylinders F time))

/-- Passing to the original section preserves the whole weak nerve type. -/
theorem originalPresentationSection_weak :
    WeakEquivalence (nerveMap (originalPresentationSection F j hfirst hlast)) := by
  let i := originalPresentationSection F j hfirst hlast
  let e := presentationProjection F j (originalLeft F j) (originalRight F j) hfirst hlast
  have hi : i ⋙ e = 𝟭 _ := originalPresentationSection_projection F j hfirst hlast
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap e) :=
    presentationProjection_weak F j (originalLeft F j) (originalRight F j) hfirst hlast
      (original_crossAgreement F j)
  have hid : nerveMap (𝟭 (JTParametrizedTargetFamilies.Presentation
      (L := L) (time := time))) = 𝟙 _ :=
    nerveFunctor.map_id (Cat.of (JTParametrizedTargetFamilies.Presentation (L := L) (time := time)))
  have h : nerveMap i ≫ nerveMap e = 𝟙 _ :=
    (nerveFunctor.map_comp i.toCatHom e.toCatHom).symm.trans
      ((congrArg nerveMap hi).trans hid)
  letI : WeakEquivalence (C := SSet.{0}) (nerveMap i ≫ nerveMap e) := by
    rw [h]
    infer_instance
  exact weakEquivalence_of_postcomp (nerveMap i) (nerveMap e)

end OriginalSection

end

end DaggerModels.PartII.JTCoveredJointCylinder
