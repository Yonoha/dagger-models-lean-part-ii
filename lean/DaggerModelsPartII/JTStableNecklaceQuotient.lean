import DaggerModelsPartII.JTStableEndpointQuotient
import DaggerModelsPartII.JTNativeNormalizationEpi
import DaggerModelsPartII.JTTargetCommaPullback
import OriginalProductNormalizedMono
import DaggerModelsPartII.GrothendieckContractibleFibers
import ActualNecklaceConeGadgetComparison
import NativeGroupoidCompletionNerveBaseCases

/-! Finite outgoing observations have a literal normalized necklace representative. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification DaggerSSetGluing
open HomotopicalAlgebra
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen
open DaggerModels.PartII.BoundaryNecklaceComma (necklaceUnder)
open scoped DaggerModels.PartII.JTStableEndpointQuotient

namespace DaggerModels.PartII.JTStableNecklaceQuotient

noncomputable section

variable {I : Type} [SmallCategory I] [∀ p : I,
  Finite (JTStableEndpointQuotient.Ends p)]
variable (E : I ⥤ NecklaceCode) (U : I → NecklaceCode)
variable (r : ∀ p, E.obj p ⟶ U p)

private abbrev X := E ⋙ necklaceUnder
private abbrev Y (U : I → NecklaceCode) : I → Under JTXiEndpointCollapse.boundary :=
  fun p ↦ necklaceUnder.obj (U p)
private abbrev q (r : ∀ p, E.obj p ⟶ U p) (p : I) :
    (X E).obj p ⟶ Y U p := necklaceUnder.map (r p)

private abbrev Out (p : I) := JTStableEndpointQuotient.Ends p

private instance outFintype (p : I) : Fintype (Out p) := Fintype.ofFinite _

private instance : HasStrongEpiMonoFactorisations SSet.{0} :=
  inferInstanceAs (HasStrongEpiMonoFactorisations (SimplexCategoryᵒᵖ ⥤ Type))

private def enumeration (p : I) : Fin (Fintype.card (Out p)) ≃ Out p :=
  (Fintype.equivFin (Out p)).symm

private def factors (p : I) : Fin (Fintype.card (Out p)) → NecklaceCode :=
  fun i ↦ U ((enumeration p) i).1

/-- Identify the observed product with the original finite product of necklace codes. -/
def productIso (p : I) :
    (JTStableEndpointQuotient.products (Y U)).obj p ≅
      DaggerOriginalProductGadget.productSpace
        (Fintype.card (Out p)) (factors U p) :=
  (Pi.reindex (enumeration p) (JTStableEndpointQuotient.factors (Y U) p)).symm

/-- The actual source necklace maps into the reindexed product of all observations. -/
def observedMap (p : I) : (E.obj p).toSSet ⟶
    DaggerOriginalProductGadget.productSpace
      (Fintype.card (Out p)) (factors U p) :=
  (JTStableEndpointQuotient.probes (X E) (Y U) (q E U r)).app p ≫
    (productIso U p).hom

private def start (p : I) := (observedMap E U r p).app (op ⦋0⦌) (E.obj p).first
private def finish (p : I) := (observedMap E U r p).app (op ⦋0⦌) (E.obj p).last

/-- The original, unnormalized source in the finite product target. -/
def observedNecklace (p : I) :
    NecklacesOver
      (DaggerOriginalProductGadget.productSpace
        (Fintype.card (Out p)) (factors U p))
      (start E U r p) (finish E U r p) where
  code := E.obj p
  map := observedMap E U r p
  first := rfl
  last := rfl

/-- The literal normalized necklace code representing the stable image. -/
def normalizedCode (p : I) : NecklaceCode :=
  (normOver (observedNecklace E U r p)).code

private def normalizedInProduct (p : I) :
    (normalizedCode E U r p).toSSet ⟶
      (JTStableEndpointQuotient.products (Y U)).obj p :=
  (normOver (observedNecklace E U r p)).map ≫ (productIso U p).inv

private theorem normalized_factor (p : I) :
    (originalNormalization (observedNecklace E U r p)).hom.map ≫
      normalizedInProduct E U r p =
      (JTStableEndpointQuotient.probes (X E) (Y U) (q E U r)).app p := by
  dsimp [normalizedInProduct]
  rw [← Category.assoc, originalNormalization_triangle]
  change ((JTStableEndpointQuotient.probes (X E) (Y U) (q E U r)).app p ≫
      (productIso U p).hom) ≫ (productIso U p).inv = _
  simp

private instance normalized_mono (p : I) : Mono (normalizedInProduct E U r p) := by
  dsimp [normalizedInProduct]
  haveI : Mono (normOver (observedNecklace E U r p)).map :=
    DaggerOriginalProductGadget.normOver_product_mono _
  infer_instance

private instance normalization_strongEpi (p : I) :
    StrongEpi (originalNormalization (observedNecklace E U r p)).hom.map := by
  haveI : Epi (originalNormalization (observedNecklace E U r p)).hom.map :=
    JTNativeNormalizationEpi.originalNormalization_epi _
  exact strongEpi_of_epi _

/-- The normalized code is the actual image of the simultaneous probe. -/
def normalizedImageIso (p : I) :
    (normalizedCode E U r p).toSSet ≅
      (JTStableEndpointQuotient.images (X E) (Y U) (q E U r)).obj p :=
  image.isoStrongEpiMono
    (originalNormalization (observedNecklace E U r p)).hom.map
    (normalizedInProduct E U r p) (normalized_factor E U r p)

/-- The original normalization is an arrow under the ordered boundary. -/
def normalizationUnder (p : I) :
    (X E).obj p ⟶ necklaceUnder.obj (normalizedCode E U r p) :=
  necklaceUnder.map (originalNormalization (observedNecklace E U r p)).hom

theorem quotient_right_eq (p : I) :
    ((JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r)).app p).right =
      (normalizationUnder E U r p).right ≫ (normalizedImageIso E U r p).hom := by
  let v := (JTStableEndpointQuotient.probes (X E) (Y U) (q E U r)).app p
  change factorThruImage v =
    (originalNormalization (observedNecklace E U r p)).hom.map ≫
      (normalizedImageIso E U r p).hom
  apply (cancel_mono (image.ι v)).mp
  rw [Category.assoc]
  have hi := image.isoStrongEpiMono_hom_comp_ι
    (originalNormalization (observedNecklace E U r p)).hom.map
    (normalizedInProduct E U r p) (normalized_factor E U r p)
  change (normalizedImageIso E U r p).hom ≫ image.ι v =
    normalizedInProduct E U r p at hi
  rw [hi, image.fac]
  exact (normalized_factor E U r p).symm

/-- The image isomorphism respects the fixed ordered boundary. -/
def normalizedUnderIso (p : I) :
    necklaceUnder.obj (normalizedCode E U r p) ≅
      (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).obj p :=
  Under.isoMk (normalizedImageIso E U r p) (by
    calc
      (necklaceUnder.obj (normalizedCode E U r p)).hom ≫
          (normalizedImageIso E U r p).hom =
        (((X E).obj p).hom ≫ (normalizationUnder E U r p).right) ≫
          (normalizedImageIso E U r p).hom := by
          rw [Under.w (normalizationUnder E U r p)]
      _ = ((X E).obj p).hom ≫ ((normalizationUnder E U r p).right ≫
          (normalizedImageIso E U r p).hom) := Category.assoc _ _ _
      _ = ((X E).obj p).hom ≫
          ((JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r)).app p).right :=
        congrArg (fun f ↦ ((X E).obj p).hom ≫ f)
          (quotient_right_eq E U r p).symm
      _ = ((JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).obj p).hom :=
        Under.w ((JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r)).app p))

theorem quotient_eq_normalization (p : I) :
    (JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r)).app p =
      normalizationUnder E U r p ≫ (normalizedUnderIso E U r p).hom := by
  apply Under.UnderMorphism.ext
  exact quotient_right_eq E U r p

/-- Transport every stable image arrow to an original necklace-code morphism. -/
def normalizedDiagram : I ⥤ NecklaceCode where
  obj p := normalizedCode E U r p
  map {p p'} f := JTTargetCommaPullback.nativeArrow
    ((normalizedUnderIso E U r p).hom ≫
      (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map f ≫
      (normalizedUnderIso E U r p').inv)
  map_id p := by
    apply NecklaceCode.Hom.ext
    have h : necklaceUnder.map (JTTargetCommaPullback.nativeArrow
        ((normalizedUnderIso E U r p).hom ≫
          (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map (𝟙 p) ≫
          (normalizedUnderIso E U r p).inv)) =
        𝟙 (necklaceUnder.obj (normalizedCode E U r p)) := by
      rw [JTTargetCommaPullback.map_nativeArrow,
        (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map_id]
      simp
    exact congrArg (fun k ↦ k.right) h

  map_comp {p p' p''} f g := by
    apply NecklaceCode.Hom.ext
    have h : necklaceUnder.map (JTTargetCommaPullback.nativeArrow
        ((normalizedUnderIso E U r p).hom ≫
          (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map (f ≫ g) ≫
          (normalizedUnderIso E U r p'').inv)) =
        necklaceUnder.map (JTTargetCommaPullback.nativeArrow
          ((normalizedUnderIso E U r p).hom ≫
            (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map f ≫
            (normalizedUnderIso E U r p').inv) ≫
          JTTargetCommaPullback.nativeArrow
          ((normalizedUnderIso E U r p').hom ≫
            (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map g ≫
            (normalizedUnderIso E U r p'').inv)) := by
      rw [JTTargetCommaPullback.map_nativeArrow, necklaceUnder.map_comp,
        JTTargetCommaPullback.map_nativeArrow, JTTargetCommaPullback.map_nativeArrow,
        (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map_comp]
      simp [Category.assoc]
    exact congrArg (fun k ↦ k.right) h

/-- The simultaneous stable image diagram is represented by original codes. -/
def diagramIso : normalizedDiagram E U r ⋙ necklaceUnder ≅
    JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r) :=
  NatIso.ofComponents (normalizedUnderIso E U r) (by
    intro p p' f
    change necklaceUnder.map (JTTargetCommaPullback.nativeArrow
        ((normalizedUnderIso E U r p).hom ≫
          (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map f ≫
          (normalizedUnderIso E U r p').inv)) ≫
          (normalizedUnderIso E U r p').hom =
        (normalizedUnderIso E U r p).hom ≫
          (JTStableEndpointQuotient.diagram (X E) (Y U) (q E U r)).map f
    rw [JTTargetCommaPullback.map_nativeArrow]
    simp [Category.assoc])

/-- The quotient itself is natural as a transformation of original necklace codes. -/
def normalizedQuotient : E ⟶ normalizedDiagram E U r where
  app p := (originalNormalization (observedNecklace E U r p)).hom
  naturality {p p'} f := by
    let ρ := JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r) ≫
      (diagramIso E U r).inv
    have hρ (j : I) : ρ.app j = normalizationUnder E U r j := by
      change (JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r)).app j ≫
        (normalizedUnderIso E U r j).inv = normalizationUnder E U r j
      rw [quotient_eq_normalization]
      simp
    have h := ρ.naturality f
    rw [hρ, hρ] at h
    exact NecklaceCode.Hom.ext (congrArg (fun m ↦ m.right) h)

/-- Under the boundary, the original quotient is recovered via the representative isomorphism. -/
theorem normalizedQuotient_iso :
    Functor.whiskerRight (normalizedQuotient E U r) necklaceUnder ≫
      (diagramIso E U r).hom =
      JTStableEndpointQuotient.quotient (X E) (Y U) (q E U r) := by
  apply NatTrans.ext
  funext p
  exact (quotient_eq_normalization E U r p).symm


section Fibers

private abbrev B := JTXiEndpointCollapse.boundary

/-- An object represented by an actual necklace under the given ordered
boundary has a weakly contractible complete internal-necklace category. -/
theorem fiber_point_GW_of_iso {A : Under B} (T : NecklaceCode)
    (e : BoundaryNecklaceComma.necklaceUnder.obj T ≅ A) :
    GW (pointMap (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder A))) := by
  let U := BoundaryNecklaceComma.necklaceUnder.obj T
  let e₁ := Cat.equivOfIso (BoundaryNecklaceComma.diagram.mapIso e.symm)
  let e₂ := BoundaryNecklaceComma.equivalence U
  have hf : BoundaryNecklaceComma.first U = T.first :=
    congrArg Prod.fst ((JTEndpointObjects.boundaryHomEquiv T.toSSet).apply_symm_apply
      (T.first, T.last))
  have hl : BoundaryNecklaceComma.last U = T.last :=
    congrArg Prod.snd ((JTEndpointObjects.boundaryHomEquiv T.toSSet).apply_symm_apply
      (T.first, T.last))
  let a := (e₁.trans e₂).functor
  haveI : WeakEquivalence (nerveMap a) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence a
  have hw : GW (pointMap (nerve (NecklacesOver U.right
      (BoundaryNecklaceComma.first U) (BoundaryNecklaceComma.last U)))) := by
    rw [hf, hl]
    exact DaggerActualNecklaceConeGadgetComparison.necklace_point_GW T
  haveI : WeakEquivalence (pointMap (nerve (NecklacesOver U.right
      (BoundaryNecklaceComma.first U) (BoundaryNecklaceComma.last U)))) :=
    (weakEquivalence_iff_GW _).mpr hw
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence (pointMap (nerve (↑(BoundaryNecklaceComma.diagram.obj A) : Type)))
  rw [← pointIsTerminal.hom_ext (nerveMap a ≫ pointMap _) (pointMap _)]
  infer_instance

/-- The complete necklace presentation of a diagram represented objectwise
by necklaces has the weak nerve type of the original indexing category. -/
theorem forget_weak_of_necklace_iso {I : Type} [SmallCategory I]
    (E : I ⥤ Under B)
    (h : ∀ p, ∃ T : NecklaceCode, Nonempty (BoundaryNecklaceComma.necklaceUnder.obj T ≅ E.obj p)) :
    WeakEquivalence (nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram E))) := by
  apply GrothendieckContractibleFibers.projection_weak
  intro p
  obtain ⟨T, ⟨e⟩⟩ := h p
  exact fiber_point_GW_of_iso T e

end Fibers

end
end DaggerModels.PartII.JTStableNecklaceQuotient
