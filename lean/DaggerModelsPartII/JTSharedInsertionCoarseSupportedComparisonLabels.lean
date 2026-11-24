import DaggerModelsPartII.JTSharedInsertionCoarseSupportedLabels
import DaggerModelsPartII.JTSharedInsertionCoarseDecoratedComparison
import DaggerModelsPartII.JTSupportedPathWhiskeredEndpointLabels

/-!
# Native restriction of the actual coarse supported path

Retain the full supported path coefficient, restricted along the existing
actual old-to-coarse native comparison. The source keeps every original old
native operator, and the comparison keeps the whole supported chain degree.
No product Family, raw equation, compatibility or parameter section is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionCoarseSupportedComparisonLabels

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev boundaryPoint := OrderedNecklaceVertexPoints.boundaryPoint
private abbrev projection (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev presheaf (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)

private instance {W : Source} {x y : Vertex W} : (projection W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private theorem wedgeIdentity (T U : NecklaceCode) :
    NecklaceCode.wedgeMap (𝟙 T) (𝟙 U) = 𝟙 (NecklaceCode.wedge T U) :=
  NecklaceCode.wedgeMap_id

section Restriction

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (N : I ⥤ NecklaceCode) (n : N ⟶ codes C)

private abbrev restrictedTag := N.prod' (degrees C)

private def restrictionOperator : restrictedTag C N ⟶ C ⋙ projection W x y where
  app p := (n.app p, 𝟙 _)
  naturality _ _ f := Prod.ext (n.naturality f)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private def restrictedPoint (p : I) :
    (presheaf W x y).obj (op ((restrictedTag C N).obj p)) :=
  (presheaf W x y).map ((restrictionOperator C N n).app p).op
    (OrderedLabelElements.label W (boundaryPoint W x y) (C.obj p))

private theorem restrictedPoint_natural {p q : I} (f : p ⟶ q) :
    (presheaf W x y).map ((restrictedTag C N).map f).op (restrictedPoint C N n q) =
      restrictedPoint C N n p := by
  unfold restrictedPoint
  rw [← FunctorToTypes.map_comp_apply, ← op_comp,
    (restrictionOperator C N n).naturality f]
  rw [op_comp, FunctorToTypes.map_comp_apply]
  exact congrArg ((presheaf W x y).map ((restrictionOperator C N n).app p).op)
    ((C.map f).unop.property)

private def restrictLabels : I ⥤ DecoratedNecklaceHomDiagram.Index W x y where
  obj p := op ⟨op ((restrictedTag C N).obj p), restrictedPoint C N n p⟩
  map f := Quiver.Hom.op ⟨((restrictedTag C N).map f).op, restrictedPoint_natural C N n f⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((restrictedTag C N).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((restrictedTag C N).map_comp f g)

private def restrictComparison : restrictLabels C N n ⟶ C where
  app p := Quiver.Hom.op ⟨((restrictionOperator C N n).app p).op, rfl⟩
  naturality _ _ f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((restrictionOperator C N n).naturality f)

private theorem restrictComparison_projection (p : I) :
    (projection W x y).map ((restrictComparison C N n).app p) = (n.app p, 𝟙 _) := rfl

private theorem restrictLabels_codes : codes (restrictLabels C N n) = N := rfl

private theorem restrictLabels_degrees : degrees (restrictLabels C N n) = degrees C := rfl

private theorem restrictComparison_native :
    JTWhiskeredSeamTarget.nativeOf (restrictComparison C N n) = n := rfl

private theorem restrictComparison_degree :
    JTParametrizedTargetFamilyComparison.coefficient (restrictComparison C N n) =
      𝟙 (degrees C) := rfl

private theorem restrictComparison_coefficient (p : I) :
    JTOrderedLabelBinaryGlue.coefficient W x y (N.obj p) ((degrees C).obj p)
        ((restrictLabels C N n).obj p).unop.2 =
      SSet.stdSimplex.map (𝟙 ((degrees C).obj p)) ≫
        JTOrderedLabelBinaryGlue.coefficient W x y ((codes C).obj p) ((degrees C).obj p)
          (C.obj p).unop.2 ≫
        diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map (n.app p).map) W :=
  JTOrderedLabelWedge.coefficient_of_indexHom _ _ _ _
    ((restrictComparison C N n).app p) (restrictComparison_projection C N n p)

end Restriction

section CartesianFactor

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {X N C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable (r : N ⟶ C) (f : X ⟶ C)
variable (a : X ⋙ projection W x y ⟶ N ⋙ projection W x y)
variable (ha : a ≫ Functor.whiskerRight r (projection W x y) =
  Functor.whiskerRight f (projection W x y))

include ha in
private def factorComparison : X ⟶ N where
  app p := Quiver.Hom.op ⟨(a.app p).op, by
    change (presheaf W x y).map (a.app p).op (N.obj p).unop.2 = (X.obj p).unop.2
    rw [← (r.app p).unop.property, ← FunctorToTypes.map_comp_apply]
    have h := NatTrans.congr_app ha p
    change a.app p ≫ (projection W x y).map (r.app p) =
      (projection W x y).map (f.app p) at h
    change (presheaf W x y).map
      ((a.app p ≫ (projection W x y).map (r.app p)).op) (C.obj p).unop.2 = _
    rw [h]
    exact (f.app p).unop.property⟩
  naturality _ _ g := by
    apply (projection W x y).map_injective
    change (X ⋙ projection W x y).map g ≫ a.app _ =
      a.app _ ≫ (N ⋙ projection W x y).map g
    exact a.naturality g

private theorem factorComparison_projection (p : I) :
    (projection W x y).map ((factorComparison r f a ha).app p) = a.app p := rfl

include ha in
private theorem factorComparison_comp : factorComparison r f a ha ≫ r = f := by
  apply NatTrans.ext
  funext p
  apply (projection W x y).map_injective
  exact NatTrans.congr_app ha p

end CartesianFactor

section OperatorFactor

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {X N C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}

private def pairedOperator (n : codes X ⟶ codes N) (d : degrees X ⟶ degrees N) :
    X ⋙ projection W x y ⟶ N ⋙ projection W x y where
  app p := (n.app p, d.app p)
  naturality _ _ g := Prod.ext (n.naturality g) (d.naturality g)

private theorem pairedOperator_square (r : N ⟶ C) (f : X ⟶ C)
    (n : codes X ⟶ codes N) (d : degrees X ⟶ degrees N)
    (hn : n ≫ JTWhiskeredSeamTarget.nativeOf r = JTWhiskeredSeamTarget.nativeOf f)
    (hd : d ≫ JTParametrizedTargetFamilyComparison.coefficient r =
      JTParametrizedTargetFamilyComparison.coefficient f) :
    pairedOperator n d ≫ Functor.whiskerRight r (projection W x y) =
      Functor.whiskerRight f (projection W x y) := by
  apply NatTrans.ext
  funext p
  exact Prod.ext (NatTrans.congr_app hn p) (NatTrans.congr_app hd p)

private def factorByOperators (r : N ⟶ C) (f : X ⟶ C)
    (n : codes X ⟶ codes N) (d : degrees X ⟶ degrees N)
    (hn : n ≫ JTWhiskeredSeamTarget.nativeOf r = JTWhiskeredSeamTarget.nativeOf f)
    (hd : d ≫ JTParametrizedTargetFamilyComparison.coefficient r =
      JTParametrizedTargetFamilyComparison.coefficient f) : X ⟶ N :=
  factorComparison r f (pairedOperator n d) (pairedOperator_square r f n d hn hd)

private theorem factorByOperators_comp (r : N ⟶ C) (f : X ⟶ C)
    (n : codes X ⟶ codes N) (d : degrees X ⟶ degrees N)
    (hn : n ≫ JTWhiskeredSeamTarget.nativeOf r = JTWhiskeredSeamTarget.nativeOf f)
    (hd : d ≫ JTParametrizedTargetFamilyComparison.coefficient r =
      JTParametrizedTargetFamilyComparison.coefficient f) :
    factorByOperators r f n d hn hd ≫ r = f :=
  factorComparison_comp r f (pairedOperator n d) (pairedOperator_square r f n d hn hd)

end OperatorFactor

private def nativeReindex {I B : Type} [SmallCategory I] [SmallCategory B]
    (b : B ⥤ I) {N C : I ⥤ NecklaceCode} {CP : B ⥤ NecklaceCode}
    (n : N ⟶ C) (e : CP = b ⋙ C) : b ⋙ N ⟶ CP :=
  Functor.whiskerLeft b n ≫ eqToHom e.symm

private theorem nativeReindex_congr {I B : Type} [SmallCategory I] [SmallCategory B]
    (b : B ⥤ I) {N C : I ⥤ NecklaceCode} {CP : B ⥤ NecklaceCode}
    (e : CP = b ⋙ C) {n n' : N ⟶ C} (h : n = n') :
    nativeReindex b n e = nativeReindex b n' e :=
  congrArg (fun v ↦ nativeReindex b v e) h

private def zeroToLabels {I : Type} [SmallCategory I] (W : Source)
    (x z y : Vertex W) (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
    (S : I ⥤ SimplexCategory) (u : S ⟶ degrees M)
    (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
      JTSupportedOrderedCoefficientChoices.old W z M p =
        JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)
    (P R : I ⥤ NecklaceCode) (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    (C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (e : JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O = C) :=
  JTSupportedPathWhiskeredEndpointLabels.zeroToOld W x z y M S u hs P R O ≫
    eqToHom (congrArg (fun D ↦
      (JTSupportedPathChainEndpoints.endpointSection W z M S u hs 0 ⋙
        JTSupportedPathChainLabels.toOriginal W z M S u hs) ⋙ D) e)

private def nativeAtPath {I : Type} [SmallCategory I] (W : Source)
    (x z y : Vertex W) (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
    (S : I ⥤ SimplexCategory) (u : S ⟶ degrees M)
    (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
      JTSupportedOrderedCoefficientChoices.old W z M p =
        JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)
    (P R : I ⥤ NecklaceCode) (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    {N C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ C)
    (e : JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O = C) :=
  Functor.whiskerLeft (JTSupportedPathChainLabels.toOriginal W z M S u hs)
    (JTWhiskeredSeamTarget.nativeOf (r ≫ eqToHom e.symm))

private theorem projectedComposition {W : Source} {x y : Vertex W}
    {X Y Z U : DecoratedNecklaceHomDiagram.Index W x y}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ U} {k : U ⟶ Z} (e : f ≫ g = h ≫ k) :
    (projection W x y).map f ≫ (projection W x y).map g =
      (projection W x y).map h ≫ (projection W x y).map k := by
  simpa only [(projection W x y).map_comp] using congrArg (projection W x y).map e

section PathRestriction

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (S : I ⥤ SimplexCategory)
variable (u : S ⟶ degrees M)
variable (hs : ∀ p : I, SSet.stdSimplex.map (u.app p) ≫
  JTSupportedOrderedCoefficientChoices.old W z M p =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z M S p)
variable (P R : I ⥤ NecklaceCode)
variable (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
variable {N C : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ C)
variable (e : JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O = C)

private abbrev pathBase := JTSupportedPathChainLabels.toOriginal W z M S u hs
private abbrev pathTarget := JTSupportedPathWhiskeredDiagram.labels W x z y M S u hs P R O
private abbrev pathNative := nativeAtPath W x z y M S u hs P R O r e

private def zeroBaseAtPath :=
  JTSupportedPathChainEndpoints.endpointSection W z M S u hs 0 ⋙ pathBase W z M S u hs

private def proofAtZero {H : I → Prop} (h : ∀ q : I, H q)
    (p : JTSupportedPathChainLabels.First W z M S u hs) :=
  h ((zeroBaseAtPath W z M S u hs).obj p)

include e in
private theorem pathCodesToTarget :
    codes (pathTarget W x z y M S u hs P R O) = pathBase W z M S u hs ⋙ codes C :=
  (JTSupportedPathWhiskeredGraph.code_reindex W x z y M S u hs P R O).trans
    (congrArg (fun D ↦ pathBase W z M S u hs ⋙ codes D) e)

private theorem zeroTargetProjection (p : JTSupportedPathChainLabels.First W z M S u hs) :
    HEq ((projection W x y).map ((zeroToLabels W x z y M S u hs P R O C e).app p))
      (𝟙 ((codes (JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O)).obj
          ((zeroBaseAtPath W z M S u hs).obj p)),
        (JTSupportedPathChainEndpoints.endpointDegree W z M S u hs 0).app p) := by
  subst C
  have hp := JTSupportedPathWhiskeredEndpointLabels.zeroToOld_projection
    W x z y M S u hs P R O p
  change (projection W x y).map
      ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld W x z y M S u hs P R O).app p) =
    (NecklaceCode.wedgeMap
      (𝟙 (P.obj ((zeroBaseAtPath W z M S u hs).obj p)))
      (NecklaceCode.wedgeMap
        (𝟙 ((codes M).obj ((zeroBaseAtPath W z M S u hs).obj p)))
        (𝟙 (R.obj ((zeroBaseAtPath W z M S u hs).obj p)))),
      (JTSupportedPathChainEndpoints.endpointDegree W z M S u hs 0).app p) at hp
  rw [wedgeIdentity, wedgeIdentity] at hp
  simpa only [zeroToLabels, eqToHom_refl, Category.comp_id] using heq_of_eq hp

private theorem nativeAtPath_transport : pathNative W x z y M S u hs P R O r e =
    nativeReindex (pathBase W z M S u hs) (JTWhiskeredSeamTarget.nativeOf r)
      (pathCodesToTarget W x z y M S u hs P R O e) := by
  subst C
  simp only [pathNative, nativeAtPath, nativeReindex, eqToHom_refl, Category.comp_id]

private theorem nativeAtPath_original {n : codes N ⟶ codes C}
    (hn : JTWhiskeredSeamTarget.nativeOf r = n) :
    pathNative W x z y M S u hs P R O r e =
      nativeReindex (pathBase W z M S u hs) n
        (pathCodesToTarget W x z y M S u hs P R O e) :=
  (nativeAtPath_transport W x z y M S u hs P R O r e).trans
    (nativeReindex_congr (pathBase W z M S u hs)
      (pathCodesToTarget W x z y M S u hs P R O e) hn)

private def labelsAtPath := restrictLabels (pathTarget W x z y M S u hs P R O)
  (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private def comparisonAtPath := restrictComparison (pathTarget W x z y M S u hs P R O)
  (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private theorem codesAtPath : codes (labelsAtPath W x z y M S u hs P R O r e) =
    pathBase W z M S u hs ⋙ codes N :=
  restrictLabels_codes (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private theorem degreesAtPath : degrees (labelsAtPath W x z y M S u hs P R O r e) =
    degrees (pathTarget W x z y M S u hs P R O) :=
  restrictLabels_degrees (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private theorem nativeAtPath_projection :
    JTWhiskeredSeamTarget.nativeOf (comparisonAtPath W x z y M S u hs P R O r e) =
      pathNative W x z y M S u hs P R O r e :=
  restrictComparison_native (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private theorem degreeAtPath :
    JTParametrizedTargetFamilyComparison.coefficient
        (comparisonAtPath W x z y M S u hs P R O r e) =
      𝟙 (degrees (pathTarget W x z y M S u hs P R O)) :=
  restrictComparison_degree (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e)

private def operatorsAtPath (p : JTSupportedPathChainLabels.Index W z M S u hs) :=
  restrictComparison_projection (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e) p

private def coefficientAtPath (p : JTSupportedPathChainLabels.Index W z M S u hs) :=
  restrictComparison_coefficient (pathTarget W x z y M S u hs P R O)
    (pathBase W z M S u hs ⋙ codes N) (pathNative W x z y M S u hs P R O r e) p

private abbrev zeroSectionAtPath :=
  JTSupportedPathChainEndpoints.endpointSection W z M S u hs 0
private abbrev zeroOriginal := Functor.whiskerLeft (zeroBaseAtPath W z M S u hs)
  (r ≫ eqToHom e.symm)
private abbrev zeroComposite :=
  Functor.whiskerLeft (zeroSectionAtPath W z M S u hs)
      (comparisonAtPath W x z y M S u hs P R O r e) ≫
    JTSupportedPathWhiskeredEndpointLabels.zeroToOld W x z y M S u hs P R O

variable [hiso : IsIso (JTParametrizedTargetFamilyComparison.coefficient (r ≫ eqToHom e.symm))]

include hiso in
private theorem zeroOriginal_degree_isIso : IsIso
    (JTParametrizedTargetFamilyComparison.coefficient
      (zeroOriginal W x z y M S u hs P R O r e)) := by
  change IsIso (Functor.whiskerLeft (zeroBaseAtPath W z M S u hs)
    (JTParametrizedTargetFamilyComparison.coefficient (r ≫ eqToHom e.symm)))
  infer_instance

attribute [local instance] zeroOriginal_degree_isIso

include hiso in
private def zeroDegreeAtPath :=
  JTParametrizedTargetFamilyComparison.coefficient (zeroComposite W x z y M S u hs P R O r e) ≫
    inv (JTParametrizedTargetFamilyComparison.coefficient
      (zeroOriginal W x z y M S u hs P R O r e))

omit hiso in
private theorem zeroNativeFactor :
    𝟙 (zeroBaseAtPath W z M S u hs ⋙ codes N) ≫
        JTWhiskeredSeamTarget.nativeOf (zeroOriginal W x z y M S u hs P R O r e) =
      JTWhiskeredSeamTarget.nativeOf (zeroComposite W x z y M S u hs P R O r e) := by
  apply NatTrans.ext
  funext p
  change 𝟙 _ ≫ ((projection W x y).map
      ((r ≫ eqToHom e.symm).app ((zeroBaseAtPath W z M S u hs).obj p))).1 =
    ((projection W x y).map
      (((comparisonAtPath W x z y M S u hs P R O r e).app
          ((zeroSectionAtPath W z M S u hs).obj p)) ≫
        ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
          W x z y M S u hs P R O).app p))).1
  have hp : (projection W x y).map
      ((comparisonAtPath W x z y M S u hs P R O r e).app
        ((zeroSectionAtPath W z M S u hs).obj p)) =
      ((pathNative W x z y M S u hs P R O r e).app
        ((zeroSectionAtPath W z M S u hs).obj p), 𝟙 _) :=
    operatorsAtPath W x z y M S u hs P R O r e _
  rw [(projection W x y).map_comp, hp,
    JTSupportedPathWhiskeredEndpointLabels.zeroToOld_projection]
  simp only [prod_comp_fst, Category.id_comp]
  rw [wedgeIdentity, wedgeIdentity]
  change ((projection W x y).map
      ((r ≫ eqToHom e.symm).app ((zeroBaseAtPath W z M S u hs).obj p))).1 =
    ((projection W x y).map
      ((r ≫ eqToHom e.symm).app ((zeroBaseAtPath W z M S u hs).obj p))).1 ≫ 𝟙 _
  exact (Category.comp_id _).symm

include hiso in
private theorem zeroDegreeFactor : zeroDegreeAtPath W x z y M S u hs P R O r e ≫
    JTParametrizedTargetFamilyComparison.coefficient
        (zeroOriginal W x z y M S u hs P R O r e) =
      JTParametrizedTargetFamilyComparison.coefficient
        (zeroComposite W x z y M S u hs P R O r e) := by
  rw [zeroDegreeAtPath, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include hiso in
private def zeroComparisonAtPath := factorByOperators
  (zeroOriginal W x z y M S u hs P R O r e) (zeroComposite W x z y M S u hs P R O r e)
  (𝟙 (zeroBaseAtPath W z M S u hs ⋙ codes N)) (zeroDegreeAtPath W x z y M S u hs P R O r e)
  (zeroNativeFactor W x z y M S u hs P R O r e) (zeroDegreeFactor W x z y M S u hs P R O r e)

include hiso in
private theorem zeroSquareAtPath :
    Functor.whiskerLeft (zeroSectionAtPath W z M S u hs)
        (comparisonAtPath W x z y M S u hs P R O r e) ≫
      zeroToLabels W x z y M S u hs P R O C e =
    zeroComparisonAtPath W x z y M S u hs P R O r e ≫
      Functor.whiskerLeft (zeroBaseAtPath W z M S u hs) r := by
  have h := (factorByOperators_comp
    (zeroOriginal W x z y M S u hs P R O r e) (zeroComposite W x z y M S u hs P R O r e)
    (𝟙 (zeroBaseAtPath W z M S u hs ⋙ codes N)) (zeroDegreeAtPath W x z y M S u hs P R O r e)
    (zeroNativeFactor W x z y M S u hs P R O r e)
    (zeroDegreeFactor W x z y M S u hs P R O r e)).symm
  subst C
  simpa only [zeroOriginal, zeroComposite, zeroToLabels, eqToHom_refl,
    Category.comp_id] using h

include hiso in
private def zeroProjectedAtPath (p : JTSupportedPathChainLabels.First W z M S u hs) :=
  projectedComposition
    (NatTrans.congr_app (zeroSquareAtPath W x z y M S u hs P R O r e) p)

include hiso in
private theorem zeroComparisonAtPath_projection
    (p : JTSupportedPathChainLabels.First W z M S u hs) :
    (projection W x y).map ((zeroComparisonAtPath W x z y M S u hs P R O r e).app p) =
      (𝟙 _, (zeroDegreeAtPath W x z y M S u hs P R O r e).app p) := rfl

include hiso in
private theorem zeroDegreeSquareAtPath
    (p : JTSupportedPathChainLabels.First W z M S u hs) :
    (zeroDegreeAtPath W x z y M S u hs P R O r e).app p ≫
        ((projection W x y).map (r.app ((zeroBaseAtPath W z M S u hs).obj p))).2 =
      ((projection W x y).map ((zeroToLabels W x z y M S u hs P R O C e).app p)).2 := by
  have h := congrArg Prod.snd (zeroProjectedAtPath W x z y M S u hs P R O r e p)
  change ((projection W x y).map
        ((comparisonAtPath W x z y M S u hs P R O r e).app
          ((zeroSectionAtPath W z M S u hs).obj p))).2 ≫
      ((projection W x y).map ((zeroToLabels W x z y M S u hs P R O C e).app p)).2 =
    ((projection W x y).map ((zeroComparisonAtPath W x z y M S u hs P R O r e).app p)).2 ≫
      ((projection W x y).map (r.app ((zeroBaseAtPath W z M S u hs).obj p))).2 at h
  have hp : (projection W x y).map
      ((comparisonAtPath W x z y M S u hs P R O r e).app
        ((zeroSectionAtPath W z M S u hs).obj p)) =
      ((pathNative W x z y M S u hs P R O r e).app
        ((zeroSectionAtPath W z M S u hs).obj p), 𝟙 _) :=
    operatorsAtPath W x z y M S u hs P R O r e _
  rw [hp, zeroComparisonAtPath_projection W x z y M S u hs P R O r e] at h
  simpa only [Category.id_comp] using h.symm

end PathRestriction

private theorem isIsoFromEq {C : Type} [Category C] {X Y : C}
    {f g : X ⟶ Y} (h : f = g) (hg : IsIso g) : IsIso f := by
  rw [h]
  exact hg

private theorem identityIso {C : Type} [Category C] (X : C) : IsIso (𝟙 X) := by
  infer_instance

private theorem retargetDegreeIso {I : Type} [SmallCategory I] {W : Source}
    {x y : Vertex W} {N C D : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    (r : N ⟶ C) (e : D = C) (hi : IsIso (JTParametrizedTargetFamilyComparison.coefficient r)) :
    IsIso (JTParametrizedTargetFamilyComparison.coefficient (r ≫ eqToHom e.symm)) := by
  letI := hi
  change IsIso (Functor.whiskerRight (r ≫ eqToHom e.symm)
    (projection W x y ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory))
  rw [Functor.whiskerRight_comp]
  infer_instance

private theorem closeDegreeSquare {a b : SimplexCategory}
    {q s t : a ⟶ b} {r : b ⟶ b} (h : q ≫ r = s) (hr : r = 𝟙 b) (hs : s = t) :
    q = t := by
  rw [hr, Category.comp_id] at h
  exact h.trans hs

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j

/-- The exact actual supported-path choice category, including both full chains. -/
abbrev Index := JTSharedInsertionCoarseSupportedLabels.Index F j

/-- Retain the original shared insertion choices and every original operator. -/
abbrev toChoices := JTSharedInsertionCoarseSupportedLabels.toChoices F j

/-- The existing complete actual coarse supported path, with global endpoints x,y. -/
abbrev coarsePathLabels := JTSharedInsertionCoarseSupportedLabels.labels F j

/-- The actual corrected old split, without changing its whole coefficient. -/
abbrev oldLabels := (JTSharedInsertionNormalizedSeam.oldFamily F j).labels

/-- The exact native operator into the supported path, with the explicit code transport. -/
def native := nativeAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The restriction is EXACTLY the frozen original native comparison with code transport. -/
def native_eq_original := nativeAtPath_original
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)
  (JTSharedInsertionCoarseDecoratedComparison.native_comparison F j)

/-- The full actual path coefficient restricted to the original old native code. -/
def labels := labelsAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The whole native restriction maps naturally to the SAME actual coarse path. -/
def comparison := comparisonAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- Every original old native operator is retained throughout the supported path. -/
def codes_reindex := codesAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The source and target use exactly the SAME full supported coefficient degree. -/
def degrees_eq := degreesAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The comparison's projected native map is precisely the actual native restriction. -/
def comparison_native := nativeAtPath_projection W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- Its coefficient operator is the literal identity on the whole supported degree. -/
def comparison_degree := degreeAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- Both complete operators are preserved at each actual supported-path object. -/
def comparison_projection (p : Index F j) := operatorsAtPath
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j) p

/-- The source's ENTIRE ordered coefficient is the native restriction of the target's. -/
def coefficient (p : Index F j) := coefficientAtPath
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j) p

/-- The entire first path-choice chain, before inserting the contraction endpoint. -/
abbrev ZeroIndex := JTSupportedPathChainLabels.First
  W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- Insert the SAME complete first chain at path time zero. -/
abbrev zeroSection := JTSupportedPathChainEndpoints.endpointSection
  W (z j) (M F j) (S F j) (u F j) (hs F j) 0

/-- The unchanged original insertion choices beneath the full zero endpoint. -/
abbrev zeroBase := zeroBaseAtPath W (z j) (M F j) (S F j) (u F j) (hs F j)

/-- The full time-zero target comparison lands in the EXACT actual coarse labels. -/
def zeroToCoarse := zeroToLabels W x (z j) y (M F j) (S F j) (u F j) (hs F j)
  (P F j) (R F j) (O F j) (JTSharedInsertionCoarseLabels.labels F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

private def actualDegreeIso := retargetDegreeIso
  (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
  (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)
  (isIsoFromEq (JTSharedInsertionCoarseDecoratedComparison.coefficient_comparison F j)
    (identityIso (JTSharedInsertionChoices.ordinals F j)))

/-- The full time-zero restricted path maps to the EXACT actual corrected old labels. -/
def zeroToOld :=
  letI := actualDegreeIso F j
  zeroComparisonAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
    (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
    (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The original old-to-coarse comparison is recovered on the ENTIRE zero face. -/
def zero_square :=
  letI := actualDegreeIso F j
  zeroSquareAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
    (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
    (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j)

/-- The zero comparison retains the literal native identity and its exact degree operator. -/
def zero_projection (p : ZeroIndex F j) :=
  letI := actualDegreeIso F j
  zeroComparisonAtPath_projection W x (z j) y (M F j) (S F j) (u F j) (hs F j)
    (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
    (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j) p

/-- The coarse zero face has the original native identity and exact endpoint degree. -/
def zero_target_projection (p : ZeroIndex F j) := eq_of_heq
  (zeroTargetProjection W x (z j) y (M F j) (S F j) (u F j) (hs F j)
    (P F j) (R F j) (O F j) (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j) p)

private def actualDegreeComponents (p : JTSharedInsertionChoices.Index F j) :=
  congrArg Prod.snd (JTSharedInsertionCoarseDecoratedComparison.projection_app F j p)

private def actualDegreeAtZero (p : ZeroIndex F j) :=
  proofAtZero W (z j) (M F j) (S F j) (u F j) (hs F j)
    (actualDegreeComponents F j) p

/-- The old zero comparison uses EXACTLY the original complete endpoint coefficient map. -/
def zero_degree (p : ZeroIndex F j) :=
  (congrArg Prod.snd (zero_projection F j p)).trans (by
    letI := actualDegreeIso F j
    have h := zeroDegreeSquareAtPath W x (z j) y (M F j) (S F j) (u F j) (hs F j)
      (P F j) (R F j) (O F j) (JTSharedInsertionCoarseDecoratedComparison.comparison F j)
      (JTSharedInsertionCoarseWhiskeredData.oldLabels_eq F j) p
    have hc := congrArg Prod.snd (zero_target_projection F j p)
    have hr := actualDegreeAtZero F j p
    exact closeDegreeSquare h hr hc)


end
end DaggerModels.PartII.JTSharedInsertionCoarseSupportedComparisonLabels
