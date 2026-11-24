import DaggerModelsPartII.JTSimplicialTargetRowGraphResolution
import DaggerModelsPartII.JTNativeTargetKanWeak
import DaggerModelsPartII.JTParametrizedBeadGraphTargetResolution
import DaggerModelsPartII.JTParametrizedBeadGraphTimeMapOperators
import DaggerModelsPartII.JTParametrizedProductSimplices

/-! The entire diagram of simplices of the original prism products maps to
the exact face resolution of a one-bead target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTRowGraphFaceResolution (Resolution)
open JTParametrizedProductSimplices (degree simplex simplex_natural)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
variable (L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : A ⥤ SimplexCategory)

/-- The original two-coordinate diagram before either endpoint line is collapsed. -/
abbrev products : A ⥤ SSet.{0} :=
  (((codes L) ⋙ NecklaceCode.simplicialFunctor).prod' (time ⋙ J)) ⋙ tensor SSet.{0}

abbrev ProductIndex := JTParametrizedProductSimplices.Index (products L time)

variable {L time}
variable (F : Family Q L time) {n : ℕ} (r : Q.code.toSSet ≅ (Δ[n] : SSet.{0}))

private abbrev X := products L time
private abbrev dim (P : ProductIndex L time) := ((degree (X (L := L) (time := time))).obj P).len
private abbrev codeAt (P : ProductIndex L time) := ((codes L).obj P.base).toSSet
private abbrev timeAt (P : ProductIndex L time) := J.obj (time.obj P.base)

private def codeMap (P : ProductIndex L time) :
    (NecklaceCode.single (dim P)).toSSet ⟶ codeAt P :=
  (NecklaceCode.singleIso (dim P)).hom ≫ simplex (X (L := L) (time := time)) P ≫ fst _ _

private def timeMap (P : ProductIndex L time) :
    (NecklaceCode.single (dim P)).toSSet ⟶ timeAt P :=
  (NecklaceCode.singleIso (dim P)).hom ≫ simplex (X (L := L) (time := time)) P ≫ snd _ _

private abbrev u {P Q : ProductIndex L time} (f : P ⟶ Q) :=
  (degree (X (L := L) (time := time))).map f

private theorem codeComm {P Q : ProductIndex L time} (f : P ⟶ Q) :
    (NecklaceCode.singleIso (dim P)).inv ≫ codeMap P ≫ ((codes L).map f.base).map =
      SSet.stdSimplex.map (u f) ≫ (NecklaceCode.singleIso (dim Q)).inv ≫ codeMap Q := by
  have h := congrArg (· ≫ fst (codeAt Q) (timeAt Q))
    (simplex_natural (X (L := L) (time := time)) f)
  change (simplex _ P ≫ (((codes L).map f.base).map ⊗ₘ J.map (time.map f.base))) ≫
    fst (codeAt Q) (timeAt Q) = _ at h
  simpa only [codeMap, Category.assoc, Iso.inv_hom_id_assoc, tensorHom_fst] using h

private theorem timeComm {P Q : ProductIndex L time} (f : P ⟶ Q) :
    (NecklaceCode.singleIso (dim P)).inv ≫ timeMap P ≫ J.map (time.map f.base) =
      SSet.stdSimplex.map (u f) ≫ (NecklaceCode.singleIso (dim Q)).inv ≫ timeMap Q := by
  have h := congrArg (· ≫ snd (codeAt Q) (timeAt Q))
    (simplex_natural (X (L := L) (time := time)) f)
  change (simplex _ P ≫ (((codes L).map f.base).map ⊗ₘ J.map (time.map f.base))) ≫
    snd (codeAt Q) (timeAt Q) = _ at h
  simpa only [timeMap, Category.assoc, Iso.inv_hom_id_assoc, tensorHom_snd] using h

private abbrev face (P : ProductIndex L time) := targetFace F r P.base (dim P) (codeMap P)

private def faceMap {P Q : ProductIndex L time} (f : P ⟶ Q) : face F r P ⟶ face F r Q :=
  targetFaceArrow F r P.base (dim P) (codeMap P) f.base (dim Q) (codeMap Q) (u f) (codeComm f)

/-- The exact face diagram of the whole native prism product. -/
def productFaces : ProductIndex L time ⥤ Over ⦋n⦌ where
  obj := face F r
  map f := faceMap F r f
  map_id P := Over.OverMorphism.ext ((degree (X (L := L) (time := time))).map_id P)
  map_comp f g := Over.OverMorphism.ext ((degree (X (L := L) (time := time))).map_comp f g)

private abbrev exactGraph (P : ProductIndex L time) :=
  fiberGraphWithTime F P.base (dim P) (codeMap P) (timeMap P)

private def graph (P : ProductIndex L time) : Resolution (targetSimplex r) :=
  ⟨op (face F r P), op ⟨(exactGraph F P).obj, (exactGraph F P).property.trans
    (targetFace_value F r P.base (dim P) (codeMap P)).symm⟩⟩

private def graphMap {P Q : ProductIndex L time} (f : P ⟶ Q) : graph F r Q ⟶ graph F r P :=
  ⟨(faceMap F r f).op, Quiver.Hom.op ⟨mixedFiberGraphArrowWithTime F f.base (codeMap P)
    (codeMap Q) (timeMap P) (timeMap Q) (u f) (codeComm f) (timeComm f)⟩⟩

/-- Every prism simplex and every mixed operator is represented in the
weakly contractible face resolution with the same raw horizontal value. -/
def productGraphDiagram : (ProductIndex L time)ᵒᵖ ⥤ Resolution (targetSimplex r) where
  obj P := (JTRowGraphFaceResolution.supported _).obj (graph F r P.unop)
  map f := (JTRowGraphFaceResolution.supported _).map (graphMap F r f.unop)
  map_id P := JTRowGraphFaceResolution.supported_ext _ (graph F r P.unop)
    (congrArg Quiver.Hom.op ((productFaces F r).map_id P.unop))
  map_comp {_ _ P} f g := JTRowGraphFaceResolution.supported_ext _ (graph F r P.unop)
    (congrArg Quiver.Hom.op ((productFaces F r).map_comp g.unop f.unop))

theorem productGraphDiagram_forget :
    productGraphDiagram F r ⋙ Grothendieck.forget (JTRowGraphFaceResolution.diagram _) =
      (productFaces F r).op := rfl

private theorem prismRaw_reduced (P : ProductIndex L time) :
    (NecklaceCode.singleIso (dim P)).inv ≫ beadRaw F P.base (dim P) (codeMap P) =
      simplex (X (L := L) (time := time)) P ≫
        (JTNecklaceEndpointCylinder.cylinder ((codes L).obj P.base)).app (time.obj P.base) ≫
        augmentation ((codes L).obj P.base) (time.obj P.base) ≫ (F.collapse.app P.base).map ≫
        Q.map := by
  rw [beadRaw, codeMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    ((JTNecklaceEndpointCylinder.cylinder ((codes L).obj P.base)).app (time.obj P.base)),
    augmentation_cylinder]
  rfl

/-- On every prism simplex the face value is the literal native projection
after the original endpoint collapse and augmentation. -/
theorem productFaceReducedValue (P : ProductIndex L time) :
    JTRowGraphFaceResolution.value (targetSimplex r) ((productFaces F r).obj P) =
      simplex (X (L := L) (time := time)) P ≫
        (JTNecklaceEndpointCylinder.cylinder ((codes L).obj P.base)).app (time.obj P.base) ≫
        augmentation ((codes L).obj P.base) (time.obj P.base) ≫ (F.collapse.app P.base).map ≫
        Q.map :=
  (targetFace_value F r P.base (dim P) (codeMap P)).trans (prismRaw_reduced F P)

section ArbitraryTarget

open JTSimplicialTargetRowGraphResolution (diagram supported supported_ext)
open DaggerSSetGluing DaggerOriginalProductGadget

private abbrev targetSSet := Q.code.toSSet

private def nativeSimplex (P : ProductIndex L time) :
    (Δ[dim P] : SSet.{0}) ⟶ targetSSet (Q := Q) :=
  (NecklaceCode.singleIso (dim P)).inv ≫ codeMap P ≫ (F.collapse.app P.base).map

private theorem nativeSimplex_map {P P' : ProductIndex L time} (f : P ⟶ P') :
    nativeSimplex F P = SSet.stdSimplex.map (u f) ≫ nativeSimplex F P' := by
  have hc : ((codes L).map f.base).map ≫ (F.collapse.app P'.base).map =
      (F.collapse.app P.base).map :=
    congrArg (fun g : (codes L).obj P.base ⟶ Q.code ↦ g.map)
      ((F.collapse.naturality f.base).trans (Category.comp_id _))
  unfold nativeSimplex
  have h := congrArg (· ≫ (F.collapse.app P'.base).map) (codeComm f)
  simp only [Category.assoc, hc] at h
  exact h

private def targetElement (P : ProductIndex L time) : (targetSSet (Q := Q)).Elements :=
  ⟨op ⦋dim P⦌, SSet.yonedaEquiv (nativeSimplex F P)⟩

private def targetElementMap {P P' : ProductIndex L time} (f : P ⟶ P') :
    targetElement F P' ⟶ targetElement F P :=
  ⟨(u f).op, by
    have e := congrArg SSet.yonedaEquiv (nativeSimplex_map F f)
    rw [SSet.yonedaEquiv_map_comp] at e
    exact e.symm⟩

/-- Every original prism simplex determines its actual simplex in the fixed target necklace. -/
def targetElements : (ProductIndex L time)ᵒᵖ ⥤ (targetSSet (Q := Q)).Elements where
  obj P := targetElement F P.unop
  map f := targetElementMap F f.unop
  map_id P := by
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((degree (X (L := L) (time := time))).map_id P.unop)
  map_comp f g := by
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((degree (X (L := L) (time := time))).map_comp g.unop f.unop)

/-- The native simplex of the comparison is exactly the horizontal projection
of the original prism simplex followed by the native collapse. -/
theorem targetElements_native (P : ProductIndex L time) :
    SSet.yonedaEquiv.symm ((targetElements F).obj (op P)).2 =
      simplex (products L time) P ≫ fst (codeAt P) (timeAt P) ≫
        (F.collapse.app P.base).map := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (nativeSimplex F P)) = _
  rw [Equiv.symm_apply_apply, nativeSimplex, codeMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem targetElement_value (P : ProductIndex L time) :
    JTSimplicialTargetRowGraphResolution.value Q.map (targetElement F P) =
      (NecklaceCode.singleIso (dim P)).inv ≫ beadRaw F P.base (dim P) (codeMap P) := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (nativeSimplex F P)) ≫ Q.map = _
  rw [Equiv.symm_apply_apply, nativeSimplex, beadRaw]
  simp only [Category.assoc]

private abbrev NativeResolution := JTSimplicialTargetRowGraphResolution.Resolution Q.map

private def nativeGraph (P : ProductIndex L time) : NativeResolution (Q := Q) :=
  ⟨targetElement F P, op ⟨(exactGraph F P).obj, (exactGraph F P).property.trans
    (targetElement_value F P).symm⟩⟩

private def nativeGraphMap {P P' : ProductIndex L time} (f : P ⟶ P') :
    nativeGraph F P' ⟶ nativeGraph F P :=
  ⟨targetElementMap F f, Quiver.Hom.op ⟨mixedFiberGraphArrowWithTime F f.base (codeMap P)
    (codeMap P') (timeMap P) (timeMap P') (u f) (codeComm f) (timeComm f)⟩⟩

/-- The whole prism diagram maps to actual raw graphs over all simplices
of a possibly multi-bead target. -/
def nativeGraphDiagram : (ProductIndex L time)ᵒᵖ ⥤ NativeResolution (Q := Q) where
  obj P := (supported Q.map).obj (nativeGraph F P.unop)
  map f := (supported Q.map).map (nativeGraphMap F f.unop)
  map_id P := supported_ext Q.map (nativeGraph F P.unop) ((targetElements F).map_id P)
  map_comp {_ _ P} f g :=
    supported_ext Q.map (nativeGraph F P.unop) ((targetElements F).map_comp f g)

theorem nativeGraphDiagram_forget :
    nativeGraphDiagram F ⋙ Grothendieck.forget (diagram Q.map) = targetElements F := rfl

/-- The original endpoint quotient and augmentation give its exact raw value. -/
theorem nativeGraphReducedValue (P : ProductIndex L time) :
    JTSimplicialTargetRowGraphResolution.value Q.map ((targetElements F).obj (op P)) =
      simplex (X (L := L) (time := time)) P ≫
        (JTNecklaceEndpointCylinder.cylinder ((codes L).obj P.base)).app (time.obj P.base) ≫
        augmentation ((codes L).obj P.base) (time.obj P.base) ≫ (F.collapse.app P.base).map ≫
        Q.map :=
  (targetElement_value F P).trans (prismRaw_reduced F P)

/-- The codomain of the entire native prism graph comparison is weakly contractible. -/
theorem nativeGraphResolution_point_GW : GW (pointMap (nerve (NativeResolution (Q := Q)))) :=
  JTSimplicialTargetRowGraphResolution.point_GW Q.map (JTNativeTargetKanWeak.point_GW Q.code)

end ArbitraryTarget

end
end DaggerModels.PartII.JTParametrizedBeadGraph
