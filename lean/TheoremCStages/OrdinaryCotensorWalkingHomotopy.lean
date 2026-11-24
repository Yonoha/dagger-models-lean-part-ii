import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinaryPrecompletionWalkingHomotopy
import OrdinarySegalCotensorMappingIso
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The original groupoid-time contraction as a categorical walking homotopy

The checked homotopy into the horizontal cotensor is transposed through the
same pointwise closed adjunction in the vertical diagram. The parameter is
the original groupoid-completed one-simplex at every horizontal index.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinaryCotensorWalkingHomotopy

open OrdinaryCSSLocalization (Space discrete walkingSpace)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (pointIso)

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k
private abbrev C (k : SimplexCategory) (W : Space) := cotensor (E k) W

/-- Curry the checked whole cotensor homotopy in the original vertical diagram. -/
def curried (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    (C k W).flip ⟶ (C k W).flip ⋙ ihom (E ⦋1⦌) :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
      (OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W) ≫
    (OrdinarySegalCotensorMappingIso.rowFamilyIso (E ⦋1⦌) (C k W)).hom

/-- Uncurry the same natural transformation through the checked pointwise adjunction. -/
def uncurried (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    (C k W).flip ⋙ tensorLeft (E ⦋1⦌) ⟶ (C k W).flip :=
  (((ihom.adjunction (E ⦋1⦌)).whiskerRight SimplexCategoryᵒᵖ).homEquiv
    (C k W).flip (C k W).flip).symm (curried k j W)

private theorem uncurried_app (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space) (q : SimplexCategoryᵒᵖ) :
    (uncurried k j W).app q = uncurry ((curried k j W).app q) := by
  unfold uncurried
  rw [Adjunction.homEquiv_counit]
  change (E ⦋1⦌ ◁ (curried k j W).app q) ≫
      (ihom.ev (E ⦋1⦌)).app ((C k W).flip.obj q) = _
  exact (uncurry_eq ((curried k j W).app q)).symm

/-- The chosen product with the actual walking object has the source of the
pointwise tensor adjunction after transposing the two simplex indices. -/
def productToTensor (X : Space) :
    X ⨯ walkingSpace ⟶ (X.flip ⋙ tensorLeft (E ⦋1⦌)).flip where
  app n := CartesianMonoidalCategory.lift
    ((prod.snd : X ⨯ walkingSpace ⟶ walkingSpace).app n)
    ((prod.fst : X ⨯ walkingSpace ⟶ X).app n)
  naturality := by
    intro m n θ
    apply NatTrans.ext
    funext q z
    apply Prod.ext
    · change (((X ⨯ walkingSpace).map θ ≫
          (prod.snd : X ⨯ walkingSpace ⟶ walkingSpace).app n).app q) z =
        (((prod.snd : X ⨯ walkingSpace ⟶ walkingSpace).app m ≫
          walkingSpace.map θ).app q) z
      exact congrFun (NatTrans.congr_app
        ((prod.snd : X ⨯ walkingSpace ⟶ walkingSpace).naturality θ) q) z
    · change (((X ⨯ walkingSpace).map θ ≫
          (prod.fst : X ⨯ walkingSpace ⟶ X).app n).app q) z =
        (((prod.fst : X ⨯ walkingSpace ⟶ X).app m ≫ X.map θ).app q) z
      exact congrFun (NatTrans.congr_app
        ((prod.fst : X ⨯ walkingSpace ⟶ X).naturality θ) q) z

/-- The checked whole groupoid-time contraction as an actual product homotopy. -/
def categoricalHomotopy (k : SimplexCategory) (j : Fin (k.len + 1))
    (W : Space) : C k W ⨯ walkingSpace ⟶ C k W :=
  productToTensor (C k W) ≫
    (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
      (uncurried k j W)

private theorem zeroLevel_subsingleton (n : SimplexCategoryᵒᵖ)
    (x y : (Δ[0] : SSet.{0}).obj n) : x = y := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  haveI : Subsingleton (Fin (⦋0⦌.len + 1)) := by
    change Subsingleton (Fin 1)
    infer_instance
  exact Subsingleton.elim _ _

/-- The horizontal discrete point is terminal in the unchanged simplicial-space category. -/
private def discreteZeroTerminal :
    IsTerminal (discrete.obj (Δ[0] : SSet.{0})) := by
  refine IsTerminal.ofUniqueHom (fun X => ?_) (fun X f => ?_)
  · refine ⟨fun n => SSet.const (SSet.stdSimplex.const 0 0 n), ?_⟩
    intro n m θ
    apply NatTrans.ext
    funext q z
    exact zeroLevel_subsingleton m _ _
  · apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext q z
    exact zeroLevel_subsingleton n _ _

/-- The literal first or second vertex of the original walking groupoid. -/
def chosenVertex (i : Fin 2) : (⊤_ Space) ⟶ walkingSpace :=
  discreteZeroTerminal.from (⊤_ Space) ≫
    discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)

private theorem categoricalHomotopy_section_factor (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space) (i : Fin 2) :
    OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W) (chosenVertex i) ≫
        categoricalHomotopy k j W =
      (OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W)
          (chosenVertex i) ≫ productToTensor (C k W)) ≫
        (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
          (uncurried k j W) := by
  rw [categoricalHomotopy]
  exact (Category.assoc _ _ _).symm

private theorem vertexSection_parameter (V : Space) (i : Fin 2) :
    OrdinaryPrecompletionWalkingHomotopy.vertexSection V (chosenVertex i) =
      prod.lift (𝟙 V)
        (discreteZeroTerminal.from V ≫
          discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)) := by
  have h : terminal.from V ≫ discreteZeroTerminal.from (⊤_ Space) =
      discreteZeroTerminal.from V := discreteZeroTerminal.hom_ext _ _
  change prod.lift (𝟙 V)
      (terminal.from V ≫
        (discreteZeroTerminal.from (⊤_ Space) ≫
          discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i))) = _
  rw [← Category.assoc, h]

private theorem level_pre {K L : SSet.{0}} (f : K ⟶ L) (V : Space)
    (q : SimplexCategoryᵒᵖ)
    (t : (diagramMappingSpace (discrete.obj L) V).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv K V q.unop)
        ((diagramMappingPrecomp (discrete.map f) V).app q t) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv L V q.unop) t := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f V) q) t
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem point_level (V : Space) (n : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (t : (V.obj (op n)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv
      ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
        (((pointIso V).inv.app (op n)).app q t) =
      (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n)).hom ≫
        (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm t := by
  induction n using SimplexCategory.rec with | _ d =>
    change (OrdinaryDiscreteMapping.levelEquiv
        ((Δ[0] : SSet.{0}) ⊗ (Δ[d] : SSet.{0})) V q.unop)
          ((diagramMappingPrecomp
            (discrete.map
              (SSet.stdSimplex.leftUnitor (Δ[d] : SSet.{0})).hom) V).app q
              ((OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv.app q t)) = _
    rw [level_pre]
    congr 1
    apply SSet.yonedaEquiv.injective
    change (OrdinarySegalWalkingEvaluation.simplexMappingIso V d).hom.app q
        ((OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv.app q t) =
      SSet.yonedaEquiv ((SSet.yonedaEquiv (X := V.flip.obj q)).symm t)
    rw [Equiv.apply_symm_apply]
    exact congrFun (NatTrans.congr_app
      (OrdinarySegalWalkingEvaluation.simplexMappingIso V d).inv_hom_id q) t

private theorem row_yoneda (B : SSet.{0}) (V : Space)
    (q : SimplexCategoryᵒᵖ) (n : SimplexCategory)
    (t : ((cotensor B V).obj (op n)).obj q) :
    (SSet.yonedaEquiv
        (X := (ihom B).obj (V.flip.obj q)) (n := n)).symm
        ((OrdinarySegalCotensorMappingIso.rowIso B V q).hom.app (op n) t) =
      curry ((OrdinaryDiscreteMapping.levelEquiv
        (B ⊗ SSet.stdSimplex.obj n) V q.unop) t) := by
  change (SSet.yonedaEquiv
      (X := (ihom B).obj (V.flip.obj q)) (n := n)).symm
      (SSet.yonedaEquiv (curry ((OrdinaryDiscreteMapping.levelEquiv
        (B ⊗ SSet.stdSimplex.obj n) V q.unop) t))) = _
  exact Equiv.symm_apply_apply _ _

private theorem evaluation_point_inv (V : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ E ⦋1⦌) :
    OrdinarySegalCotensorPointEvaluation.evaluation (E ⦋1⦌) V v ≫
        (pointIso V).inv = OrdinarySegalHorizontalCotensor.pre v V := by
  simp only [OrdinarySegalCotensorPointEvaluation.evaluation,
    OrdinarySegalHorizontalCotensor.evaluateVertex, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem vertex_tensor (B X : SSet.{0})
    (v : (Δ[0] : SSet.{0}) ⟶ B) (n : SimplexCategory)
    (Z : SSet.stdSimplex.obj n ⟶ X) :
    (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n)).hom ≫
        CartesianMonoidalCategory.lift
          (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n) ≫ v) Z =
      (v ▷ SSet.stdSimplex.obj n) ≫ (B ◁ Z) := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨a, b⟩
  change (v.app q ((SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.obj n)).app q b), Z.app q b) =
    (v.app q a, Z.app q b)
  exact Prod.ext (congrArg (v.app q) (zeroLevel_subsingleton q _ _)) rfl

private theorem vertex_time (V : Space) (i : Fin 2)
    (n : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (V.obj (op n)).obj q) :
    (((discreteZeroTerminal.from V ≫
        discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)).app
          (op n)).app q) z =
      ((SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n) ≫
        JTParameterContraction.parameterVertex ⦋1⦌ i).app (op n))
        (SSet.stdSimplex.objEquiv.symm (𝟙 n)) := by
  change (JTParameterContraction.parameterVertex ⦋1⦌ i).app (op n)
      (SSet.stdSimplex.const 0 0 (op n)) =
    (JTParameterContraction.parameterVertex ⦋1⦌ i).app (op n)
      ((SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n)).app
        (op n) (SSet.stdSimplex.objEquiv.symm (𝟙 n)))
  exact congrArg ((JTParameterContraction.parameterVertex ⦋1⦌ i).app (op n))
    (zeroLevel_subsingleton (op n) _ _)

private theorem curried_row (k : SimplexCategory) (j : Fin (k.len + 1))
    (W : Space) (q : SimplexCategoryᵒᵖ) (n : SimplexCategory)
    (z : ((C k W).flip.obj q).obj (op n)) :
    (((curried k j W).app q).app (op n)) z =
      ((OrdinarySegalCotensorMappingIso.rowIso (E ⦋1⦌) (C k W) q).hom.app
          (op n))
        (((OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W).app
          (op n)).app q z) := by
  rfl

private theorem curried_uncurry_yoneda (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space)
    (q : SimplexCategoryᵒᵖ) (n : SimplexCategory)
    (z : ((C k W).flip.obj q).obj (op n)) :
    (E ⦋1⦌ ◁ (SSet.yonedaEquiv
        (X := (C k W).flip.obj q) (n := n)).symm z) ≫
        uncurry ((curried k j W).app q) =
      (OrdinaryDiscreteMapping.levelEquiv
        (E ⦋1⦌ ⊗ SSet.stdSimplex.obj n) (C k W) q.unop)
        (((OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W).app
          (op n)).app q z) := by
  let V := C k W
  let B := E ⦋1⦌
  let g := OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W
  let h := (curried k j W).app q
  let Z := (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm z
  let G := (OrdinaryDiscreteMapping.levelEquiv
    (B ⊗ SSet.stdSimplex.obj n) V q.unop) ((g.app (op n)).app q z)
  have hc : Z ≫ h = curry G := by
    change (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm z ≫
      (curried k j W).app q = curry G
    rw [SSet.yonedaEquiv_symm_comp]
    change (SSet.yonedaEquiv
        (X := (ihom B).obj (V.flip.obj q)) (n := n)).symm
          ((h.app (op n)) z) = curry G
    rw [curried_row]
    exact row_yoneda B V q n ((g.app (op n)).app q z)
  calc
    B ◁ Z ≫ uncurry h = uncurry (Z ≫ h) :=
      (uncurry_natural_left Z h).symm
    _ = uncurry (curry G) := congrArg uncurry hc
    _ = G := uncurry_curry G

private theorem section_productToTensor_value (V : Space) (i : Fin 2)
    (a : SimplexCategoryᵒᵖ) (q : SimplexCategoryᵒᵖ)
    (z : (V.obj a).obj q) :
    (((OrdinaryPrecompletionWalkingHomotopy.vertexSection V (chosenVertex i) ≫
        productToTensor V).app a).app q) z =
      (((discreteZeroTerminal.from V ≫
        discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)).app a).app q z, z) := by
  let s := OrdinaryPrecompletionWalkingHomotopy.vertexSection V (chosenVertex i)
  let t := discreteZeroTerminal.from V ≫
    discrete.map (JTParameterContraction.parameterVertex ⦋1⦌ i)
  have hs : s ≫ (prod.snd : V ⨯ walkingSpace ⟶ walkingSpace) = t := by
    change (OrdinaryPrecompletionWalkingHomotopy.vertexSection V (chosenVertex i)) ≫
      (prod.snd : V ⨯ walkingSpace ⟶ walkingSpace) = t
    rw [vertexSection_parameter]
    exact prod.lift_snd (𝟙 V) t
  have hf : s ≫ (prod.fst : V ⨯ walkingSpace ⟶ V) = 𝟙 V := by
    change (OrdinaryPrecompletionWalkingHomotopy.vertexSection V (chosenVertex i)) ≫
      (prod.fst : V ⨯ walkingSpace ⟶ V) = 𝟙 V
    rw [vertexSection_parameter]
    exact prod.lift_fst (𝟙 V) t
  have hfst : (s ≫ productToTensor V).app a ≫
      CartesianMonoidalCategory.fst (walkingSpace.obj a) (V.obj a) = t.app a := by
    change s.app a ≫
      CartesianMonoidalCategory.lift
        ((prod.snd : V ⨯ walkingSpace ⟶ walkingSpace).app a)
        ((prod.fst : V ⨯ walkingSpace ⟶ V).app a) ≫
      CartesianMonoidalCategory.fst _ _ = t.app a
    rw [CartesianMonoidalCategory.lift_fst]
    exact congrArg (fun f ↦ f.app a) hs
  have hsnd : (s ≫ productToTensor V).app a ≫
      CartesianMonoidalCategory.snd (walkingSpace.obj a) (V.obj a) =
        𝟙 (V.obj a) := by
    change s.app a ≫
      CartesianMonoidalCategory.lift
        ((prod.snd : V ⨯ walkingSpace ⟶ walkingSpace).app a)
        ((prod.fst : V ⨯ walkingSpace ⟶ V).app a) ≫
      CartesianMonoidalCategory.snd _ _ = 𝟙 (V.obj a)
    rw [CartesianMonoidalCategory.lift_snd]
    simpa only [NatTrans.id_app] using congrArg (fun f ↦ f.app a) hf
  apply Prod.ext
  · exact congrFun (NatTrans.congr_app hfst q) z
  · exact congrFun (NatTrans.congr_app hsnd q) z

private theorem yoneda_lift {A B : SSet.{0}} (n : SimplexCategory)
    (f : SSet.stdSimplex.obj n ⟶ A) (g : SSet.stdSimplex.obj n ⟶ B) :
    SSet.yonedaEquiv (CartesianMonoidalCategory.lift f g) =
      (SSet.yonedaEquiv f, SSet.yonedaEquiv g) := by
  apply Prod.ext
  · have h := congrArg SSet.yonedaEquiv (CartesianMonoidalCategory.lift_fst f g)
    exact h
  · have h := congrArg SSet.yonedaEquiv (CartesianMonoidalCategory.lift_snd f g)
    exact h

private theorem yoneda_app_id {A : SSet.{0}} (n : SimplexCategory)
    (f : SSet.stdSimplex.obj n ⟶ A) :
    SSet.yonedaEquiv f = f.app (op n) (SSet.stdSimplex.objEquiv.symm (𝟙 n)) := by
  rfl

private theorem categoricalHomotopy_yoneda (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space) (i : Fin 2)
    (n : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : ((C k W).obj (op n)).obj q) :
    (SSet.yonedaEquiv (X := (C k W).flip.obj q) (n := n)).symm
      (((OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W)
        (chosenVertex i) ≫ categoricalHomotopy k j W).app (op n)).app q z) =
      CartesianMonoidalCategory.lift
        (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n) ≫
          JTParameterContraction.parameterVertex ⦋1⦌ i)
        ((SSet.yonedaEquiv (X := (C k W).flip.obj q) (n := n)).symm z) ≫
        uncurry ((curried k j W).app q) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  have hfac := congrFun (NatTrans.congr_app
    (NatTrans.congr_app (categoricalHomotopy_section_factor k j W i) (op n)) q) z
  rw [hfac]
  have hflip :
      ((((OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W)
          (chosenVertex i) ≫ productToTensor (C k W)) ≫
            (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
              (uncurried k j W)).app (op n)).app q) z =
        ((uncurried k j W).app q).app (op n)
          (((OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W)
            (chosenVertex i) ≫ productToTensor (C k W)).app (op n)).app q z) := by
    rfl
  rw [hflip, section_productToTensor_value, uncurried_app, vertex_time]
  rw [yoneda_lift, Equiv.apply_symm_apply, yoneda_app_id]

/-- Restricting the product homotopy at either literal walking vertex
is the original cotensor evaluation at the same parameter vertex. -/
theorem categoricalHomotopy_endpoint (k : SimplexCategory)
    (j : Fin (k.len + 1)) (W : Space) (i : Fin 2) :
    OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W) (chosenVertex i) ≫
        categoricalHomotopy k j W =
      OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W ≫
        OrdinarySegalCotensorPointEvaluation.evaluation (E ⦋1⦌) (C k W)
          (JTParameterContraction.parameterVertex ⦋1⦌ i) := by
  apply NatTrans.ext
  funext a
  apply NatTrans.ext
  funext q z
  let n := a.unop
  let V := C k W
  let B := E ⦋1⦌
  let v := JTParameterContraction.parameterVertex ⦋1⦌ i
  let g := OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy k j W
  let L := ((OrdinaryPrecompletionWalkingHomotopy.vertexSection V
    (chosenVertex i) ≫ categoricalHomotopy k j W).app a).app q z
  let R := ((g ≫ OrdinarySegalCotensorPointEvaluation.evaluation B V v).app a).app q z
  let Z := (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm z
  let G := (OrdinaryDiscreteMapping.levelEquiv
    (B ⊗ SSet.stdSimplex.obj n) V q.unop) ((g.app a).app q z)
  let U := (SSet.stdSimplex.leftUnitor (SSet.stdSimplex.obj n)).hom
  have hL : U ≫ (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm L =
      (v ▷ SSet.stdSimplex.obj n) ≫ G := by
    calc
      U ≫ (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm L =
          (U ≫ CartesianMonoidalCategory.lift
            (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n) ≫ v) Z) ≫
              uncurry ((curried k j W).app q) := by
                rw [categoricalHomotopy_yoneda]
                rfl
      _ = ((v ▷ SSet.stdSimplex.obj n) ≫ (B ◁ Z)) ≫
            uncurry ((curried k j W).app q) := by
              rw [vertex_tensor]
      _ = (v ▷ SSet.stdSimplex.obj n) ≫ G := by
        rw [Category.assoc, curried_uncurry_yoneda]
  have hEval : (((pointIso V).inv.app a).app q)
        (((OrdinarySegalCotensorPointEvaluation.evaluation B V v).app a).app q
          ((g.app a).app q z)) =
      (((OrdinarySegalHorizontalCotensor.pre v V).app a).app q)
        ((g.app a).app q z) := by
    simpa only [NatTrans.comp_app, types_comp_apply] using
      congrFun (NatTrans.congr_app
        (NatTrans.congr_app (evaluation_point_inv V v) a) q)
          ((g.app a).app q z)
  have hR : (OrdinaryDiscreteMapping.levelEquiv
      ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
        (((pointIso V).inv.app a).app q R) =
      (v ▷ SSet.stdSimplex.obj n) ≫ G := by
    calc
      _ = (OrdinaryDiscreteMapping.levelEquiv
          ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
            ((((OrdinarySegalHorizontalCotensor.pre v V).app a).app q)
              ((g.app a).app q z)) := congrArg _ hEval
      _ = (v ▷ SSet.stdSimplex.obj n) ≫ G := by
        change (OrdinaryDiscreteMapping.levelEquiv
          ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
            ((diagramMappingPrecomp
              (discrete.map (v ▷ SSet.stdSimplex.obj n)) V).app q
                ((g.app a).app q z)) = _
        exact level_pre (v ▷ SSet.stdSimplex.obj n) V q ((g.app a).app q z)
  have hY : U ≫ (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm L =
      U ≫ (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm R := by
    calc
      _ = (v ▷ SSet.stdSimplex.obj n) ≫ G := hL
      _ = (OrdinaryDiscreteMapping.levelEquiv
          ((Δ[0] : SSet.{0}) ⊗ SSet.stdSimplex.obj n) V q.unop)
            (((pointIso V).inv.app a).app q R) := hR.symm
      _ = U ≫ (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm R :=
        point_level V n q R
  exact (SSet.yonedaEquiv (X := V.flip.obj q) (n := n)).symm.injective
    ((cancel_epi U).mp hY)

/-- The first original walking vertex gives the identity of the cotensor. -/
theorem endpoint_zero (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W) (chosenVertex 0) ≫
      categoricalHomotopy k j W = 𝟙 (C k W) := by
  rw [categoricalHomotopy_endpoint]
  exact OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero k j W

/-- The second original walking vertex gives evaluation followed by the
same exact constant section of the original groupoid-simplex parameter. -/
theorem endpoint_one (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    OrdinaryPrecompletionWalkingHomotopy.vertexSection (C k W) (chosenVertex 1) ≫
      categoricalHomotopy k j W =
    OrdinarySegalCotensorPointEvaluation.evaluation (E k) W
        (JTParameterContraction.parameterVertex k j) ≫
      OrdinarySegalHorizontalCotensorPoint.constantSection (E k) W := by
  rw [categoricalHomotopy_endpoint]
  exact OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one k j W

#print axioms curried
#print axioms uncurried
#print axioms categoricalHomotopy
#print axioms chosenVertex
#print axioms endpoint_zero
#print axioms endpoint_one

end

end DaggerModels.PartII.OrdinaryCotensorWalkingHomotopy
