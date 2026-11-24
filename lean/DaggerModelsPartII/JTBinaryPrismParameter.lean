import DaggerModelsPartII.JTOrderedLabelBinaryGlue
import DaggerModelsPartII.JTGroupoidParameterPrism
import DaggerModelsPartII.JTParameterContraction
import ChosenNecklaceTripleWedge
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Binary necklace parameters over an arbitrary time simplicial set

The connector keeps both boundary maps as full time-dependent maps.  Its
codiscrete vertex labels choose the left boundary over the first horizontal
vertex and the right boundary over the last horizontal vertex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismParameter

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1
private abbrev iso (K : SimplexCategory) := parameterCodiscreteIso.app K

variable (T U : DaggerChosenRigidificationNecklace.NecklaceCode)
variable (K : SimplexCategory) (I : SSet.{0})
variable (s : T.toSSet ⊗ I ⟶ J.obj K) (t : U.toSSet ⊗ I ⟶ J.obj K)

/-- The full left boundary map, retaining all time simplices. -/
def leftBoundary : I ⟶ J.obj K :=
  (lift (SSet.stdSimplex.isTerminalObj₀.from I) (𝟙 I)) ≫
    (pointAt T (ULift.up (Fin.last T.len)) ⊗ₘ 𝟙 I) ≫ s

/-- The full right boundary map, retaining all time simplices. -/
def rightBoundary : I ⟶ J.obj K :=
  (lift (SSet.stdSimplex.isTerminalObj₀.from I) (𝟙 I)) ≫
    (pointAt U (ULift.up 0) ⊗ₘ 𝟙 I) ≫ t

private def connectorLabel (x : (E.toSSet ⊗ I).obj (op ⦋0⦌)) : Fin (K.len + 1) :=
  if ((singleIso.{0} 1).hom.app (op ⦋0⦌) x.1) 0 = (0 : Fin 2) then
    vertexLabels ((leftBoundary T K I s) ≫ (iso K).hom) x.2
  else
    vertexLabels ((rightBoundary U K I t) ≫ (iso K).hom) x.2

/-- The actual one-bead parameter, with both boundary-time labels. -/
def connector : E.toSSet ⊗ I ⟶ J.obj K :=
  mapOfVertices (E.toSSet ⊗ I) (connectorLabel T U K I s t) ≫ (iso K).inv


/-- The inserted connector is determined by the two complete boundary maps.
The original source necklaces of the two pairs of maps may differ. -/
theorem connector_eq_of_boundary {T' U' : DaggerChosenRigidificationNecklace.NecklaceCode}
    {s' : T'.toSSet ⊗ I ⟶ J.obj K} {t' : U'.toSSet ⊗ I ⟶ J.obj K}
    (hs : leftBoundary T K I s = leftBoundary T' K I s')
    (ht : rightBoundary U K I t = rightBoundary U' K I t') :
    connector T U K I s t = connector T' U' K I s' t' := by
  have h : connectorLabel T U K I s t = connectorLabel T' U' K I s' t' := by
    funext a
    simp only [connectorLabel, hs, ht]
  unfold connector
  rw [h]

private theorem codiscrete_hom_ext {X : SSet.{0}}
    {f g : X ⟶ codiscreteNerve.obj (Fin (K.len + 1))}
    (h : ∀ x : X.obj (op ⦋0⦌), vertexLabels f x = vertexLabels g x) : f = g := by
  apply NatTrans.ext
  funext n z
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  calc
    ((f.app n z).obj i).as =
        vertexLabels f (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op z) :=
      (vertexLabels_natural f n z i).symm
    _ = vertexLabels g (X.map ((⦋0⦌ : SimplexCategory).const n.unop i).op z) := h _
    _ = ((g.app n z).obj i).as := vertexLabels_natural g n z i

private theorem vertexLabels_mapOfVertices {X : SSet.{0}}
    (φ : X.obj (op ⦋0⦌) → Fin (K.len + 1)) (x : X.obj (op ⦋0⦌)) :
    vertexLabels (mapOfVertices X φ) x = φ x := by
  change φ (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) = φ x
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]


private theorem vertexLabels_comp {X Y : SSet.{0}}
    (f : X ⟶ Y) (g : Y ⟶ codiscreteNerve.obj (Fin (K.len + 1)))
    (x : X.obj (op ⦋0⦌)) :
    vertexLabels (f ≫ g) x = vertexLabels g (f.app (op ⦋0⦌) x) := rfl

private theorem connectorLabel_first (x : I.obj (op ⦋0⦌)) :
    connectorLabel T U K I s t
        ((pointAt E (ULift.up 0)).app (op ⦋0⦌) (zeroSimplex 0), x) =
      vertexLabels ((leftBoundary T K I s) ≫ (iso K).hom) x := by
  unfold connectorLabel
  have h : ((singleIso.{0} 1).hom.app (op ⦋0⦌)
      ((pointAt E (ULift.up 0)).app (op ⦋0⦌) (zeroSimplex 0))) 0 = (0 : Fin 2) := by
    rw [singleIso_hom]
    exact pointAt_inclusion_apply.{0} (single 1) (ULift.up 0) (zeroSimplex 0) 0
  simp only [h, ↓reduceIte]

private theorem connectorLabel_last (x : I.obj (op ⦋0⦌)) :
    connectorLabel T U K I s t
        ((pointAt.{0} E (ULift.up (Fin.last E.len))).app (op ⦋0⦌) (zeroSimplex.{0} 0), x) =
      vertexLabels ((rightBoundary U K I t) ≫ (iso K).hom) x := by
  unfold connectorLabel
  have h : ((singleIso.{0} 1).hom.app (op ⦋0⦌)
      ((pointAt.{0} E (ULift.up (Fin.last E.len))).app (op ⦋0⦌) (zeroSimplex.{0} 0))) 0 ≠
      (0 : Fin 2) := by
    rw [singleIso_hom]
    have hv : ((DaggerChosenRigidificationNecklace.NecklaceCode.inclusion.{0} (single 1)).app (op ⦋0⦌)
        ((pointAt.{0} E (ULift.up (Fin.last E.len))).app (op ⦋0⦌) (zeroSimplex.{0} 0))) 0 =
        Fin.last 1 :=
      pointAt_inclusion_apply.{0} (single 1) (ULift.up (Fin.last 1))
        (zeroSimplex.{0} 0) 0
    intro h0
    have hn : (Fin.last 1 : Fin 2) ≠ 0 := by decide
    exact hn (hv.symm.trans h0)
  simp only [h, ↓reduceIte]

/-- The first connector boundary is the full left time family. -/
theorem connector_first :
    (pointAt E (ULift.up 0) ⊗ₘ 𝟙 I) ≫ connector T U K I s t =
      (pointAt T (ULift.up (Fin.last T.len)) ⊗ₘ 𝟙 I) ≫ s := by
  apply (cancel_mono (iso K).hom).mp
  rw [Category.assoc, connector, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext K
  intro x
  rcases x with ⟨a, b⟩
  have ha : a = (SSet.stdSimplex.isTerminalObj₀.from I).app (op ⦋0⦌) b :=
    Subsingleton.elim _ _
  subst a
  rw [vertexLabels_comp K, vertexLabels_mapOfVertices]
  have hb : (SSet.stdSimplex.isTerminalObj₀.from I).app (op ⦋0⦌) b =
      zeroSimplex 0 := zeroSimplex_unique _
  rw [hb]
  change connectorLabel T U K I s t
      ((pointAt E (ULift.up 0)).app (op ⦋0⦌) (zeroSimplex 0), b) =
    vertexLabels ((leftBoundary T K I s) ≫ (iso K).hom) b
  exact connectorLabel_first T U K I s t b

/-- The second connector boundary is the full right time family. -/
theorem connector_last :
    (pointAt E (ULift.up (Fin.last E.len)) ⊗ₘ 𝟙 I) ≫ connector T U K I s t =
      (pointAt U (ULift.up 0) ⊗ₘ 𝟙 I) ≫ t := by
  apply (cancel_mono (iso K).hom).mp
  rw [Category.assoc, connector, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext K
  intro x
  rcases x with ⟨a, b⟩
  have ha : a = (SSet.stdSimplex.isTerminalObj₀.from I).app (op ⦋0⦌) b :=
    Subsingleton.elim _ _
  subst a
  rw [vertexLabels_comp K, vertexLabels_mapOfVertices]
  have hb : (SSet.stdSimplex.isTerminalObj₀.from I).app (op ⦋0⦌) b =
      zeroSimplex 0 := zeroSimplex_unique _
  rw [hb]
  change connectorLabel T U K I s t
      ((pointAt E (ULift.up (Fin.last E.len))).app (op ⦋0⦌) (zeroSimplex 0), b) =
    vertexLabels ((rightBoundary U K I t) ≫ (iso K).hom) b
  exact connectorLabel_last T U K I s t b


private def prismCurry {X : SSet.{0}} (f : X ⊗ I ⟶ J.obj K) :
    X ⟶ (ihom I).obj (J.obj K) :=
  MonoidalClosed.curry ((β_ I X).hom ≫ f)

private def prismUncurry {X : SSet.{0}} (f : X ⟶ (ihom I).obj (J.obj K)) :
    X ⊗ I ⟶ J.obj K :=
  (β_ X I).hom ≫ MonoidalClosed.uncurry f

private theorem prismCurry_prismUncurry {X : SSet.{0}}
    (f : X ⟶ (ihom I).obj (J.obj K)) :
    prismCurry K I (prismUncurry K I f) = f := by
  unfold prismCurry prismUncurry
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
    MonoidalClosed.curry_uncurry]

private theorem prismUncurry_prismCurry {X : SSet.{0}}
    (f : X ⊗ I ⟶ J.obj K) :
    prismUncurry K I (prismCurry K I f) = f := by
  unfold prismCurry prismUncurry
  rw [MonoidalClosed.uncurry_curry, SymmetricCategory.symmetry_assoc]

private theorem prismCurry_natural {X Y : SSet.{0}} (v : X ⟶ Y)
    (f : Y ⊗ I ⟶ J.obj K) :
    prismCurry K I ((v ⊗ₘ 𝟙 I) ≫ f) = v ≫ prismCurry K I f := by
  unfold prismCurry
  have hb := BraidedCategory.braiding_naturality (𝟙 I) v
  simp only [MonoidalCategory.id_tensorHom] at hb
  rw [← Category.assoc, ← hb, Category.assoc]
  exact MonoidalClosed.curry_natural_left v ((β_ I Y).hom ≫ f)

private theorem prismUncurry_natural {X Y : SSet.{0}} (v : X ⟶ Y)
    (f : Y ⟶ (ihom I).obj (J.obj K)) :
    (v ⊗ₘ 𝟙 I) ≫ prismUncurry K I f =
      prismUncurry K I (v ≫ f) := by
  calc
    (v ⊗ₘ 𝟙 I) ≫ prismUncurry K I f =
        prismUncurry K I (prismCurry K I ((v ⊗ₘ 𝟙 I) ≫ prismUncurry K I f)) :=
      (prismUncurry_prismCurry K I _).symm
    _ = prismUncurry K I (v ≫ f) := by
      rw [prismCurry_natural, prismCurry_prismUncurry]

/-- Glue the three complete time-dependent parameter families. -/
def parameter :
    (JTOrderedLabelBinaryGlue.code T U).toSSet ⊗ I ⟶ J.obj K :=
  prismUncurry K I
    (tripleRightDesc T E U (prismCurry K I s)
      (prismCurry K I (connector T U K I s t)) (prismCurry K I t)
      (by
        rw [← prismCurry_natural K I, ← prismCurry_natural K I]
        exact congrArg (prismCurry K I) (connector_first T U K I s t).symm)
      (by
        rw [← prismCurry_natural K I, ← prismCurry_natural K I]
        exact congrArg (prismCurry K I) (connector_last T U K I s t)))

/-- The first bead restriction is exactly the original left time family. -/
theorem parameter_left :
    (tripleRightT T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t = s := by
  unfold parameter
  rw [prismUncurry_natural, tripleRightDesc_T, prismUncurry_prismCurry]

/-- The connector restriction retains the whole chosen time family. -/
theorem parameter_middle :
    (tripleRightU T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t =
      connector T U K I s t := by
  unfold parameter
  rw [prismUncurry_natural, tripleRightDesc_U, prismUncurry_prismCurry]

/-- The last bead restriction is exactly the original right time family. -/
theorem parameter_right :
    (tripleRightV T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t = t := by
  unfold parameter
  rw [prismUncurry_natural, tripleRightDesc_V, prismUncurry_prismCurry]


private theorem leftBoundary_mapTime {I' : SSet.{0}} (j : I' ⟶ I) :
    leftBoundary T K I' ((𝟙 T.toSSet ⊗ₘ j) ≫ s) =
      j ≫ leftBoundary T K I s := by
  apply NatTrans.ext
  funext q x
  rfl

private theorem rightBoundary_mapTime {I' : SSet.{0}} (j : I' ⟶ I) :
    rightBoundary U K I' ((𝟙 U.toSSet ⊗ₘ j) ≫ t) =
      j ≫ rightBoundary U K I t := by
  apply NatTrans.ext
  funext q x
  rfl


/-- The connector preserves every simplicial operator in the time variable. -/
theorem connector_mapTime {I' : SSet.{0}} (j : I' ⟶ I) :
    connector T U K I'
        ((𝟙 T.toSSet ⊗ₘ j) ≫ s) ((𝟙 U.toSSet ⊗ₘ j) ≫ t) =
      (𝟙 E.toSSet ⊗ₘ j) ≫ connector T U K I s t := by
  apply (cancel_mono (iso K).hom).mp
  rw [connector, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, connector, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply codiscrete_hom_ext K
  intro x
  rcases x with ⟨a, b⟩
  rw [vertexLabels_comp K, vertexLabels_mapOfVertices, vertexLabels_mapOfVertices]
  change connectorLabel T U K I'
      ((𝟙 T.toSSet ⊗ₘ j) ≫ s) ((𝟙 U.toSSet ⊗ₘ j) ≫ t) (a, b) =
    connectorLabel T U K I s t (a, j.app (op ⦋0⦌) b)
  unfold connectorLabel
  by_cases h : ((singleIso.{0} 1).hom.app (op ⦋0⦌) a) 0 = (0 : Fin 2)
  · simp only [h, ↓reduceIte, leftBoundary_mapTime, Category.assoc]
    rfl
  · simp only [h, ↓reduceIte, rightBoundary_mapTime, Category.assoc]
    rfl


private theorem parameter_hom_ext
    {f g : (JTOrderedLabelBinaryGlue.code T U).toSSet ⊗ I ⟶ J.obj K}
    (hT : (tripleRightT T E U ⊗ₘ 𝟙 I) ≫ f =
      (tripleRightT T E U ⊗ₘ 𝟙 I) ≫ g)
    (hE : (tripleRightU T E U ⊗ₘ 𝟙 I) ≫ f =
      (tripleRightU T E U ⊗ₘ 𝟙 I) ≫ g)
    (hU : (tripleRightV T E U ⊗ₘ 𝟙 I) ≫ f =
      (tripleRightV T E U ⊗ₘ 𝟙 I) ≫ g) : f = g := by
  have h : prismCurry K I f = prismCurry K I g := by
    apply tripleRight_hom_ext
    · rw [← prismCurry_natural, ← prismCurry_natural]
      exact congrArg (prismCurry K I) hT
    · rw [← prismCurry_natural, ← prismCurry_natural]
      exact congrArg (prismCurry K I) hE
    · rw [← prismCurry_natural, ← prismCurry_natural]
      exact congrArg (prismCurry K I) hU
  calc
    f = prismUncurry K I (prismCurry K I f) :=
      (prismUncurry_prismCurry K I f).symm
    _ = prismUncurry K I (prismCurry K I g) := congrArg (prismUncurry K I) h
    _ = g := prismUncurry_prismCurry K I g

private theorem tensor_square {X Y I' : SSet.{0}} (v : X ⟶ Y) (j : I' ⟶ I) :
    (v ⊗ₘ 𝟙 I') ≫ (𝟙 Y ⊗ₘ j) =
      (𝟙 X ⊗ₘ j) ≫ (v ⊗ₘ 𝟙 I) := by
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- The binary parameter commutes with every map of time simplicial sets. -/
theorem parameter_mapTime {I' : SSet.{0}} (j : I' ⟶ I) :
    (𝟙 (JTOrderedLabelBinaryGlue.code T U).toSSet ⊗ₘ j) ≫
        parameter T U K I s t =
      parameter T U K I'
        ((𝟙 T.toSSet ⊗ₘ j) ≫ s) ((𝟙 U.toSSet ⊗ₘ j) ≫ t) := by
  apply parameter_hom_ext T U K I'
  · calc
      _ = (𝟙 T.toSSet ⊗ₘ j) ≫ (tripleRightT T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t := by
        simp only [← Category.assoc]
        exact congrArg (fun u ↦ u ≫ parameter T U K I s t)
          (tensor_square (I := I) (tripleRightT T E U) j)
      _ = (𝟙 T.toSSet ⊗ₘ j) ≫ s :=
        congrArg (fun u ↦ (𝟙 T.toSSet ⊗ₘ j) ≫ u) (parameter_left T U K I s t)
      _ = _ := (parameter_left T U K I' _ _).symm
  · calc
      _ = (𝟙 E.toSSet ⊗ₘ j) ≫ (tripleRightU T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t := by
        simp only [← Category.assoc]
        exact congrArg (fun u ↦ u ≫ parameter T U K I s t)
          (tensor_square (I := I) (tripleRightU T E U) j)
      _ = (𝟙 E.toSSet ⊗ₘ j) ≫ connector T U K I s t :=
        congrArg (fun u ↦ (𝟙 E.toSSet ⊗ₘ j) ≫ u) (parameter_middle T U K I s t)
      _ = connector T U K I' _ _ := (connector_mapTime T U K I s t j).symm
      _ = _ := (parameter_middle T U K I' _ _).symm
  · calc
      _ = (𝟙 U.toSSet ⊗ₘ j) ≫ (tripleRightV T E U ⊗ₘ 𝟙 I) ≫ parameter T U K I s t := by
        simp only [← Category.assoc]
        exact congrArg (fun u ↦ u ≫ parameter T U K I s t)
          (tensor_square (I := I) (tripleRightV T E U) j)
      _ = (𝟙 U.toSSet ⊗ₘ j) ≫ t :=
        congrArg (fun u ↦ (𝟙 U.toSSet ⊗ₘ j) ≫ u) (parameter_right T U K I s t)
      _ = _ := (parameter_right T U K I' _ _).symm


private theorem post_vertexLabel {X : SSet.{0}} {K' : SimplexCategory}
    (g : K ⟶ K') (u : X ⟶ J.obj K) (x : X.obj (op ⦋0⦌)) :
    vertexLabels ((u ≫ J.map g) ≫ (iso K').hom) x =
      g.toOrderHom (vertexLabels (u ≫ (iso K).hom) x) := by
  have h : J.map g ≫ (iso K').hom = (iso K).hom ≫ codiscreteNerve.map (vertices.map g) :=
    parameterCodiscreteIso.hom.naturality g
  rw [Category.assoc, h, ← Category.assoc]
  rfl

private theorem connector_codiscrete :
    connector T U K I s t ≫ (iso K).hom =
      mapOfVertices (E.toSSet ⊗ I) (connectorLabel T U K I s t) := by
  rw [connector, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The connector respects a common coefficient operator on all its time simplices. -/
theorem connector_postcomp {K' : SimplexCategory} (g : K ⟶ K') :
    connector T U K I s t ≫ J.map g =
      connector T U K' I (s ≫ J.map g) (t ≫ J.map g) := by
  apply (cancel_mono (iso K').hom).mp
  apply codiscrete_hom_ext K'
  intro x
  rw [post_vertexLabel, connector_codiscrete, connector_codiscrete,
    vertexLabels_mapOfVertices, vertexLabels_mapOfVertices]
  unfold connectorLabel
  split
  · have h : leftBoundary T K' I (s ≫ J.map g) =
        leftBoundary T K I s ≫ J.map g := by
      simp only [leftBoundary, Category.assoc]
    rw [h, post_vertexLabel]
  · have h : rightBoundary U K' I (t ≫ J.map g) =
        rightBoundary U K I t ≫ J.map g := by
      simp only [rightBoundary, Category.assoc]
    rw [h, post_vertexLabel]

/-- The entire binary parameter respects the same coefficient operator. -/
theorem parameter_postcomp {K' : SimplexCategory} (g : K ⟶ K') :
    parameter T U K I s t ≫ J.map g =
      parameter T U K' I (s ≫ J.map g) (t ≫ J.map g) := by
  apply parameter_hom_ext T U K' I
  · rw [← Category.assoc, parameter_left, parameter_left]
  · rw [← Category.assoc, parameter_middle, parameter_middle, connector_postcomp]
  · rw [← Category.assoc, parameter_right, parameter_right]

section SideOperators

open DaggerChosenRigidificationNecklace (NecklaceCode)

variable {L R L' R' : NecklaceCode}
variable (f : NecklaceCode.Hom.{0} L L') (g : NecklaceCode.Hom.{0} R R')

/-- The actual joined native operator on the two side arrows. -/
def sideMap : NecklaceCode.Hom.{0} (JTOrderedLabelBinaryGlue.code L R)
    (JTOrderedLabelBinaryGlue.code L' R') :=
  wedgeMap f (wedgeMap (𝟙 E) g)

theorem sideMap_left :
    tripleRightT L E R ≫ (sideMap f g).map = f.map ≫ tripleRightT L' E R' :=
  wedgeMap_left f (wedgeMap (𝟙 E) g)

theorem sideMap_middle :
    tripleRightU L E R ≫ (sideMap f g).map = tripleRightU L' E R' := by
  unfold tripleRightU sideMap
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left]
  change (𝟙 E.toSSet ≫ wedgeιLeft E R') ≫ _ = _
  rw [Category.id_comp]

theorem sideMap_right :
    tripleRightV L E R ≫ (sideMap f g).map = g.map ≫ tripleRightV L' E R' := by
  unfold tripleRightV sideMap
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_right, Category.assoc]

variable (u : L'.toSSet ⊗ I ⟶ J.obj K) (v : R'.toSSet ⊗ I ⟶ J.obj K)

private abbrev pullLeft := (f.map ⊗ₘ 𝟙 I) ≫ u
private abbrev pullRight := (g.map ⊗ₘ 𝟙 I) ≫ v

/-- The complete groupoid parameter restricts naturally along any pair of
native side arrows, including its time-dependent connector. -/
theorem parameter_mapSides :
    ((sideMap f g).map ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v =
      parameter L R K I (pullLeft K I f u) (pullRight K I g v) := by
  have hl : leftBoundary L K I (pullLeft K I f u) = leftBoundary L' K I u := by
    unfold leftBoundary pullLeft
    rw [← Category.assoc (pointAt L (ULift.up (Fin.last L.len)) ⊗ₘ 𝟙 I),
      tensorHom_comp_tensorHom, pointAt_last_comp, Category.id_comp]
  have hr : rightBoundary R K I (pullRight K I g v) = rightBoundary R' K I v := by
    unfold rightBoundary pullRight
    rw [← Category.assoc (pointAt R (ULift.up 0) ⊗ₘ 𝟙 I),
      tensorHom_comp_tensorHom, pointAt_first_comp, Category.id_comp]
  apply parameter_hom_ext L R K I
  · calc
      _ = ((f.map ≫ tripleRightT L' E R') ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, sideMap_left]
      _ = (f.map ⊗ₘ 𝟙 I) ≫ (tripleRightT L' E R' ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = _ := by rw [parameter_left, parameter_left]
  · rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, sideMap_middle,
      parameter_middle, parameter_middle]
    exact (connector_eq_of_boundary L R K I _ _ hl hr).symm
  · calc
      _ = ((g.map ≫ tripleRightV L' E R') ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, sideMap_right]
      _ = (g.map ⊗ₘ 𝟙 I) ≫ (tripleRightV L' E R' ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = _ := by rw [parameter_right, parameter_right]

end SideOperators

end

end DaggerModels.PartII.JTBinaryPrismParameter
