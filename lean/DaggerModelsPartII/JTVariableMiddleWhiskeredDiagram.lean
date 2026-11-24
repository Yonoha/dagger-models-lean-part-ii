import DaggerModelsPartII.JTWhiskeredSeamDiagram

/-! Three-piece decorated labels with all three native necklaces varying. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTVariableMiddleWhiskeredDiagram

open JTThreePieceLabelOperators (Data index indexMap indexMap_projection)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}

private abbrev proj (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private instance : (proj W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

/-- Three natural full coefficients, with changing left, middle, and right
native necklaces and one common coefficient degree. -/
structure Family (P M R : I ⥤ NecklaceCode) (K : I ⥤ SimplexCategory) where
  data : ∀ a : I, Data W (P.obj a) (M.obj a) (R.obj a) (K.obj a) x y
  left_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).left = std.map (K.map g) ≫ (data b).left ≫ pre W (P.map g).map
  middle_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).middle = std.map (K.map g) ≫ (data b).middle ≫ pre W (M.map g).map
  right_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).right = std.map (K.map g) ≫ (data b).right ≫ pre W (R.map g).map

variable {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}

/-- The decorated operator is determined by the three full coefficient
naturality equations. -/
def Family.arrow (F : Family (W := W) (x := x) (y := y) P M R K)
    {a b : I} (g : a ⟶ b) : index (F.data a) ⟶ index (F.data b) :=
  indexMap (F.data a) (F.data b) (P.map g) (M.map g) (R.map g) (K.map g)
    (F.left_nat g) (F.middle_nat g) (F.right_nat g)

theorem Family.arrow_projection
    (F : Family (W := W) (x := x) (y := y) P M R K)
    {a b : I} (g : a ⟶ b) :
    (proj W x y).map (F.arrow g) =
      (wedgeMap (P.map g) (wedgeMap (M.map g) (R.map g)), K.map g) :=
  indexMap_projection (F.data a) (F.data b)
    (P.map g) (M.map g) (R.map g) (K.map g)
    (F.left_nat g) (F.middle_nat g) (F.right_nat g)

/-- The varying three-piece data form one genuine decorated-label functor. -/
def Family.labels (F : Family (W := W) (x := x) (y := y) P M R K) :
    I ⥤ DecoratedNecklaceHomDiagram.Index W x y where
  obj a := index (F.data a)
  map g := F.arrow g
  map_id a := by
    apply (proj W x y).map_injective
    rw [F.arrow_projection, (proj W x y).map_id,
      P.map_id, M.map_id, R.map_id, K.map_id]
    change (wedgeMap (𝟙 (P.obj a))
      (wedgeMap (𝟙 (M.obj a)) (𝟙 (R.obj a))), 𝟙 (K.obj a)) =
      (𝟙 (wedge (P.obj a) (wedge (M.obj a) (R.obj a))), 𝟙 (K.obj a))
    exact congrArg (fun u : (wedge (P.obj a)
        (wedge (M.obj a) (R.obj a))) ⟶
          wedge (P.obj a) (wedge (M.obj a) (R.obj a)) ↦
          (u, 𝟙 (K.obj a)))
      ((congrArg (wedgeMap (𝟙 (P.obj a)))
        (wedgeMap_id (T := M.obj a) (U := R.obj a))).trans
        (wedgeMap_id (T := P.obj a) (U := wedge (M.obj a) (R.obj a))))
  map_comp g h := by
    apply (proj W x y).map_injective
    rw [F.arrow_projection, (proj W x y).map_comp,
      F.arrow_projection, F.arrow_projection,
      P.map_comp, M.map_comp, R.map_comp, K.map_comp]
    apply Prod.ext
    · change wedgeMap (Hom.comp (P.map g) (P.map h))
          (wedgeMap (Hom.comp (M.map g) (M.map h))
            (Hom.comp (R.map g) (R.map h))) =
        Hom.comp
          (wedgeMap (P.map g) (wedgeMap (M.map g) (R.map g)))
          (wedgeMap (P.map h) (wedgeMap (M.map h) (R.map h)))
      rw [← wedgeMap_comp, ← wedgeMap_comp]
    · rfl

theorem Family.labels_projection
    (F : Family (W := W) (x := x) (y := y) P M R K) (a : I) :
    (proj W x y).obj ((F.labels).obj a) =
      (wedge (P.obj a) (wedge (M.obj a) (R.obj a)), K.obj a) := rfl

/-- A coherent change of the middle native diagram and common coefficient
degree, with the surrounding native diagrams retained literally. -/
structure MiddleChange {N : I ⥤ NecklaceCode} {L : I ⥤ SimplexCategory}
    (F : Family (W := W) (x := x) (y := y) P M R K)
    (G : Family (W := W) (x := x) (y := y) P N R L) where
  middle : M ⟶ N
  degree : K ⟶ L
  left : ∀ a : I,
    (F.data a).left = std.map (degree.app a) ≫ (G.data a).left ≫
      pre W ((𝟙 (P.obj a) : P.obj a ⟶ P.obj a).map)
  center : ∀ a : I,
    (F.data a).middle = std.map (degree.app a) ≫ (G.data a).middle ≫
      pre W (middle.app a).map
  right : ∀ a : I,
    (F.data a).right = std.map (degree.app a) ≫ (G.data a).right ≫
      pre W ((𝟙 (R.obj a) : R.obj a ⟶ R.obj a).map)

variable {N : I ⥤ NecklaceCode} {L : I ⥤ SimplexCategory}
variable {F : Family (W := W) (x := x) (y := y) P M R K}
variable {G : Family (W := W) (x := x) (y := y) P N R L}

/-- Each coefficient change gives the corresponding actual decorated arrow. -/
def MiddleChange.app (C : MiddleChange F G) (a : I) :
    F.labels.obj a ⟶ G.labels.obj a :=
  indexMap (F.data a) (G.data a) (𝟙 (P.obj a)) (C.middle.app a)
    (𝟙 (R.obj a)) (C.degree.app a)
    (C.left a) (C.center a) (C.right a)

theorem MiddleChange.app_projection (C : MiddleChange F G) (a : I) :
    (proj W x y).map (C.app a) =
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap (C.middle.app a) (𝟙 (R.obj a))), C.degree.app a) :=
  indexMap_projection (F.data a) (G.data a) (𝟙 (P.obj a))
    (C.middle.app a) (𝟙 (R.obj a)) (C.degree.app a)
    (C.left a) (C.center a) (C.right a)

/-- The component decorated arrows are natural for all three native
operators and the coefficient-degree operator. -/
def MiddleChange.hom (C : MiddleChange F G) : F.labels ⟶ G.labels where
  app := C.app
  naturality {a b} g := by
    apply (proj W x y).map_injective
    simp only [Functor.map_comp]
    change (proj W x y).map (F.arrow g) ≫ (proj W x y).map (C.app b) =
      (proj W x y).map (C.app a) ≫ (proj W x y).map (G.arrow g)
    rw [F.arrow_projection, G.arrow_projection,
      C.app_projection, C.app_projection]
    apply Prod.ext
    · change Hom.comp
          (wedgeMap (P.map g) (wedgeMap (M.map g) (R.map g)))
          (wedgeMap (𝟙 (P.obj b))
            (wedgeMap (C.middle.app b) (𝟙 (R.obj b)))) =
        Hom.comp
          (wedgeMap (𝟙 (P.obj a))
            (wedgeMap (C.middle.app a) (𝟙 (R.obj a))))
          (wedgeMap (P.map g) (wedgeMap (N.map g) (R.map g)))
      rw [← wedgeMap_comp, ← wedgeMap_comp,
        ← wedgeMap_comp, ← wedgeMap_comp]
      have hp₀ : Hom.comp (P.map g) (𝟙 (P.obj b)) = P.map g :=
        Hom.ext (Category.comp_id (P.map g).map)
      have hp₁ : Hom.comp (𝟙 (P.obj a)) (P.map g) = P.map g :=
        Hom.ext (Category.id_comp (P.map g).map)
      have hr₀ : Hom.comp (R.map g) (𝟙 (R.obj b)) = R.map g :=
        Hom.ext (Category.comp_id (R.map g).map)
      have hr₁ : Hom.comp (𝟙 (R.obj a)) (R.map g) = R.map g :=
        Hom.ext (Category.id_comp (R.map g).map)
      rw [hp₀, hp₁, hr₀, hr₁]
      exact congrArg (wedgeMap (P.map g))
        (congrArg (fun q ↦ wedgeMap q (R.map g)) (C.middle.naturality g))
    · change K.map g ≫ C.degree.app b = C.degree.app a ≫ L.map g
      exact C.degree.naturality g

theorem MiddleChange.hom_projection (C : MiddleChange F G) (a : I) :
    (proj W x y).map ((C.hom).app a) =
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap (C.middle.app a) (𝟙 (R.obj a))), C.degree.app a) :=
  C.app_projection a

end
end DaggerModels.PartII.JTVariableMiddleWhiskeredDiagram
