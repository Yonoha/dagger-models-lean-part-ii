import DaggerModelsPartII.JTXiEndpointCollapse

/-!
# The literal endpoint-collapsed CE interval augmentation

The CE pushout maps to the constant ordinary interval by forgetting the
groupoid parameter in the interval cylinder and using the original
boundary inclusion. A chosen vertex of the groupoid parameter provides
a pointwise section of this augmentation.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTCEAugmentation

open JTXiEndpointCollapse GroupoidSimplex

noncomputable section

/-- Forget the J factor in the literal interval cylinder. -/
def intervalProjection : intervalCylinder ⟶
    (Functor.const SimplexCategory).obj interval where
  app k := CartesianMonoidalCategory.fst interval (parameter.obj k)
  naturality k l f := by
    change (𝟙 interval ⊗ₘ parameter.map f) ≫
      CartesianMonoidalCategory.fst interval (parameter.obj l) =
        CartesianMonoidalCategory.fst interval (parameter.obj k)
    simpa only [Category.comp_id] using
      (CartesianMonoidalCategory.tensorHom_fst
        (𝟙 interval) (parameter.map f))

private theorem intervalProjection_compatibility :
    cylinderInclusion ≫ intervalProjection =
      cylinderProjection ≫
        (Functor.const SimplexCategory).map (SSet.boundary 1).ι := by
  apply NatTrans.ext
  funext k
  change ((SSet.boundary 1).ι ⊗ₘ 𝟙 (parameter.obj k)) ≫
      CartesianMonoidalCategory.fst interval (parameter.obj k) =
        CartesianMonoidalCategory.fst boundary (parameter.obj k) ≫
          (SSet.boundary 1).ι
  exact CartesianMonoidalCategory.tensorHom_fst
    (SSet.boundary 1).ι (𝟙 (parameter.obj k))

/-- The actual CE diagram maps naturally to the constant ordinary
interval. Both pushout legs are the original chosen maps. -/
def CEAugmentation : CE ⟶ (Functor.const SimplexCategory).obj interval :=
  pushout.desc intervalProjection
    ((Functor.const SimplexCategory).map (SSet.boundary 1).ι)
    intervalProjection_compatibility

/-- On the interval-cylinder copy, augmentation is the first projection. -/
theorem CEAugmentation_interval (k : SimplexCategory) :
    CE_interval.app k ≫ CEAugmentation.app k =
      CartesianMonoidalCategory.fst interval (parameter.obj k) := by
  exact NatTrans.congr_app
    (pushout.inl_desc intervalProjection
      ((Functor.const SimplexCategory).map (SSet.boundary 1).ι)
      intervalProjection_compatibility) k

/-- On the ordered boundary, augmentation is exactly the original
boundary inclusion into `Δ[1]`. -/
theorem CEAugmentation_boundary (k : SimplexCategory) :
    CE_boundary.app k ≫ CEAugmentation.app k = (SSet.boundary 1).ι := by
  exact NatTrans.congr_app
    (pushout.inr_desc intervalProjection
      ((Functor.const SimplexCategory).map (SSet.boundary 1).ι)
      intervalProjection_compatibility) k

/-- The map from the terminal zero-simplex selected by a literal vertex
of the groupoid parameter. -/
def parameterVertexMap (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ parameter.obj k :=
  SSet.yonedaEquiv.symm v

/-- A chosen J vertex gives a literal section of the interval-cylinder
projection at parameter degree `k`. -/
def intervalSectionInput (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    interval ⟶ intervalCylinder.obj k :=
  CartesianMonoidalCategory.lift (𝟙 interval)
    (SSet.stdSimplex.isTerminalObj₀.from interval ≫ parameterVertexMap k v)

/-- The resulting section into the actual CE pushout. -/
def intervalSection (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    interval ⟶ CE.obj k :=
  intervalSectionInput k v ≫ CE_interval.app k

/-- The chosen section is a strict right inverse to CE augmentation. -/
theorem intervalSection_aug (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    intervalSection k v ≫ CEAugmentation.app k = 𝟙 interval := by
  rw [intervalSection, Category.assoc, CEAugmentation_interval]
  exact CartesianMonoidalCategory.lift_fst _ _

/-- The same vertex yields a section of the ordered boundary cylinder. -/
private def boundarySectionInput (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    boundary ⟶ boundaryCylinder.obj k :=
  CartesianMonoidalCategory.lift (𝟙 boundary)
    (SSet.stdSimplex.isTerminalObj₀.from boundary ≫ parameterVertexMap k v)

private theorem boundarySection_cylinderInclusion (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    (SSet.boundary 1).ι ≫ intervalSectionInput k v =
      boundarySectionInput k v ≫ cylinderInclusion.app k := by
  have hterminal : (SSet.boundary 1).ι ≫
      SSet.stdSimplex.isTerminalObj₀.from interval =
        SSet.stdSimplex.isTerminalObj₀.from boundary :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply NatTrans.ext
  funext n x
  apply Prod.ext
  · rfl
  · exact congrArg ((parameterVertexMap k v).app n)
      (congrFun (NatTrans.congr_app hterminal n) x)

/-- A chosen J vertex section preserves the literal ordered boundary. -/
theorem boundary_intervalSection (k : SimplexCategory)
    (v : (parameter.obj k).obj (Opposite.op ⦋0⦌)) :
    (SSet.boundary 1).ι ≫ intervalSection k v = CE_boundary.app k := by
  rw [intervalSection, ← Category.assoc, boundarySection_cylinderInclusion]
  rw [Category.assoc]
  have h := (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)
  change IsPushout (cylinderInclusion.app k) (cylinderProjection.app k)
    (CE_interval.app k) (CE_boundary.app k) at h
  rw [h.w]
  change boundarySectionInput k v ≫
      CartesianMonoidalCategory.fst boundary (parameter.obj k) ≫
        CE_boundary.app k = CE_boundary.app k
  have hp : boundarySectionInput k v ≫
      CartesianMonoidalCategory.fst boundary (parameter.obj k) = 𝟙 boundary :=
    CartesianMonoidalCategory.lift_fst _ _
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f : boundary ⟶ boundary => f ≫ CE_boundary.app k) hp

end

end DaggerModels.PartII.JTCEAugmentation
