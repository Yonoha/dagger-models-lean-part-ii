import DaggerModelsPartII.ReedyMaps

/-! Low-degree calculations for the exact Reedy indexing diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

/-- The sole degeneracy index in degree one. -/
def latchingIndexOne : LatchingIndex 1 :=
  ⟨CostructuredArrow.mk (SimplexCategory.σ (0 : Fin 1)).op,
    ⟨Nat.zero_lt_one, by
      change Epi (SimplexCategory.σ (0 : Fin 1))
      infer_instance⟩⟩

/-- Every proper surjection out of `[1]` has target `[0]`. -/
theorem latchingIndexOne_left (s : LatchingIndex 1) : s.obj.left.unop = ⦋0⦌ :=
  SimplexCategory.ext _ _ (Nat.lt_one_iff.mp s.property.1)

/-- The degree-one degeneracy index is terminal in the latching category. -/
def latchingIndexOneIsTerminal : IsTerminal latchingIndexOne :=
  IsTerminal.ofUniqueHom
    (fun s ↦ ObjectProperty.homMk (CostructuredArrow.homMk
      (eqToHom (congrArg op (latchingIndexOne_left s))) (by
        apply Quiver.Hom.unop_inj
        exact (SimplexCategory.isTerminalZero.ofIso
          (eqToIso (latchingIndexOne_left s).symm)).hom_ext _ _)))
    (fun s f ↦ by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      exact (SimplexCategory.isTerminalZero.ofIso
        (eqToIso (latchingIndexOne_left s).symm)).hom_ext _ _)

/-- The face selecting vertex `i` of the one-simplex. -/
def matchingFaceOne (i : Fin 2) : MatchingIndex 1 :=
  ⟨StructuredArrow.mk (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op,
    ⟨Nat.zero_lt_one, by
      change Mono (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)
      apply SimplexCategory.mono_iff_injective.mpr
      change Function.Injective (fun _ : Fin 1 ↦ i)
      exact fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩

/-- A proper face in degree one has source `[0]`. -/
theorem matchingIndexOne_right (s : MatchingIndex 1) : s.obj.right.unop = ⦋0⦌ :=
  SimplexCategory.ext _ _ (Nat.lt_one_iff.mp s.property.1)

def matchingIndexOneVertex (s : MatchingIndex 1) : Fin 2 :=
  s.obj.hom.unop.toOrderHom 0

/-- The two vertex faces exhaust the matching index in degree one. -/
theorem matchingIndexOne_cases (s : MatchingIndex 1) :
    ∃ i : Fin 2, s = matchingFaceOne i := by
  rcases s with ⟨s, hs⟩
  obtain ⟨Y, g, rfl⟩ := StructuredArrow.mk_surjective s
  have hY : Y = op ⦋0⦌ := congrArg op (matchingIndexOne_right ⟨_, hs⟩)
  subst Y
  refine ⟨g.unop.toOrderHom 0, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  change StructuredArrow.mk g =
    StructuredArrow.mk (SimplexCategory.const ⦋0⦌ ⦋1⦌ (g.unop.toOrderHom 0)).op
  congr 1
  apply Quiver.Hom.unop_inj
  ext j : 3
  have hj : j = 0 := by
    change (j : Fin 1) = 0
    exact @Subsingleton.elim (Fin 1) inferInstance j 0
  subst j
  rfl

/-- A morphism between vertex faces preserves the selected vertex. -/
theorem matchingFaceOne_vertex_eq {i j : Fin 2}
    (f : matchingFaceOne i ⟶ matchingFaceOne j) : i = j := by
  have h := congrArg Quiver.Hom.unop (StructuredArrow.w f.hom)
  change f.hom.right.unop ≫ SimplexCategory.const ⦋0⦌ ⦋1⦌ i =
    SimplexCategory.const ⦋0⦌ ⦋1⦌ j at h
  have hId : f.hom.right.unop = 𝟙 ⦋0⦌ := SimplexCategory.isTerminalZero.hom_ext _ _
  rw [hId] at h
  have h' : SimplexCategory.const ⦋0⦌ ⦋1⦌ i = SimplexCategory.const ⦋0⦌ ⦋1⦌ j :=
    (Category.id_comp (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).symm.trans h
  exact SimplexCategory.congr_toOrderHom_apply h' 0

/-- Endomorphisms of a vertex face are identities. -/
theorem matchingFaceOne_endomorphism_eq_id {i : Fin 2}
    (f : matchingFaceOne i ⟶ matchingFaceOne i) : f = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.isTerminalZero.hom_ext _ _

noncomputable section

variable {C : Type u} [Category.{v} C]

section Matching

variable [HasLimitsOfSize.{0, 0} C]

/-- The product cone over the two vertex faces in degree one. -/
def matchingOneCone (W : SimplexCategoryᵒᵖ ⥤ C) : Cone (matchingProjection 1 ⋙ W) where
  pt := ∏ᶜ fun _ : Fin 2 ↦ W.obj (op ⦋0⦌)
  π :=
    { app := fun s ↦ Pi.π _ (matchingIndexOneVertex s) ≫
        W.map (eqToHom (congrArg op (matchingIndexOne_right s).symm))
      naturality := by
        intro s t f
        obtain ⟨i, rfl⟩ := matchingIndexOne_cases s
        obtain ⟨j, rfl⟩ := matchingIndexOne_cases t
        obtain rfl := matchingFaceOne_vertex_eq f
        rw [matchingFaceOne_endomorphism_eq_id f]
        simp }

@[simp] theorem matchingOneCone_π_face (W : SimplexCategoryᵒᵖ ⥤ C) (i : Fin 2) :
    (matchingOneCone W).π.app (matchingFaceOne i) =
      Pi.π (fun _ : Fin 2 ↦ W.obj (op ⦋0⦌)) i := by
  change Pi.π (fun _ : Fin 2 ↦ W.obj (op ⦋0⦌)) i ≫
    W.map (eqToHom (rfl : op ⦋0⦌ = op ⦋0⦌)) = Pi.π (fun _ : Fin 2 ↦ W.obj (op ⦋0⦌)) i
  simp

/-- The product cone is limiting. -/
def matchingOneConeIsLimit (W : SimplexCategoryᵒᵖ ⥤ C) :
    IsLimit (matchingOneCone W) where
  lift s := Pi.lift (fun i ↦ s.π.app (matchingFaceOne i))
  fac s j := by
    obtain ⟨i, rfl⟩ := matchingIndexOne_cases j
    rw [matchingOneCone_π_face, Pi.lift_π]
  uniq s m h := by
    apply Pi.hom_ext
    intro i
    rw [Pi.lift_π]
    simpa only [matchingOneCone_π_face] using h (matchingFaceOne i)

/-- Degree-one matching is the product of the two zeroth-level vertex objects. -/
def matchingOneIso (W : SimplexCategoryᵒᵖ ⥤ C) :
    (matchingFunctor 1).obj W ≅ ∏ᶜ fun _ : Fin 2 ↦ W.obj (op ⦋0⦌) :=
  limit.isoLimitCone ⟨matchingOneCone W, matchingOneConeIsLimit W⟩

/-- The two projections of the degree-one matching map are the vertex faces. -/
theorem matchingComparison_one (W : SimplexCategoryᵒᵖ ⥤ C) (i : Fin 2) :
    (matchingComparison 1).app W ≫ (matchingOneIso W).hom ≫
        Pi.π (fun _ : Fin 2 ↦ W.obj (op ⦋0⦌)) i =
      W.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op := by
  rw [← matchingOneCone_π_face W i]
  change limit.lift _ (matchingCone 1 W) ≫
      (limit.isoLimitCone ⟨matchingOneCone W, matchingOneConeIsLimit W⟩).hom ≫
        (matchingOneCone W).π.app (matchingFaceOne i) = _
  rw [limit.isoLimitCone_hom_π]
  exact limit.lift_π _ _

end Matching

variable [HasColimitsOfSize.{0, 0} C]

/-- The degree-one latching object is canonically the zeroth level. -/
def latchingOneIso (W : SimplexCategoryᵒᵖ ⥤ C) :
    (latchingFunctor 1).obj W ≅ W.obj (op ⦋0⦌) := by
  letI := isIso_ι_of_isTerminal latchingIndexOneIsTerminal (latchingProjection 1 ⋙ W)
  exact (asIso (colimit.ι (latchingProjection 1 ⋙ W) latchingIndexOne)).symm

/-- The degree-one latching map is the degeneracy from the zeroth level. -/
theorem latchingComparison_one (W : SimplexCategoryᵒᵖ ⥤ C) :
    (latchingOneIso W).inv ≫ (latchingComparison 1).app W =
      W.map (SimplexCategory.σ (0 : Fin 1)).op :=
  colimit.ι_desc _ _

end

end DaggerModels.PartII
