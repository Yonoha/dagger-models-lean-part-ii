import DaggerModelsPartII.HomotopyMappingEquivalence
import TopCatModelCategory.SSet.SingularConnected

/-! The passage from vertices and edges of a resolution mapping space to homotopy classes. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII.CosimplicialResolution

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance mappingComponentsReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

variable {X : C} (R : CosimplicialResolution X)

/-- The cofibrant object in degree zero of a source resolution. -/
abbrev sourceZero : C := (R.oppositeDiagram.obj (op ⦋0⦌)).unop

/-- The degree-zero augmentation to the original source. -/
abbrev augmentationZero : R.sourceZero ⟶ X := (R.augmentationOp.app (op ⦋0⦌)).unop

theorem sourceZero_isCofibrant : IsCofibrant R.sourceZero := by
  letI := R.fibrantOp
  letI := reedyFibrant_obj R.oppositeDiagram (op ⦋0⦌)
  let p := terminal.from (R.oppositeDiagram.obj (op ⦋0⦌))
  have h := mem_fibrations p
  rw [fibrations_op] at h
  exact (isCofibrant_iff_of_isInitial p.unop (initialUnopOfTerminal terminalIsTerminal)).mpr
    ((cofibration_iff _).mpr h)

theorem augmentationZero_trivialFibration : trivialFibrations C R.augmentationZero := by
  refine ⟨?_, R.augmentation_weak _⟩
  have h : reedyLatchingProperty (cofibrations Cᵒᵖ) R.augmentationOp :=
    R.augmentationOp_mem.1
  have h₀ := h 0
  change cofibrations Cᵒᵖ (R.augmentationOp.app (op ⦋0⦌))
  rw [← relativeLatchingMap_zero R.augmentationOp]
  exact ((cofibrations Cᵒᵖ).cancel_left_of_respectsIso
    (relativeLatchingZeroSourceIso R.augmentationOp).inv _).mpr h₀

private def mappingCylinder : Cylinder R.sourceZero where
  I := (R.oppositeDiagram.obj (op ⦋1⦌)).unop
  i₀ := (R.oppositeDiagram.map (SimplexCategory.δ (1 : Fin 2)).op).unop
  i₁ := (R.oppositeDiagram.map (SimplexCategory.δ (0 : Fin 2)).op).unop
  π := (R.oppositeDiagram.map (SimplexCategory.σ (0 : Fin 1)).op).unop
  i₀_π := by
    rw [← unop_comp, ← R.oppositeDiagram.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ' (by decide : (1 : Fin 2) = (0 : Fin 1).succ),
      op_id, R.oppositeDiagram.map_id, unop_id]
  i₁_π := by
    rw [← unop_comp, ← R.oppositeDiagram.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self' (by decide : (0 : Fin 2) = (0 : Fin 1).castSucc),
      op_id, R.oppositeDiagram.map_id, unop_id]
  weakEquivalence_π := by
    apply (weakEquivalence_iff _).mpr
    have h := congrArg Quiver.Hom.unop
      (R.augmentationOp.naturality (SimplexCategory.σ (0 : Fin 1)).op)
    change (R.augmentationOp.app (op ⦋1⦌)).unop ≫ 𝟙 X =
      (R.oppositeDiagram.map (SimplexCategory.σ (0 : Fin 1)).op).unop ≫
        R.augmentationZero at h
    have h' := (Category.comp_id ((R.augmentationOp.app (op ⦋1⦌)).unop)).symm.trans h
    exact (weakEquivalences C).of_postcomp _ _ (R.augmentation_weak (op ⦋0⦌))
      (h' ▸ R.augmentation_weak (op ⦋1⦌))

/-- Vertices of the mapping space are maps out of the zeroth level. Each edge
gives a cylinder homotopy, so components determine left homotopy classes. -/
def componentToLeftHomotopyClass (Z : C) :
    (R.mappingSSet.obj Z).π₀ → LeftHomotopyClass R.sourceZero Z :=
  Quot.lift (fun x ↦ LeftHomotopyClass.mk x.unop) (by
    rintro _ _ ⟨e, rfl, rfl⟩
    apply LeftHomotopyClass.sound
    exact ⟨R.mappingCylinder, ⟨{ h := e.unop, h₀ := rfl, h₁ := rfl }⟩⟩)

private theorem bijective_mapπ₀_of_weak {A B : SSet.{v}} (f : A ⟶ B)
    (hf : weakEquivalences SSet.{v} f) : Function.Bijective (SSet.mapπ₀ f) := by
  let G := SSet.toTop.{v} ⋙ TopCat.toSSet
  have hG : WeakEquivalence (G.map f) :=
    (TopCat.weakEquivalence_toSSet_map_iff _).mpr ((SSet.modelCategoryQuillen.weakEquivalence_iff _).mp
      ((weakEquivalence_iff _).mpr hf))
  have hmap := ((SSet.weakEquivalence_iff_kanComplexW _).mp hG).bijective_mapπ₀
  have hA := SSet.bijective_mapπ₀_sSetTopAdj_unit_app A
  have hB := SSet.bijective_mapπ₀_sSetTopAdj_unit_app B
  apply (Function.Bijective.of_comp_iff' hB _).mp
  have hcomp : SSet.mapπ₀ (sSetTopAdj.unit.app B) ∘ SSet.mapπ₀ f =
      SSet.mapπ₀ (G.map f) ∘ SSet.mapπ₀ (sSetTopAdj.unit.app A) := by
    funext x
    change SSet.mapπ₀ _ (SSet.mapπ₀ _ x) = SSet.mapπ₀ _ (SSet.mapπ₀ _ x)
    rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply]
    exact congrArg (fun k ↦ SSet.mapπ₀ k x) (sSetTopAdj.unit.naturality f)
  rw [hcomp]
  exact hmap.comp hA

private theorem weakEquivalence_of_homotopyInverse {A B : C}
    [IsCofibrant A] [IsCofibrant B] [IsFibrant A] [IsFibrant B]
    (f : A ⟶ B) (g : B ⟶ A) (hA : LeftHomotopyRel (f ≫ g) (𝟙 A))
    (hB : LeftHomotopyRel (g ≫ f) (𝟙 B)) : WeakEquivalence f := by
  let d := factorizationData (trivialCofibrations C) (fibrations C) f
  letI : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  letI : IsFibrant d.Z := isFibrant_of_fibration d.p
  have h₀ : RightHomotopyRel (d.p ≫ (g ≫ d.i)) (𝟙 d.Z) := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence d.Z d.i).1
    change (RightHomotopyClass.mk (d.p ≫ g ≫ d.i)).precomp d.i =
      (RightHomotopyClass.mk (𝟙 d.Z)).precomp d.i
    rw [RightHomotopyClass.precomp_mk, RightHomotopyClass.precomp_mk,
      ← Category.assoc d.i d.p, d.fac, Category.comp_id, ← Category.assoc,
      RightHomotopyClass.mk_eq_mk_iff]
    simpa using (hA.postcomp d.i).rightHomotopyRel
  have h₁ : RightHomotopyRel ((g ≫ d.i) ≫ d.p) (𝟙 B) := by
    rw [Category.assoc, d.fac]
    exact hB.rightHomotopyRel
  haveI : WeakEquivalence d.p :=
    DaggerNativeFibrationHomotopyInverseWeak.fibration_weakEquivalence_of_homotopy_inverse
      d.p (g ≫ d.i) h₀ h₁
  rw [← d.fac]
  infer_instance

/-- A map between fibrant objects is weak if precomposition gives weak equivalences
of derived mapping spaces into its source and its target. -/
theorem weak_of_mappingTests_self {Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    (hX : homotopyMappingWeakEquivalences X f)
    (hY : homotopyMappingWeakEquivalences Y f) : weakEquivalences C f := by
  let R := cosimplicialResolution X
  let S := cosimplicialResolution Y
  let d := R.comparison S f
  let p : R.sourceZero ⟶ S.sourceZero := (d.mapOp.app (op ⦋0⦌)).unop
  have comm : p ≫ S.augmentationZero = R.augmentationZero ≫ f :=
    congrArg Quiver.Hom.unop (congr_app d.comm (op ⦋0⦌))
  letI := R.sourceZero_isCofibrant
  letI := S.sourceZero_isCofibrant
  letI : Fibration R.augmentationZero := (fibration_iff _).mpr R.augmentationZero_trivialFibration.1
  letI : Fibration S.augmentationZero := (fibration_iff _).mpr S.augmentationZero_trivialFibration.1
  letI : WeakEquivalence R.augmentationZero :=
    (weakEquivalence_iff _).mpr R.augmentationZero_trivialFibration.2
  letI : WeakEquivalence S.augmentationZero :=
    (weakEquivalence_iff _).mpr S.augmentationZero_trivialFibration.2
  letI : IsFibrant R.sourceZero := isFibrant_of_fibration R.augmentationZero
  letI : IsFibrant S.sourceZero := isFibrant_of_fibration S.augmentationZero
  have hx := bijective_mapπ₀_of_weak _ ((homotopyMappingWeakEquivalences_iff X d).mp hX)
  have hy := bijective_mapπ₀_of_weak _ ((homotopyMappingWeakEquivalences_iff Y d).mp hY)
  let componentR {Z : C} (q : R.sourceZero ⟶ Z) :=
    SSet.π₀.mk (X := R.mappingSSet.obj Z) q.op
  let componentS {Z : C} (q : S.sourceZero ⟶ Z) :=
    SSet.π₀.mk (X := S.mappingSSet.obj Z) q.op
  obtain ⟨a, ha⟩ := hx.2 (componentR R.augmentationZero)
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  let a' : S.sourceZero ⟶ X := a.unop
  change componentR (p ≫ a') = componentR R.augmentationZero at ha
  have hb : componentS (a' ≫ f) = componentS S.augmentationZero := by
    apply hy.1
    change componentR (p ≫ a' ≫ f) = componentR (p ≫ S.augmentationZero)
    rw [comm, ← Category.assoc]
    exact congrArg (SSet.mapπ₀ (R.mappingSSet.map f)) ha
  have sq : CommSq (initial.to R.sourceZero) (initial.to S.sourceZero) R.augmentationZero a' :=
    ⟨initial.hom_ext _ _⟩
  let g := sq.lift
  have hg : g ≫ R.augmentationZero = a' := sq.fac_right
  have h₀ : LeftHomotopyRel (p ≫ g) (𝟙 R.sourceZero) := by
    rw [← LeftHomotopyClass.mk_eq_mk_iff]
    apply (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
      R.sourceZero R.augmentationZero).1
    simp only [LeftHomotopyClass.postcomp_mk, Category.assoc, hg, Category.id_comp]
    exact congrArg (R.componentToLeftHomotopyClass X) ha
  have h₁ : LeftHomotopyRel (g ≫ p) (𝟙 S.sourceZero) := by
    rw [← LeftHomotopyClass.mk_eq_mk_iff]
    apply (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
      S.sourceZero S.augmentationZero).1
    simp only [LeftHomotopyClass.postcomp_mk, Category.assoc, comm, ← Category.assoc g, hg,
      Category.id_comp]
    exact congrArg (S.componentToLeftHomotopyClass Y) hb
  have hp : weakEquivalences C p := (weakEquivalence_iff _).mp
    (weakEquivalence_of_homotopyInverse p g h₀ h₁)
  exact (weakEquivalences C).of_precomp _ _ R.augmentationZero_trivialFibration.2
    (comm ▸ (weakEquivalences C).comp_mem _ _ hp S.augmentationZero_trivialFibration.2)

end

end DaggerModels.PartII.CosimplicialResolution
