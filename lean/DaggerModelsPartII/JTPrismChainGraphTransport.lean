import DaggerModelsPartII.JTPrismChainGraphCover

/-!
# Canonical transport of full prism-chain graph covers

A map of graph domains and compatible coefficient operators send every lifted
vertex assignment to its image assignment. The construction retains all source
operators and has exact projection and lifted-parameter squares. No surjectivity,
fibrancy, raw equation or parameter section is required.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTPrismChainGraphTransport

open JTCodiscreteParameterPairing (coord coord_map)
open JTJointRelativeParameters (parameter_ext)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)

variable {I : Type} [SmallCategory I]

section Ext

variable (Y : I ⥤ SSet.{0}) {k m : I ⥤ SimplexCategory}
variable (p : Y ⟶ k ⋙ J) (α : m ⟶ k)

private theorem parameter_choice (i : I)
    (v : ((JTPrismChainGraphCover.cover Y p α).obj i).obj zero) :
    coord (m.obj i) zero (((JTPrismChainGraphCover.parameter Y p α).app i).app zero v) 0 =
      ((JTVertexAssignmentCover.coveredChoice Y m _ _).app i v).val.2 := by
  let φ := fun i (v : ((JTPrismChainGraphCover.cover Y p α).obj i).obj zero) ↦
    ((JTVertexAssignmentCover.coveredChoice Y m _ _).app i v).val.2
  have hφ : ∀ {i j : I} (f : i ⟶ j)
      (v : ((JTPrismChainGraphCover.cover Y p α).obj i).obj zero),
      φ j (((JTPrismChainGraphCover.cover Y p α).map f).app zero v) =
        (m.map f).toOrderHom (φ i v) := by
    intro i j f v
    exact congrArg (fun u ↦ u.val.2)
      (congrFun ((JTVertexAssignmentCover.coveredChoice Y m _ _).naturality f) v)
  exact JTJointRelativeParameters.parameterOfNaturalVertices_coord _ m φ hφ i v

/-- The complete graph projection and lifted parameter determine a cover map. -/
theorem hom_ext {A : I ⥤ SSet.{0}}
    {f g : A ⟶ JTPrismChainGraphCover.cover Y p α}
    (hπ : f ≫ JTPrismChainGraphCover.projection Y p α =
      g ≫ JTPrismChainGraphCover.projection Y p α)
    (hq : f ≫ JTPrismChainGraphCover.parameter Y p α =
      g ≫ JTPrismChainGraphCover.parameter Y p α) : f = g := by
  apply Limits.pullback.hom_ext
  · exact hπ
  · apply NatTrans.ext
    funext i
    apply ((evaluationAdjunctionLeft (Type 0) zero).homEquiv (A.obj i) _).symm.injective
    rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    funext v
    change ((JTVertexAssignmentCover.coveredChoice Y m _ _).app i
        ((f.app i).app zero v)) =
      ((JTVertexAssignmentCover.coveredChoice Y m _ _).app i ((g.app i).app zero v))
    apply Subtype.ext
    apply Prod.ext
    · rw [JTVertexAssignmentCover.coveredChoice_vertex,
        JTVertexAssignmentCover.coveredChoice_vertex]
      exact congrFun (NatTrans.congr_app (NatTrans.congr_app hπ i) zero) v
    · have h := congrArg (fun u ↦ coord (m.obj i) zero u 0)
        (congrFun (NatTrans.congr_app (NatTrans.congr_app hq i) zero) v)
      change coord (m.obj i) zero
          (((JTPrismChainGraphCover.parameter Y p α).app i).app zero
            ((f.app i).app zero v)) 0 =
        coord (m.obj i) zero
          (((JTPrismChainGraphCover.parameter Y p α).app i).app zero
            ((g.app i).app zero v)) 0 at h
      rwa [parameter_choice, parameter_choice] at h

end Ext

section Lift

variable (Y : I ⥤ SSet.{0}) {k m : I ⥤ SimplexCategory}
variable (p : Y ⟶ k ⋙ J) (α : m ⟶ k)
variable (A : I ⥤ SSet.{0}) (c : A ⟶ Y) (q : A ⟶ m ⋙ J)
variable (hq : q ≫ Functor.whiskerRight α J = c ≫ p)

private def value (i : I) (v : (A.obj i).obj zero) : Fin ((m.obj i).len + 1) :=
  coord (m.obj i) zero ((q.app i).app zero v) 0

private theorem value_natural {i j : I} (f : i ⟶ j) (v : (A.obj i).obj zero) :
    value A q j ((A.map f).app zero v) = (m.map f).toOrderHom (value A q i v) := by
  have h := congrFun (NatTrans.congr_app (q.naturality f) zero) v
  change (q.app j).app zero ((A.map f).app zero v) =
    (J.map (m.map f)).app zero ((q.app i).app zero v) at h
  unfold value
  rw [h, coord_map]

include hq in
private theorem value_allowed (i : I) (v : (A.obj i).obj zero) :
    (α.app i).toOrderHom (value A q i v) =
      coord (k.obj i) zero ((p.app i).app zero ((c.app i).app zero v)) 0 := by
  have h := congrFun (NatTrans.congr_app (NatTrans.congr_app hq i) zero) v
  change (J.map (α.app i)).app zero ((q.app i).app zero v) =
    (p.app i).app zero ((c.app i).app zero v) at h
  have h' := congrArg (fun u ↦ coord (k.obj i) zero u 0) h
  dsimp only at h'
  rw [coord_map] at h'
  exact h'

/-- A compatible full groupoid parameter determines its canonical assignment lift. -/
def lift : A ⟶ JTPrismChainGraphCover.cover Y p α :=
  JTVertexAssignmentCover.liftOfAssignments Y m _ _ A c (value A q)
    (value_natural A q) (value_allowed Y p α A c q hq)

/-- The canonical assignment lift preserves the entire underlying graph map. -/
theorem lift_projection :
    lift Y p α A c q hq ≫ JTPrismChainGraphCover.projection Y p α = c :=
  JTVertexAssignmentCover.liftOfAssignments_projection Y m _ _ A c (value A q)
    (value_natural A q) (value_allowed Y p α A c q hq)

/-- Its tautological lifted parameter is the prescribed full simplicial parameter. -/
theorem lift_parameter :
    lift Y p α A c q hq ≫ JTPrismChainGraphCover.parameter Y p α = q := by
  apply NatTrans.ext
  funext i
  apply parameter_ext
  intro v
  exact JTVertexAssignmentCover.liftOfAssignments_trace_vertex Y m _ _ A c (value A q)
    (value_natural A q) (value_allowed Y p α A c q hq) i v

end Lift

section Transport

variable (X Y : I ⥤ SSet.{0}) {k mX mY : I ⥤ SimplexCategory}
variable (pX : X ⟶ k ⋙ J) (pY : Y ⟶ k ⋙ J)
variable (αX : mX ⟶ k) (αY : mY ⟶ k) (β : mX ⟶ mY)
variable (hα : β ≫ αY = αX) (c : X ⟶ Y) (hc : c ≫ pY = pX)

include hα hc in
private theorem parameter_square :
    (JTPrismChainGraphCover.parameter X pX αX ≫ Functor.whiskerRight β J) ≫
        Functor.whiskerRight αY J =
      (JTPrismChainGraphCover.projection X pX αX ≫ c) ≫ pY := by
  rw [Category.assoc, ← Functor.whiskerRight_comp, hα,
    JTPrismChainGraphCover.parameter_projection, Category.assoc, hc]

/-- Send every source assignment through the compatible coefficient operator. -/
def map : JTPrismChainGraphCover.cover X pX αX ⟶ JTPrismChainGraphCover.cover Y pY αY :=
  lift Y pY αY (JTPrismChainGraphCover.cover X pX αX)
    (JTPrismChainGraphCover.projection X pX αX ≫ c)
    (JTPrismChainGraphCover.parameter X pX αX ≫ Functor.whiskerRight β J)
    (parameter_square X Y pX pY αX αY β hα c hc)

/-- Graph transport commutes with the complete native/product projection. -/
theorem map_projection :
    map X Y pX pY αX αY β hα c hc ≫ JTPrismChainGraphCover.projection Y pY αY =
      JTPrismChainGraphCover.projection X pX αX ≫ c :=
  lift_projection Y pY αY (JTPrismChainGraphCover.cover X pX αX)
    (JTPrismChainGraphCover.projection X pX αX ≫ c)
    (JTPrismChainGraphCover.parameter X pX αX ≫ Functor.whiskerRight β J)
    (parameter_square X Y pX pY αX αY β hα c hc)

/-- Graph transport retains every simplex of the lifted coefficient parameter. -/
theorem map_parameter :
    map X Y pX pY αX αY β hα c hc ≫ JTPrismChainGraphCover.parameter Y pY αY =
      JTPrismChainGraphCover.parameter X pX αX ≫ Functor.whiskerRight β J :=
  lift_parameter Y pY αY (JTPrismChainGraphCover.cover X pX αX)
    (JTPrismChainGraphCover.projection X pX αX ≫ c)
    (JTPrismChainGraphCover.parameter X pX αX ≫ Functor.whiskerRight β J)
    (parameter_square X Y pX pY αX αY β hα c hc)

end Transport

section Laws

variable (X : I ⥤ SSet.{0}) {k m : I ⥤ SimplexCategory}
variable (p : X ⟶ k ⋙ J) (α : m ⟶ k)

/-- Identity native and coefficient operators induce the literal identity cover map. -/
theorem map_id :
    map X X p p α α (𝟙 m) (Category.id_comp α) (𝟙 X) (Category.id_comp p) =
      𝟙 (JTPrismChainGraphCover.cover X p α) := by
  apply hom_ext X p α
  · rw [map_projection, Category.comp_id, Category.id_comp]
  · rw [map_parameter]
    have hi : Functor.whiskerRight (𝟙 m) J = 𝟙 (m ⋙ J) := by
      apply NatTrans.ext
      funext i
      exact J.map_id (m.obj i)
    rw [hi, Category.comp_id, Category.id_comp]

variable (Y Z : I ⥤ SSet.{0}) {mY mZ : I ⥤ SimplexCategory}
variable (pY : Y ⟶ k ⋙ J) (pZ : Z ⟶ k ⋙ J)
variable (αY : mY ⟶ k) (αZ : mZ ⟶ k)
variable (β : m ⟶ mY) (γ : mY ⟶ mZ)
variable (hβ : β ≫ αY = α) (hγ : γ ≫ αZ = αY)
variable (c : X ⟶ Y) (d : Y ⟶ Z) (hc : c ≫ pY = p) (hd : d ≫ pZ = pY)

/-- Compatible native and coefficient composition is strict on the full covers. -/
theorem map_comp :
    map X Y p pY α αY β hβ c hc ≫ map Y Z pY pZ αY αZ γ hγ d hd =
      map X Z p pZ α αZ (β ≫ γ) (by rw [Category.assoc, hγ, hβ])
        (c ≫ d) (by rw [Category.assoc, hd, hc]) := by
  apply hom_ext Z pZ αZ
  · rw [Category.assoc, map_projection, ← Category.assoc, map_projection,
      map_projection, Category.assoc]
  · rw [Category.assoc, map_parameter, ← Category.assoc, map_parameter,
      map_parameter, Category.assoc, Functor.whiskerRight_comp]

end Laws

end
end DaggerModels.PartII.JTPrismChainGraphTransport
