import DaggerModelsPartII.JTVariableMiddleWhiskeredDiagram
import DaggerModelsPartII.JTParametrizedTargetFamilies

/-!
Expose native projections before specializing coefficient data. The existing
family projection theorems retain both native and ordinal operators. These
smaller native-only statements avoid repeated kernel conversion of the
complete coefficient diagram when forming identity-component comparisons.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
namespace DaggerModels.PartII.JTVariableMiddleNativeProjection

noncomputable section

variable {I : Type} [SmallCategory I]
section Generic

variable {C : Type} [SmallCategory C] {N₀ N₁ : I ⥤ C}
variable (h : ∀ a : I, N₀.obj a = N₁.obj a)
variable (hn : ∀ {a b : I} (f : a ⟶ b),
  N₀.map f ≫ eqToHom (h b) = eqToHom (h a) ≫ N₁.map f)

/-- Build a natural isomorphism from explicit object equalities and their
operator square, without unfolding a concrete construction of either functor. -/
def isoOfObjectEqualities : N₀ ≅ N₁ :=
  NatIso.ofComponents (fun a ↦ eqToIso (h a)) hn

/-- The forward component formula is proved before any concrete functor
or coefficient data are substituted into the isomorphism. -/
theorem isoOfObjectEqualities_hom_app (a : I) :
    (isoOfObjectEqualities h hn).hom.app a = eqToHom (h a) := rfl

/-- The inverse component is the same explicit object transport backwards. -/
theorem isoOfObjectEqualities_inv_app (a : I) :
    (isoOfObjectEqualities h hn).inv.app a = eqToHom (h a).symm := rfl

end Generic

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}
variable (F : JTVariableMiddleWhiskeredDiagram.Family
  (W := W) (x := x) (y := y) P M R K)
/-- Native objects depend only on the three supplied code diagrams. -/
theorem obj (a : I) : (JTParametrizedTargetFamilies.codes F.labels).obj a =
    wedge (P.obj a) (wedge (M.obj a) (R.obj a)) :=
  congrArg Prod.fst (F.labels_projection a)

/-- Native operators retain the three original operators literally. -/
theorem map {a b : I} (f : a ⟶ b) :
    (JTParametrizedTargetFamilies.codes F.labels).map f =
      wedgeMap (P.map f) (wedgeMap (M.map f) (R.map f)) :=
  congrArg Prod.fst (F.arrow_projection f)

variable (G : JTVariableMiddleWhiskeredDiagram.Family
  (W := W) (x := x) (y := y) P M R K)

private def objectEquality (a : I) :
    (JTParametrizedTargetFamilies.codes F.labels).obj a =
      (JTParametrizedTargetFamilies.codes G.labels).obj a :=
  (obj F a).trans (obj G a).symm

private theorem native_naturality {a b : I} (f : a ⟶ b) :
    (JTParametrizedTargetFamilies.codes F.labels).map f ≫
        eqToHom (objectEquality F G b) =
      eqToHom (objectEquality F G a) ≫
        (JTParametrizedTargetFamilies.codes G.labels).map f := by
  rw [map F f, map G f]
  have h₀ : objectEquality F G a = rfl := Subsingleton.elim _ _
  have h₁ : objectEquality F G b = rfl := Subsingleton.elim _ _
  rw [h₀, h₁]
  simp

/-- Changing coefficients with the native diagrams retained gives an
identity-component natural isomorphism on the complete native diagram. -/
def nativeIso : JTParametrizedTargetFamilies.codes F.labels ≅
    JTParametrizedTargetFamilies.codes G.labels :=
  isoOfObjectEqualities (objectEquality F G) (native_naturality F G)

/-- Exact forward component, with the existing native object equality
retained explicitly instead of forcing a large definitional conversion. -/
theorem nativeIso_hom_app_transport (a : I) :
    (nativeIso F G).hom.app a = eqToHom ((obj F a).trans (obj G a).symm) :=
  isoOfObjectEqualities_hom_app (objectEquality F G) (native_naturality F G) a

/-- Exact reverse component with the same object equality reversed. -/
theorem nativeIso_inv_app_transport (a : I) :
    (nativeIso F G).inv.app a = eqToHom ((obj F a).trans (obj G a).symm).symm :=
  isoOfObjectEqualities_inv_app (objectEquality F G) (native_naturality F G) a

/-- The component is the native identity, expressed heterogeneously so its
source and target object expressions need not first be reduced together. -/
theorem nativeIso_hom_app_heq (a : I) :
    HEq ((nativeIso F G).hom.app a)
      (𝟙 ((JTParametrizedTargetFamilies.codes F.labels).obj a)) :=
  (heq_of_eq (nativeIso_hom_app_transport F G a)).trans
    (eqToHom_heq_id_dom _ _ ((obj F a).trans (obj G a).symm))

/-- The inverse is the identity on its own native source in the same sense. -/
theorem nativeIso_inv_app_heq (a : I) :
    HEq ((nativeIso F G).inv.app a)
      (𝟙 ((JTParametrizedTargetFamilies.codes G.labels).obj a)) :=
  (heq_of_eq (nativeIso_inv_app_transport F G a)).trans
    (eqToHom_heq_id_dom _ _ ((obj F a).trans (obj G a).symm).symm)

end
end DaggerModels.PartII.JTVariableMiddleNativeProjection
