import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import DaggerModelsPartII.JTEndpointGraphCoefficientSlice
import DaggerModelsPartII.JTFiniteCoefficientBridgeMixedPrism

/-! Finite common-parent overlaps carry entire functorial bridge parameters. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTEndpointGraphCoefficientOverlap

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTEndpointGraphCoefficientSlice
open JTFiniteCoefficientBridgeOrder (bridge vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv)
open JTHigherInterleavedParameter (common)

noncomputable section

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)

/-- A child with maps to all the designated parents and a common comparison to P. -/
abbrev Overlap := Cone (WidePullbackShape.wideCospan P parents refineTo)

abbrev source : Overlap P parents refineTo ⥤ MixedGraphs q := Cones.forget _

/-- The source graph, with its actual arrow to one parent. -/
def toParent (e : Fin (m + 1)) : Overlap P parents refineTo ⥤ Over (parents e) :=
  Over.lift (source P parents refineTo)
    { app := fun A ↦ A.π.app (some e)
      naturality := fun _ _ f ↦ (f.w (some e)).trans (Category.comp_id _).symm }

/-- The source graph, with its actual arrow to the common graph. -/
def toCommon : Overlap P parents refineTo ⥤ Over P :=
  Over.lift (source P parents refineTo)
    { app := fun A ↦ A.π.app none
      naturality := fun _ _ f ↦ (f.w none).trans (Category.comp_id _).symm }

abbrev degree := source P parents refineTo ⋙ coefficientDegree

variable {P parents refineTo}
variable (A : Overlap P parents refineTo)

abbrev side (e : Fin (m + 1)) : (degree P parents refineTo).obj A ⟶
    coefficientDegree.obj (parents e) :=
  coefficientDegree.map (A.π.app (some e))

abbrev final : (degree P parents refineTo).obj A ⟶ coefficientDegree.obj P :=
  coefficientDegree.map (A.π.app none)

theorem side_final (e : Fin (m + 1)) :
    side A e ≫ coefficientDegree.map (refineTo e) = final A := by
  rw [← coefficientDegree.map_comp]
  exact congrArg coefficientDegree.map (A.w (WidePullbackShape.Hom.term e))

variable {A}

theorem side_natural {B : Overlap P parents refineTo} (f : A ⟶ B) (e : Fin (m + 1)) :
    (degree P parents refineTo).map f ≫ side B e = side A e := by
  change coefficientDegree.map f.hom ≫ coefficientDegree.map (B.π.app (some e)) =
    coefficientDegree.map (A.π.app (some e))
  rw [← coefficientDegree.map_comp]
  exact congrArg coefficientDegree.map (f.w (some e))

theorem final_natural {B : Overlap P parents refineTo} (f : A ⟶ B) :
    (degree P parents refineTo).map f ≫ final B = final A := by
  change coefficientDegree.map f.hom ≫ coefficientDegree.map (B.π.app none) =
    coefficientDegree.map (A.π.app none)
  rw [← coefficientDegree.map_comp]
  exact congrArg coefficientDegree.map (f.w none)

variable (P parents refineTo)

abbrev ParameterIndex := Overlap P parents refineTo × SemiSimplexCategory
private abbrev ord := SemiSimplexCategory.toSimplexCategory

abbrev coefficientsAt (A : ParameterIndex P parents refineTo) := side A.1
abbrev finalAt (A : ParameterIndex P parents refineTo) := final A.1
abbrev sourceDegreeAt (A : ParameterIndex P parents refineTo) := (degree P parents refineTo).obj A.1
abbrev timeAt (A : ParameterIndex P parents refineTo) := ord.obj A.2

variable {P parents refineTo}

private theorem rank_condition {U V : ParameterIndex P parents refineTo} (f : U ⟶ V) :
    JTFiniteCoefficientBridgeMixedOrder.RespectsRanks (coefficientsAt P parents refineTo U)
      (coefficientsAt P parents refineTo V) ((degree P parents refineTo).map f.1)
      (ord.map f.2) (𝟙 ⦋m⦌) := by
  apply JTFiniteCoefficientBridgeMixedOrder.ranks_of_operators
    (v := fun e ↦ JTCommonCoefficientParameter.map ((degree P parents refineTo).map f.1)
      (side_natural f.1 e) (ord.map f.2) (SemiSimplexCategory.homEquiv f.2).injective)
  intro e x
  exact JTCommonCoefficientParameter.map_vertexEquiv _ _ _ _ x

variable (P parents refineTo)

private def bridgeMap {U V : ParameterIndex P parents refineTo} (f : U ⟶ V) :
    bridge (sourceDegreeAt P parents refineTo U) (timeAt P parents refineTo U) m ⟶
      bridge (sourceDegreeAt P parents refineTo V) (timeAt P parents refineTo V) m :=
  JTFiniteCoefficientBridgeMixedOrder.map (side U.1) (side V.1)
    ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
    (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f)

private theorem bridgeMap_vertex {U V : ParameterIndex P parents refineTo} (f : U ⟶ V)
    (x : JTFiniteCoefficientBridgeOrder.Vertex
      (sourceDegreeAt P parents refineTo U) (timeAt P parents refineTo U) m) :
    (bridgeMap P parents refineTo f).toOrderHom (vertexEquiv (side U.1) (final U.1) (ord.obj U.2) x) =
    vertexEquiv (side V.1) (final V.1) (ord.obj V.2)
      ((((degree P parents refineTo).map f.1).toOrderHom x.1.1, (ord.map f.2).toOrderHom x.1.2), x.2) :=
  JTFiniteCoefficientBridgeMixedOrder.map_vertex (side U.1) (side V.1)
    ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
    (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f) x

/-- The enlarged coefficient bridge acts on all actual overlap arrows and injective times. -/
def bridgeParameter : ParameterIndex P parents refineTo ⥤ SimplexCategory where
  obj U := bridge (sourceDegreeAt P parents refineTo U) (timeAt P parents refineTo U) m
  map f := bridgeMap P parents refineTo f
  map_id U := by
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    funext z
    obtain ⟨x, rfl⟩ := (vertexEquiv (side U.1) (final U.1) (ord.obj U.2)).surjective z
    have h₁ : (degree P parents refineTo).map (𝟙 U : U ⟶ U).1 = 𝟙 _ :=
      (degree P parents refineTo).map_id U.1
    have h₂ : ord.map (𝟙 U : U ⟶ U).2 = 𝟙 _ := ord.map_id U.2
    rw [bridgeMap_vertex, h₁, h₂]
    rfl
  map_comp {U V Z} f g := by
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    funext z
    obtain ⟨x, rfl⟩ := (vertexEquiv (side U.1) (final U.1) (ord.obj U.2)).surjective z
    have h₁ : (degree P parents refineTo).map (f ≫ g).1 =
        (degree P parents refineTo).map f.1 ≫ (degree P parents refineTo).map g.1 :=
      (degree P parents refineTo).map_comp f.1 g.1
    have h₂ : ord.map (f ≫ g).2 = ord.map f.2 ≫ ord.map g.2 := ord.map_comp f.2 g.2
    change (bridgeMap P parents refineTo (f ≫ g)).toOrderHom
        (vertexEquiv (side U.1) (final U.1) (ord.obj U.2) x) =
      (bridgeMap P parents refineTo g).toOrderHom ((bridgeMap P parents refineTo f).toOrderHom
        (vertexEquiv (side U.1) (final U.1) (ord.obj U.2) x))
    rw [bridgeMap_vertex, bridgeMap_vertex, bridgeMap_vertex, h₁, h₂]
    rfl

/-- The joined time simplex keeps every copy and acts by the original time operator. -/
def joinedTime : ParameterIndex P parents refineTo ⥤ SimplexCategory where
  obj U := time m (timeAt P parents refineTo U)
  map f := JTFiniteCoefficientBridgeTimeReindex.map (𝟙 ⦋m⦌) (fun _ _ h ↦ h) (ord.map f.2)
  map_id U := by
    change JTFiniteCoefficientBridgeTimeReindex.map (𝟙 ⦋m⦌)
      (fun _ _ h ↦ h) (ord.map (𝟙 U.2)) = 𝟙 _
    rw [ord.map_id]
    exact JTFiniteCoefficientBridgeTimeReindex.map_id m _
  map_comp {U V Z} f g := by
    change JTFiniteCoefficientBridgeTimeReindex.map (𝟙 ⦋m⦌)
      (fun _ _ h ↦ h) (ord.map (f.2 ≫ g.2)) = _
    rw [ord.map_comp]
    have h := JTFiniteCoefficientBridgeTimeReindex.map_comp (𝟙 ⦋m⦌)
      (fun _ _ h ↦ h) (𝟙 ⦋m⦌) (fun _ _ h ↦ h) (ord.map f.2) (ord.map g.2)
    exact h

/-- The parameter of one of the original common-coefficient choices. -/
abbrev sideParameter (e : Fin (m + 1)) : ParameterIndex P parents refineTo ⥤ SimplexCategory :=
  (((CategoryTheory.Prod.fst _ _) ⋙ toParent P parents refineTo e ⋙ coefficients (parents e)).prod'
      (CategoryTheory.Prod.snd _ _)) ⋙
    JTCommonCoefficientParameter.parameter (coefficientDegree.obj (parents e))

/-- Each original enlarged parameter embeds naturally into the full bridge. -/
def sideToBridge (e : Fin (m + 1)) :
    sideParameter P parents refineTo e ⟶ bridgeParameter P parents refineTo where
  app U := JTFiniteCoefficientBridgeOrder.side (side U.1) (final U.1)
    (fun t ↦ coefficientDegree.map (refineTo t)) (side_final U.1) (ord.obj U.2) e
  naturality {U V} f := by
    have h := JTFiniteCoefficientBridgeMixedOrder.side_map (side U.1) (side V.1)
      ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
      (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f)
      (fun t ↦ coefficientDegree.map (refineTo t)) (fun t ↦ coefficientDegree.map (refineTo t))
      (side_final U.1) (side_final V.1) e
      (JTCommonCoefficientParameter.map ((degree P parents refineTo).map f.1)
        (side_natural f.1 e) (ord.map f.2) (SemiSimplexCategory.homEquiv f.2).injective)
      (fun x ↦ JTCommonCoefficientParameter.map_vertexEquiv _ _ _ _ x)
    exact h.symm

abbrev sideTime : ParameterIndex P parents refineTo ⥤ SimplexCategory :=
  CategoryTheory.Prod.snd _ _ ⋙ ord

/-- Include one full time simplex into the joined time, naturally on all overlaps. -/
def timeToJoined (e : Fin (m + 1)) :
    sideTime P parents refineTo ⟶ joinedTime P parents refineTo where
  app U := JTFiniteCoefficientBridgeTime.timeSide (ord.obj U.2) e
  naturality {_ _} f :=
    (JTFiniteCoefficientBridgeTimeReindex.timeSide_map (𝟙 ⦋m⦌)
      (fun _ _ h ↦ h) (ord.map f.2) e).symm

variable {P parents refineTo}

theorem bridgeParameter_base {U V : ParameterIndex P parents refineTo} (f : U ⟶ V) :
    (bridgeParameter P parents refineTo).map f ≫
      JTFiniteCoefficientBridgeOrder.base (side V.1) (final V.1) (ord.obj V.2) =
    JTFiniteCoefficientBridgeOrder.base (side U.1) (final U.1) (ord.obj U.2) :=
  JTFiniteCoefficientBridgeMixedOrder.map_base (side U.1) (side V.1)
    ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
    (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f)

theorem prism_natural {U V : ParameterIndex P parents refineTo} (f : U ⟶ V) :
    JTFiniteCoefficientBridgePrism.prism.{0} (side U.1) (final U.1) (ord.obj U.2) ≫
      SSet.stdSimplex.map ((bridgeParameter P parents refineTo).map f) =
    (SSet.stdSimplex.map ((degree P parents refineTo).map f.1) ⊗ₘ
      SSet.stdSimplex.map ((joinedTime P parents refineTo).map f)) ≫
      JTFiniteCoefficientBridgePrism.prism (side V.1) (final V.1) (ord.obj V.2) :=
  JTFiniteCoefficientBridgeMixedPrism.prism_map (side U.1) (side V.1)
    ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
    (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f)

theorem paired_natural {U V : ParameterIndex P parents refineTo} (f : U ⟶ V) :
    JTFiniteCoefficientBridgeGroupoid.paired (side U.1) (final U.1) (ord.obj U.2) ≫
      GroupoidSimplex.parameter.map ((bridgeParameter P parents refineTo).map f) =
    (GroupoidSimplex.parameter.map ((degree P parents refineTo).map f.1) ⊗ₘ
      GroupoidSimplex.parameter.map ((joinedTime P parents refineTo).map f)) ≫
      JTFiniteCoefficientBridgeGroupoid.paired (side V.1) (final V.1) (ord.obj V.2) :=
  JTFiniteCoefficientBridgeMixedPrism.paired_map (side U.1) (side V.1)
    ((degree P parents refineTo).map f.1) (ord.map f.2) (𝟙 ⦋m⦌)
    (final_natural f.1) (fun _ _ h ↦ h) (rank_condition f)

end
end DaggerModels.PartII.JTEndpointGraphCoefficientOverlap
