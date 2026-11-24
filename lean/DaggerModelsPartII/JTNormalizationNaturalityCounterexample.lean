import OriginalFlagOriginalNormalization
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# Beadwise normalization is not functorial along all necklace morphisms

In the codiscrete groupoid simplex, the long edge of the triangle with
vertex labels (0, 1, 0) is degenerate. The long-edge map cannot survive
normalization as a map preserving both ordered endpoints.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.JTNormalizationNaturalityCounterexample

noncomputable section

private abbrev X : SSet.{0} :=
  DaggerModels.PartII.GroupoidSimplex.parameter.obj ⦋1⦌

private abbrev e := DaggerModels.PartII.GroupoidSimplex.parameterCodiscreteIso.app ⦋1⦌

private def label (v : Fin 3) : Fin 2 := if v = 1 then 1 else 0

private def qSimplex : (Δ[2] : SSet.{0}) ⟶ X :=
  mapOfVertices _ (fun z ↦ label (SSet.stdSimplex.obj₀Equiv z)) ≫ e.inv

private def pSimplex : (Δ[1] : SSet.{0}) ⟶ X :=
  mapOfVertices _ (fun _ ↦ (0 : Fin 2)) ≫ e.inv

private def edge : ⦋1⦌ ⟶ ⦋2⦌ :=
  SimplexCategory.mkOfLe 0 (Fin.last 2) (Fin.zero_le _)

private def a : X.obj (op ⦋0⦌) :=
  e.inv.app (op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (0 : Fin 2)))

private theorem p_first :
    pSimplex.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) = a := by
  apply (e.app (op ⦋0⦌)).toEquiv.injective
  rfl

private theorem p_last :
    pSimplex.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 1)) = a := by
  apply (e.app (op ⦋0⦌)).toEquiv.injective
  rfl

private theorem q_first :
    qSimplex.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) = a := by
  apply (e.app (op ⦋0⦌)).toEquiv.injective
  rfl

private theorem q_last :
    qSimplex.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 2)) = a := by
  apply (e.app (op ⦋0⦌)).toEquiv.injective
  rfl

private def P : NecklacesOver X a a where
  code := single 1
  map := (singleIso 1).hom ≫ pSimplex
  first := by
    change pSimplex.app _ ((singleIso 1).hom.app _ (single 1).first) = a
    rw [singleIso_first]
    exact p_first
  last := by
    change pSimplex.app _ ((singleIso 1).hom.app _ (single 1).last) = a
    rw [singleIso_last]
    exact p_last

private def Q : NecklacesOver X a a where
  code := single 2
  map := (singleIso 2).hom ≫ qSimplex
  first := by
    change qSimplex.app _ ((singleIso 2).hom.app _ (single 2).first) = a
    rw [singleIso_first]
    exact q_first
  last := by
    change qSimplex.app _ ((singleIso 2).hom.app _ (single 2).last) = a
    rw [singleIso_last]
    exact q_last

private theorem p_edge_q : SSet.stdSimplex.map edge ≫ qSimplex = pSimplex := by
  apply (cancel_mono e.hom).mp
  apply NatTrans.ext
  funext n z
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  simp only [qSimplex, pSimplex, mapOfVertices, Category.assoc]
  change label (edge.toOrderHom ((SSet.stdSimplex.objEquiv z).toOrderHom i)) = 0
  have hv : ∀ v : Fin 2, label (edge.toOrderHom v) = 0 := by
    intro v
    fin_cases v <;> rfl
  exact hv _

private def f : P ⟶ Q where
  hom :=
    { map := (singleIso 1).hom ≫ SSet.stdSimplex.map edge ≫ (singleIso 2).inv
      first := by
        change (singleIso 2).inv.app _
          ((SSet.stdSimplex.map edge).app _ ((singleIso 1).hom.app _ (single 1).first)) =
          (single 2).first
        rw [singleIso_first, stdSimplex_map_vertex]
        apply (singleIso 2).app (op ⦋0⦌) |>.toEquiv.injective
        simp [edge, SimplexCategory.mkOfLe, singleIso_first]
      last := by
        change (singleIso 2).inv.app _
          ((SSet.stdSimplex.map edge).app _ ((singleIso 1).hom.app _ (single 1).last)) =
          (single 2).last
        rw [singleIso_last, stdSimplex_map_vertex]
        apply (singleIso 2).app (op ⦋0⦌) |>.toEquiv.injective
        simp [edge, SimplexCategory.mkOfLe, singleIso_last] }
  w := by
    change ((singleIso 1).hom ≫ SSet.stdSimplex.map edge ≫ (singleIso 2).inv) ≫
        ((singleIso 2).hom ≫ qSimplex) = (singleIso 1).hom ≫ pSimplex
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [p_edge_q]

private theorem constant_labels_factor (Y : SSet.{0}) :
    mapOfVertices Y (fun _ ↦ (0 : Fin 2)) =
      SSet.stdSimplex.isTerminalObj₀.from Y ≫
        mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ (0 : Fin 2)) := by
  apply NatTrans.ext
  funext n z
  apply nerve.ext_of_isThin
  funext i
  apply Codiscrete.ext
  rfl

private theorem p_factor :
    pSimplex = SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫
      SSet.yonedaEquiv.symm a := by
  have hp : mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ (0 : Fin 2)) ≫ e.inv =
      SSet.yonedaEquiv.symm a := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv.apply_symm_apply]
    rfl
  unfold pSimplex
  rw [constant_labels_factor, Category.assoc, hp]

private def zeroData (c : P.code.Bead) : NondegenerateBeadData P c where
  dim := 0
  operator := SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0
  epi := SimplexCategory.epi_iff_surjective.mpr (by
    change Function.Surjective (fun _ : Fin (c.length + 1) ↦ (0 : Fin 1))
    intro v
    exact ⟨0, Subsingleton.elim _ _⟩)
  simplex := ⟨a, by simp⟩
  fac := by
    have hmap : P.code.beadSimplex c ≫ P.map =
        SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0) ≫
          SSet.yonedaEquiv.symm a := by
      change P.code.beadSimplex c ≫ (singleIso 1).hom ≫ pSimplex = _
      rw [p_factor]
      have hterm : P.code.beadSimplex c ≫ (singleIso 1).hom ≫
          SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) =
          SSet.stdSimplex.map (SimplexCategory.const ⦋c.length⦌ ⦋0⦌ 0) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      calc
        P.code.beadSimplex c ≫ (singleIso 1).hom ≫
            SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫
            SSet.yonedaEquiv.symm a =
            (P.code.beadSimplex c ≫ (singleIso 1).hom ≫
              SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
              SSet.yonedaEquiv.symm a := by simp only [Category.assoc]
        _ = _ := congrArg (fun g ↦ g ≫ SSet.yonedaEquiv.symm a) hterm
    have h := congrArg SSet.yonedaEquiv hmap
    simp only [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map] at h
    exact h

private theorem P_norm_point : (normOver P).code = NecklaceCode.point := by
  apply normOver_all_zero_code
  intro i
  exact beadNormalization_dim_unique P (jointBead P.code i)
    (normalizeBead P (jointBead P.code i)) (zeroData (jointBead P.code i))

private def qMiddle : X.obj (op ⦋0⦌) :=
  qSimplex.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))

private theorem qMiddle_ne_a : qMiddle ≠ a := by
  intro h
  have h' := congrArg (fun z ↦ (nerveEquiv (e.hom.app (op ⦋0⦌) z)).as) h
  change (1 : Fin 2) = 0 at h'
  exact Fin.zero_ne_one h'.symm

private theorem q_nondegenerate :
    SSet.yonedaEquiv qSimplex ∈ X.nonDegenerate 2 := by
  apply (SSet.nonDegenerate_iff_of_isIso e.hom _).mp
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate,
    SSet.degenerate_eq_iUnion_range_σ]
  intro hd
  simp only [Set.mem_iUnion, Set.mem_range] at hd
  obtain ⟨i, z, hz⟩ := hd
  let s := e.hom.app (op ⦋2⦌) (SSet.yonedaEquiv qSimplex)
  have heq : s.obj i.castSucc = s.obj i.succ := by
    dsimp only [s]
    rw [← hz]
    change ((nerve (Codiscrete (Fin 2))).σ i z).obj i.castSucc =
      ((nerve (Codiscrete (Fin 2))).σ i z).obj i.succ
    simp only [nerve.σ_obj, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  fin_cases i
  · have h := congrArg Codiscrete.as heq
    change (0 : Fin 2) = 1 at h
    exact Fin.zero_ne_one h
  · have h := congrArg Codiscrete.as heq
    change (1 : Fin 2) = 0 at h
    exact Fin.zero_ne_one h.symm

private theorem q_long_face_degenerate :
    X.map edge.op (SSet.yonedaEquiv qSimplex) ∈ X.degenerate 1 := by
  have hpoint : SSet.yonedaEquiv pSimplex = X.σ (0 : Fin 1) a := by
    rw [p_factor]
    have hterm : SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0}) =
        SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [hterm]
    rfl
  have hface : X.map edge.op (SSet.yonedaEquiv qSimplex) =
      SSet.yonedaEquiv pSimplex := by
    calc
      X.map edge.op (SSet.yonedaEquiv qSimplex) =
          SSet.yonedaEquiv (SSet.stdSimplex.map edge ≫ qSimplex) := by
        rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
        rfl
      _ = SSet.yonedaEquiv pSimplex := congrArg SSet.yonedaEquiv p_edge_q
  rw [hface, hpoint]
  exact X.σ_mem_degenerate (0 : Fin 1) a

private def qMiddleCode : Q.code.toSSet.obj (op ⦋0⦌) :=
  (singleIso 2).inv.app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))

private theorem qMiddleCode_image : Q.map.app (op ⦋0⦌) qMiddleCode = qMiddle := by
  change qSimplex.app _ ((singleIso 2).hom.app _
    ((singleIso 2).inv.app _ (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3)))) = _
  have hh := congrFun (NatTrans.congr_app (singleIso 2).inv_hom_id (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))
  change (singleIso 2).hom.app _ ((singleIso 2).inv.app _ _) = _ at hh
  rw [hh]
  rfl

private theorem Q_norm_positive : (normOver Q).code.len ≠ 0 := by
  intro hz
  have hc := code_zero_eq_point (normOver Q).code hz
  have heq : (originalNormalization Q).hom.map.app (op ⦋0⦌) Q.code.first =
      (originalNormalization Q).hom.map.app (op ⦋0⦌) qMiddleCode := by
    have huniq : ∀ x y : (normOver Q).code.toSSet.obj (op ⦋0⦌), x = y := by
      rw [hc]
      intro x y
      exact (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm
    exact huniq _ _
  have hmap := congrArg ((normOver Q).map.app (op ⦋0⦌)) heq
  have htri := originalNormalization_triangle Q
  have hfirst := congrFun (NatTrans.congr_app htri (op ⦋0⦌)) Q.code.first
  have hmiddle := congrFun (NatTrans.congr_app htri (op ⦋0⦌)) qMiddleCode
  change (normOver Q).map.app _ ((originalNormalization Q).hom.map.app _ Q.code.first) =
    Q.map.app _ Q.code.first at hfirst
  change (normOver Q).map.app _ ((originalNormalization Q).hom.map.app _ qMiddleCode) =
    Q.map.app _ qMiddleCode at hmiddle
  rw [hfirst, hmiddle] at hmap
  have hqa : Q.map.app (op ⦋0⦌) Q.code.first = a := Q.first
  rw [hqa, qMiddleCode_image] at hmap
  exact qMiddle_ne_a hmap.symm

private theorem no_normalized_arrow : ¬ Nonempty (normOver P ⟶ normOver Q) := by
  rintro ⟨g⟩
  have hp : (normOver P).code.first = (normOver P).code.last := by
    rw [P_norm_point]
    rfl
  have hq : (normOver Q).code.first = (normOver Q).code.last := by
    exact g.hom.first.symm.trans ((congrArg (g.hom.map.app (op ⦋0⦌)) hp).trans
      g.hom.last)
  have hv : (0 : Fin ((normOver Q).code.len + 1)) =
      Fin.last (normOver Q).code.len := by
    have hh := congrArg (normOver Q).code.verticesEquiv hq
    simpa only [NecklaceCode.first, NecklaceCode.last, Equiv.apply_symm_apply,
      ULift.up.injEq] using hh
  have hlen := congrArg Fin.val hv
  apply Q_norm_positive
  simpa using hlen.symm

/-- There is no functor on these necklaces whose values are objectwise
isomorphic to their beadwise normalizations. -/
theorem no_objectwise_normalization_functor :
    ¬ ∃ F : NecklacesOver X a a ⥤ NecklacesOver X a a,
      ∀ T, Nonempty (F.obj T ≅ normOver T) := by
  rintro ⟨F, hF⟩
  obtain ⟨eP⟩ := hF P
  obtain ⟨eQ⟩ := hF Q
  exact no_normalized_arrow ⟨eP.inv ≫ F.map f ≫ eQ.hom⟩

end

end DaggerModels.PartII.JTNormalizationNaturalityCounterexample
