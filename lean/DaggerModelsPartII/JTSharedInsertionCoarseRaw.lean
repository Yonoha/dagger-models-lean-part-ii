import DaggerModelsPartII.JTSharedInsertionCoarseRegroupedPieces
import DaggerModelsPartII.JTSharedInsertionCoarseRegroupedCoefficient
import DaggerModelsPartII.JTSharedInsertionCoarseGraph
import DaggerModelsPartII.JTSharedInsertionOuterRaw
import DaggerModelsPartII.JTWhiskeredGraphRaw

/-!
# Exact raw realization of the ACTUAL coarse graph in the original Q

Every original-time coefficient lift is retained. The two COMPLETE native
inverse images use checked coalesced outer raw equations, their actual full
coefficients and their native factors BEFORE Q. The original coarse coefficient
is recovered along the SAME checked native regroup. No raw, coefficient
compatibility, new Family or parameter section is supplied by the caller.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseRaw

open JTParametrizedTargetFamilies (Family codes)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {S T : SSet.{0}} (f : S ⟶ T) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map f) W

private theorem coordinate_piece {X B C S I P : SSet.{0}}
    (h : X ⟶ B) (q : X ⟶ P) (t : X ⟶ I) (n : B ⟶ C)
    (r : C ⊗ I ⟶ P) (hq : q = lift (h ≫ n) t ≫ r)
    (i : S ⟶ B) (n' : S ⟶ C) (hi : i ≫ n = n') :
    pullback.fst h i ≫ q =
      lift (pullback.snd h i ≫ n') (pullback.fst h i ≫ t) ≫ r := by
  have hn : pullback.fst h i ≫ (h ≫ n) = pullback.snd h i ≫ n' := by
    rw [← Category.assoc, pullback.condition, Category.assoc, hi]
  rw [hq, ← Category.assoc, comp_lift, hn]

private theorem restrict_target {X B S T : SSet.{0}}
    (h : X ⟶ B) (i : S ⟶ B) (g : B ⟶ T) :
    pullback.fst h i ≫ (h ≫ g) = pullback.snd h i ≫ i ≫ g := by
  rw [← Category.assoc, pullback.condition, Category.assoc]

private theorem factor_target {X S P T R : SSet.{0}}
    (h : X ⟶ S) (i : S ⟶ P) (n : P ⟶ T) (j : S ⟶ T)
    (g : T ⟶ R) (hi : i ≫ n = j) :
    h ≫ i ≫ n ≫ g = h ≫ j ≫ g := by
  rw [← Category.assoc i, hi]

private theorem product_coordinate {X S T I P : SSet.{0}}
    (π : X ⟶ S ⊗ I) (n : S ⟶ T) (r : T ⊗ I ⟶ P) :
    π ≫ ((n ⊗ₘ 𝟙 I) ≫ r) =
      lift ((π ≫ fst S I) ≫ n) (π ≫ snd S I) ≫ r := by
  have h := congrArg (fun f ↦ π ≫ f ≫ r) (lift_fst_comp_snd_comp n (𝟙 I))
  simpa only [Category.comp_id, comp_lift, Category.assoc] using h.symm

private theorem regroup_coordinate {X S G T I P : SSet.{0}}
    (π : X ⟶ S ⊗ I) (q : X ⟶ P) (a : S ⟶ T) (d : S ⟶ G) (n : G ⟶ T)
    (r : T ⊗ I ⟶ P) (ha : d ≫ n = a)
    (hq : q = π ≫ ((a ⊗ₘ 𝟙 I) ≫ r)) :
    q = lift (((π ≫ fst S I) ≫ d) ≫ n) (π ≫ snd S I) ≫ r := by
  rw [hq, product_coordinate, ← ha]
  simp only [Category.assoc]

private theorem same_degree_raw (W : Source) {X : SSet.{0}} {S T : NecklaceCode}
    {k : SimplexCategory} (h : X ⟶ S.toSSet) (q : X ⟶ J.obj k)
    (i : S.toSSet ⟶ T.toSSet) (g : T.toSSet ⟶ Raw W)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W T)
    (d : std.obj k ⟶ TripleBeadEndpointLabel.labels W S)
    (hc : d = c ≫ pre W i)
    (H : lift (h ≫ i) q ≫ realizedLabel T.toSSet W k (SSet.yonedaEquiv c) =
      (h ≫ i) ≫ g) :
    lift h q ≫ realizedLabel S.toSSet W k (SSet.yonedaEquiv d) = h ≫ i ≫ g := by
  have hd : d = std.map (𝟙 k) ≫ c ≫ pre W i := by
    simpa only [std.map_id, Category.id_comp] using hc
  exact JTWhiskeredGraphRawTransport.raw W (h ≫ i) q c g H h q (𝟙 X)
    i (𝟙 k) d hd (Category.id_comp _) (by simp only [J.map_id, Category.comp_id,
      Category.id_comp])

private theorem code_comp {S T U : NecklaceCode} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).map = f.map ≫ g.map := rfl

private def Compatible (W : Source) {k l t : SimplexCategory} {T : SSet.{0}}
    (α : k ⟶ l) (θ : T ⊗ J.obj t ⟶ J.obj l) (g : T ⟶ Raw W)
    (S : NecklaceCode) (n : S.toSSet ⟶ T)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W S) : Prop :=
  ∀ {X : SSet.{0}} (h : X ⟶ S.toSSet) (q : X ⟶ J.obj k) (r : X ⟶ J.obj t),
    q ≫ J.map α = lift (h ≫ n) r ≫ θ →
    lift h q ≫ realizedLabel S.toSSet W k (SSet.yonedaEquiv c) = h ≫ n ≫ g

private theorem restrict_compatible (W : Source) {k l t : SimplexCategory} {T : SSet.{0}}
    (α : k ⟶ l) (θ : T ⊗ J.obj t ⟶ J.obj l) (g : T ⟶ Raw W)
    (S U : NecklaceCode) (i : S.toSSet ⟶ U.toSSet)
    (n : S.toSSet ⟶ T) (m : U.toSSet ⟶ T) (hn : i ≫ m = n)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W S)
    (d : std.obj k ⟶ TripleBeadEndpointLabel.labels W U) (hc : c = d ≫ pre W i)
    (H : Compatible W α θ g U m d) : Compatible W α θ g S n c := by
  intro X h q r hq
  rw [hc, ← JTWhiskerEdgeGraphRaw.native_restrict W i h q d]
  have hp : q ≫ J.map α = lift ((h ≫ i) ≫ m) r ≫ θ := by
    simpa only [Category.assoc, hn] using hq
  have h' : lift (h ≫ i) q ≫ realizedLabel U.toSSet W k (SSet.yonedaEquiv d) =
      h ≫ i ≫ m ≫ g := by
    simpa only [Category.assoc] using H (h ≫ i) q r hp
  exact h'.trans (factor_target h i m n g hn)

private theorem assemble_compatible (W : Source) {k l t : SimplexCategory} {T : SSet.{0}}
    (α : k ⟶ l) (θ : T ⊗ J.obj t ⟶ J.obj l) (g : T ⟶ Raw W)
    (S U : NecklaceCode) (n : (wedge S U).toSSet ⟶ T)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W (wedge S U))
    (HL : Compatible W α θ g S (wedgeιLeft S U ≫ n) (c ≫ pre W (wedgeιLeft S U)))
    (HR : Compatible W α θ g U (wedgeιRight S U ≫ n) (c ≫ pre W (wedgeιRight S U))) :
    Compatible W α θ g (wedge S U) n c := by
  intro X h q r hq
  apply JTActualJointChainSideRaw.binary_hom_ext h
  · rw [JTWhiskeredGraphRaw.piece_restrict W h q (wedgeιLeft S U) c
      (c ≫ pre W (wedgeιLeft S U)) rfl]
    rw [restrict_target h (wedgeιLeft S U) (n ≫ g)]
    have hp := coordinate_piece h (q ≫ J.map α) r n θ hq
      (wedgeιLeft S U) (wedgeιLeft S U ≫ n) rfl
    simpa only [Category.assoc] using HL (pullback.snd h (wedgeιLeft S U))
      (pullback.fst h (wedgeιLeft S U) ≫ q) (pullback.fst h (wedgeιLeft S U) ≫ r)
      (by simpa only [Category.assoc] using hp)
  · rw [JTWhiskeredGraphRaw.piece_restrict W h q (wedgeιRight S U) c
      (c ≫ pre W (wedgeιRight S U)) rfl]
    rw [restrict_target h (wedgeιRight S U) (n ≫ g)]
    have hp := coordinate_piece h (q ≫ J.map α) r n θ hq
      (wedgeιRight S U) (wedgeιRight S U ≫ n) rfl
    simpa only [Category.assoc] using HR (pullback.snd h (wedgeιRight S U))
      (pullback.fst h (wedgeιRight S U) ≫ q) (pullback.fst h (wedgeιRight S U) ≫ r)
      (by simpa only [Category.assoc] using hp)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The complete shared insertion choices, without triangle-filler choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev rho := JTSharedInsertionCoarseCoalescedCoefficients.rho F j
private abbrev old (p : Index F j) :=
  (JTSharedInsertionChainSupport.originalBase F j).obj p
private abbrev K (p : Index F j) := (JTSharedInsertionChoices.ordinals F j).obj p
private abbrev α (p : Index F j) := (JTSharedInsertionChoices.toOriginal F j).app p
private abbrev P (p : Index F j) := JTSharedInsertionCoarseCoalescedCoefficients.leftCode F j p
private abbrev R (p : Index F j) := JTSharedInsertionCoarseCoalescedCoefficients.rightCode F j p
private abbrev G (p : Index F j) := wedge (P F j p) (R F j p)
private abbrev grouped (p : Index F j) :=
  JTCoarseCoefficientRegrouping.groupedCoefficient (JTSharedInsertionCoarseRawData.data F j p)
private abbrev native (p : Index F j) :=
  (JTSharedInsertionCoarseRegroupedNative.groupedAssembly F j p).map
private abbrev after (p : Index F j) :=
  (F.collapse.app (old F j p)).map ≫ Q.map
private abbrev iL (p : Index F j) := wedgeιLeft (P F j p) (R F j p)
private abbrev iR (p : Index F j) := wedgeιRight (P F j p) (R F j p)
private abbrev l (p : Index F j) := JTSharedInsertionCoarseCoalescedCoefficients.leftMap F j p
private abbrev r (p : Index F j) :=
  JTSharedInsertionCoarseCoalescedCoefficients.rightInclusion F j p
private abbrev nL (p : Index F j) :=
  JTSharedInsertionNativeAssembly.leftToOriginal F j (rho F j p)
private abbrev nR (p : Index F j) :=
  JTSharedInsertionNativeAssembly.rightToOriginal F j (rho F j p)
private abbrev cL (p : Index F j) :=
  JTSharedInsertionSeamSurroundings.leftCoefficient F j (rho F j p)
private abbrev cR (p : Index F j) :=
  JTSharedInsertionSeamSurroundings.rightCoefficient F j (rho F j p)

set_option maxHeartbeats 400000 in
private def left_compatible (p : Index F j) {X : SSet.{0}} :=
  fun (h : X ⟶ (P F j p).toSSet) q t hq ↦
  restrict_compatible W (α F j p) (F.parameter (old F j p)) (after F j p)
    (P F j p) ((JTSharedInsertionSeamSurroundings.leftNative F j).obj (rho F j p))
    (l F j p) (iL F j p ≫ native F j p) (nL F j p)
    (JTSharedInsertionCoarseRegroupedPieces.left_factor F j p)
    (grouped F j p ≫ pre W (iL F j p)) (cL F j p)
    (JTSharedInsertionCoarseCoalescedCoefficients.grouped_left_coefficient F j p)
    (fun {_Y} h q t hq ↦ JTSharedInsertionOuterRaw.left_raw F j (rho F j p) h q t hq)
    h q t hq

set_option maxHeartbeats 400000 in
private def right_compatible (p : Index F j) {X : SSet.{0}} :=
  fun (h : X ⟶ (R F j p).toSSet) q t hq ↦
  restrict_compatible W (α F j p) (F.parameter (old F j p)) (after F j p)
    (R F j p) ((JTSharedInsertionSeamSurroundings.rightNative F j).obj (rho F j p))
    (r F j p) (iR F j p ≫ native F j p) (nR F j p)
    (JTSharedInsertionCoarseRegroupedPieces.right_factor F j p)
    (grouped F j p ≫ pre W (iR F j p)) (cR F j p)
    (JTSharedInsertionCoarseCoalescedCoefficients.grouped_right_coefficient F j p)
    (fun {_Y} h q t hq ↦ JTSharedInsertionOuterRaw.right_raw F j (rho F j p) h q t hq)
    h q t hq

private def grouped_raw (p : Index F j) {X : SSet.{0}} :=
  fun (h : X ⟶ (G F j p).toSSet) q t hq ↦
  assemble_compatible W (α F j p) (F.parameter (old F j p)) (after F j p)
    (P F j p) (R F j p) (native F j p) (grouped F j p)
    (fun {Y} h q t hq ↦ left_compatible F j p (X := Y) h q t hq)
    (fun {Y} h q t hq ↦ right_compatible F j p (X := Y) h q t hq)
    h q t hq

private abbrev coarseCode (p : Index F j) :=
  (codes (JTSharedInsertionCoarseLabels.labels F j)).obj p
private abbrev π (p : Index F j) := (JTSharedInsertionCoarseGraph.projection F j).app p
private abbrev θ (p : Index F j) := (JTSharedInsertionCoarseGraph.parameter F j).app p
private abbrev h₀ (p : Index F j) :=
  π F j p ≫ fst (coarseCode F j p).toSSet (J.obj (time.obj (old F j p)))
private abbrev clock (p : Index F j) :=
  π F j p ≫ snd (coarseCode F j p).toSSet (J.obj (time.obj (old F j p)))
private abbrev δ (p : Index F j) := (JTSharedInsertionCoarseRegroupedNative.regroup F j p).map
private abbrev assembly (p : Index F j) :=
  ((JTSharedInsertionCoarseNative.assembly F j).app p).map

private theorem projected_parameter (p : Index F j) :
    θ F j p ≫ J.map (α F j p) =
      π F j p ≫ ((assembly F j p ⊗ₘ 𝟙 (J.obj (time.obj (old F j p)))) ≫
        F.parameter (old F j p)) := by
  have h := congrArg (fun η : JTSharedInsertionCoarseGraph.graph F j ⟶
      JTSharedInsertionCoarseGraph.oldDegrees F j ⋙ J ↦ η.app p)
    (JTSharedInsertionCoarseGraph.parameter_projection F j)
  change θ F j p ≫ J.map (α F j p) =
    π F j p ≫ (JTSharedInsertionCoarseGraph.coarseParameter F j).app p at h
  rw [JTSharedInsertionCoarseGraph.coarseParameter_app] at h
  exact h

private theorem grouped_coordinate (p : Index F j) :
    θ F j p ≫ J.map (α F j p) =
      lift ((h₀ F j p ≫ δ F j p) ≫ native F j p) (clock F j p) ≫
        F.parameter (old F j p) :=
  regroup_coordinate (π F j p) (θ F j p ≫ J.map (α F j p)) (assembly F j p)
    (δ F j p) (native F j p) (F.parameter (old F j p))
    (JTSharedInsertionCoarseRegroupedNative.regroup_assembly_map F j p)
    (projected_parameter F j p)

private theorem raw_target_factor (p : Index F j) :
    δ F j p ≫ native F j p ≫ after F j p =
      ((JTSharedInsertionCoarseNative.target F j).app p).map ≫ Q.map := by
  rw [← Category.assoc, JTSharedInsertionCoarseRegroupedNative.regroup_assembly_map]
  simp only [JTSharedInsertionCoarseNative.target, NatTrans.comp_app,
    Functor.whiskerLeft_app, code_comp, after, Category.assoc]

set_option maxHeartbeats 400000 in
private def actual_grouped_raw (p : Index F j) :=
  grouped_raw F j p (h₀ F j p ≫ δ F j p) (θ F j p)
    (clock F j p) (grouped_coordinate F j p)

set_option maxHeartbeats 400000 in
private def ordered_raw_core (p : Index F j) :=
  same_degree_raw W (S := coarseCode F j p) (T := G F j p) (k := K F j p)
    (h₀ F j p) (θ F j p) (δ F j p) (native F j p ≫ after F j p) (grouped F j p)
    (JTSharedInsertionCoarseRawData.orderedCoefficient F j p)
    (JTSharedInsertionCoarseRegroupedCoefficient.coefficient F j p)
    (actual_grouped_raw F j p)

private def final_raw_proof (p : Index F j) :=
  (ordered_raw_core F j p).trans
    (congrArg (h₀ F j p ≫ ·) (raw_target_factor F j p))

set_option maxHeartbeats 400000 in
/-- The exact complete ordered raw equation on EVERY lift of the ACTUAL coarse graph,
retaining original Q, full original time and both global endpoints. -/
theorem ordered_raw (p : Index F j) :
    lift (h₀ F j p) (θ F j p) ≫
        realizedLabel (coarseCode F j p).toSSet W (K F j p)
          (SSet.yonedaEquiv (JTSharedInsertionCoarseRawData.orderedCoefficient F j p)) =
      h₀ F j p ≫ ((JTSharedInsertionCoarseNative.target F j).app p).map ≫ Q.map :=
  final_raw_proof F j p

end
end DaggerModels.PartII.JTSharedInsertionCoarseRaw
