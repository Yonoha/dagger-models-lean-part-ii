import DaggerModelsPartII.JTJointSubdivisionBeadCharts
import DaggerModelsPartII.JTJointSubdivisionRefinements
import DaggerModelsPartII.JTJointCutSubdivision
import DaggerModelsPartII.JTNativePulledCutComparison
import DaggerModelsPartII.JTActualJointChainSeamRaw

/-!
One actual cut insertion inside an admissible adjacent interval. The original
intervals and their zero-length pieces remain explicit. Native concatenation
compares the full ordered prefix-middle-suffix codes over the original Q.
The coefficient and full time parameter are pulled from the original Family;
this does not identify normalized correction labels with unrelated intervals.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTJointSubdivisionInsertion

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

private def wedgeDiagram {C : Type} [SmallCategory C]
    (P R : C ⥤ NecklaceCode) : C ⥤ NecklaceCode where
  obj p := wedge (P.obj p) (R.obj p)
  map f := wedgeMap (P.map f) (R.map f)
  map_id p := by rw [P.map_id, R.map_id]; exact wedgeMap_id
  map_comp f g := by rw [P.map_comp, R.map_comp]; exact wedgeMap_comp _ _ _ _

private def wedgeNat {C : Type} [SmallCategory C]
    {P P' R R' : C ⥤ NecklaceCode} (α : P ⟶ P') (β : R ⟶ R') :
    wedgeDiagram P R ⟶ wedgeDiagram P' R' where
  app p := wedgeMap (α.app p) (β.app p)
  naturality p q f := by
    change NecklaceCode.Hom.comp (wedgeMap (P.map f) (R.map f))
      (wedgeMap (α.app q) (β.app q)) =
      NecklaceCode.Hom.comp (wedgeMap (α.app p) (β.app p))
        (wedgeMap (P'.map f) (R'.map f))
    rw [← wedgeMap_comp, ← wedgeMap_comp]
    exact congrArg₂ wedgeMap (α.naturality f) (β.naturality f)

private theorem timed_triangle {S U T : NecklaceCode}
    (g : S ⟶ U) (e : U ⟶ T) (f : S ⟶ T) (h : g ≫ e = f)
    (n d : SimplexCategory) (p : T.toSSet ⊗ J.obj n ⟶ J.obj d) :
    (g.map ⊗ₘ 𝟙 (J.obj n)) ≫ ((e.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
      (f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  have hm : g.map ≫ e.map = f.map := congrArg (fun u : S ⟶ T ↦ u.map) h
  rw [hm]

private theorem parameter_natural {P P' T T' I I' D D' : SSet.{0}}
    (s : P ⟶ P') (n : T ⟶ T') (e : P ⟶ T) (e' : P' ⟶ T')
    (clock : I ⟶ I') (degree : D ⟶ D') (p : T ⊗ I ⟶ D) (p' : T' ⊗ I' ⟶ D')
    (hn : s ≫ e' = e ≫ n) (hp : (n ⊗ₘ clock) ≫ p' = p ≫ degree) :
    (s ⊗ₘ clock) ≫ ((e' ⊗ₘ 𝟙 I') ≫ p') =
      ((e ⊗ₘ 𝟙 I) ≫ p) ≫ degree := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hn]
  rw [← Category.id_comp clock, ← tensorHom_comp_tensorHom, Category.assoc, hp,
    ← Category.assoc]

private theorem interval_point {T : NecklaceCode} {u v : Fin (T.len + 1)}
    (h : u ≤ v) (e : u = v) : intervalCode T u v h = NecklaceCode.point := by
  subst v
  exact intervalCode_diagonal _ _

private theorem wedge_over_natural {X Y : SSet.{0}}
    {x₀ x₁ x₂ : X.obj (op ⦋0⦌)} {y₀ y₁ y₂ : Y.obj (op ⦋0⦌)}
    (P : NecklacesOver X x₀ x₁) (R : NecklacesOver X x₁ x₂)
    (P' : NecklacesOver Y y₀ y₁) (R' : NecklacesOver Y y₁ y₂)
    (f : P.code ⟶ P'.code) (g : R.code ⟶ R'.code) (n : X ⟶ Y)
    (hf : f.map ≫ P'.map = P.map ≫ n) (hg : g.map ≫ R'.map = R.map ≫ n) :
    (wedgeMap f g).map ≫ (NecklacesOver.wedge P' R').map =
      (NecklacesOver.wedge P R).map ≫ n := by
  apply (wedgeIsPushout P.code R.code).hom_ext
  · rw [← Category.assoc, wedgeMap_left, Category.assoc, NecklacesOver.wedge_left,
      ← Category.assoc, NecklacesOver.wedge_left, hf]
  · rw [← Category.assoc, wedgeMap_right, Category.assoc, NecklacesOver.wedge_right,
      ← Category.assoc, NecklacesOver.wedge_right, hg]

private def nativeOf {T : NecklaceCode}
    (P : NecklacesOver (T.toSSet : SSet.{0})
      (T.verticesEquiv.symm (ULift.up 0))
      (T.verticesEquiv.symm (ULift.up (Fin.last T.len)))) : P.code ⟶ T where
  map := P.map
  first := P.first
  last := P.last

private theorem pair_ext {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
    {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
    {F : Family Q L time} {j : Joint Q.code} {a : A}
    {p q : JTJointPairSourceDiagram.Pair F j a}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p; cases q; cases hl; cases hr; rfl

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev Chart := JTJointSubdivisionBeadCharts.Index F j
private abbrev chartBase := JTJointSubdivisionBeadCharts.base F j
private abbrev chartCode (p : Chart F j) := (codes L).obj ((chartBase F j).obj p)
private abbrev vertices {p q : Chart F j} (f : p ⟶ q) :=
  orderMap ((codes L).map ((chartBase F j).map f)).map

/-- Every vertex between the actual adjacent cuts is allowed, including both endpoints. -/
abbrev Middle (p : Chart F j) :=
  {b : Fin ((chartCode F j p).len + 1) // p.2.firstCut ≤ b ∧ b ≤ p.2.lastCut}

private def middleTransport {p q : Chart F j} (f : p ⟶ q) (b : Middle F j p) :
    Middle F j q := by
  refine ⟨vertices F j f b.val, ?_, ?_⟩
  · have h := (vertices F j f).monotone b.property.1
    have hl := JTJointPairSourceDiagram.left_map F j
      ((JTJointSubdivisionBeadCharts.toPairs F j).map f)
    change vertices F j f p.2.firstCut = q.2.firstCut at hl
    rw [hl] at h
    exact h
  · have h := (vertices F j f).monotone b.property.2
    have hr := JTJointPairSourceDiagram.right_map F j
      ((JTJointSubdivisionBeadCharts.toPairs F j).map f)
    change vertices F j f p.2.lastCut = q.2.lastCut at hr
    rw [hr] at h
    exact h

/-- Actual insertion data transport by the unchanged original source arrows. -/
def middles : Chart F j ⥤ Type where
  obj := Middle F j
  map f := middleTransport F j f
  map_id p := by
    funext b
    apply Subtype.ext
    change orderMap ((codes L).map ((chartBase F j).map (𝟙 p))).map b.val = b.val
    rw [(chartBase F j).map_id, (codes L).map_id]
    exact orderMap_id_apply _ _
  map_comp f g := by
    funext b
    apply Subtype.ext
    change orderMap ((codes L).map ((chartBase F j).map (f ≫ g))).map b.val = _
    rw [(chartBase F j).map_comp, (codes L).map_comp]
    exact orderMap_comp_apply _ _ _

/-- A genuine admissible adjacent chart with one inserted original vertex.
Arrows retain every original operator, including coalescing insertion data. -/
abbrev Index := (middles F j).Elements

/-- Every admissible vertex insertion has an actual adjacent chart around it.
This chooses a chart object only; it does not assert a natural choice of brackets. -/
def ofCut (p : JTJointPairSourceDiagram.Index F j)
    (C : JTJointPairSubdivisionDiagram.Subdivision F j p)
    (t : Fin (((codes L).obj p.1).len + 1))
    (ht : p.2.left.val ≤ t ∧ t ≤ p.2.right.val) : Index F j := by
  let before := C.val.filter (fun v ↦ v ≤ t)
  let after := C.val.filter (fun v ↦ t ≤ v)
  have hb : before.Nonempty :=
    ⟨p.2.left.val, Finset.mem_filter.mpr ⟨C.property.1, ht.1⟩⟩
  have ha : after.Nonempty :=
    ⟨p.2.right.val, Finset.mem_filter.mpr ⟨C.property.2.1, ht.2⟩⟩
  let u := before.max' hb
  let v := after.min' ha
  have hu := Finset.mem_filter.mp (Finset.max'_mem before hb)
  have hv := Finset.mem_filter.mp (Finset.min'_mem after ha)
  have hadj : JTJointSubdivisionBeadCharts.Adjacent F j p C u v := by
    refine ⟨hu.1, hv.1, hu.2.trans hv.2, ?_⟩
    intro w hw huw hwv
    by_cases hwt : w ≤ t
    · have hwu : w ≤ u := Finset.le_max' before w (Finset.mem_filter.mpr ⟨hw, hwt⟩)
      exact (not_le_of_gt huw) hwu
    · have hvw : v ≤ w := Finset.min'_le after w
        (Finset.mem_filter.mpr ⟨hw, (le_of_not_ge hwt)⟩)
      exact (not_le_of_gt hwv) hvw
  exact ⟨⟨p, ⟨C, u, v, hadj⟩⟩, ⟨t, hu.2, hv.2⟩⟩

/-- Forget only the proposed inserted cut, keeping its actual adjacent chart. -/
abbrev toCharts : Index F j ⥤ Chart F j := CategoryOfElements.π (middles F j)

/-- The original source object and original arrow remain unchanged. -/
abbrev base : Index F j ⥤ A := toCharts F j ⋙ chartBase F j

private abbrev T (p : Index F j) := (codes L).obj ((base F j).obj p)
private abbrev a (p : Index F j) := p.1.2.firstCut
private abbrev b (p : Index F j) := p.2.val
private abbrev c (p : Index F j) := p.1.2.lastCut
private abbrev hab (p : Index F j) := p.2.property.1
private abbrev hbc (p : Index F j) := p.2.property.2
private abbrev hac (p : Index F j) := p.1.2.adjacent.2.2.1
private abbrev oldPair (p : Index F j) :=
  (JTJointSubdivisionBeadCharts.toPairs F j).obj p.1
private abbrev oldNative {p q : Index F j} (f : p ⟶ q) :=
  (codes L).map ((base F j).map f)

private theorem first_map {p q : Index F j} (f : p ⟶ q) :
    orderMap (oldNative F j f).map (a F j p) = a F j q :=
  JTJointPairSourceDiagram.left_map F j
    ((JTJointSubdivisionBeadCharts.toPairs F j).map f.val)

private theorem middle_map {p q : Index F j} (f : p ⟶ q) :
    orderMap (oldNative F j f).map (b F j p) = b F j q :=
  congrArg Subtype.val f.property

private theorem last_map {p q : Index F j} (f : p ⟶ q) :
    orderMap (oldNative F j f).map (c F j p) = c F j q :=
  JTJointPairSourceDiagram.right_map F j
    ((JTJointSubdivisionBeadCharts.toPairs F j).map f.val)

/-- The inserted vertex itself lies over the same genuine target joint. -/
theorem middle_at_joint (p : Index F j) :
    orderMap (F.collapse.app ((base F j).obj p)).map (b F j p) = j.val := by
  apply le_antisymm
  · exact ((orderMap (F.collapse.app ((base F j).obj p)).map).monotone
      (hbc F j p)).trans (oldPair F j p).2.right.property.le
  · exact (oldPair F j p).2.left.property.symm.le.trans
      ((orderMap (F.collapse.app ((base F j).obj p)).map).monotone (hab F j p))

private theorem middle_bounds (p : Index F j) :
    p.1.1.2.left.val ≤ b F j p ∧ b F j p ≤ p.1.1.2.right.val :=
  ⟨(p.1.2.cuts.property.2.2.1 (a F j p) p.1.2.adjacent.1).1.trans (hab F j p),
    (hbc F j p).trans
      (p.1.2.cuts.property.2.2.1 (c F j p) p.1.2.adjacent.2.1).2⟩

/-- The actual admissible cut set after insertion, not an unrelated interval choice. -/
def refinedCuts (p : Index F j) : JTJointPairSubdivisionDiagram.Subdivision F j p.1.1 :=
  JTJointSubdivisionRefinements.insertCut F j p.1.1 p.1.2.cuts (b F j p)
    (middle_bounds F j p)

/-- This is the literal vertical refinement in the existing subdivision category. -/
def refinement (p : Index F j) :
    (⟨p.1.1, p.1.2.cuts⟩ : JTJointPairSubdivisionDiagram.Index F j) ⟶
      ⟨p.1.1, refinedCuts F j p⟩ :=
  JTJointPairSubdivisionDiagram.refinement F j p.1.1 p.1.2.cuts (refinedCuts F j p)
    (JTJointSubdivisionRefinements.le_insertCut F j p.1.1 p.1.2.cuts (b F j p)
      (middle_bounds F j p))

/-- Reinserting an endpoint, or any already present cut, retains the exact old cut set. -/
theorem refinedCuts_eq_of_mem (p : Index F j) (h : b F j p ∈ p.1.2.cuts.val) :
    refinedCuts F j p = p.1.2.cuts :=
  JTJointSubdivisionRefinements.insertCut_of_mem F j p.1.1 p.1.2.cuts (b F j p)
    (middle_bounds F j p) h

/-- The left new interval is adjacent in the actual inserted subdivision. -/
theorem lower_adjacent (p : Index F j) :
    JTJointSubdivisionBeadCharts.Adjacent F j p.1.1 (refinedCuts F j p)
      (a F j p) (b F j p) := by
  refine ⟨Finset.mem_insert_of_mem p.1.2.adjacent.1, Finset.mem_insert_self _ _,
    hab F j p, ?_⟩
  intro t ht hat htb
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (lt_irrefl _ htb)
  · exact p.1.2.adjacent.2.2.2 t ht hat (htb.trans_le (hbc F j p))

/-- The right new interval is adjacent in that same actual inserted subdivision. -/
theorem upper_adjacent (p : Index F j) :
    JTJointSubdivisionBeadCharts.Adjacent F j p.1.1 (refinedCuts F j p)
      (b F j p) (c F j p) := by
  refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem p.1.2.adjacent.2.1,
    hbc F j p, ?_⟩
  intro t ht hbt htc
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (lt_irrefl _ hbt)
  · exact p.1.2.adjacent.2.2.2 t ht ((hab F j p).trans_lt hbt) htc

/-- The exact marked cut at which the already checked raw449 seam cover can be pulled back. -/
def insertedCut : Index F j ⥤ JTExactlyMarkedSourceDiagram.Index F j where
  obj p := ⟨(base F j).obj p, ⟨b F j p, middle_at_joint F j p⟩⟩
  map f := ⟨(base F j).map f, Subtype.ext (middle_map F j f)⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

private def leftPair : Index F j ⥤ JTJointPairSourceDiagram.Index F j where
  obj p := ⟨(base F j).obj p,
    ⟨(oldPair F j p).2.left, ⟨b F j p, middle_at_joint F j p⟩, hab F j p⟩⟩
  map f := ⟨(base F j).map f, by
    apply pair_ext
    · exact Subtype.ext (first_map F j f)
    · exact Subtype.ext (middle_map F j f)⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

private def rightPair : Index F j ⥤ JTJointPairSourceDiagram.Index F j where
  obj p := ⟨(base F j).obj p,
    ⟨⟨b F j p, middle_at_joint F j p⟩, (oldPair F j p).2.right, hbc F j p⟩⟩
  map f := ⟨(base F j).map f, by
    apply pair_ext
    · exact Subtype.ext (middle_map F j f)
    · exact Subtype.ext (last_map F j f)⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

private abbrev coarsePair := toCharts F j ⋙ JTJointSubdivisionBeadCharts.toPairs F j
private abbrev initialPiece := coarsePair F j ⋙ JTJointPairSourceDiagram.leftCut F j ⋙
  JTExactlyMarkedCutDiagrams.leftNative F j
private abbrev suffix := coarsePair F j ⋙ JTJointPairSourceDiagram.rightCut F j ⋙
  JTExactlyMarkedCutDiagrams.rightNative F j
private abbrev middle := toCharts F j ⋙ JTJointSubdivisionBeadCharts.native F j
private abbrev lower := leftPair F j ⋙ JTJointPairGapDiagram.native F j
private abbrev upper := rightPair F j ⋙ JTJointPairGapDiagram.native F j

/-- The old whole prefix, exact adjacent interval, and old whole suffix. -/
abbrev coarseCodes := wedgeDiagram (initialPiece F j) (wedgeDiagram (middle F j) (suffix F j))

/-- Insertion splits only the named original interval; every surrounding piece stays explicit. -/
abbrev refinedCodes := wedgeDiagram (initialPiece F j)
  (wedgeDiagram (wedgeDiagram (lower F j) (upper F j)) (suffix F j))

private abbrev prefixOver (p : Index F j) := intervalOver (T F j p) 0 (a F j p) (Fin.zero_le _)
private abbrev middleOver (p : Index F j) :=
  intervalOver (T F j p) (a F j p) (c F j p) (hac F j p)
private abbrev suffixOver (p : Index F j) :=
  intervalOver (T F j p) (c F j p) (Fin.last (T F j p).len) (Fin.le_last _)
private abbrev lowerOver (p : Index F j) :=
  intervalOver (T F j p) (a F j p) (b F j p) (hab F j p)
private abbrev upperOver (p : Index F j) :=
  intervalOver (T F j p) (b F j p) (c F j p) (hbc F j p)
private abbrev coarseOver (p : Index F j) := NecklacesOver.wedge (prefixOver F j p)
  (NecklacesOver.wedge (middleOver F j p) (suffixOver F j p))
private abbrev refinedOver (p : Index F j) := NecklacesOver.wedge (prefixOver F j p)
  (NecklacesOver.wedge (NecklacesOver.wedge (lowerOver F j p) (upperOver F j p))
    (suffixOver F j p))

/-- A cut inserted at the first endpoint retains the literal zero left interval. -/
theorem lower_point (p : Index F j) (h : b F j p = a F j p) :
    (lower F j).obj p = NecklaceCode.point := by
  change intervalCode (T F j p) (a F j p) (b F j p) _ = _
  exact interval_point _ h.symm

/-- A cut inserted at the last endpoint retains the literal zero right interval. -/
theorem upper_point (p : Index F j) (h : b F j p = c F j p) :
    (upper F j).obj p = NecklaceCode.point := by
  change intervalCode (T F j p) (b F j p) (c F j p) _ = _
  exact interval_point _ h

/-- The old full ordered code maps to the literal original native source. -/
def coarseAssembly (p : Index F j) : (coarseCodes F j).obj p ⟶ T F j p :=
  nativeOf (coarseOver F j p)

/-- The refined full ordered code maps to that SAME original native source. -/
def refinedAssembly (p : Index F j) : (refinedCodes F j).obj p ⟶ T F j p :=
  nativeOf (refinedOver F j p)

private def comparisonOver (p : Index F j) : refinedOver F j p ⟶ coarseOver F j p :=
  NecklacesOver.wedgeHom (𝟙 (prefixOver F j p))
    (NecklacesOver.wedgeHom
      (JTJointCutSubdivision.concat (T F j p) (a F j p) (b F j p) (c F j p)
        (hab F j p) (hbc F j p)) (𝟙 (suffixOver F j p)))

/-- The full actual native insertion map, with all zero pieces retained. -/
def comparison (p : Index F j) : (refinedCodes F j).obj p ⟶ (coarseCodes F j).obj p :=
  (comparisonOver F j p).hom

private abbrev concatenate (p : Index F j) :=
  (JTJointCutSubdivision.concat (T F j p) (a F j p) (b F j p) (c F j p)
    (hab F j p) (hbc F j p)).hom

private theorem concatenate_naturality {p q : Index F j} (f : p ⟶ q) :
    wedgeMap ((lower F j).map f) ((upper F j).map f) ≫ concatenate F j q =
      concatenate F j p ≫ (middle F j).map f := by
  apply NecklaceCode.Hom.ext
  apply (cancel_mono (intervalι (T F j q) (a F j q) (c F j q) (hac F j q))).mp
  change (wedgeMap ((lower F j).map f) ((upper F j).map f)).map ≫
      (concatenate F j q).map ≫ intervalι (T F j q) (a F j q) (c F j q) _ =
    (concatenate F j p).map ≫
      ((middle F j).map f).map ≫ intervalι (T F j q) (a F j q) (c F j q) _
  have hm : ((middle F j).map f).map ≫
      intervalι (T F j q) (a F j q) (c F j q) (hac F j q) =
      intervalι (T F j p) (a F j p) (c F j p) (hac F j p) ≫ (oldNative F j f).map :=
    JTJointPairGapDiagram.codeMap_fac F j ((coarsePair F j).map f)
  rw [hm]
  apply (wedgeIsPushout ((lower F j).obj p) ((upper F j).obj p)).hom_ext
  · have hl : ((lower F j).map f).map ≫
        intervalι (T F j q) (a F j q) (b F j q) (hab F j q) =
        intervalι (T F j p) (a F j p) (b F j p) (hab F j p) ≫ (oldNative F j f).map :=
      JTJointPairGapDiagram.codeMap_fac F j ((leftPair F j).map f)
    have hq : wedgeιLeft ((lower F j).obj q) ((upper F j).obj q) ≫
        (concatenate F j q).map ≫
          intervalι (T F j q) (a F j q) (c F j q) (hac F j q) =
            intervalι (T F j q) (a F j q) (b F j q) (hab F j q) :=
      JTJointCutSubdivision.concat_first _ _ _ _ _ _
    have hp : wedgeιLeft ((lower F j).obj p) ((upper F j).obj p) ≫
        (concatenate F j p).map ≫
          intervalι (T F j p) (a F j p) (c F j p) (hac F j p) =
            intervalι (T F j p) (a F j p) (b F j p) (hab F j p) :=
      JTJointCutSubdivision.concat_first _ _ _ _ _ _
    have hpa := congrArg (fun u ↦ u ≫ (oldNative F j f).map) hp
    simp only [Category.assoc] at hpa
    rw [← Category.assoc (wedgeιLeft _ _)
      (wedgeMap ((lower F j).map f) ((upper F j).map f)).map,
      wedgeMap_left, Category.assoc, hq, hl, hpa]
  · have hr : ((upper F j).map f).map ≫
        intervalι (T F j q) (b F j q) (c F j q) (hbc F j q) =
        intervalι (T F j p) (b F j p) (c F j p) (hbc F j p) ≫ (oldNative F j f).map :=
      JTJointPairGapDiagram.codeMap_fac F j ((rightPair F j).map f)
    have hq : wedgeιRight ((lower F j).obj q) ((upper F j).obj q) ≫
        (concatenate F j q).map ≫
          intervalι (T F j q) (a F j q) (c F j q) (hac F j q) =
            intervalι (T F j q) (b F j q) (c F j q) (hbc F j q) :=
      JTJointCutSubdivision.concat_last _ _ _ _ _ _
    have hp : wedgeιRight ((lower F j).obj p) ((upper F j).obj p) ≫
        (concatenate F j p).map ≫
          intervalι (T F j p) (a F j p) (c F j p) (hac F j p) =
            intervalι (T F j p) (b F j p) (c F j p) (hbc F j p) :=
      JTJointCutSubdivision.concat_last _ _ _ _ _ _
    have hpa := congrArg (fun u ↦ u ≫ (oldNative F j f).map) hp
    simp only [Category.assoc] at hpa
    rw [← Category.assoc (wedgeιRight _ _)
      (wedgeMap ((lower F j).map f) ((upper F j).map f)).map,
      wedgeMap_right, Category.assoc, hq, hr, hpa]

private def concatenateNatural : wedgeDiagram (lower F j) (upper F j) ⟶ middle F j where
  app := concatenate F j
  naturality _ _ f := concatenate_naturality F j f

/-- Insertion compares the fine native diagram to the coarse native diagram.
Naturality retains the original source arrows and their exact image cut data. -/
def comparisonNatural : refinedCodes F j ⟶ coarseCodes F j :=
  wedgeNat (𝟙 (initialPiece F j))
    (wedgeNat (concatenateNatural F j) (𝟙 (suffix F j)))

/-- The natural comparison is the full explicit insertion map. -/
theorem comparisonNatural_app (p : Index F j) :
    (comparisonNatural F j).app p = comparison F j p := rfl

/-- Concatenation commutes with the complete original native inclusion. -/
theorem comparison_fac (p : Index F j) :
    comparison F j p ≫ coarseAssembly F j p = refinedAssembly F j p :=
  NecklaceCode.Hom.ext (comparisonOver F j p).w

/-- The whole coarse inclusion is natural before collapsing to the fixed target. -/
theorem coarseAssembly_naturality {p q : Index F j} (f : p ⟶ q) :
    (coarseCodes F j).map f ≫ coarseAssembly F j q =
      coarseAssembly F j p ≫ oldNative F j f := by
  apply NecklaceCode.Hom.ext
  have hl : ((initialPiece F j).map f).map ≫ (prefixOver F j q).map =
      (prefixOver F j p).map ≫ (oldNative F j f).map :=
    cutLeftHom_fac (oldNative F j f) (a F j p) (a F j q) (first_map F j f)
  have hm : ((middle F j).map f).map ≫ (middleOver F j q).map =
      (middleOver F j p).map ≫ (oldNative F j f).map :=
    JTJointPairGapDiagram.codeMap_fac F j ((coarsePair F j).map f)
  have hr : ((suffix F j).map f).map ≫ (suffixOver F j q).map =
      (suffixOver F j p).map ≫ (oldNative F j f).map :=
    cutRightHom_fac (oldNative F j f) (c F j p) (c F j q) (last_map F j f)
  exact wedge_over_natural (prefixOver F j p)
    (NecklacesOver.wedge (middleOver F j p) (suffixOver F j p))
    (prefixOver F j q) (NecklacesOver.wedge (middleOver F j q) (suffixOver F j q))
    ((initialPiece F j).map f) (wedgeMap ((middle F j).map f) ((suffix F j).map f))
    (oldNative F j f).map hl
    (wedge_over_natural (middleOver F j p) (suffixOver F j p)
      (middleOver F j q) (suffixOver F j q) ((middle F j).map f) ((suffix F j).map f)
      (oldNative F j f).map hm hr)

/-- The whole fine inclusion retains precisely the same original native operator. -/
theorem refinedAssembly_naturality {p q : Index F j} (f : p ⟶ q) :
    (refinedCodes F j).map f ≫ refinedAssembly F j q =
      refinedAssembly F j p ≫ oldNative F j f := by
  have hn := (comparisonNatural F j).naturality f
  change (refinedCodes F j).map f ≫ comparison F j q =
    comparison F j p ≫ (coarseCodes F j).map f at hn
  rw [← comparison_fac F j q, ← Category.assoc, hn, Category.assoc,
    coarseAssembly_naturality, ← Category.assoc, comparison_fac]

/-- The old whole code includes naturally in the original native family. -/
def coarseAssemblyNatural : coarseCodes F j ⟶ base F j ⋙ codes L where
  app := coarseAssembly F j
  naturality _ _ f := coarseAssembly_naturality F j f

/-- The inserted whole code includes naturally in that same original family. -/
def refinedAssemblyNatural : refinedCodes F j ⟶ base F j ⋙ codes L where
  app := refinedAssembly F j
  naturality _ _ f := refinedAssembly_naturality F j f

/-- The native insertion is a full triangle of natural transformations. -/
theorem comparison_natural_triangle :
    comparisonNatural F j ≫ coarseAssemblyNatural F j = refinedAssemblyNatural F j := by
  ext p
  exact comparison_fac F j p

/-- Both full code maps remain over the original fixed native target Q. -/
theorem over_original_Q (p : Index F j) :
    comparison F j p ≫ (coarseAssembly F j p ≫ F.collapse.app ((base F j).obj p)) =
      refinedAssembly F j p ≫ F.collapse.app ((base F j).obj p) := by
  rw [← Category.assoc, comparison_fac]

/-- The complete original time parameter is restricted along the old full code. -/
abbrev coarseParameter (p : Index F j) :=
  ((coarseAssembly F j p).map ⊗ₘ 𝟙 (J.obj (time.obj ((base F j).obj p)))) ≫
    F.parameter ((base F j).obj p)

/-- The refined code retains every time simplex of that same original parameter. -/
abbrev refinedParameter (p : Index F j) :=
  ((refinedAssembly F j p).map ⊗ₘ 𝟙 (J.obj (time.obj ((base F j).obj p)))) ≫
    F.parameter ((base F j).obj p)

/-- The full timed native insertion commutes before any raw realization or endpoint quotient. -/
theorem parameter_square (p : Index F j) :
    ((comparison F j p).map ⊗ₘ 𝟙 (J.obj (time.obj ((base F j).obj p)))) ≫
        coarseParameter F j p = refinedParameter F j p :=
  timed_triangle (comparison F j p) (coarseAssembly F j p) (refinedAssembly F j p)
    (comparison_fac F j p) (time.obj ((base F j).obj p)) _
    (F.parameter ((base F j).obj p))

private abbrev degrees := base F j ⋙ L ⋙
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
  CategoryTheory.Prod.snd NecklaceCode SimplexCategory

/-- Every original operator commutes with the complete old time parameter. -/
theorem coarseParameter_map {p q : Index F j} (f : p ⟶ q) :
    (((coarseCodes F j).map f).map ⊗ₘ J.map (time.map ((base F j).map f))) ≫
        coarseParameter F j q = coarseParameter F j p ≫ J.map ((degrees F j).map f) := by
  have hn : ((coarseCodes F j).map f).map ≫ (coarseAssembly F j q).map =
      (coarseAssembly F j p).map ≫ (oldNative F j f).map :=
    congrArg (fun u : (coarseCodes F j).obj p ⟶ T F j q ↦ u.map)
      (coarseAssembly_naturality F j f)
  exact parameter_natural _ _ _ _ _ _ _ _ hn (F.parameter_map ((base F j).map f))

/-- The same mixed native, clock, and coefficient equation holds after insertion. -/
theorem refinedParameter_map {p q : Index F j} (f : p ⟶ q) :
    (((refinedCodes F j).map f).map ⊗ₘ J.map (time.map ((base F j).map f))) ≫
        refinedParameter F j q = refinedParameter F j p ≫ J.map ((degrees F j).map f) := by
  have hn : ((refinedCodes F j).map f).map ≫ (refinedAssembly F j q).map =
      (refinedAssembly F j p).map ≫ (oldNative F j f).map :=
    congrArg (fun u : (refinedCodes F j).obj p ⟶ T F j q ↦ u.map)
      (refinedAssembly_naturality F j f)
  exact parameter_natural _ _ _ _ _ _ _ _ hn (F.parameter_map ((base F j).map f))

/-- The complete original-label evaluation on the old explicit subdivision. -/
def coarseEvaluation (p : Index F j) :=
  JTNativePulledCutComparison.evaluation (L.obj ((base F j).obj p))
    (time.obj ((base F j).obj p)) (F.collapse.app ((base F j).obj p))
    (F.parameter ((base F j).obj p)) (F.raw ((base F j).obj p)) (coarseAssembly F j p)

/-- Every internal necklace of the refined full original-label graph is retained. -/
def refinedEvaluation (p : Index F j) :=
  JTNativePulledCutComparison.evaluation (L.obj ((base F j).obj p))
    (time.obj ((base F j).obj p)) (F.collapse.app ((base F j).obj p))
    (F.parameter ((base F j).obj p)) (F.raw ((base F j).obj p)) (refinedAssembly F j p)

/-- Full internal-necklace comparison in the unchanged original Q and global endpoints.
The labels here are literal native pullbacks of the original label. -/
def evaluationComparison (p : Index F j) :=
  JTNativePulledCutComparison.compare (L.obj ((base F j).obj p))
    (time.obj ((base F j).obj p)) (F.collapse.app ((base F j).obj p))
    (F.parameter ((base F j).obj p)) (F.raw ((base F j).obj p))
    (refinedAssembly F j p) (coarseAssembly F j p) (comparison F j p) (comparison_fac F j p)

end
end DaggerModels.PartII.JTJointSubdivisionInsertion
