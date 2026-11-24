import DaggerModelsPartII.JTGraphInterpolatedChainOver
import DaggerModelsPartII.JTGraphChainArrowIndex

/-! Coherent exact graph families on the original simplex-map factorizations. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSpanFamily

open JTGraphCylinderSimplexSpan (Simplices SpanIndex smaller larger firstVertex degree)
open JTGraphSimplexLastVertex (lastVertex)
open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)

noncomputable section

section Ordinal

variable {C : Type} [SmallCategory C]

private abbrev vertex (s : Simplices C) (i : Fin (s.unop.fst.unop.len + 1)) :=
  s.unop.snd.obj i

private abbrev toVertex (s : Simplices C) (i : Fin (s.unop.fst.unop.len + 1)) :
    first s.unop.snd ⟶ vertex s i :=
  s.unop.snd.map (homOfLE (Fin.zero_le i))

private abbrev suffix (s : Simplices C) (i : Fin (s.unop.fst.unop.len + 1)) :
    vertex s i ⟶ last s.unop.snd :=
  s.unop.snd.map (homOfLE (Fin.le_last i))

private abbrev inTime {s t : Simplices C} (f : s ⟶ t) (i : Fin (s.unop.fst.unop.len + 1)) :
    Fin (t.unop.fst.unop.len + 1) :=
  f.unop.val.unop.toOrderHom i

private theorem vertex_eq {s t : Simplices C} (f : s ⟶ t) (i : Fin (s.unop.fst.unop.len + 1)) :
    vertex s i = vertex t (inTime f i) :=
  congrArg (fun a : (nerve C).obj s.unop.fst ↦ a.obj i) f.unop.property.symm

private theorem prefix_reindex {s t : Simplices C} (f : s ⟶ t)
    (i : Fin (s.unop.fst.unop.len + 1)) :
    (firstVertex C).map f.unop ≫ toVertex s i =
      toVertex t (inTime f i) ≫ eqToHom (vertex_eq f i).symm := by
  obtain ⟨f, rfl⟩ : ∃ g : t.unop ⟶ s.unop, g.op = f := ⟨f.unop, rfl⟩
  rcases s with ⟨⟨p, s⟩⟩
  rcases t with ⟨⟨q, t⟩⟩
  rcases f with ⟨j, h⟩
  change q ⟶ p at j
  change (nerve C).map j t = s at h
  subst s
  change (initialArrow j t ≫ eqToHom _) ≫
      ((nerve C).map j t).map (homOfLE (Fin.zero_le i)) =
    t.map (homOfLE (Fin.zero_le (j.unop.toOrderHom i))) ≫ eqToHom _
  simp only [eqToHom_refl, Category.comp_id]
  change t.map _ ≫ t.map _ = t.map _
  rw [← t.map_comp]
  congr 1

private theorem suffix_reindex {s t : Simplices C} (f : s ⟶ t)
    (i : Fin (s.unop.fst.unop.len + 1)) :
    suffix s i ≫ (lastVertex C).map f =
      eqToHom (vertex_eq f i) ≫ suffix t (inTime f i) := by
  obtain ⟨f, rfl⟩ : ∃ g : t.unop ⟶ s.unop, g.op = f := ⟨f.unop, rfl⟩
  rcases s with ⟨⟨p, s⟩⟩
  rcases t with ⟨⟨q, t⟩⟩
  rcases f with ⟨j, h⟩
  change q ⟶ p at j
  change (nerve C).map j t = s at h
  subst s
  change ((nerve C).map j t).map (homOfLE (Fin.le_last i)) ≫
      (eqToHom _ ≫ lastArrow j t) =
    eqToHom _ ≫ t.map (homOfLE (Fin.le_last (j.unop.toOrderHom i)))
  simp only [eqToHom_refl, Category.id_comp]
  change t.map _ ≫ t.map _ = t.map _
  rw [← t.map_comp]
  congr 1

variable (C)

/-- The initial vertex of the larger simplex of an actual factorization. -/
def head : SpanIndex C ⥤ C :=
  larger C ⋙ unopUnop ((nerve C).Elements) ⋙ firstVertex C

/-- The final vertex of the smaller simplex of an actual factorization. -/
def tail : SpanIndex C ⥤ C := smaller C ⋙ lastVertex C

variable {C}

private abbrev small (P : SpanIndex C) := (smaller C).obj P
private abbrev big (P : SpanIndex C) := P.unop.fst.2
private abbrev spanArrow (P : SpanIndex C) : small P ⟶ big P := P.unop.snd
private abbrev nativePrefix (P : SpanIndex C) (i : Fin ((small P).unop.fst.unop.len + 1)) :
    (head C).obj P ⟶ vertex (small P) i :=
  (firstVertex C).map (spanArrow P).unop ≫ toVertex (small P) i

private abbrev nativeSuffix (P : SpanIndex C) (i : Fin ((small P).unop.fst.unop.len + 1)) :
    vertex (small P) i ⟶ (tail C).obj P :=
  suffix (small P) i

private theorem prefix_square {P P' : SpanIndex C} (f : P ⟶ P')
    (i : Fin ((small P).unop.fst.unop.len + 1)) :
    (head C).map f ≫ nativePrefix P' (inTime ((smaller C).map f) i) =
      nativePrefix P i ≫ eqToHom (vertex_eq ((smaller C).map f) i) := by
  let s := (smaller C).map f
  let j := spanArrow P
  let j' := spanArrow P'
  let l : big P' ⟶ big P := f.unop.val.2
  let F := firstVertex C
  have h : s ≫ j' ≫ l = j := f.unop.property
  have hh : F.map l.unop ≫ F.map j'.unop ≫ F.map s.unop = F.map j.unop := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun u : small P ⟶ big P ↦ F.map u.unop) h
  let e := vertex_eq s i
  have hp : F.map s.unop ≫ toVertex (small P) i =
      toVertex (small P') (inTime s i) ≫ eqToHom e.symm := prefix_reindex s i
  have hp' : toVertex (small P') (inTime s i) =
      F.map s.unop ≫ toVertex (small P) i ≫ eqToHom e := by
    rw [← Category.assoc, hp, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  change F.map l.unop ≫ F.map j'.unop ≫ toVertex (small P') (inTime s i) =
    (F.map j.unop ≫ toVertex (small P) i) ≫ eqToHom e
  rw [hp', ← Category.assoc _ (F.map s.unop), ← Category.assoc (F.map l.unop)]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun u ↦ u ≫ toVertex (small P) i ≫ eqToHom e) hh

private abbrev traversalApp (P : SpanIndex C) : (head C).obj P ⟶ (tail C).obj P :=
  (firstVertex C).map (spanArrow P).unop ≫
    (small P).unop.snd.map (homOfLE (Fin.zero_le (Fin.last (small P).unop.fst.unop.len)))

private theorem prefix_suffix (P : SpanIndex C) (i : Fin ((small P).unop.fst.unop.len + 1)) :
    nativePrefix P i ≫ nativeSuffix P i = traversalApp P := by
  change (_ ≫ (small P).unop.snd.map _) ≫ (small P).unop.snd.map _ =
    _ ≫ (small P).unop.snd.map _
  rw [Category.assoc, ← (small P).unop.snd.map_comp]
  congr 1

/-- Prefix and suffix combine to give the exact original traversal arrow. -/
def traversal : head C ⟶ tail C where
  app P := traversalApp P
  naturality := by
    intro P P' f
    let s := (smaller C).map f
    let i : Fin ((small P).unop.fst.unop.len + 1) := 0
    have hs : nativeSuffix P i ≫ (tail C).map f =
        eqToHom (vertex_eq s i) ≫ nativeSuffix P' (inTime s i) := suffix_reindex s i
    change (head C).map f ≫ traversalApp P' = traversalApp P ≫ (tail C).map f
    calc
      _ = ((head C).map f ≫ nativePrefix P' (inTime s i)) ≫
          nativeSuffix P' (inTime s i) := by
        rw [← prefix_suffix P' (inTime s i)]
        exact (Category.assoc _ _ _).symm
      _ = (nativePrefix P i ≫ eqToHom (vertex_eq s i)) ≫
          nativeSuffix P' (inTime s i) :=
        congrArg (fun g ↦ g ≫ nativeSuffix P' (inTime s i)) (prefix_square f i)
      _ = (nativePrefix P i ≫ nativeSuffix P i) ≫ (tail C).map f := by
        rw [Category.assoc, ← hs, ← Category.assoc]
      _ = _ := by rw [prefix_suffix]

end Ordinal

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict restrict_comp)
open JTGraphInterpolatedChainOver (identityLift)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev C := TargetComma Q

/-- Take the prescribed lift at the selected vertex, restricted to the
larger chain's first source and transported to the smaller chain's last target. -/
def family (P : SpanIndex (C (Q := Q))) (i : Fin ((small P).unop.fst.unop.len + 1)) :
    GraphLift ((tail (C (Q := Q))).obj P).left ((head (C (Q := Q))).obj P).left.fiber.left :=
  (restrict (identityLift (vertex (small P) i)).val
    ((nativeCode Q).map (nativePrefix P i))).transport (nativeSuffix P i).left

/-- Every graph in the family uses the same exact native traversal. -/
theorem family_collapse (P : SpanIndex (C (Q := Q))) (i : Fin ((small P).unop.fst.unop.len + 1)) :
    (family P i).collapse = (nativeCode Q).map ((traversal (C := C (Q := Q))).app P) := by
  change (((nativeCode Q).map (nativePrefix P i) ≫
      (identityLift (vertex (small P) i)).val.collapse) ≫
      (nativeCode Q).map (nativeSuffix P i)) = _
  rw [(identityLift (vertex (small P) i)).property]
  change (((nativeCode Q).map (nativePrefix P i) ≫
      𝟙 ((nativeCode Q).obj (vertex (small P) i))) ≫
      (nativeCode Q).map (nativeSuffix P i)) = _
  rw [Category.comp_id, ← (nativeCode Q).map_comp]
  exact (nativeCode Q).congr_map (prefix_suffix P i)

private theorem graph_square {S S' T T' U U' : C (Q := Q)}
    (e : T = T') (p : S ⟶ T) (p' : S' ⟶ T') (g : S ⟶ S')
    (v : T ⟶ U) (v' : T' ⟶ U') (a : U ⟶ U')
    (hp : g ≫ p' = p ≫ eqToHom e) (hv : v ≫ a = eqToHom e ≫ v') :
    ((restrict (identityLift T).val ((nativeCode Q).map p)).transport v.left).transport a.left =
      restrict ((restrict (identityLift T').val ((nativeCode Q).map p')).transport v'.left)
        ((nativeCode Q).map g) := by
  subst T'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hp hv
  let D := identityLift T
  let N := nativeCode Q
  have hh : N.map p = N.map g ≫ N.map p' := by rw [← N.map_comp, hp]
  change ((restrict D.val (N.map p)).transport v.left).transport a.left =
    restrict ((restrict D.val (N.map p')).transport v'.left) (N.map g)
  rw [GraphLift.transport_comp]
  have ha : v.left ≫ a.left = v'.left := congrArg CommaMorphism.left hv
  rw [ha, hh, ← restrict_comp]
  exact JTGraphTransportRestriction.transport_restrict
    (restrict D.val (N.map p')) (N.map g) v'

/-- The exact graph families agree under every original span operator. The
native prefix changes the source while the suffix transports the target. -/
theorem family_map {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P')
    (i : Fin ((small P).unop.fst.unop.len + 1)) :
    (family P i).transport (((tail (C (Q := Q))).map f).left) =
      restrict (family P' (inTime ((smaller (C (Q := Q))).map f) i))
        ((nativeCode Q).map ((head (C (Q := Q))).map f)) :=
  graph_square (vertex_eq ((smaller (C (Q := Q))).map f) i)
    (nativePrefix P i) (nativePrefix P' _) ((head (C (Q := Q))).map f)
    (nativeSuffix P i) (nativeSuffix P' _) ((tail (C (Q := Q))).map f)
    (prefix_square f i) (suffix_reindex ((smaller (C (Q := Q))).map f) i)

end
end DaggerModels.PartII.JTGraphSpanFamily

