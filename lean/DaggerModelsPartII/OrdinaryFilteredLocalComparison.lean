import OriginalOrdinaryMovingHomColimitReconciled
import FilteredGeometric
import RigidificationCofBase
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-!
# Filtered local comparison for ordinary simplicial categories

The proof works with the actual ordinary enriched colimit cocones. The Hom
diagrams retain both moving endpoint casts. Restriction to a final under
category supplies compatible endpoints for an arbitrary pair of colimit
objects. The geometric filtered-colimit theorem then applies to the literal
Hom comparison, provided transition maps are Hom-monic. Object coverage follows
from the actual vertex colimit and does not require object-injective transitions.

The conclusion concerns the geometric weak-equivalence condition on every
ordinary enriched Hom map. It does not install an ordinary model category.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalOrdinaryMovingHomColimits
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryFilteredLocalComparison

noncomputable section

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {F G : J ⥤ SimplicialCat.{u, u}}
variable (η : F ⟶ G)

/-- The target endpoint section induced from a source endpoint section. -/
private def mappedObj (s : ∀ j, (F.obj j).Obj) (j : J) : (G.obj j).Obj :=
  (η.app j).obj (s j)

omit [IsFiltered J] in
private theorem mappedObj_naturality (s : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    {j k : J} (α : j ⟶ k) :
    (G.map α).obj (mappedObj η s j) = mappedObj η s k := by
  have h := congrArg (fun f : F.obj j ⟶ G.obj k ↦ f.obj (s j))
    (η.naturality α)
  change (η.app k).obj ((F.map α).obj (s j)) =
    (G.map α).obj ((η.app j).obj (s j)) at h
  exact h.symm.trans (congrArg (η.app k).obj (hs α))

/-- The Hom comparison from the source moving endpoints to their literal
images under the natural transformation. -/
private def movingHomComparison
    (s t : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k) :
    homDiagram F s t hs ht ⟶
      homDiagram G (mappedObj η s) (mappedObj η t)
        (mappedObj_naturality η s hs) (mappedObj_naturality η t ht) where
  app j := (η.app j).map (s j) (t j)
  naturality := by
    intro j k α
    change castMap (F.map α) (s j) (t j) (s k) (t k)
        (hs α) (ht α) ≫
          castMap (η.app k) (s k) (t k)
            (mappedObj η s k) (mappedObj η t k) rfl rfl =
      castMap (η.app j) (s j) (t j)
          (mappedObj η s j) (mappedObj η t j) rfl rfl ≫
        castMap (G.map α) (mappedObj η s j) (mappedObj η t j)
          (mappedObj η s k) (mappedObj η t k)
          (mappedObj_naturality η s hs α)
          (mappedObj_naturality η t ht α)
    rw [← castMap_comp, ← castMap_comp]
    exact castMap_congr (η.naturality α) (s j) (t j)
      (mappedObj η s k) (mappedObj η t k) _ _ _ _

omit [IsFiltered J] in
/-- The actual final target endpoint is the image under the comparison
of the actual final source endpoint. -/
private theorem mapped_endpoint
    {c : Cocone F} {d : Cocone G} (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (s : ∀ j, (F.obj j).Obj) (x : c.pt.Obj)
    (hx : ∀ j, (c.ι.app j).obj (s j) = x) (j : J) :
    (d.ι.app j).obj (mappedObj η s j) = g.obj x := by
  have h := congrArg (fun f : F.obj j ⟶ d.pt ↦ f.obj (s j)) (hlegs j)
  change g.obj ((c.ι.app j).obj (s j)) =
    (d.ι.app j).obj ((η.app j).obj (s j)) at h
  exact h.symm.trans (congrArg g.obj (hx j))

omit [IsFiltered J] in
/-- The literal Hom comparison at the colimit is induced by the moving
Hom comparisons. The proof uses composition of both endpoint transports. -/
private theorem movingHomComparison_leg
    {c : Cocone F} {d : Cocone G} (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (s t : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)
    (x y : c.pt.Obj)
    (hx : ∀ j, (c.ι.app j).obj (s j) = x)
    (hy : ∀ j, (c.ι.app j).obj (t j) = y) (j : J) :
    (homCocone F s t hs ht c x y hx hy).ι.app j ≫ g.map x y =
      (movingHomComparison η s t hs ht).app j ≫
        (homCocone G (mappedObj η s) (mappedObj η t)
          (mappedObj_naturality η s hs) (mappedObj_naturality η t ht)
          d (g.obj x) (g.obj y)
          (mapped_endpoint η g hlegs s x hx)
          (mapped_endpoint η g hlegs t y hy)).ι.app j := by
  rw [show g.map x y = castMap g x y (g.obj x) (g.obj y) rfl rfl from by
    simp [castMap]]
  change castMap (c.ι.app j) (s j) (t j) x y (hx j) (hy j) ≫
      castMap g x y (g.obj x) (g.obj y) rfl rfl =
    castMap (η.app j) (s j) (t j) (mappedObj η s j) (mappedObj η t j) rfl rfl ≫
      castMap (d.ι.app j) (mappedObj η s j) (mappedObj η t j)
        (g.obj x) (g.obj y)
        (mapped_endpoint η g hlegs s x hx j)
        (mapped_endpoint η g hlegs t y hy j)
  rw [← castMap_comp, ← castMap_comp]
  exact castMap_congr (hlegs j) (s j) (t j) (g.obj x) (g.obj y) _ _ _ _

omit [IsFiltered J] in
/-- A source Hom transition monomorphism stays monic after the actual
moving-endpoint casts. -/
private theorem movingHomMap_mono
    (s t : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)
    (hmono : ∀ {j k : J} (α : j ⟶ k) (a b : (F.obj j).Obj),
      Mono ((F.map α).map a b))
    {j k : J} (α : j ⟶ k) :
    Mono ((homDiagram F s t hs ht).map α) := by
  dsimp [homDiagram, homMap, castMap,
    OriginalOrdinaryEndpointTransport.transport]
  letI : Mono ((F.map α).map (s j) (t j)) := hmono α (s j) (t j)
  exact mono_comp _ _

/-- Stagewise local geometric equivalences yield a geometric equivalence
on one literal final Hom map, for any supplied compatible endpoint sections. -/
theorem filtered_local_of_sections
    {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d)
    (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (s t : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)
    (x y : c.pt.Obj)
    (hx : ∀ j, (c.ι.app j).obj (s j) = x)
    (hy : ∀ j, (c.ι.app j).obj (t j) = y)
    (hmonoF : ∀ {j k : J} (α : j ⟶ k) (a b : (F.obj j).Obj),
      Mono ((F.map α).map a b))
    (hmonoG : ∀ {j k : J} (α : j ⟶ k) (a b : (G.obj j).Obj),
      Mono ((G.map α).map a b))
    (hlocal : ∀ j : J, DaggerOrdinaryRigidificationCof.geometric
      ((η.app j).map (s j) (t j))) :
    DaggerOrdinaryRigidificationCof.geometric (g.map x y) := by
  let sG := mappedObj η s
  let tG := mappedObj η t
  let hsG : ∀ {j k : J} (α : j ⟶ k),
      (G.map α).obj (sG j) = sG k :=
    fun {_ _} α ↦ mappedObj_naturality η s hs α
  let htG : ∀ {j k : J} (α : j ⟶ k),
      (G.map α).obj (tG j) = tG k :=
    fun {_ _} α ↦ mappedObj_naturality η t ht α
  let hxG := mapped_endpoint η g hlegs s x hx
  let hyG := mapped_endpoint η g hlegs t y hy
  let cHom := homCocone F s t hs ht c x y hx hy
  let dHom := homCocone G sG tG hsG htG d (g.obj x) (g.obj y) hxG hyG
  have hcHom : IsColimit cHom := homIsColimit hc s t hs ht x y hx hy
  have hdHom : IsColimit dHom := homIsColimit hd sG tG hsG htG
    (g.obj x) (g.obj y) hxG hyG
  let μ := movingHomComparison η s t hs ht
  apply DaggerGeometricFilteredColimits.geometric_of_filtered_mono
    hcHom hdHom
    (fun α ↦ movingHomMap_mono s t hs ht hmonoF α)
    (fun α ↦ movingHomMap_mono sG tG hsG htG hmonoG α)
    μ (g.map x y) (movingHomComparison_leg η g hlegs s t hs ht x y hx hy) ?_
  intro j
  exact hlocal j

/-- A filtered colimit comparison is locally geometric on every pair of
objects of its actual source vertex. The endpoint sections used by the Hom
colimit theorem are formed after restricting to the final category under a
common stage representing both objects. -/
theorem filtered_local_of_colimits
    {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d)
    (g : c.pt ⟶ d.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ d.ι.app j)
    (hmonoF : ∀ {j k : J} (α : j ⟶ k) (a b : (F.obj j).Obj),
      Mono ((F.map α).map a b))
    (hmonoG : ∀ {j k : J} (α : j ⟶ k) (a b : (G.obj j).Obj),
      Mono ((G.map α).map a b))
    (hlocal : ∀ j : J, ∀ a b : (F.obj j).Obj,
      DaggerOrdinaryRigidificationCof.geometric ((η.app j).map a b))
    (x y : c.pt.Obj) :
    DaggerOrdinaryRigidificationCof.geometric (g.map x y) := by
  obtain ⟨jx, a, ha⟩ := object_jointly_surjective hc x
  obtain ⟨jy, b, hb⟩ := object_jointly_surjective hc y
  let j0 := IsFiltered.max jx jy
  let ux : jx ⟶ j0 := IsFiltered.leftToMax jx jy
  let uy : jy ⟶ j0 := IsFiltered.rightToMax jx jy
  let a0 : (F.obj j0).Obj := (F.map ux).obj a
  let b0 : (F.obj j0).Obj := (F.map uy).obj b
  have ha0 : (c.ι.app j0).obj a0 = x := by
    have h := congrArg (fun f : F.obj jx ⟶ c.pt ↦ f.obj a) (c.w ux)
    change (c.ι.app j0).obj ((F.map ux).obj a) =
      (c.ι.app jx).obj a at h
    exact h.trans ha
  have hb0 : (c.ι.app j0).obj b0 = y := by
    have h := congrArg (fun f : F.obj jy ⟶ c.pt ↦ f.obj b) (c.w uy)
    change (c.ι.app j0).obj ((F.map uy).obj b) =
      (c.ι.app jy).obj b at h
    exact h.trans hb
  let U : Under j0 ⥤ J := Under.forget j0
  let F' : Under j0 ⥤ SimplicialCat.{u, u} := U ⋙ F
  let G' : Under j0 ⥤ SimplicialCat.{u, u} := U ⋙ G
  let η' : F' ⟶ G' := Functor.whiskerLeft U η
  let c' : Cocone F' := c.whisker U
  let d' : Cocone G' := d.whisker U
  have hc' : IsColimit c' :=
    ((Functor.Final.isColimitWhiskerEquiv U c).symm hc)
  have hd' : IsColimit d' :=
    ((Functor.Final.isColimitWhiskerEquiv U d).symm hd)
  let s : ∀ k : Under j0, (F'.obj k).Obj :=
    fun k ↦ (F.map k.hom).obj a0
  let t : ∀ k : Under j0, (F'.obj k).Obj :=
    fun k ↦ (F.map k.hom).obj b0
  have hs : ∀ {k l : Under j0} (α : k ⟶ l),
      (F'.map α).obj (s k) = s l := by
    intro k l α
    change (F.map α.right).obj ((F.map k.hom).obj a0) =
      (F.map l.hom).obj a0
    rw [← SimplicialCat.comp_obj, ← F.map_comp, Under.w α]
  have ht : ∀ {k l : Under j0} (α : k ⟶ l),
      (F'.map α).obj (t k) = t l := by
    intro k l α
    change (F.map α.right).obj ((F.map k.hom).obj b0) =
      (F.map l.hom).obj b0
    rw [← SimplicialCat.comp_obj, ← F.map_comp, Under.w α]
  have hx : ∀ k : Under j0, (c'.ι.app k).obj (s k) = x := by
    intro k
    have h := congrArg (fun f : F.obj j0 ⟶ c.pt ↦ f.obj a0) (c.w k.hom)
    change (c.ι.app k.right).obj ((F.map k.hom).obj a0) =
      (c.ι.app j0).obj a0 at h
    exact h.trans ha0
  have hy : ∀ k : Under j0, (c'.ι.app k).obj (t k) = y := by
    intro k
    have h := congrArg (fun f : F.obj j0 ⟶ c.pt ↦ f.obj b0) (c.w k.hom)
    change (c.ι.app k.right).obj ((F.map k.hom).obj b0) =
      (c.ι.app j0).obj b0 at h
    exact h.trans hb0
  have hlegs' : ∀ k : Under j0,
      c'.ι.app k ≫ g = η'.app k ≫ d'.ι.app k := by
    intro k
    exact hlegs k.right
  have hmonoF' : ∀ {k l : Under j0} (α : k ⟶ l)
      (p q : (F'.obj k).Obj), Mono ((F'.map α).map p q) := by
    intro k l α p q
    exact hmonoF α.right p q
  have hmonoG' : ∀ {k l : Under j0} (α : k ⟶ l)
      (p q : (G'.obj k).Obj), Mono ((G'.map α).map p q) := by
    intro k l α p q
    exact hmonoG α.right p q
  exact filtered_local_of_sections η' hc' hd' g hlegs' s t hs ht x y hx hy
    hmonoF' hmonoG' (fun k ↦ hlocal k.right (s k) (t k))

end

end DaggerModels.OrdinaryFilteredLocalComparison
