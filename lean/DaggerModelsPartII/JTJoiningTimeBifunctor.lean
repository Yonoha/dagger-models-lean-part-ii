import DaggerModelsPartII.JTHigherGraphTimeFamily

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTJoiningTimeBifunctor

open JTHigherInterleavedParameter (mapTime mapTime_vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv mapCopies mapCopies_vertex)

noncomputable section

private abbrev inc := SemiSimplexCategory.toSimplexCategory

private theorem injective {i j : SemiSimplexCategory} (a : i ⟶ j) :
    Function.Injective (inc.map a).toOrderHom :=
  (SemiSimplexCategory.homEquiv a).injective

/-- A proper phase face and an arbitrary time operator act on the original
lexicographic common time in their respective coordinates. -/
def joiningTime : SemiSimplexCategory × SimplexCategory ⥤ SimplexCategory where
  obj p := JTHigherInterleavedParameter.common (inc.obj p.1) p.2
  map {p q} f := mapTime (inc.obj p.1) f.2 ≫
    mapCopies (inc.map f.1) (injective f.1) q.2
  map_id p := by
    change mapTime (inc.obj p.1) (𝟙 p.2) ≫
      mapCopies (inc.map (𝟙 p.1)) (injective (𝟙 p.1)) p.2 = 𝟙 _
    rw [JTHigherInterleavedParameter.mapTime_id, Category.id_comp]
    simp only [inc.map_id]
    ext v : 3
    obtain ⟨x, rfl⟩ := (timeVertexEquiv p.1.len p.2).surjective v
    rw [mapCopies_vertex]
    rfl
  map_comp {p q r} f g := by
    change mapTime (inc.obj p.1) (f.2 ≫ g.2) ≫
        mapCopies (inc.map (f.1 ≫ g.1)) (injective (f.1 ≫ g.1)) r.2 =
      (mapTime (inc.obj p.1) f.2 ≫
        mapCopies (inc.map f.1) (injective f.1) q.2) ≫
        (mapTime (inc.obj q.1) g.2 ≫
          mapCopies (inc.map g.1) (injective g.1) r.2)
    have hc : mapCopies (inc.map (f.1 ≫ g.1)) (injective (f.1 ≫ g.1)) r.2 =
        mapCopies (inc.map f.1) (injective f.1) r.2 ≫
          mapCopies (inc.map g.1) (injective g.1) r.2 := by
      rw [← JTFiniteCoefficientBridgeTime.mapCopies_comp]
      simp only [inc.map_comp]
    rw [JTHigherInterleavedParameter.mapTime_comp, hc]
    have hcomm := JTHigherGraphTimeFamily.mapCopies_mapTime
      (inc.map f.1) (injective f.1) g.2
    have he := congrArg (fun t ↦
      mapTime (inc.obj p.1) f.2 ≫ t ≫
        mapCopies (inc.map g.1) (injective g.1) r.2) hcomm
    simpa only [Category.assoc] using he.symm

/-- The map of the bifunctor is exactly time transport followed by all-copy
restriction along the injective phase face. -/
theorem joiningTime_obj (p : SemiSimplexCategory × SimplexCategory) :
    joiningTime.obj p = time p.1.len p.2 := rfl

theorem joiningTime_map {p q : SemiSimplexCategory × SimplexCategory} (f : p ⟶ q) :
    joiningTime.map f =
      mapTime (inc.obj p.1) f.2 ≫ mapCopies (inc.map f.1) (injective f.1) q.2 := rfl

end
end DaggerModels.PartII.JTJoiningTimeBifunctor
