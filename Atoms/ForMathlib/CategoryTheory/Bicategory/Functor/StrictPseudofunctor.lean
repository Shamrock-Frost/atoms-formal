import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

theorem PrelaxFunctor.ext_of_heq {F G : PrelaxFunctor B C} (h_obj : ∀ a, F.obj a = G.obj a)
    (h_map : ∀ {a b : B} (f : a ⟶ b), F.map f ≍ G.map f)
    (h_map₂ : ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g), F.map₂ η ≍ G.map₂ η) : F = G := by
  obtain ⟨⟨⟨Fobj, Fmap⟩, Fmap₂⟩, _, _⟩ := F
  obtain ⟨⟨⟨Gobj, Gmap⟩, Gmap₂⟩, _, _⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  obtain rfl : @Fmap = @Gmap := by
    funext a b f
    exact eq_of_heq (h_map f)
  obtain rfl : @Fmap₂ = @Gmap₂ := by
    funext a b f g η
    exact eq_of_heq (h_map₂ η)
  rfl

theorem StrictPseudofunctor.ext_of_heq {F G : StrictPseudofunctor B C}
    (h_obj : ∀ a, F.obj a = G.obj a) (h_map : ∀ {a b : B} (f : a ⟶ b), F.map f ≍ G.map f)
    (h_map₂ : ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g), F.map₂ η ≍ G.map₂ η) : F = G := by
  have h : F.toPrelaxFunctor = G.toPrelaxFunctor := PrelaxFunctor.ext_of_heq h_obj h_map h_map₂
  obtain ⟨⟨⟨F₀, FmapId, FmapComp, _, _, _, _, _⟩, Fmap_id, FmapId_eq⟩, Fmap_comp, FmapComp_eq⟩ := F
  obtain ⟨⟨⟨G₀, GmapId, GmapComp, _, _, _, _, _⟩, Gmap_id, GmapId_eq⟩, Gmap_comp, GmapComp_eq⟩ := G
  obtain rfl : F₀ = G₀ := h
  obtain rfl : FmapId = GmapId := by
    funext a
    exact (FmapId_eq a).trans (GmapId_eq a).symm
  obtain rfl : @FmapComp = @GmapComp := by
    funext a b c f g
    exact (FmapComp_eq f g).trans (GmapComp_eq f g).symm
  rfl

end CategoryTheory
