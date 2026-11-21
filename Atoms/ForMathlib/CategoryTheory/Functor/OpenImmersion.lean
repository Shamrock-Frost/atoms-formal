import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

structure IsOpenImmersion {U : Type u₁} [Category.{v₁} U] {X : Type u₂} [Category.{v₂} X]
    (j : U ⥤ X) : Prop where
  full : j.Full
  faithful : j.Faithful
  injective_obj : Function.Injective j.obj
  mem_range_of_hom {x : X} {u : U} : (x ⟶ j.obj u) → x ∈ Set.range j.obj

namespace IsOpenImmersion

variable {U : Type u₁} [Category.{v₁} U] {X : Type u₂} [Category.{v₂} X] {C : Type u₃}
  [Category.{v₃} C] {j : U ⥤ X}

theorem mem_range_of_hom_obj (hj : j.IsOpenImmersion) {x y : X} (f : x ⟶ y)
    (hy : y ∈ Set.range j.obj) : x ∈ Set.range j.obj :=
  hj.mem_range_of_hom (f ≫ eqToHom hy.choose_spec.symm)

private theorem choose_eq (hj : j.IsOpenImmersion) {x : X} (hx : x ∈ Set.range j.obj) {v : U}
    (hv : j.obj v = x) : hx.choose = v :=
  hj.injective_obj (hx.choose_spec.trans hv.symm)

open scoped Classical in
private noncomputable def extendObj (j : U ⥤ X) (u : U ⥤ C) (t : C) (x : X) : C :=
  if h : x ∈ Set.range j.obj then u.obj h.choose else t

private theorem extendObj_eq (hj : j.IsOpenImmersion) (u : U ⥤ C) (t : C) {x : X} {v : U}
    (hv : j.obj v = x) : extendObj j u t x = u.obj v :=
  (dif_pos ⟨v, hv⟩).trans (congrArg u.obj (hj.choose_eq ⟨v, hv⟩ hv))

private theorem extendObj_of_notMem (u : U ⥤ C) (t : C) {x : X} (hx : x ∉ Set.range j.obj) :
    extendObj j u t x = t :=
  dif_neg hx

open scoped Classical in
private noncomputable def extendMap (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C}
    (ht : IsTerminal t) {x y : X} (f : x ⟶ y) : extendObj j u t x ⟶ extendObj j u t y :=
  haveI := hj.full
  if hy : y ∈ Set.range j.obj then
    eqToHom (hj.extendObj_eq u t (hj.mem_range_of_hom_obj f hy).choose_spec) ≫
      u.map (j.preimage (eqToHom (hj.mem_range_of_hom_obj f hy).choose_spec ≫ f ≫
        eqToHom hy.choose_spec.symm)) ≫ eqToHom (hj.extendObj_eq u t hy.choose_spec).symm
  else ht.from _ ≫ eqToHom (extendObj_of_notMem u t hy).symm

private theorem extendMap_congr (hj : j.IsOpenImmersion) (u : U ⥤ C) (t : C) [j.Full]
    {x y : X} (f : x ⟶ y) {v v' w w' : U} (ev : v = v') (ew : w = w') (hv : j.obj v = x)
    (hw : j.obj w = y) (hv' : j.obj v' = x) (hw' : j.obj w' = y) :
    eqToHom (hj.extendObj_eq u t hv) ≫ u.map (j.preimage (eqToHom hv ≫ f ≫
      eqToHom hw.symm)) ≫ eqToHom (hj.extendObj_eq u t hw).symm =
    eqToHom (hj.extendObj_eq u t hv') ≫ u.map (j.preimage (eqToHom hv' ≫ f ≫
      eqToHom hw'.symm)) ≫ eqToHom (hj.extendObj_eq u t hw').symm := by
  subst ev ew
  rfl

private theorem extendMap_of_eq (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C}
    (ht : IsTerminal t) [j.Full] {x y : X} (f : x ⟶ y) {v w : U} (hv : j.obj v = x)
    (hw : j.obj w = y) :
    hj.extendMap u ht f = eqToHom (hj.extendObj_eq u t hv) ≫
      u.map (j.preimage (eqToHom hv ≫ f ≫ eqToHom hw.symm)) ≫
        eqToHom (hj.extendObj_eq u t hw).symm := by
  rw [extendMap, dif_pos ⟨w, hw⟩]
  exact hj.extendMap_congr u t f (hj.choose_eq _ hv) (hj.choose_eq _ hw)
    (hj.mem_range_of_hom_obj f ⟨w, hw⟩).choose_spec (⟨w, hw⟩ : y ∈ Set.range j.obj).choose_spec
    hv hw

private theorem hom_ext_of_notMem (u : U ⥤ C) {t : C} (ht : IsTerminal t) {c : C} {y : X}
    (hy : y ∉ Set.range j.obj) (f g : c ⟶ extendObj j u t y) : f = g := by
  rw [← cancel_mono (eqToHom (extendObj_of_notMem u t hy))]
  exact ht.hom_ext _ _

noncomputable def extend (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C} (ht : IsTerminal t) :
    X ⥤ C where
  obj := extendObj j u t
  map := hj.extendMap u ht
  map_id x := by
    have := hj.full
    have := hj.faithful
    by_cases hx : x ∈ Set.range j.obj
    · rw [hj.extendMap_of_eq u ht _ hx.choose_spec hx.choose_spec]
      simp
    · exact hom_ext_of_notMem u ht hx _ _
  map_comp {x y z} f g := by
    have := hj.full
    have := hj.faithful
    by_cases hz : z ∈ Set.range j.obj
    · have hy := hj.mem_range_of_hom_obj g hz
      have hx := hj.mem_range_of_hom_obj f hy
      rw [hj.extendMap_of_eq u ht _ hx.choose_spec hz.choose_spec,
        hj.extendMap_of_eq u ht _ hx.choose_spec hy.choose_spec,
        hj.extendMap_of_eq u ht _ hy.choose_spec hz.choose_spec]
      have : j.preimage (eqToHom hx.choose_spec ≫ (f ≫ g) ≫ eqToHom hz.choose_spec.symm) =
          j.preimage (eqToHom hx.choose_spec ≫ f ≫ eqToHom hy.choose_spec.symm) ≫
            j.preimage (eqToHom hy.choose_spec ≫ g ≫ eqToHom hz.choose_spec.symm) :=
        j.map_injective (by simp)
      rw [this, u.map_comp]
      simp
    · exact hom_ext_of_notMem u ht hz _ _

theorem comp_extend (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C} (ht : IsTerminal t) :
    j ⋙ hj.extend u ht = u := by
  have := hj.full
  have := hj.faithful
  refine Functor.ext (fun v => hj.extendObj_eq u t rfl) fun v w g => ?_
  change hj.extendMap u ht (j.map g) = _
  rw [hj.extendMap_of_eq u ht _ rfl rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.preimage_map]
  rfl

theorem extend_obj_of_notMem (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C} (ht : IsTerminal t)
    {x : X} (hx : x ∉ Set.range j.obj) : (hj.extend u ht).obj x = t :=
  extendObj_of_notMem u t hx

theorem eq_extend (hj : j.IsOpenImmersion) (u : U ⥤ C) {t : C} (ht : IsTerminal t)
    (F : X ⥤ C) (h₁ : j ⋙ F = u) (h₂ : ∀ x ∉ Set.range j.obj, F.obj x = t) :
    F = hj.extend u ht := by
  have := hj.full
  have hobj : ∀ x, F.obj x = (hj.extend u ht).obj x := fun x => by
    by_cases hx : x ∈ Set.range j.obj
    · obtain ⟨v, rfl⟩ := hx
      exact (Functor.congr_obj h₁ v).trans (Functor.congr_obj (hj.comp_extend u ht) v).symm
    · rw [h₂ x hx, hj.extend_obj_of_notMem u ht hx]
  refine Functor.ext hobj fun x y f => ?_
  by_cases hy : y ∈ Set.range j.obj
  · obtain ⟨w, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := hj.mem_range_of_hom f
    obtain ⟨g, rfl⟩ := j.map_surjective f
    have e₁ := Functor.congr_hom h₁ g
    have e₂ := Functor.congr_hom (hj.comp_extend u ht) g
    simp only [Functor.comp_map] at e₁ e₂
    rw [e₁, e₂]
    simp
  · rw [← cancel_mono (eqToHom (h₂ y hy))]
    exact ht.hom_ext _ _

end IsOpenImmersion

end CategoryTheory.Functor
