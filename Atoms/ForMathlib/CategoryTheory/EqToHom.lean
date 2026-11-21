import Mathlib.CategoryTheory.EqToHom

universe v₁ v₂ u₁ u₂

theorem Prefunctor.hext {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]
    {F G : Prefunctor V W} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G := by
  obtain ⟨Fo, Fm⟩ := F
  obtain ⟨Go, Gm⟩ := G
  obtain rfl : Fo = Go := funext h_obj
  congr
  funext X Y f
  exact eq_of_heq (h_map X Y f)

namespace CategoryTheory

theorem eqToHom_comp_comp_eqToHom_eq {D : Type u₂} [Category.{v₂} D]
    {x x' x'' y y' y'' : D} (M : x'' ⟶ y'') (a : x = x') (b : x' = x'') (c : y'' = y')
    (d : y' = y) (e : x = x'') (e' : y'' = y) :
    eqToHom a ≫ (eqToHom b ≫ M ≫ eqToHom c) ≫ eqToHom d = eqToHom e ≫ M ≫ eqToHom e' := by
  subst a b c d
  simp

theorem eq_eqToHom_conj_conj {C : Type u₁} [Category.{v₁} C] {X X' Y Y' : C} (h : X = X')
    (h' : X' = X) (φ : X ⟶ Y) (k : Y = Y') (k' : Y' = Y) :
    φ = eqToHom h ≫ (eqToHom h' ≫ φ ≫ eqToHom k) ≫ eqToHom k' := by
  subst h k
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def ConjEqToHom {C : Type u₁} [Category.{v₁} C] {X Y X' Y' : C} (φ : X ⟶ Y) (ψ : X' ⟶ Y') :
    Prop :=
  ∃ (e : X = X') (e' : Y' = Y), φ = eqToHom e ≫ ψ ≫ eqToHom e'

theorem eqToHom_comp_comp_eqToHom_comp_comp_eqToHom {C : Type u₁} [Category.{v₁} C] {a b c : C}
    (p : a = a) (q : b = b) (r : c = c) (f : a ⟶ b) (g : b ⟶ c) :
    eqToHom p ≫ f ≫ eqToHom q ≫ g ≫ eqToHom r = f ≫ g := by
  simp

namespace ConjEqToHom

variable {C : Type u₁} [Category.{v₁} C]

theorem comp {X Y Z X' Y' Z' : C} {φ : X ⟶ Y} {φ' : Y ⟶ Z} {ψ : X' ⟶ Y'} {ψ' : Y' ⟶ Z'}
    (h : ConjEqToHom φ ψ) (h' : ConjEqToHom φ' ψ') : ConjEqToHom (φ ≫ φ') (ψ ≫ ψ') := by
  obtain ⟨e, e₁, rfl⟩ := h
  obtain ⟨e₂, e', rfl⟩ := h'
  refine ⟨e, e', ?_⟩
  subst e₁
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]

theorem eq {X Y X' Y' : C} {φ φ' : X ⟶ Y} {ψ : X' ⟶ Y'} (h : ConjEqToHom φ ψ)
    (h' : ConjEqToHom φ' ψ) : φ = φ' := by
  obtain ⟨e, e', rfl⟩ := h
  obtain ⟨-, -, rfl⟩ := h'
  rfl

theorem eq_of_eq {X Y X' Y' : C} {φ φ' : X ⟶ Y} {ψ ψ' : X' ⟶ Y'} (h : ConjEqToHom φ ψ)
    (h' : ConjEqToHom φ' ψ') (hψ : ψ = ψ') : φ = φ' :=
  h.eq (hψ ▸ h')

theorem conj {X Y X' Y' X₀ Y₀ X₁ Y₁ : C} {φ : X ⟶ Y} {ψ : X' ⟶ Y'} (h : ConjEqToHom φ ψ)
    (a : X₀ = X) (b : Y = Y₀) (c : X₁ = X') (d : Y' = Y₁) :
    ConjEqToHom (eqToHom a ≫ φ ≫ eqToHom b) (eqToHom c ≫ ψ ≫ eqToHom d) := by
  obtain ⟨e, e', rfl⟩ := h
  refine ⟨a.trans (e.trans c.symm), (d.symm.trans (e'.trans b)), ?_⟩
  subst a b c d e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem trans {X Y X' Y' X'' Y'' : C} {φ : X ⟶ Y} {ψ : X' ⟶ Y'} {χ : X'' ⟶ Y''}
    (h : ConjEqToHom φ ψ) (h' : ConjEqToHom ψ χ) : ConjEqToHom φ χ := by
  obtain ⟨e, e', rfl⟩ := h
  obtain ⟨e₂, e₂', rfl⟩ := h'
  refine ⟨e.trans e₂, e₂'.trans e', ?_⟩
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem symm {X Y X' Y' : C} {φ : X ⟶ Y} {ψ : X' ⟶ Y'} (h : ConjEqToHom φ ψ) :
    ConjEqToHom ψ φ := by
  obtain ⟨e, e', rfl⟩ := h
  refine ⟨e.symm, e'.symm, ?_⟩
  subst e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem heq {X Y X' Y' : C} {φ : X ⟶ Y} {ψ : X' ⟶ Y'} (h : ConjEqToHom φ ψ) : φ ≍ ψ := by
  obtain ⟨e, e', rfl⟩ := h
  subst e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, heq_eq_eq]

end ConjEqToHom

theorem conjEqToHom_id {C : Type u₁} [Category.{v₁} C] {X X' : C} (e : X = X') :
    ConjEqToHom (𝟙 X) (𝟙 X') :=
  ⟨e, e.symm, by
    subst e
    simp only [eqToHom_refl, Category.id_comp]⟩

theorem conjEqToHom_refl {C : Type u₁} [Category.{v₁} C] {X Y : C} (φ : X ⟶ Y) :
    ConjEqToHom φ φ :=
  ⟨rfl, rfl, by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]⟩

theorem comp_eqToHom_eq_eqToHom_comp {C : Type u₁} [Category.{v₁} C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (r : Y = Y') (s : X = X') (hf : ∃ p, f = eqToHom p)
    (hg : ∃ q, g = eqToHom q) : f ≫ eqToHom r = eqToHom s ≫ g := by
  obtain ⟨p, rfl⟩ := hf
  obtain ⟨q, rfl⟩ := hg
  simp

theorem eqToHom_comp_map_eqToHom_comp_id {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {W : D} {X Y : C} (p : W = F.obj X) (q : X = Y) :
    eqToHom p ≫ F.map (eqToHom q ≫ 𝟙 Y) = eqToHom (p.trans (congrArg F.obj q)) := by
  subst p q
  simp

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

theorem eqToHom_comp_map_eq_map_eqToHom_comp {x y z : C} (e : x = y) (f : y ⟶ z)
    (e' : G.obj x = G.obj y) (h₁ : G.obj x = G.obj x) (h₂ : G.obj z = G.obj z) :
    eqToHom e' ≫ G.map f = eqToHom h₁ ≫ G.map (eqToHom e ≫ f) ≫ eqToHom h₂ := by
  subst e
  simp

theorem map_eqToHom_comp_eq {x y z : C} (e : x = y) (f : y ⟶ z) (h₁ : G.obj x = G.obj y)
    (h₂ : G.obj z = G.obj z) :
    G.map (eqToHom e ≫ f) = eqToHom h₁ ≫ G.map f ≫ eqToHom h₂ := by
  subst e
  simp

end Functor

end CategoryTheory
