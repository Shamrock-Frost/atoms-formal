import Mathlib.CategoryTheory.Comma.Arrow

namespace CategoryTheory.Arrow

variable {T : Type*} [Category* T]

theorem mk_comp_eq_mk_comp {a b c a' b' c' : T} {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'}
    {g' : b' ⟶ c'} (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨rfl, rfl, hf⟩ := (Arrow.mk_eq_mk_iff f f').1 hf
  obtain ⟨_, rfl, hg⟩ := (Arrow.mk_eq_mk_iff g g').1 hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [hf, hg]

theorem arrow_mk_eqToHom_eq {X Y X' Y' : T} (p : X = Y) (q : X' = Y') (hX : X = X') :
    Arrow.mk (eqToHom p) = Arrow.mk (eqToHom q) := by
  subst p q hX
  rfl

theorem exists_eq_eqToHom {X Y X' Y' : T} {f : X ⟶ Y} (p : X' = Y')
    (h : Arrow.mk f = Arrow.mk (eqToHom p)) : ∃ e : X = Y, f = eqToHom e := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
  exact ⟨hX.trans (p.trans hY.symm), hf.trans (by simp)⟩

end CategoryTheory.Arrow
