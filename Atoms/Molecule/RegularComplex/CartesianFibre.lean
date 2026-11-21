import Atoms.Molecule.RegularComplex.CartesianAtom
import Atoms.Molecule.RegularComplex.Thin

universe u v

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}}

namespace IsMap

variable {f : P → Q} (hf : IsMap f)
include hf

theorem exists_mem_faces_apply_eq_of_lt {z : P} (hz : ∃ z' < z, f z' = f z) (α : Bool) :
    ∃ y ∈ P.faces α z, f y = f z :=
  let ⟨_, hz', he⟩ := hz
  hf.exists_mem_faces_apply_eq (hf.fibration.grade_apply_lt_of_lt hz' he) α

variable [hf.monotone.functor.IsFibered]

theorem exists_covBy_apply_eq_of_grade_add_lt (hthin : P.IsOrientedThin) {x y : P}
    (hxy : x ≤ y) (hd : grade ℕ (f y) + grade ℕ x < grade ℕ y + grade ℕ (f x)) :
    ∃ y', y' ⋖ y ∧ x ≤ y' ∧ f y' = f y := by
  obtain ⟨m, hm⟩ : ∃ m, grade ℕ y - grade ℕ x = m := ⟨_, rfl⟩
  induction m using Nat.strong_induction_on generalizing y with
  | _ m ih =>
    have hxy' : x < y := lt_of_le_of_ne hxy fun e => by
      subst e
      omega
    obtain ⟨y₁, hxy₁, hy₁y⟩ := exists_le_covBy_of_lt hxy'
    by_cases h₁ : f y₁ = f y
    · exact ⟨y₁, hy₁y, hxy₁, h₁⟩
    have hc₁ := hf.monotone.apply_covBy_apply hy₁y h₁
    have hdy := Nat.covBy_iff_add_one_eq.1 (hy₁y.grade ℕ)
    have hdfy := Nat.covBy_iff_add_one_eq.1 (hc₁.grade ℕ)
    have hdx := grade_mono (𝕆 := ℕ) hxy₁
    obtain ⟨y₂, hy₂y₁, hxy₂, hf₂⟩ := ih _ (by omega) hxy₁ (by omega) rfl
    have hdy₁ := Nat.covBy_iff_add_one_eq.1 (hy₂y₁.grade ℕ)
    obtain ⟨z₁, z₂, hz, hint, -⟩ := hthin.diamond y y₂ (hy₂y₁.lt.trans hy₁y.lt) (by omega)
    have hy₁I : y₁ ∈ Ioo y₂ y := ⟨hy₂y₁.lt, hy₁y.lt⟩
    obtain ⟨ys, hysI, hys⟩ : ∃ ys ∈ Ioo y₂ y, ys ≠ y₁ := by
      rw [hint] at hy₁I ⊢
      rcases hy₁I with e | e
      · exact ⟨z₂, Or.inr rfl, fun e' => hz (e.symm.trans e'.symm)⟩
      · rw [mem_singleton_iff] at e
        exact ⟨z₁, Or.inl rfl, fun e' => hz (e'.trans e)⟩
    obtain ⟨hy₂ys, hysy⟩ := hysI
    have hdys := grade_strictMono (𝕆 := ℕ) hy₂ys
    have hdys' := grade_strictMono (𝕆 := ℕ) hysy
    have hysc : ys ⋖ y := GradeOrder.covBy_of_le_of_grade_eq_add_one hysy.le (by omega)
    refine ⟨ys, hysc, hxy₂.trans hy₂ys.le, ?_⟩
    by_contra hne
    obtain ⟨w, hwy, hwe, hwmax⟩ :=
      hf.monotone.exists_lift (hf.monotone (hy₂y₁.le.trans hy₁y.le))
    have hy₁w : y₁ ≤ w := hwmax y₁ hy₁y.le hf₂.symm.le
    have hw : w = y₁ := by
      rcases hy₁y.eq_or_eq hy₁w hwy with e | e
      · exact e
      · exact absurd (by rw [← hwe, e]) fun h : f y₂ = f y => h₁ (hf₂.symm.trans h)
    have hlt : f y₂ < f ys := by
      refine lt_of_le_of_ne (hf.monotone hy₂ys.le) fun e => hys ?_
      have hle := hwmax ys hysy.le e.symm.le
      rw [hw] at hle
      exact GradeOrder.eq_of_le_of_grade_le hle (by omega)
    have hcs := hf.monotone.apply_covBy_apply hysc hne
    have h₁' := Nat.covBy_iff_add_one_eq.1 (hcs.grade ℕ)
    have h₂' := grade_strictMono (𝕆 := ℕ) hlt
    rw [hf₂] at h₂'
    omega

theorem exists_le_minimal_fibre_top (hthin : P.IsOrientedThin) {t : P} (ht : IsTop t) {x : P}
    (hmin : Minimal (fun w => f w = f x) x) :
    ∃ z, x ≤ z ∧ Minimal (fun w => f w = f t) z := by
  have hdx := (hf.minimal_fibre_iff x).1 hmin
  suffices ∀ m (z : P), grade ℕ z - grade ℕ (f t) = m → x ≤ z → f z = f t →
      ∃ z, x ≤ z ∧ Minimal (fun w => f w = f t) z from this _ t rfl (ht x) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro z hm hxz hzt
    by_cases hz : Minimal (fun w => f w = f t) z
    · exact ⟨z, hxz, hz⟩
    obtain ⟨z', hz'e, hz'z, hzz'⟩ := (not_minimal_iff (P := fun w => f w = f t) hzt).1 hz
    have hd := hf.fibration.grade_apply_lt_of_lt (lt_of_le_not_ge hz'z hzz') (hz'e.trans hzt.symm)
    obtain ⟨y', hy'z, hxy', hy'e⟩ :=
      hf.exists_covBy_apply_eq_of_grade_add_lt hthin hxz (by omega)
    have := Nat.covBy_iff_add_one_eq.1 (hy'z.grade ℕ)
    rw [hzt] at hd
    exact ih _ (by omega) y' rfl hxy' (hy'e.trans hzt)

end IsMap

theorem IsMap.eq_of_forall_minimal_fibre_top (hP : P.IsMolecule) {f f' : P → Q} (hf : IsMap f)
    [hf.monotone.functor.IsFibered] (hf' : IsMap f') [hf'.monotone.functor.IsFibered] {t : P}
    (ht : IsTop t) (h : ∀ z, Minimal (fun w => f w = f t) z → ∀ w ≤ z, f' w = f w) :
    f' = f := by
  have hthin := (isRDC_of_isMolecule hP).isOrientedThin
  funext z
  induction z using WellFoundedLT.induction with
  | _ z ih =>
    by_cases hz : Minimal (fun w => f w = f z) z
    · obtain ⟨z₀, hzz₀, hz₀⟩ := hf.exists_le_minimal_fibre_top hthin ht hz
      exact h z₀ hz₀ z hzz₀
    obtain ⟨z', hz'e, hz'z, hzz'⟩ := (not_minimal_iff (P := fun w => f w = f z) rfl).1 hz
    have hlt : ∃ z'' < z, f z'' = f z := ⟨z', lt_of_le_not_ge hz'z hzz', hz'e⟩
    obtain ⟨y₀, hy₀, he₀⟩ := hf.exists_mem_faces_apply_eq_of_lt hlt false
    obtain ⟨y₁, hy₁, he₁⟩ := hf.exists_mem_faces_apply_eq_of_lt hlt true
    have hne : y₀ ≠ y₁ := fun e =>
      Set.disjoint_left.1 (P.disjoint_faces z false) hy₀ (e ▸ hy₁)
    have h₀ := ih y₀ hy₀.1.lt
    have h₁ := ih y₁ hy₁.1.lt
    have hz' := hf'.monotone.apply_eq_of_minimal_upper_bound hy₀.1.le hy₁.1.le
      (fun _ hw₀ hw₁ hwz => hy₀.1.eq_of_le_of_le hy₁.1 hne hw₀ hw₁ hwz)
      (by rw [h₀, h₁, he₀, he₁])
    rw [hz', h₀, he₀]

end Atoms.Molecule.OGP
