import Mathlib.Order.Fin.Basic

namespace Fin

theorem exists_surjective_orderHom_castAdd_natAdd {k r n : ℕ} (hk : k ≤ n) {τ : Fin r → Fin n}
    (hτ : Monotone τ) (hle : ∀ a i, castLE hk a ≤ τ i)
    (hval : ∀ j : Fin n, k ≤ j.val → ∃ i, τ i = j) :
    ∃ σ : Fin (k + r) →o Fin n, Function.Surjective σ ∧
      (∀ a, σ (castAdd r a) = castLE hk a) ∧ ∀ i, σ (natAdd k i) = τ i := by
  refine ⟨⟨addCases (castLE hk) τ, fun a a' h => ?_⟩, fun j => ?_,
    fun a => addCases_left (motive := fun _ => Fin n) (right := τ) a,
    fun i => addCases_right (motive := fun _ => Fin n) (left := castLE hk) i⟩
  · induction a using addCases with
    | left a =>
      induction a' using addCases with
      | left a' =>
        simp only [addCases_left]
        exact le_iff_val_le_val.2 (le_iff_val_le_val.1 h)
      | right i' => simpa only [addCases_left, addCases_right] using hle a i'
    | right i =>
      induction a' using addCases with
      | left a' =>
        have := le_iff_val_le_val.1 h
        simp only [val_natAdd, val_castAdd] at this
        omega
      | right i' =>
        simpa only [addCases_right] using hτ ((natAdd_le_natAdd_iff k).1 h)
  · by_cases hj : j.val < k
    · exact ⟨castAdd r ⟨j, hj⟩,
        (addCases_left (motive := fun _ => Fin n) (right := τ) _).trans (Fin.ext rfl)⟩
    · obtain ⟨i, rfl⟩ := hval j (Nat.le_of_not_lt hj)
      exact ⟨natAdd k i, addCases_right (motive := fun _ => Fin n) (left := castLE hk) i⟩

end Fin
