import Init.Data.Char.Basic

namespace Char

theorem isWhitespace_eq_false_of_isDigit {c : Char} (h : c.isDigit = true) :
    c.isWhitespace = false := by
  have key : ∀ x : Char, x.isWhitespace = true → x.isDigit = false := by
    intro x hx
    simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with ((rfl | rfl) | rfl) | rfl <;> rfl
  cases hw : c.isWhitespace
  · rfl
  · rw [key c hw] at h
    exact absurd h (by decide)

end Char
