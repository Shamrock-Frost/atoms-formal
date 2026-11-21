import Mathlib.Data.Fin.SuccPred

namespace Fin

theorem val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.castSucc < p
  · rw [succAbove_of_castSucc_lt _ _ h, if_pos (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 h), if_neg (by simpa [Fin.lt_def] using h)]
    rfl

theorem val_predAbove {m : ℕ} (p : Fin m) (i : Fin (m + 1)) :
    (p.predAbove i).val = if i.val ≤ p.val then i.val else i.val - 1 := by
  by_cases h : i ≤ p.castSucc
  · rw [predAbove_of_le_castSucc _ _ h, if_pos (by simpa [Fin.le_def] using h)]
    rfl
  · rw [predAbove_of_castSucc_lt _ _ (Fin.not_le.1 h), if_neg (by simpa [Fin.le_def] using h)]
    rfl

end Fin
