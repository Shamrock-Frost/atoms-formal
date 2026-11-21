import Mathlib.Data.FinEnum
import Mathlib.Data.List.Sigma

namespace FinEnum

variable {α : Type*}

theorem toList_ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs)
    (h' : xs.Nodup) : @toList α (ofNodupList xs h h') = xs := by
  let _ := ofNodupList xs h h'
  have hl : (toList α).length = xs.length := by
    rw [toList, List.length_map, List.length_finRange]
    rfl
  refine List.ext_getElem hl fun i _ _ => ?_
  simp only [toList, List.getElem_map, List.getElem_finRange]
  rfl

theorem toList_ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) :
    @toList α (ofList xs h) = xs.dedup :=
  toList_ofNodupList _ _ _

@[simp] theorem toList_fin (n : ℕ) : toList (Fin n) = List.finRange n :=
  (toList_ofList _ _).trans (List.nodup_finRange n).dedup

theorem toList_sigma {β : α → Type*} [FinEnum α] [∀ a, FinEnum (β a)] :
    toList (Sigma β) = (toList α).sigma fun a => toList (β a) :=
  (toList_ofList _ _).trans (nodup_toList.sigma fun _ => nodup_toList).dedup

theorem filter_toList_sigma {β : α → Type*} [FinEnum α] [∀ a, FinEnum (β a)] (a : α) :
    (toList (Sigma β)).filter (fun x => decide (x.1 = a)) = (toList (β a)).map (Sigma.mk a) := by
  rw [toList_sigma]
  have key : ∀ l : List α, l.Nodup →
      (l.sigma fun a => toList (β a)).filter (fun x => decide (x.1 = a)) =
        if a ∈ l then (toList (β a)).map (Sigma.mk a) else [] := by
    intro l hl
    induction l with
    | nil => simp [List.sigma]
    | cons b l ih =>
        rw [List.nodup_cons] at hl
        simp only [List.sigma, List.flatMap_cons, List.filter_append] at ih ⊢
        rw [ih hl.2]
        by_cases hb : b = a
        · subst hb
          simp [List.filter_map, Function.comp_def, hl.1]
        · simp [List.filter_map, Function.comp_def, hb, Ne.symm hb]
  rw [key _ nodup_toList, if_pos (mem_toList a)]

end FinEnum
