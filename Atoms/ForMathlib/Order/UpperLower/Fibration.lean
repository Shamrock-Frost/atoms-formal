import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.UpperLower.Fibration

open Set

namespace Relation

variable {α β : Type*} [Preorder α] [Preorder β] {f : α → β}

theorem Fibration.image_lowerClosure (hf : Fibration (· ≤ ·) (· ≤ ·) f) (hm : Monotone f)
    (s : Set α) : f '' lowerClosure s = lowerClosure (f '' s) := by
  ext y
  simp only [mem_image, SetLike.mem_coe, mem_lowerClosure, exists_exists_and_eq_and]
  constructor
  · rintro ⟨x, ⟨z, hz, hxz⟩, rfl⟩
    exact ⟨z, hz, hm hxz⟩
  · rintro ⟨z, hz, hyz⟩
    obtain ⟨x, hxz, rfl⟩ := hf hyz
    exact ⟨x, ⟨z, hz, hxz⟩, rfl⟩

end Relation
