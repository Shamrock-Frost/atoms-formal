import Atoms.Molecule.Cylinder.StagedOver
import Atoms.Molecule.Interior

universe u

open Order

namespace Atoms.Molecule.OGP

section Round

variable {U : OGP.{u}} {A B : LowerSet U} {n : ℕ}

theorem IsRound.coe_boundaryFull_diff_interior_boundary (hr : U.IsRound A) (hA : IsMoleculeIn U A)
    {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim A) (α : Bool) :
    (U.boundaryFull A k : Set U) \ U.interior (U.boundary A k α) = U.boundary A k (!α) := by
  have hmeet := hr.inf_boundary_eq_properBoundary hA hk α
  ext x
  simp only [Set.mem_sdiff, SetLike.mem_coe, mem_boundaryFull, OGP.mem_interior, not_and,
    not_not]
  constructor
  · rintro ⟨⟨δ, hx⟩, hxi⟩
    rcases Bool.eq_or_eq_not δ α with rfl | rfl
    · exact (hmeet.ge (hxi hx)).2
    · exact hx
  · intro hx
    exact ⟨⟨!α, hx⟩, fun hx' => hmeet.le ⟨hx', hx⟩⟩

theorem mem_boundaryFull_iff_of_isPastingIn_cond (α : Bool) (hrA : U.IsRound A)
    (hrB : U.IsRound B) (hA : IsMoleculeIn U A) (hB : IsMoleculeIn U B)
    (hkA : (n : WithBot ℕ∞) < krullDim A) (hkB : (n : WithBot ℕ∞) < krullDim B)
    {W : LowerSet U} (hp : U.IsPastingIn n (cond α A B) (cond α B A) W) {x : U} (hx : x ∈ B) :
    x ∈ U.boundaryFull W n ↔ x ∈ U.boundary B n α := by
  obtain ⟨-, hiB, hiA⟩ := (isPastingIn_cond_iff α).1 hp
  have hp' : U.IsPastingIn n (cond (!α) B A) (cond (!α) A B) W := by
    rwa [Bool.cond_not, Bool.cond_not]
  rw [mem_boundaryFull]
  refine ⟨fun ⟨δ, hxδ⟩ => ?_, fun h => ⟨α, (hp.boundary_cond α).ge h⟩⟩
  rcases Bool.eq_or_eq_not δ α with rfl | rfl
  · exact (hp.boundary_cond δ).le hxδ
  have hxA : x ∈ U.boundary A n (!α) := (hp'.boundary_cond (!α)).le hxδ
  have hxAB : x ∈ A ⊓ B := ⟨boundary_le A n (!α) hxA, hx⟩
  have hpb : x ∈ U.properBoundary (U.boundary B n (!α)) := by
    rw [← hiB, hiA, ← hrA.inf_boundary_eq_properBoundary hA hkA α]
    exact ⟨hiA ▸ hxAB, hxA⟩
  rw [← hrB.inf_boundary_eq_properBoundary hB hkB (!α), Bool.not_not] at hpb
  exact hpb.2

end Round

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U}

theorem boundary_over_eq_copy_of_boundary_le {A : LowerSet U} (hg : U.IsGlobular A) {n : ℕ}
    {γ : Bool} (hK : U.boundary A n γ ≤ K) (β : Bool) :
    (partialCylinder U K).boundary (over K A) n β = copy K β (U.boundary A n β) := by
  rcases n with _ | m
  · exact boundary_over_zero A β
  · rw [boundary_over_succ hg, over_eq_copy_of_le
      ((hg.boundary_le_boundary (Nat.lt_succ_self m) (!β) γ).trans hK) β, ← copy_sup]
    exact congrArg _ (sup_eq_left.2 (hg.boundary_le_boundary (Nat.lt_succ_self m) (!β) β))

theorem isPastingIn_copy_over_cond (α : Bool) {A B W : LowerSet U} (hB : U.IsGlobular B)
    {n : ℕ} (hp : U.IsPastingIn n (cond α A B) (cond α B A) W) (hK : U.boundary B n α ≤ K) :
    (partialCylinder U K).IsPastingIn n (cond α (copy K (!α) A) (over K B))
      (cond α (over K B) (copy K (!α) A)) (copy K (!α) A ⊔ over K B) := by
  obtain ⟨-, hiB, hiA⟩ := (isPastingIn_cond_iff α).1 hp
  refine (isPastingIn_cond_iff α).2 ⟨rfl, ?_, ?_⟩
  · rw [copy_inf_over, boundary_over_eq_copy_of_boundary_le hB hK, hiB]
  · rw [copy_inf_over, boundary_copy, hiA]

variable {F G : LowerSet U} {n : ℕ}

theorem isPastingIn_copy_sup_over_over_sup_copy (hp : U.IsPastingIn n F G ⊤)
    (hF : IsMoleculeIn U F) (hG : IsMoleculeIn U G) (hdF : krullDim F ≤ (n + 1 : ℕ))
    (hdG : krullDim G ≤ (n + 1 : ℕ)) (hKF : U.boundary F n false ≤ K)
    (hKG : U.boundary G n true ≤ K) :
    (partialCylinder U K).IsPastingIn (n + 1) (copy K false F ⊔ over K G)
      (over K F ⊔ copy K true G) ⊤ := by
  have gF := hF.isGlobular
  have gG := hG.isGlobular
  have p₁ : (partialCylinder U K).IsPastingIn n (copy K false F) (over K G)
      (copy K false F ⊔ over K G) := isPastingIn_copy_over_cond true gG hp hKG
  have p₂ : (partialCylinder U K).IsPastingIn n (over K F) (copy K true G)
      (over K F ⊔ copy K true G) := by
    rw [sup_comm]; exact isPastingIn_copy_over_cond false gF hp hKF
  have gcF := (isMoleculeIn_copy (K := K) hF false).isGlobular
  have gcG := (isMoleculeIn_copy (K := K) hG true).isGlobular
  have goF := (isMoleculeIn_over (K := K) hF).isGlobular
  have goG := (isMoleculeIn_over (K := K) hG).isGlobular
  have b₁ := (p₁.boundary_of_lt gcF goG (Nat.lt_succ_self n) true).sup_eq
  have b₂ := (p₂.boundary_of_lt goF gcG (Nat.lt_succ_self n) false).sup_eq
  rw [boundary_copy, boundary_eq_self hdF, boundary_over_succ gG, boundary_eq_self hdG,
    Bool.not_true, ← hp.inf_eq_input] at b₁
  rw [boundary_copy, boundary_eq_self hdG, boundary_over_succ gF, boundary_eq_self hdF,
    Bool.not_false, ← hp.inf_eq_output] at b₂
  have hinf : (copy K false F ⊔ over K G) ⊓ (over K F ⊔ copy K true G) =
      copy K false F ⊔ (copy K true G ⊔ over K (F ⊓ G)) := by
    refine le_antisymm ?_ (sup_le (le_inf le_sup_left (le_sup_of_le_left (copy_le_over _ _)))
      (sup_le (le_inf (le_sup_of_le_right (copy_le_over _ _)) le_sup_right)
        (le_inf (le_sup_of_le_right (over_mono inf_le_right))
          (le_sup_of_le_left (over_mono inf_le_left)))))
    rw [inf_sup_left, inf_sup_right, inf_sup_right]
    refine sup_le (sup_le (inf_le_left.trans le_sup_left) ?_)
      (sup_le (inf_le_left.trans le_sup_left) (inf_le_right.trans (le_sup_of_le_right le_sup_left)))
    rw [← over_inf, inf_comm]
    exact le_sup_of_le_right le_sup_right
  refine ⟨?_, hinf.trans b₁, hinf.trans (Eq.trans ?_ b₂)⟩
  · rw [eq_top_iff, ← over_top, ← hp.sup_eq, over_sup]
    exact sup_le (le_sup_of_le_right le_sup_left) (le_sup_of_le_left le_sup_right)
  · rw [sup_assoc, sup_comm (over K (F ⊓ G))]

end PartialCylinder

end Atoms.Molecule.OGP
