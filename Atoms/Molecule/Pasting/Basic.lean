import Atoms.Molecule.Construction.Dual
import Atoms.Molecule.Transport

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

section Union

variable {A B : LowerSet P} {k : ℕ} {α : Bool}

theorem boundary_le_sup_boundary_sup (A B : LowerSet P) (k : ℕ) (α : Bool) :
    P.boundary A k α ≤ B ⊔ P.boundary (A ⊔ B) k α := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
  by_cases hzB : z ∈ B
  · exact Or.inl (B.lower hxz hzB)
  · exact Or.inr (mem_boundary_sup_of_notMem hz hzB hxz)

theorem inf_boundary_sup_le (h : A ⊓ B ≤ P.boundary A k α) :
    A ⊓ P.boundary (A ⊔ B) k α ≤ P.boundary A k α := by
  rintro x ⟨hxA, hx⟩
  rcases boundary_sup_le A B k α hx with hx | hx
  · exact hx
  · exact h ⟨hxA, boundary_le B k α hx⟩

theorem boundary_sup_eq_lowerClosure_sdiff_sup {D : LowerSet P} (hD : krullDim D ≤ k)
    (B : LowerSet P) (α : Bool) :
    P.boundary (D ⊔ B) k α = lowerClosure ((D : Set P) \ B) ⊔ P.boundary B k α := by
  have hDk (y : P) (hy : y ∈ D) : grade ℕ y ≤ k := krullDim_le_coe_iff.1 hD ⟨y, hy⟩
  have hcl : lowerClosure ((D : Set P) \ B) ≤ P.boundary (D ⊔ B) k α := by
    refine lowerClosure_le.2 fun d ⟨hdD, hdB⟩ => ?_
    have hs (y : P) (hy : y ∈ {y | y ∈ D ⊔ B ∧ d ≤ y}) : grade ℕ y ≤ k := by
      obtain ⟨hyD | hyB, hdy⟩ := hy
      · exact hDk y hyD
      · exact absurd (B.lower hdy hyB) hdB
    obtain ⟨m, hdm, hm⟩ := GradeOrder.exists_le_maximal hs ⟨Or.inl hdD, le_rfl⟩
    have hmax : Maximal (· ∈ D ⊔ B) m := ⟨hm.prop.1, fun y hy hmy => hm.2 ⟨hy, hdm.trans hmy⟩ hmy⟩
    exact LowerSet.lower _ hdm (mem_boundary_of_maximal_of_grade_le hmax (hs m hm.prop) α)
  refine le_antisymm (fun x hx => ?_) (sup_le hcl fun x hx => ?_)
  · obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
    by_cases hzB : z ∈ B
    · refine Or.inr (mem_boundary.2 ⟨z, ?_, hxz⟩)
      rcases hz with hz | ⟨hz, hn⟩
      · exact Or.inl ((mem_facesIn_sup_iff.1 hz).2.2 hzB)
      · exact Or.inr ⟨(LowerSet.maximal_mem_sup_iff.1 hz).2.2 hzB, hn⟩
    · have hzDB : z ∈ D ⊔ B := by
        rcases hz with hz | hz
        · exact hz.1
        · exact hz.1.prop
      rcases hzDB with hzD | hzB'
      · exact Or.inl (mem_lowerClosure.2 ⟨z, ⟨hzD, hzB⟩, hxz⟩)
      · exact absurd hzB' hzB
  · obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
    rcases hz with hz | ⟨hz, hn⟩
    · refine mem_boundary_of_mem_facesIn
        ⟨Or.inr hz.1, hz.2.1, Set.disjoint_left.2 fun c hc hcDB => ?_⟩ hxz
      rcases hcDB with hcD | hcB
      · have h1 := hDk c hcD
        have h2 := Nat.covBy_iff_add_one_eq.1 (hc.1.grade ℕ)
        have h3 := hz.2.1
        omega
      · exact Set.disjoint_left.1 hz.2.2 hc hcB
    · by_cases hzm : Maximal (· ∈ D ⊔ B) z
      · exact mem_boundary_of_maximal hzm hn hxz
      · have hzDB : z ∈ D ⊔ B := Or.inr hz.prop
        obtain ⟨c, hzc, hc⟩ := (not_maximal_iff_exists_gt hzDB).1 hzm
        have hcB : c ∉ B := fun hcB => hzc.not_ge (hz.2 hcB hzc.le)
        rcases hc with hcD | hcB'
        · exact hcl (mem_lowerClosure.2 ⟨c, ⟨hcD, hcB⟩, hxz.trans hzc.le⟩)
        · exact absurd hcB' hcB

theorem boundary_sup_eq_sup_boundary {S T : LowerSet P} {n : ℕ} {β : Bool} (hS : krullDim S ≤ n)
    (hST : S ⊓ T ≤ P.boundary T n β) : P.boundary (S ⊔ T) n β = S ⊔ P.boundary T n β := by
  rw [boundary_sup_eq_lowerClosure_sdiff_sup hS]
  refine le_antisymm (sup_le_sup_right (lowerClosure_le.2 Set.sdiff_subset) _)
    (sup_le (fun x hx => ?_) le_sup_right)
  by_cases hxT : x ∈ T
  · exact Or.inr (hST ⟨hx, hxT⟩)
  · exact Or.inl (subset_lowerClosure ⟨hx, hxT⟩)

theorem boundary_sup_eq_of_boundary_le {U V : LowerSet P} {n : ℕ} (hU : krullDim U ≤ n)
    (hVU : V ⊓ U ≤ P.boundary V n α) (hle : P.boundary V n α ≤ U) :
    P.boundary (V ⊔ U) n α = U := by
  rw [sup_comm, boundary_sup_eq_sup_boundary hU (by rwa [inf_comm]), sup_eq_left.2 hle]

theorem boundary_sup_boundary_sup (h : A ⊓ B ≤ P.boundary A k (!α)) :
    P.boundary (A ⊔ P.boundary (A ⊔ B) k α) k (!α) = P.boundary A k (!α) ⊔ P.boundary B k α := by
  rw [sup_comm A, boundary_sup_eq_lowerClosure_sdiff_sup (krullDim_boundary_le _ k α)]
  refine le_antisymm (sup_le (lowerClosure_le.2 fun x ⟨hx, hxA⟩ => ?_) le_sup_left)
    (sup_le le_sup_right fun x hx => ?_)
  · exact Or.inr ((boundary_sup_le A B k α hx).resolve_left fun h' => hxA (boundary_le A k α h'))
  · by_cases hxA : x ∈ A
    · exact Or.inr (h ⟨hxA, boundary_le B k α hx⟩)
    · rcases boundary_le_sup_boundary_sup B A k α hx with h' | h'
      · exact absurd h' hxA
      · rw [sup_comm] at h'
        exact Or.inl (subset_lowerClosure ⟨h', hxA⟩)

theorem sup_boundary_inf_sup_boundary (hA : A ⊓ B ≤ P.boundary A k (!α))
    (hB : A ⊓ B ≤ P.boundary B k α) :
    (A ⊔ P.boundary (A ⊔ B) k α) ⊓ (B ⊔ P.boundary (A ⊔ B) k (!α)) =
      P.boundary A k (!α) ⊔ P.boundary B k α := by
  have hA' := inf_boundary_sup_le hA
  have hB' : B ⊓ P.boundary (A ⊔ B) k α ≤ P.boundary B k α := by
    rw [sup_comm]
    exact inf_boundary_sup_le (by rwa [inf_comm])
  refine le_antisymm ?_ (sup_le (le_inf ?_ ?_) (le_inf ?_ ?_))
  · rintro x ⟨hx1, hx2⟩
    have hxAB : x ∈ A ⊔ B := by
      rcases hx1 with h | h
      · exact Or.inl h
      · exact boundary_le _ k α h
    rcases hxAB with hxA | hxB
    · rcases hx2 with h | h
      · exact Or.inl (hA ⟨hxA, h⟩)
      · exact Or.inl (hA' ⟨hxA, h⟩)
    · rcases hx1 with h | h
      · exact Or.inl (hA ⟨h, hxB⟩)
      · exact Or.inr (hB' ⟨hxB, h⟩)
  · exact (boundary_le A k _).trans le_sup_left
  · exact boundary_le_sup_boundary_sup A B k (!α)
  · rw [sup_comm A B]
    exact boundary_le_sup_boundary_sup B A k α
  · exact (boundary_le B k α).trans le_sup_left

end Union

section Pasting

variable {k : ℕ} {V W U : LowerSet P}

theorem isPastingIn_self_boundary_true (U : LowerSet P) (n : ℕ) :
    P.IsPastingIn n U (P.boundary U n true) U :=
  ⟨sup_eq_left.2 (boundary_le U n true), inf_eq_right.2 (boundary_le U n true),
    (inf_eq_right.2 (boundary_le U n true)).trans (boundary_boundary_of_le le_rfl false true).symm⟩

theorem isPastingIn_boundary_false_self (U : LowerSet P) (n : ℕ) :
    P.IsPastingIn n (P.boundary U n false) U U := by
  simpa only [boundary_dual_top, Pi.top_apply, top_eq_true, Bool.not_true, cond_true] using
    (isPastingIn_dual ⊤).1 (isPastingIn_self_boundary_true (P := dual P ⊤) U n)

namespace IsPastingIn

theorem inf_boundary_le_cond (β : Bool) {A B : LowerSet P} (hA : P.IsGlobular A)
    (hB : P.IsGlobular B) (hp : P.IsPastingIn k (cond β A B) (cond β B A) U) (n : ℕ)
    (α : Bool) : B ⊓ P.boundary U n α ≤ P.boundary B n α := by
  obtain ⟨-, hiB, -⟩ := (isPastingIn_cond_iff β).1 hp
  rcases lt_trichotomy n k with hnk | rfl | hkn
  · rw [hp.boundary_eq_of_lt_cond β hA hB hnk α]
    exact inf_le_right
  · by_cases hαβ : α = β
    · rw [hαβ, hp.boundary_cond β]
      exact inf_le_right
    · rw [Bool.eq_not_of_ne hαβ, ((isPastingIn_cond_comm β).1 hp).boundary_cond (!β), ← hiB,
        inf_comm A B]
      exact inf_le_inf_left B (boundary_le A n (!β))
  · rw [hp.boundary_eq_sup_of_lt_cond β hA hB hkn α, inf_sup_left]
    refine sup_le ((inf_le_inf_left B (boundary_le A n α)).trans ?_) inf_le_right
    rw [inf_comm, hiB]
    exact hB.boundary_le_boundary hkn (!β) α

private theorem isRound_of_isRound_right (hp : P.IsPastingIn k V W U) (hV : P.IsGlobular V)
    (hW : P.IsGlobular W) (hr : P.IsRound W) (hd : krullDim W = k + 1)
    (hdU : krullDim U = k + 1) : P.IsRound U := by
  have hg := hp.isGlobular hV hW
  have hb (j : ℕ) (hj : j < k) (β : Bool) : P.boundary U j β = P.boundary W j β :=
    hp.boundary_eq_of_lt_cond true hV hW hj β
  have key : P.boundary U k false ⊓ P.boundary U k true ≤
      P.boundary W k false ⊓ P.boundary W k true :=
    hp.inf_boundary_le.trans inf_le_right
  have hW0 : 0 < krullDim W := by
    rw [hd]
    exact_mod_cast Nat.succ_pos k
  refine ⟨hg, fun _ => ?_, fun m hm => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_bot_iff.1 (key.trans (hr.inf_boundary_zero hW0).le)
    · rw [hb 0 hk, hb 0 hk]
      exact hr.inf_boundary_zero hW0
  · have hmk : m + 1 < k + 1 := by
      rw [hdU] at hm
      exact_mod_cast hm
    have hmW : ((m + 1 : ℕ) : WithBot ℕ∞) < krullDim W := by
      rw [hd]
      exact_mod_cast hmk
    rcases Nat.lt_or_ge (m + 1) k with hlt | hge
    · rw [hb _ hlt, hb _ hlt, hr.inf_boundary_succ m hmW, boundaryFull, boundaryFull,
        hb m (by omega), hb m (by omega)]
    · obtain rfl : k = m + 1 := by omega
      refine le_antisymm (key.trans ?_) ?_
      · rw [hr.inf_boundary_succ m hmW, boundaryFull, boundaryFull, hb m (by omega),
          hb m (by omega)]
      · rw [boundaryFull]
        exact sup_le (le_inf (hg.boundary_le_boundary (by omega) _ _)
            (hg.boundary_le_boundary (by omega) _ _))
          (le_inf (hg.boundary_le_boundary (by omega) _ _)
            (hg.boundary_le_boundary (by omega) _ _))

theorem isRound_cond (α : Bool) {A B : LowerSet P} (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (hr : P.IsRound B)
    (hd : krullDim B = k + 1) (hdU : krullDim U = k + 1) : P.IsRound U := by
  cases α
  · exact (isRound_dual ⊤).1 (isRound_of_isRound_right (P := dual P ⊤)
      ((isPastingIn_dual ⊤).2 hp) ((isGlobular_dual ⊤).2 hA) ((isGlobular_dual ⊤).2 hB)
      ((isRound_dual ⊤).2 hr) hd hdU)
  · exact isRound_of_isRound_right hp hA hB hr hd hdU

variable {A B X : LowerSet P}

theorem isPastingIn_right_sup (hA : P.IsPastingIn k U V A) (hX : P.IsPastingIn k A W X) :
    P.IsPastingIn k V W (V ⊔ W) := by
  have hAW : A ⊓ W = P.boundary V k true := hX.inf_eq_output.trans hA.boundary_output
  have hVW : V ⊓ W = P.boundary V k true := le_antisymm
    ((inf_le_inf_right W hA.right_le).trans hAW.le)
    (le_inf (boundary_le V k true) (hAW ▸ inf_le_right))
  exact ⟨rfl, hVW, hVW.trans (hAW.symm.trans hX.inf_eq_input)⟩

theorem assoc (hA : P.IsPastingIn k U V A) (hX : P.IsPastingIn k A W X) :
    P.IsPastingIn k U (V ⊔ W) X := by
  have hVW := hA.isPastingIn_right_sup hX
  have hAW : A ⊓ W = P.boundary V k true := hX.inf_eq_output.trans hA.boundary_output
  have hUVW : U ⊓ (V ⊔ W) = U ⊓ V := by
    refine le_antisymm ?_ (inf_le_inf_left U le_sup_left)
    rw [inf_sup_left]
    exact sup_le le_rfl (le_inf inf_le_left
      ((inf_le_inf_right W hA.left_le).trans (hAW.le.trans (boundary_le V k true))))
  exact ⟨by rw [← hX.sup_eq, ← hA.sup_eq, sup_assoc], hUVW.trans hA.inf_eq_output,
    hUVW.trans (hA.inf_eq_input.trans hVW.boundary_input.symm)⟩

theorem isPastingIn_left_sup (hB : P.IsPastingIn k V W B) (hX : P.IsPastingIn k U B X) :
    P.IsPastingIn k U V (U ⊔ V) := by
  have h : P.IsPastingIn k U V (V ⊔ U) := (isPastingIn_dual ⊤).1
    (isPastingIn_right_sup (P := dual P ⊤) ((isPastingIn_dual ⊤).2 hB) ((isPastingIn_dual ⊤).2 hX))
  rwa [sup_comm] at h

theorem assoc_symm (hB : P.IsPastingIn k V W B) (hX : P.IsPastingIn k U B X) :
    P.IsPastingIn k (U ⊔ V) W X := by
  have h : P.IsPastingIn k (V ⊔ U) W X := (isPastingIn_dual ⊤).1
    (assoc (P := dual P ⊤) ((isPastingIn_dual ⊤).2 hB) ((isPastingIn_dual ⊤).2 hX))
  rwa [sup_comm] at h

theorem assoc_cond (α : Bool) {A B C Y D : LowerSet P}
    (hA : P.IsPastingIn k (cond α A B) (cond α B A) C)
    (hY : P.IsPastingIn k (cond α Y C) (cond α C Y) D) :
    P.IsPastingIn k (cond α (Y ⊔ A) B) (cond α B (Y ⊔ A)) D := by
  cases α
  · have h := hA.assoc hY
    rwa [sup_comm] at h
  · exact hA.assoc_symm hY

end IsPastingIn

variable {n : ℕ} {U' V' A B X : LowerSet P}

theorem isPastingIn_interchange_left (hkn : k < n) (hU : P.IsGlobular U) (hU' : P.IsGlobular U')
    (hV : P.IsGlobular V) (hV' : P.IsGlobular V') (hA : P.IsPastingIn n U U' A)
    (hB : P.IsPastingIn n V V' B) (hX : P.IsPastingIn k A B X) : P.IsPastingIn k U V (U ⊔ V) := by
  have hAk : A ⊓ B = P.boundary U k true :=
    hX.inf_eq_output.trans (hA.boundary_eq_of_lt_cond false hU' hU hkn true)
  have hBk : A ⊓ B = P.boundary V k false :=
    hX.inf_eq_input.trans (hB.boundary_eq_of_lt_cond false hV' hV hkn false)
  have hUV : U ⊓ V = P.boundary U k true := by
    refine le_antisymm ((inf_le_inf hA.left_le hB.left_le).trans hAk.le)
      (le_inf (boundary_le U k true) ?_)
    rw [← hAk, hBk]
    exact boundary_le V k false
  exact ⟨rfl, hUV, hUV.trans (hAk.symm.trans hBk)⟩

theorem isPastingIn_interchange_right (hkn : k < n) (hU : P.IsGlobular U)
    (hU' : P.IsGlobular U') (hV : P.IsGlobular V) (hV' : P.IsGlobular V')
    (hA : P.IsPastingIn n U U' A) (hB : P.IsPastingIn n V V' B) (hX : P.IsPastingIn k A B X) :
    P.IsPastingIn k U' V' (U' ⊔ V') := by
  have h : P.IsPastingIn k U' V' (V' ⊔ U') := (isPastingIn_dual ⊤).1
    (isPastingIn_interchange_left (P := dual P ⊤) hkn ((isGlobular_dual ⊤).2 hV')
      ((isGlobular_dual ⊤).2 hV) ((isGlobular_dual ⊤).2 hU') ((isGlobular_dual ⊤).2 hU)
      ((isPastingIn_dual ⊤).2 hB) ((isPastingIn_dual ⊤).2 hA) ((isPastingIn_dual ⊤).2 hX))
  rwa [sup_comm] at h

theorem isPastingIn_interchange (hkn : k < n) (hU : P.IsGlobular U) (hU' : P.IsGlobular U')
    (hV : P.IsGlobular V) (hV' : P.IsGlobular V') (hA : P.IsPastingIn n U U' A)
    (hB : P.IsPastingIn n V V' B) (hX : P.IsPastingIn k A B X) :
    P.IsPastingIn n (U ⊔ V) (U' ⊔ V') X := by
  have hUV := isPastingIn_interchange_left hkn hU hU' hV hV' hA hB hX
  have hUV' := isPastingIn_interchange_right hkn hU hU' hV hV' hA hB hX
  have hAk : A ⊓ B = P.boundary U k true :=
    hX.inf_eq_output.trans (hA.boundary_eq_of_lt_cond false hU' hU hkn true)
  have hBk : A ⊓ B = P.boundary V k false :=
    hX.inf_eq_input.trans (hB.boundary_eq_of_lt_cond false hV' hV hkn false)
  have hint : (U ⊔ V) ⊓ (U' ⊔ V') = U ⊓ U' ⊔ V ⊓ V' := by
    refine le_antisymm ?_
      (sup_le (inf_le_inf le_sup_left le_sup_left) (inf_le_inf le_sup_right le_sup_right))
    rw [inf_sup_left, inf_sup_right, inf_sup_right]
    refine sup_le (sup_le le_sup_left ?_) (sup_le ?_ le_sup_right)
    · refine le_sup_of_le_right ?_
      rw [hB.inf_eq_output]
      refine (le_trans ?_ hBk.le).trans (hV.boundary_le_boundary hkn false true)
      rw [inf_comm]
      exact inf_le_inf hA.right_le hB.left_le
    · refine le_sup_of_le_left ?_
      rw [hA.inf_eq_output]
      exact ((inf_le_inf hA.left_le hB.right_le).trans hAk.le).trans
        (hU.boundary_le_boundary hkn true true)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hX.sup_eq, ← hA.sup_eq, ← hB.sup_eq, sup_sup_sup_comm]
  · rw [hint, ← (hUV.boundary_of_lt hU hV hkn true).sup_eq, hA.inf_eq_output, hB.inf_eq_output]
  · rw [hint, ← (hUV'.boundary_of_lt hU' hV' hkn false).sup_eq, hA.inf_eq_input,
      hB.inf_eq_input]

variable {C H R : LowerSet P}

private theorem whisker_aux (α : Bool) (hC : P.IsGlobular C) (hH : P.IsGlobular H)
    (hp : P.IsPastingIn k (cond α C H) (cond α H C) R) :
    P.IsPastingIn k (cond α C (P.boundary H (k + 1) false))
        (cond α (P.boundary H (k + 1) false) C) (C ⊔ P.boundary H (k + 1) false) ∧
      P.IsPastingIn k (cond α (P.boundary C (k + 1) true) H)
        (cond α H (P.boundary C (k + 1) true)) (P.boundary C (k + 1) true ⊔ H) ∧
      P.IsPastingIn (k + 1) (C ⊔ P.boundary H (k + 1) false) (P.boundary C (k + 1) true ⊔ H)
        R := by
  have hk := Nat.lt_succ_self k
  have hC' := hC.boundary (k + 1) true
  have hH' := hH.boundary (k + 1) false
  have hCC := isPastingIn_self_boundary_true C (k + 1)
  have hHH := isPastingIn_boundary_false_self H (k + 1)
  cases α
  · have h1 := isPastingIn_interchange_left hk hH' hH hC hC' hHH hCC hp
    have h2 := isPastingIn_interchange_right hk hH' hH hC hC' hHH hCC hp
    have h3 := isPastingIn_interchange hk hH' hH hC hC' hHH hCC hp
    rw [sup_comm] at h1 h2
    rw [sup_comm (P.boundary H _ _), sup_comm H] at h3
    exact ⟨h1, h2, h3⟩
  · exact ⟨isPastingIn_interchange_left hk hC hC' hH' hH hCC hHH hp,
      isPastingIn_interchange_right hk hC hC' hH' hH hCC hHH hp,
      isPastingIn_interchange hk hC hC' hH' hH hCC hHH hp⟩

theorem IsPastingIn.isPastingIn_sup_boundary_false (α : Bool) (hC : P.IsGlobular C)
    (hH : P.IsGlobular H) (hp : P.IsPastingIn k (cond α C H) (cond α H C) R) :
    P.IsPastingIn k (cond α C (P.boundary H (k + 1) false))
      (cond α (P.boundary H (k + 1) false) C) (C ⊔ P.boundary H (k + 1) false) :=
  (whisker_aux α hC hH hp).1

theorem IsPastingIn.isPastingIn_boundary_true_sup (α : Bool) (hC : P.IsGlobular C)
    (hH : P.IsGlobular H) (hp : P.IsPastingIn k (cond α C H) (cond α H C) R) :
    P.IsPastingIn k (cond α (P.boundary C (k + 1) true) H)
      (cond α H (P.boundary C (k + 1) true)) (P.boundary C (k + 1) true ⊔ H) :=
  (whisker_aux α hC hH hp).2.1

theorem IsPastingIn.whisker_interchange (α : Bool) (hC : P.IsGlobular C) (hH : P.IsGlobular H)
    (hp : P.IsPastingIn k (cond α C H) (cond α H C) R) :
    P.IsPastingIn (k + 1) (C ⊔ P.boundary H (k + 1) false) (P.boundary C (k + 1) true ⊔ H) R :=
  (whisker_aux α hC hH hp).2.2

theorem IsPasting.isMolecule {U V W : OGP.{u}} (h : IsPasting U V k W) (hU : IsMolecule U)
    (hV : IsMolecule V) : IsMolecule W := by
  obtain ⟨i, j, hi, hj, hp⟩ := h
  exact hp.isMoleculeIn (isMoleculeIn_map i hU) (isMoleculeIn_map j hV)

end Pasting

section Submolecule

variable {k : ℕ} {V W U X : LowerSet P}

theorem IsSubmoleculeOf.induction_paste {motive : LowerSet P → LowerSet P → Prop}
    (refl : ∀ U, IsMoleculeIn P U → motive U U)
    (paste : ∀ (α : Bool) (k : ℕ) (A B U X : LowerSet P),
      P.IsPastingIn k (cond α A B) (cond α B A) U → IsMoleculeIn P A → IsMoleculeIn P B →
      (k : WithBot ℕ∞) < krullDim B → A ≤ U → B ≤ U → P.IsSubmoleculeOf X A → motive X A →
      motive X U)
    (h : P.IsSubmoleculeOf X U) : motive X U := by
  obtain ⟨hU, h⟩ := h
  induction h with
  | refl => exact refl X hU
  | @tail Y U hXY hYU ih =>
    obtain ⟨k, α, Z, hp, hY, hZ⟩ := hYU
    replace hp := (isPastingIn_cond_comm α).1 hp
    have hs := ((isPastingIn_cond_iff (!α)).1 hp).1
    by_cases hZY : Z ≤ Y
    · obtain rfl : Y = U := (sup_eq_left.2 hZY).symm.trans hs
      exact ih hY
    · exact paste (!α) k Y Z U X hp hY hZ
        (lt_of_not_ge fun hk => hZY (hp.le_of_krullDim_le_cond (!α) hk))
        (hs ▸ le_sup_left) (hs ▸ le_sup_right) ⟨hY, hXY⟩ (ih hY)

namespace IsMoleculeIn

theorem boundary_isSubmoleculeOf_boundary (h : IsMoleculeIn P U) {i n : ℕ} (hin : i < n)
    (γ δ : Bool) : P.IsSubmoleculeOf (P.boundary U i γ) (P.boundary U n δ) := by
  rw [← h.isGlobular i n hin γ δ]
  exact (h.boundary n δ).boundary_isSubmoleculeOf i γ

theorem boundary_isSubmoleculeOf_boundary_of_le (h : IsMoleculeIn P U) {i n : ℕ} (hin : i ≤ n)
    (α : Bool) : P.IsSubmoleculeOf (P.boundary U i α) (P.boundary U n α) := by
  rcases hin.lt_or_eq with hin | rfl
  · exact h.boundary_isSubmoleculeOf_boundary hin α α
  · exact .refl (h.boundary i α)

theorem boundary_boundary_isSubmoleculeOf_boundary (h : IsMoleculeIn P U) {j n : ℕ}
    {α γ : Bool} (hj : j < n ∨ γ = α) :
    P.IsSubmoleculeOf (P.boundary (P.boundary U j γ) n α) (P.boundary U n α) := by
  rcases lt_or_ge j n with hjn | hnj
  · rw [boundary_boundary_of_le hjn.le]
    exact h.boundary_isSubmoleculeOf_boundary hjn γ α
  · obtain rfl : γ = α := hj.resolve_left hnj.not_gt
    rcases hnj.lt_or_eq with hnj | rfl
    · rw [h.isGlobular n j hnj γ γ]
      exact .refl (h.boundary n γ)
    · rw [boundary_boundary_of_le le_rfl]
      exact .refl (h.boundary n γ)

end IsMoleculeIn

theorem IsPastingIn.boundary_isSubmoleculeOf_boundary (α : Bool) {A B : LowerSet P}
    (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {n : ℕ} {γ : Bool} (h : k < n ∨ α = γ) :
    P.IsSubmoleculeOf (P.boundary B n γ) (P.boundary U n γ) := by
  by_cases hkn : k < n
  · exact ((hp.boundary_of_lt_cond α hA.isGlobular hB.isGlobular hkn γ).isPastingFactorOf α
      (hB.boundary n γ) (hA.boundary n γ)).isSubmoleculeOf
  · obtain rfl : α = γ := h.resolve_left hkn
    rw [← hp.boundary_eq_of_le_cond α hA.isGlobular hB.isGlobular (not_lt.1 hkn)]
    exact .refl ((hp.isPastingFactorOf α hB hA).isMoleculeIn_right.boundary n α)

theorem IsPastingFactorOf.inf_boundary_le (h : P.IsPastingFactorOf X U) (n : ℕ) (α : Bool) :
    X ⊓ P.boundary U n α ≤ P.boundary X n α := by
  obtain ⟨k, β, Y, hp, hX, hY⟩ := h
  exact hp.inf_boundary_le_cond β hY.isGlobular hX.isGlobular n α

theorem IsSubmoleculeOf.inf_boundary_le (h : P.IsSubmoleculeOf X U) (n : ℕ) (α : Bool) :
    X ⊓ P.boundary U n α ≤ P.boundary X n α := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact inf_le_right
  | @tail Y U hXY hYU ih =>
    have hXY' : X ≤ Y := IsSubmoleculeOf.le ⟨hYU.isMoleculeIn_left, hXY⟩
    exact (le_inf inf_le_left ((le_inf (inf_le_left.trans hXY') inf_le_right).trans
      (hYU.inf_boundary_le n α))).trans ih

private theorem isSubmoleculeOf_sup_step_left {Y Z : LowerSet P} {n : ℕ} {α : Bool}
    (hp : P.IsPastingIn k Y Z U) (hZ : IsMoleculeIn P Z) (hU : krullDim U ≤ n)
    (hVU : V ⊓ U ≤ P.boundary V n α) (hle : P.boundary V n α ≤ Y)
    (ih : P.IsSubmoleculeOf V (V ⊔ Y) ∧
      P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ Y) n (!α))) :
    P.IsSubmoleculeOf V (V ⊔ U) ∧
      P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ U) n (!α)) := by
  by_cases hZY : Z ≤ Y
  · rwa [← hp.sup_eq, sup_eq_left.2 hZY]
  have hkZ : (k : WithBot ℕ∞) < krullDim Z :=
    lt_of_not_ge fun h => hZY (hp.le_of_krullDim_le_cond true h)
  have hkn : k < n := by
    exact_mod_cast hkZ.trans_le ((LowerSet.krullDim_mono hp.right_le).trans hU)
  have hVY := ih.1.isMoleculeIn_right
  have hbY : P.boundary (V ⊔ Y) n α = Y :=
    boundary_sup_eq_of_boundary_le ((LowerSet.krullDim_mono hp.left_le).trans hU)
      ((inf_le_inf_left V hp.left_le).trans hVU) hle
  have hinf : (V ⊔ Y) ⊓ Z = Y ⊓ Z := by
    rw [inf_sup_right, sup_eq_right]
    exact le_inf ((inf_le_inf_left V hp.right_le).trans (hVU.trans hle)) inf_le_right
  have hp2 : P.IsPastingIn k (V ⊔ Y) Z (V ⊔ U) := by
    refine ⟨by rw [sup_assoc, hp.sup_eq], ?_, by rw [hinf, hp.inf_eq_input]⟩
    rw [hinf, hp.inf_eq_output, ← hVY.isGlobular k n hkn true α, hbY]
  exact ⟨ih.1.tail (hp2.isPastingFactorOf false hVY hZ),
    ih.2.tail ((hp2.boundary_of_lt hVY.isGlobular hZ.isGlobular hkn (!α)).isPastingFactorOf false
      (hVY.boundary n (!α)) (hZ.boundary n (!α)))⟩

private theorem isSubmoleculeOf_sup_step_right {Y Z : LowerSet P} {n : ℕ} {α : Bool}
    (hp : P.IsPastingIn k Z Y U) (hZ : IsMoleculeIn P Z) (hU : krullDim U ≤ n)
    (hVU : V ⊓ U ≤ P.boundary V n α) (hle : P.boundary V n α ≤ Y)
    (ih : P.IsSubmoleculeOf V (V ⊔ Y) ∧
      P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ Y) n (!α))) :
    P.IsSubmoleculeOf V (V ⊔ U) ∧
      P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ U) n (!α)) := by
  have h := isSubmoleculeOf_sup_step_left (P := dual P ⊤) (α := !α) ((isPastingIn_dual ⊤).2 hp)
    ((isMoleculeIn_dual ⊤).2 hZ) hU (by simpa only [boundary_dual_top, Bool.not_not] using hVU)
    (by simpa only [boundary_dual_top, Bool.not_not] using hle)
    (by simpa only [isSubmoleculeOf_dual, boundary_dual_top, Bool.not_not] using ih)
  simpa only [isSubmoleculeOf_dual, boundary_dual_top, Bool.not_not] using h

private theorem isSubmoleculeOf_sup_aux {n : ℕ} {α : Bool} (hV : IsMoleculeIn P V)
    (hsub : P.IsSubmoleculeOf (P.boundary V n α) U) (hU : krullDim U ≤ n)
    (hVU : V ⊓ U ≤ P.boundary V n α) :
    P.IsSubmoleculeOf V (V ⊔ U) ∧
      P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ U) n (!α)) := by
  obtain ⟨hUm, h⟩ := hsub
  induction h with
  | refl =>
    rw [sup_eq_left.2 (boundary_le V n α)]
    exact ⟨.refl hV, .refl (hV.boundary n (!α))⟩
  | @tail Y U hXY hYU ih =>
    have hY := hYU.isMoleculeIn_left
    have hle : P.boundary V n α ≤ Y := IsSubmoleculeOf.le ⟨hY, hXY⟩
    have ih' := ih ((LowerSet.krullDim_mono hYU.le).trans hU)
      ((inf_le_inf_left V hYU.le).trans hVU) hY
    obtain ⟨k, α, Z, hp, -, hZ⟩ := hYU
    cases α
    · exact isSubmoleculeOf_sup_step_left hp hZ hU hVU hle ih'
    · exact isSubmoleculeOf_sup_step_right hp hZ hU hVU hle ih'

theorem IsSubmoleculeOf.isSubmoleculeOf_sup {n : ℕ} {α : Bool}
    (hsub : P.IsSubmoleculeOf (P.boundary V n α) U) (hV : IsMoleculeIn P V)
    (hU : krullDim U ≤ n) (hVU : V ⊓ U ≤ P.boundary V n α) : P.IsSubmoleculeOf V (V ⊔ U) :=
  (isSubmoleculeOf_sup_aux hV hsub hU hVU).1

theorem IsSubmoleculeOf.boundary_isSubmoleculeOf_boundary_sup {n : ℕ} {α : Bool}
    (hsub : P.IsSubmoleculeOf (P.boundary V n α) U) (hV : IsMoleculeIn P V)
    (hU : krullDim U ≤ n) (hVU : V ⊓ U ≤ P.boundary V n α) :
    P.IsSubmoleculeOf (P.boundary V n (!α)) (P.boundary (V ⊔ U) n (!α)) :=
  (isSubmoleculeOf_sup_aux hV hsub hU hVU).2

end Submolecule

section GenPasting

variable {k : ℕ} {U V W : LowerSet P}

variable (P) in
structure IsGenPastingIn (k : ℕ) (U V : LowerSet P) : Prop where
  isMoleculeIn_left : IsMoleculeIn P U
  isMoleculeIn_right : IsMoleculeIn P V
  inf_isSubmoleculeOf_left : P.IsSubmoleculeOf (U ⊓ V) (P.boundary U k true)
  inf_isSubmoleculeOf_right : P.IsSubmoleculeOf (U ⊓ V) (P.boundary V k false)
  boundary_isSubmoleculeOf_left :
    P.IsSubmoleculeOf (P.boundary U k false) (P.boundary (U ⊔ V) k false)
  boundary_isSubmoleculeOf_right :
    P.IsSubmoleculeOf (P.boundary V k true) (P.boundary (U ⊔ V) k true)

theorem IsPastingIn.isGenPastingIn (hp : P.IsPastingIn k U V W) (hU : IsMoleculeIn P U)
    (hV : IsMoleculeIn P V) {m : ℕ} (hm : k ≤ m) : P.IsGenPastingIn m U V where
  isMoleculeIn_left := hU
  isMoleculeIn_right := hV
  inf_isSubmoleculeOf_left := by
    rw [hp.inf_eq_output]
    exact hU.boundary_isSubmoleculeOf_boundary_of_le hm true
  inf_isSubmoleculeOf_right := by
    rw [hp.inf_eq_input]
    exact hV.boundary_isSubmoleculeOf_boundary_of_le hm false
  boundary_isSubmoleculeOf_left := by
    rw [hp.sup_eq]
    exact hp.boundary_isSubmoleculeOf_boundary false hV hU (Or.inr rfl)
  boundary_isSubmoleculeOf_right := by
    rw [hp.sup_eq]
    exact hp.boundary_isSubmoleculeOf_boundary true hU hV (Or.inr rfl)

theorem isPastingIn_sup_boundary_cond (α : Bool) {A B : LowerSet P}
    (hA : A ⊓ B ≤ P.boundary A k (!α)) (hB : A ⊓ B ≤ P.boundary B k α) :
    P.IsPastingIn k (cond α (B ⊔ P.boundary (A ⊔ B) k (!α)) (A ⊔ P.boundary (A ⊔ B) k α))
      (cond α (A ⊔ P.boundary (A ⊔ B) k α) (B ⊔ P.boundary (A ⊔ B) k (!α))) (A ⊔ B) := by
  have hint := sup_boundary_inf_sup_boundary hA hB
  have h1 := boundary_sup_boundary_sup hA
  have h2 := boundary_sup_boundary_sup (A := B) (B := A) (α := !α)
    (by rwa [inf_comm, Bool.not_not])
  rw [sup_comm B A, Bool.not_not] at h2
  refine (isPastingIn_cond_iff α).2 ⟨le_antisymm (sup_le (sup_le le_sup_right (boundary_le _ _ _))
      (sup_le le_sup_left (boundary_le _ _ _)))
      (sup_le (le_sup_left.trans le_sup_right) (le_sup_left.trans le_sup_left)),
    (inf_comm _ _).trans (hint.trans h1.symm),
    (inf_comm _ _).trans (hint.trans ((sup_comm _ _).trans h2.symm))⟩

theorem isPastingIn_sup_boundary (hU : U ⊓ V ≤ P.boundary U k true)
    (hV : U ⊓ V ≤ P.boundary V k false) :
    P.IsPastingIn k (U ⊔ P.boundary (U ⊔ V) k false) (V ⊔ P.boundary (U ⊔ V) k true) (U ⊔ V) :=
  isPastingIn_sup_boundary_cond false hU hV

theorem isMoleculeIn_and_isSubmoleculeOf_of_genPasting (α : Bool) {X Y Z : LowerSet P}
    (hZ : Z = X ⊔ Y) (hX : IsMoleculeIn P X) (hY : IsMoleculeIn P Y)
    (h1 : P.IsSubmoleculeOf (X ⊓ Y) (P.boundary X k (!α)))
    (h2 : P.IsSubmoleculeOf (X ⊓ Y) (P.boundary Y k α))
    (h3 : P.IsSubmoleculeOf (P.boundary X k α) (P.boundary Z k α))
    (h4 : P.IsSubmoleculeOf (P.boundary Y k (!α)) (P.boundary Z k (!α)))
    (h5 : X ⊓ P.boundary Z k α ≤ P.boundary X k α)
    (h6 : Y ⊓ P.boundary Z k (!α) ≤ P.boundary Y k (!α)) :
    IsMoleculeIn P Z ∧ P.IsSubmoleculeOf X Z ∧ P.IsSubmoleculeOf Y Z := by
  subst hZ
  have sX := h3.isSubmoleculeOf_sup hX (krullDim_boundary_le _ k α) h5
  have sY := h4.isSubmoleculeOf_sup hY (krullDim_boundary_le _ k (!α)) h6
  have hp := isPastingIn_sup_boundary_cond α h1.le h2.le
  have fX := hp.isPastingFactorOf α sX.isMoleculeIn_right sY.isMoleculeIn_right
  have fY := ((isPastingIn_cond_comm α).1 hp).isPastingFactorOf (!α) sY.isMoleculeIn_right
    sX.isMoleculeIn_right
  exact ⟨fX.isMoleculeIn_right, sX.tail fX, sY.tail fY⟩

namespace IsGenPastingIn

theorem isSubmoleculeOf_sup_boundary_left (h : P.IsGenPastingIn k U V)
    (hU : U ⊓ P.boundary (U ⊔ V) k false ≤ P.boundary U k false) :
    P.IsSubmoleculeOf U (U ⊔ P.boundary (U ⊔ V) k false) :=
  h.boundary_isSubmoleculeOf_left.isSubmoleculeOf_sup h.isMoleculeIn_left
    (krullDim_boundary_le _ k false) hU

theorem isSubmoleculeOf_sup_boundary_right (h : P.IsGenPastingIn k U V)
    (hV : V ⊓ P.boundary (U ⊔ V) k true ≤ P.boundary V k true) :
    P.IsSubmoleculeOf V (V ⊔ P.boundary (U ⊔ V) k true) :=
  h.boundary_isSubmoleculeOf_right.isSubmoleculeOf_sup h.isMoleculeIn_right
    (krullDim_boundary_le _ k true) hV

theorem isMoleculeIn (h : P.IsGenPastingIn k U V)
    (hU : U ⊓ P.boundary (U ⊔ V) k false ≤ P.boundary U k false)
    (hV : V ⊓ P.boundary (U ⊔ V) k true ≤ P.boundary V k true) : IsMoleculeIn P (U ⊔ V) :=
  (isMoleculeIn_and_isSubmoleculeOf_of_genPasting false rfl h.isMoleculeIn_left
    h.isMoleculeIn_right h.inf_isSubmoleculeOf_left h.inf_isSubmoleculeOf_right
    h.boundary_isSubmoleculeOf_left h.boundary_isSubmoleculeOf_right hU hV).1

theorem cond_parts {α : Bool} {A B : LowerSet P}
    (h : P.IsGenPastingIn k (cond α B A) (cond α A B)) :
    P.IsSubmoleculeOf (A ⊓ B) (P.boundary A k (!α)) ∧
      P.IsSubmoleculeOf (A ⊓ B) (P.boundary B k α) ∧
      P.IsSubmoleculeOf (P.boundary A k α) (P.boundary (A ⊔ B) k α) ∧
      P.IsSubmoleculeOf (P.boundary B k (!α)) (P.boundary (A ⊔ B) k (!α)) := by
  cases α
  · exact ⟨h.inf_isSubmoleculeOf_left, h.inf_isSubmoleculeOf_right,
      h.boundary_isSubmoleculeOf_left, h.boundary_isSubmoleculeOf_right⟩
  · have h1 := h.inf_isSubmoleculeOf_left
    have h2 := h.inf_isSubmoleculeOf_right
    have h3 := h.boundary_isSubmoleculeOf_left
    have h4 := h.boundary_isSubmoleculeOf_right
    rw [cond_true, cond_true, inf_comm] at h1 h2
    rw [cond_true, cond_true, sup_comm] at h3 h4
    exact ⟨h2, h1, h4, h3⟩

end IsGenPastingIn

end GenPasting

end Atoms.Molecule.OGP
