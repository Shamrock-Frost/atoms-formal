import Atoms.Molecule.Rewritable.Basic

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {k n : ℕ} {α : Bool} {S T R U A B : LowerSet P} {x : P}

theorem isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary (hA : IsMoleculeIn P A)
    (hB : IsMoleculeIn P B) (hsub : P.IsSubmoleculeOf (P.boundary B k (!α)) (P.boundary A k α))
    (hinf : A ⊓ B = P.boundary B k (!α)) :
    IsMoleculeIn P (A ⊔ B) ∧ P.IsSubmoleculeOf A (A ⊔ B) ∧ P.IsSubmoleculeOf B (A ⊔ B) ∧
      P.boundary (A ⊔ B) k (!α) = P.boundary A k (!α) ∧
      P.boundary (A ⊔ B) k α = P.boundary (B ⊔ P.boundary A k α) k α ∧
      (P.IsRound A → krullDim A = k + 1 → krullDim (A ⊔ B : LowerSet P) = k + 1 →
        P.IsRound (A ⊔ B)) := by
  set D := P.boundary A k α with hD
  have hDA : D ≤ A := boundary_le A k α
  have hbD : P.boundary B k (!α) ≤ D := hsub.le
  have hBD : B ⊓ D ≤ P.boundary B k (!α) := fun x ⟨hxB, hxD⟩ => hinf ▸ ⟨hDA hxD, hxB⟩
  have hM : P.IsSubmoleculeOf B (B ⊔ D) :=
    hsub.isSubmoleculeOf_sup hB (krullDim_boundary_le A k α) hBD
  have hMm : IsMoleculeIn P (B ⊔ D) := hM.isMoleculeIn_right
  have hbM : P.boundary (B ⊔ D) k (!α) = D :=
    boundary_sup_eq_of_boundary_le (krullDim_boundary_le A k α) hBD hbD
  have hAM : A ⊓ (B ⊔ D) = D := by
    rw [inf_sup_left, hinf, inf_eq_right.2 hDA, sup_eq_right.2 hbD]
  have hAMu : A ⊔ (B ⊔ D) = A ⊔ B := by
    rw [sup_comm B D, ← sup_assoc, sup_eq_left.2 hDA]
  have hp : P.IsPastingIn k (cond α A (B ⊔ D)) (cond α (B ⊔ D) A) (A ⊔ B) :=
    (isPastingIn_cond_iff α).2 ⟨hAMu, hAM.trans hbM.symm, hAM.trans hD⟩
  have hp' := (isPastingIn_cond_comm α).1 hp
  exact ⟨(hp.isPastingFactorOf α hMm hA).isMoleculeIn_right,
    (hp'.isPastingFactorOf (!α) hA hMm).isSubmoleculeOf, hM.tail (hp.isPastingFactorOf α hMm hA),
    hp'.boundary_cond (!α), hp.boundary_cond α,
    fun hr hd hd' => hp'.isRound_cond (!α) hMm.isGlobular hA.isGlobular hr hd hd'⟩

variable (P) in
structure IsPastingAtIn (k : ℕ) (α : Bool) (S T R : LowerSet P) : Prop where
  isMoleculeIn_left : IsMoleculeIn P S
  isMoleculeIn_right : IsMoleculeIn P T
  eq_sup : R = S ⊔ T
  inf_eq : S ⊓ T = P.boundary S k (!α)
  isSubmoleculeOf_inf : P.IsSubmoleculeOf (S ⊓ T) (P.boundary T k α)

namespace IsPastingAtIn

variable (h : P.IsPastingAtIn k α S T R)
include h

theorem isSubmoleculeOf_boundary :
    P.IsSubmoleculeOf (P.boundary S k (!α)) (P.boundary T k α) :=
  h.inf_eq ▸ h.isSubmoleculeOf_inf

theorem left_le : S ≤ R := h.eq_sup ▸ le_sup_left

theorem right_le : T ≤ R := h.eq_sup ▸ le_sup_right

theorem isMoleculeIn_sup :
    IsMoleculeIn P R ∧ P.IsSubmoleculeOf S R ∧ P.IsSubmoleculeOf T R ∧
      P.boundary R k (!α) = P.boundary T k (!α) ∧
      P.boundary R k α = P.boundary (S ⊔ P.boundary T k α) k α := by
  obtain ⟨m, hT, hS, hb₁, hb₂, -⟩ := isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary
    (α := α) h.isMoleculeIn_right h.isMoleculeIn_left h.isSubmoleculeOf_boundary
    ((inf_comm T S).trans h.inf_eq)
  rw [h.eq_sup, sup_comm]
  exact ⟨m, hS, hT, hb₁, hb₂⟩

theorem isMoleculeIn : IsMoleculeIn P R :=
  h.isMoleculeIn_sup.1

theorem isRound (hr : P.IsRound T) (hdT : krullDim T = k + 1) (hdR : krullDim R = k + 1) :
    P.IsRound R := by
  have key := isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary (α := α) h.isMoleculeIn_right
    h.isMoleculeIn_left h.isSubmoleculeOf_boundary ((inf_comm T S).trans h.inf_eq)
  rw [h.eq_sup, sup_comm] at hdR ⊢
  exact key.2.2.2.2.2 hr hdT hdR

theorem isSubmoleculeOf_left : P.IsSubmoleculeOf S R :=
  h.isMoleculeIn_sup.2.1

theorem isSubmoleculeOf_right : P.IsSubmoleculeOf T R :=
  h.isMoleculeIn_sup.2.2.1

theorem boundary_not : P.boundary R k (!α) = P.boundary T k (!α) :=
  h.isMoleculeIn_sup.2.2.2.1

theorem inf_le_boundary : S ⊓ T ≤ P.boundary T k α :=
  h.isSubmoleculeOf_inf.le

theorem mem_boundary_of_mem (hS : x ∈ S) (hT : x ∈ T) : x ∈ P.boundary S k (!α) :=
  h.inf_eq ▸ ⟨hS, hT⟩

theorem inf_boundary_right : S ⊓ P.boundary T k α = S ⊓ T :=
  le_antisymm (inf_le_inf_left S (boundary_le T k α)) (le_inf inf_le_left h.inf_le_boundary)

theorem isSubmoleculeOf_boundary_left :
    P.IsSubmoleculeOf (P.boundary S k α) (P.boundary R k α) := by
  have key := h.isSubmoleculeOf_boundary.boundary_isSubmoleculeOf_boundary_sup
    h.isMoleculeIn_left (krullDim_boundary_le T k α) (h.inf_boundary_right.le.trans h.inf_eq.le)
  rw [Bool.not_not, ← h.isMoleculeIn_sup.2.2.2.2] at key
  exact key

theorem coe_boundary_eq (hkS : (k : WithBot ℕ∞) ≤ krullDim S)
    (hkT : (k : WithBot ℕ∞) ≤ krullDim T) : (P.boundary R k α : Set P) =
      ((P.boundary T k α : Set P) \ P.interior (S ⊓ T)) ∪ P.boundary S k α := by
  have hS := h.isMoleculeIn_left
  have hT := h.isMoleculeIn_right
  have hdW : krullDim (S ⊓ T : LowerSet P) = k := by
    rw [h.inf_eq]
    exact hS.krullDim_boundary hkS (!α)
  have hclosed : IsLowerSet ((P.boundary T k α : Set P) \ P.interior (S ⊓ T)) :=
    h.isSubmoleculeOf_inf.isLowerSet_diff_interior (hdW.trans (hT.krullDim_boundary hkT α).symm)
  have hbdry : (P.properBoundary (S ⊓ T) : Set P) ⊆ P.boundary S k α := by
    rw [h.inf_eq]
    exact hS.isGlobular.properBoundary_boundary_le_boundary k α (!α)
  have hDS : (P.boundary T k α : Set P) \ S = (P.boundary T k α : Set P) \ (S ⊓ T) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, fun hxST => hx.2 hxST.1⟩,
      fun hx => ⟨hx.1, fun hxS => hx.2 ⟨hxS, boundary_le T k α hx.1⟩⟩⟩
  rw [h.isMoleculeIn_sup.2.2.2.2, sup_comm S,
    boundary_sup_eq_lowerClosure_sdiff_sup (krullDim_boundary_le T k α), LowerSet.coe_sup, hDS]
  apply subset_antisymm
  · refine union_subset_union_left _ fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := mem_lowerClosure.1 hx
    exact hclosed hxy (sdiff_subset_sdiff_right (P.interior_subset _) hy)
  · rintro x (⟨hxD, hxi⟩ | hx)
    · by_cases hxW : x ∈ S ⊓ T
      · exact Or.inr (hbdry (not_not.1 fun hb => hxi ⟨hxW, hb⟩))
      · exact Or.inl (subset_lowerClosure ⟨hxD, hxW⟩)
    · exact Or.inr hx

theorem inf_boundary_eq_left (hkS : (k : WithBot ℕ∞) ≤ krullDim S)
    (hkT : (k : WithBot ℕ∞) ≤ krullDim T) : S ⊓ P.boundary R k α = P.boundary S k α := by
  have hbdry : (P.properBoundary (S ⊓ T) : Set P) ⊆ P.boundary S k α := by
    rw [h.inf_eq]
    exact h.isMoleculeIn_left.isGlobular.properBoundary_boundary_le_boundary k α (!α)
  refine le_antisymm ?_ (le_inf (boundary_le S k α) ?_)
  · rintro x ⟨hxS, hxR⟩
    have hxR' : x ∈ (P.boundary R k α : Set P) := hxR
    rw [h.coe_boundary_eq hkS hkT] at hxR'
    rcases hxR' with ⟨hxT, hxi⟩ | hx
    · have hxW : x ∈ S ⊓ T :=
        h.inf_boundary_right ▸ (⟨hxS, hxT⟩ : x ∈ S ⊓ P.boundary T k α)
      exact hbdry (not_not.1 fun hb => hxi ⟨hxW, hb⟩)
    · exact hx
  · intro x hx
    have hx' : x ∈ ((P.boundary T k α : Set P) \ P.interior (S ⊓ T)) ∪ P.boundary S k α :=
      Or.inr hx
    rw [← h.coe_boundary_eq hkS hkT] at hx'
    exact hx'

theorem sup_right (hUT : IsMoleculeIn P (U ⊔ T)) (hSU : S ⊓ U ≤ T)
    (hsub : P.IsSubmoleculeOf (P.boundary T k α) (P.boundary (U ⊔ T) k α)) :
    P.IsPastingAtIn k α S (U ⊔ T) (U ⊔ R) := by
  have hinf : S ⊓ (U ⊔ T) = S ⊓ T := by
    rw [inf_sup_left, sup_eq_right.2 (le_inf inf_le_left hSU)]
  refine ⟨h.isMoleculeIn_left, hUT, ?_, by rw [hinf, h.inf_eq], ?_⟩
  · rw [h.eq_sup, sup_left_comm]
  · rw [hinf]
    exact h.isSubmoleculeOf_inf.trans hsub

theorem isGenPastingIn_cond :
    P.IsGenPastingIn k (cond α T S) (cond α S T) ∧
      cond α T S ⊓ P.boundary (cond α T S ⊔ cond α S T) k false ≤
        P.boundary (cond α T S) k false ∧
      cond α S T ⊓ P.boundary (cond α T S ⊔ cond α S T) k true ≤
        P.boundary (cond α S T) k true := by
  have hS := h.isSubmoleculeOf_left
  have hT := h.isSubmoleculeOf_right
  have hmeet : P.IsSubmoleculeOf (S ⊓ T) (P.boundary S k (!α)) := by
    rw [h.inf_eq]
    exact IsSubmoleculeOf.refl (h.isMoleculeIn_left.boundary k (!α))
  have hnot : P.IsSubmoleculeOf (P.boundary T k (!α)) (P.boundary R k (!α)) := by
    rw [h.boundary_not]
    exact IsSubmoleculeOf.refl (h.isMoleculeIn_right.boundary k (!α))
  have hleft := h.isSubmoleculeOf_boundary_left
  rw [h.eq_sup] at hS hT hnot hleft
  cases α
  · exact ⟨⟨h.isMoleculeIn_left, h.isMoleculeIn_right, hmeet, h.isSubmoleculeOf_inf, hleft, hnot⟩,
      hS.inf_boundary_le k false, hT.inf_boundary_le k true⟩
  · rw [sup_comm S T] at hS hT hnot hleft
    rw [inf_comm] at hmeet
    exact ⟨⟨h.isMoleculeIn_right, h.isMoleculeIn_left,
      by rw [inf_comm]; exact h.isSubmoleculeOf_inf, hmeet, hnot, hleft⟩,
      hT.inf_boundary_le k false, hS.inf_boundary_le k true⟩

end IsPastingAtIn

theorem IsPastingAtIn.map (f : P ⟶ Q) [IsInclusion f] (h : P.IsPastingAtIn k α S T R) :
    Q.IsPastingAtIn k α (map f S) (map f T) (map f R) where
  isMoleculeIn_left := (isMoleculeIn_map_iff f S).2 h.isMoleculeIn_left
  isMoleculeIn_right := (isMoleculeIn_map_iff f T).2 h.isMoleculeIn_right
  eq_sup := by rw [h.eq_sup, map_sup]
  inf_eq := by rw [← map_inf, h.inf_eq, map_boundary]
  isSubmoleculeOf_inf := by
    rw [← map_inf, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 h.isSubmoleculeOf_inf

theorem IsGenPastingIn.map (f : P ⟶ Q) [IsInclusion f] (h : P.IsGenPastingIn k A B) :
    Q.IsGenPastingIn k (map f A) (map f B) where
  isMoleculeIn_left := (isMoleculeIn_map_iff f A).2 h.isMoleculeIn_left
  isMoleculeIn_right := (isMoleculeIn_map_iff f B).2 h.isMoleculeIn_right
  inf_isSubmoleculeOf_left := by
    rw [← map_inf, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 h.inf_isSubmoleculeOf_left
  inf_isSubmoleculeOf_right := by
    rw [← map_inf, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 h.inf_isSubmoleculeOf_right
  boundary_isSubmoleculeOf_left := by
    rw [← map_sup, ← map_boundary, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 h.boundary_isSubmoleculeOf_left
  boundary_isSubmoleculeOf_right := by
    rw [← map_sup, ← map_boundary, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 h.boundary_isSubmoleculeOf_right

theorem isPastingAtIn_dual (J : ℕ → Bool) :
    (dual P J).IsPastingAtIn k α S T R ↔ P.IsPastingAtIn k (xor (J (k + 1)) α) S T R :=
  ⟨fun h => ⟨(isMoleculeIn_dual J).1 h.isMoleculeIn_left,
      (isMoleculeIn_dual J).1 h.isMoleculeIn_right, h.eq_sup,
      by rw [h.inf_eq, boundary_dual, Bool.xor_not],
      by simpa only [boundary_dual, isSubmoleculeOf_dual] using h.isSubmoleculeOf_inf⟩,
    fun h => ⟨(isMoleculeIn_dual J).2 h.isMoleculeIn_left,
      (isMoleculeIn_dual J).2 h.isMoleculeIn_right, h.eq_sup,
      by rw [h.inf_eq, boundary_dual, Bool.xor_not],
      by simpa only [boundary_dual, isSubmoleculeOf_dual] using h.isSubmoleculeOf_inf⟩⟩

theorem isGenPastingIn_dual_iff (J : ℕ → Bool) :
    (dual P J).IsGenPastingIn k A B ↔
      P.IsGenPastingIn k (cond (J (k + 1)) B A) (cond (J (k + 1)) A B) := by
  cases hJ : J (k + 1) <;>
  · constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
    try refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [isMoleculeIn_dual, isSubmoleculeOf_dual, boundary_dual, hJ, cond_false, cond_true,
        Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true] at h1 h2 h3 h4 h5 h6 ⊢
      first
      | assumption
      | simpa only [inf_comm] using h3
      | simpa only [inf_comm] using h4
      | simpa only [sup_comm] using h5
      | simpa only [sup_comm] using h6

namespace IsPastingAtIn

theorem isPastingIn_of_inf_eq (h : P.IsPastingAtIn k α S T R) (he : S ⊓ T = P.boundary T k α) :
    P.IsPastingIn k (cond α T S) (cond α S T) R :=
  (isPastingIn_cond_iff α).2 ⟨(sup_comm T S).trans h.eq_sup.symm, (inf_comm T S).trans h.inf_eq,
    (inf_comm T S).trans he⟩

theorem boundary_eq_left_of_inf_eq (h : P.IsPastingAtIn k α S T R)
    (he : S ⊓ T = P.boundary T k α) : P.boundary R k α = P.boundary S k α :=
  (h.isPastingIn_of_inf_eq he).boundary_cond α

theorem assoc_right (h₁ : P.IsPastingAtIn k α S T (S ⊔ T))
    (h₂ : P.IsPastingAtIn k α (S ⊔ T) U R) :
    P.IsPastingAtIn k α T U (T ⊔ U) ∧ P.IsPastingAtIn k α S (T ⊔ U) R := by
  have hb := h₁.boundary_not
  have hTU : T ⊓ U = P.boundary T k (!α) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxT, hxU⟩
      have hx' : x ∈ (S ⊔ T) ⊓ U := ⟨Or.inr hxT, hxU⟩
      rwa [h₂.inf_eq, hb] at hx'
    · intro x hx
      have hx' : x ∈ (S ⊔ T) ⊓ U := by
        rw [h₂.inf_eq, hb]
        exact hx
      exact ⟨boundary_le T k (!α) hx, hx'.2⟩
  have h₃ : P.IsPastingAtIn k α T U (T ⊔ U) :=
    ⟨h₁.isMoleculeIn_right, h₂.isMoleculeIn_right, rfl, hTU, by
      have hsub := h₂.isSubmoleculeOf_inf
      rwa [h₂.inf_eq, hb, ← hTU] at hsub⟩
  have hSTU : S ⊓ (T ⊔ U) = S ⊓ T := by
    refine le_antisymm ?_ (inf_le_inf_left S le_sup_left)
    rintro x ⟨hxS, hxTU⟩
    rcases hxTU with hxT | hxU
    · exact ⟨hxS, hxT⟩
    · have hx' : x ∈ (S ⊔ T) ⊓ U := ⟨Or.inl hxS, hxU⟩
      rw [h₂.inf_eq, hb] at hx'
      exact ⟨hxS, boundary_le T k (!α) hx'⟩
  refine ⟨h₃, h₁.isMoleculeIn_left, h₃.isMoleculeIn, by rw [h₂.eq_sup, sup_assoc],
    by rw [hSTU]; exact h₁.inf_eq, ?_⟩
  rw [hSTU]
  exact h₁.isSubmoleculeOf_inf.trans h₃.isSubmoleculeOf_boundary_left

theorem assoc_left (h₁ : P.IsPastingAtIn k α S T (S ⊔ T)) (h₃ : P.IsPastingAtIn k α T U (T ⊔ U))
    (h₂ : P.IsPastingAtIn k α S (T ⊔ U) R) : P.IsPastingAtIn k α (S ⊔ T) U R := by
  have hb := h₁.boundary_not
  have hSTU : (S ⊔ T) ⊓ U = T ⊓ U := by
    refine le_antisymm ?_ (inf_le_inf_right U le_sup_right)
    rintro x ⟨hxST, hxU⟩
    refine ⟨?_, hxU⟩
    rcases hxST with hxS | hxT
    · have hx' : x ∈ S ⊓ (T ⊔ U) := ⟨hxS, Or.inr hxU⟩
      rw [h₂.inf_eq, ← h₁.inf_eq] at hx'
      exact hx'.2
    · exact hxT
  refine ⟨h₁.isMoleculeIn, h₃.isMoleculeIn_right, by rw [h₂.eq_sup, sup_assoc],
    by rw [hSTU, h₃.inf_eq, hb], ?_⟩
  rw [hSTU]
  exact h₃.isSubmoleculeOf_inf

end IsPastingAtIn

namespace IsPastingAtIn

variable (h : P.IsPastingAtIn k α S T R)
include h

theorem inf_le_boundary_of_lt (hkn : k < n) (β : Bool) : S ⊓ T ≤ P.boundary T n β :=
  h.isSubmoleculeOf_inf.le.trans (h.isMoleculeIn_right.isGlobular.boundary_le_boundary hkn α β)

theorem boundary_eq_sup_of_lt (hkn : k < n) (hdS : krullDim S ≤ n) (β : Bool) :
    P.boundary R n β = S ⊔ P.boundary T n β := by
  rw [h.eq_sup]
  exact boundary_sup_eq_sup_boundary hdS (h.inf_le_boundary_of_lt hkn β)

theorem inf_boundary_of_lt (hkn : k < n) (β : Bool) : S ⊓ P.boundary T n β = S ⊓ T :=
  le_antisymm (inf_le_inf_left S (boundary_le T n β))
    (le_inf inf_le_left (h.inf_le_boundary_of_lt hkn β))

theorem isPastingAtIn_boundary_of_lt (hkn : k < n) (β : Bool) :
    P.IsPastingAtIn k α S (P.boundary T n β) (S ⊔ P.boundary T n β) :=
  ⟨h.isMoleculeIn_left, h.isMoleculeIn_right.boundary n β, rfl,
    (h.inf_boundary_of_lt hkn β).trans h.inf_eq, by
      rw [h.inf_boundary_of_lt hkn β, h.isMoleculeIn_right.isGlobular k n hkn α β]
      exact h.isSubmoleculeOf_inf⟩

theorem isPastingIn_sup {Y Z : LowerSet P} (hp : P.IsPastingIn n Y Z T) (hY : IsMoleculeIn P Y)
    (hZ : IsMoleculeIn P Z) (hkn : k < n) (hdS : krullDim S ≤ n) :
    P.IsPastingIn n (S ⊔ Y) (S ⊔ Z) R ∧ P.IsPastingAtIn k α S Y (S ⊔ Y) ∧
      P.IsPastingAtIn k α S Z (S ⊔ Z) := by
  have hbY (γ : Bool) : P.boundary T k γ = P.boundary Y k γ :=
    hp.boundary_eq_of_lt_cond false hZ.isGlobular hY.isGlobular hkn γ
  have hbZ (γ : Bool) : P.boundary T k γ = P.boundary Z k γ :=
    hp.boundary_eq_of_lt_cond true hY.isGlobular hZ.isGlobular hkn γ
  have hST : S ⊓ T ≤ P.boundary T k α := h.isSubmoleculeOf_inf.le
  have key {A : LowerSet P} (hA : IsMoleculeIn P A) (hAT : A ≤ T)
      (hbA : ∀ γ, P.boundary T k γ = P.boundary A k γ) :
      S ⊓ A = S ⊓ T ∧ P.IsPastingAtIn k α S A (S ⊔ A) := by
    have hSA : S ⊓ A = S ⊓ T := by
      refine le_antisymm (inf_le_inf_left S hAT) fun x hx => ⟨hx.1, ?_⟩
      have hx' := hST hx
      rw [hbA α] at hx'
      exact boundary_le A k α hx'
    exact ⟨hSA, h.isMoleculeIn_left, hA, rfl, hSA.trans h.inf_eq, by
      rw [hSA, ← hbA α]
      exact h.isSubmoleculeOf_inf⟩
  obtain ⟨-, hpY⟩ := key hY hp.left_le hbY
  obtain ⟨-, hpZ⟩ := key hZ hp.right_le hbZ
  have hmeet : (S ⊔ Y) ⊓ (S ⊔ Z) = S ⊔ (Y ⊓ Z) := (sup_inf_left S Y Z).symm
  refine ⟨⟨?_, ?_, ?_⟩, hpY, hpZ⟩
  · rw [h.eq_sup, ← hp.sup_eq]
    exact (sup_sup_distrib_left S Y Z).symm
  · rw [hmeet, hp.inf_eq_output, hpY.boundary_eq_sup_of_lt hkn hdS true]
  · rw [hmeet, hp.inf_eq_input, hpZ.boundary_eq_sup_of_lt hkn hdS false]

end IsPastingAtIn

theorem isPastingAtIn_of_isPastingIn_not {P : OGP.{u}} {k : ℕ} {α : Bool}
    {S T R Y Z : LowerSet P} (h : P.IsPastingAtIn k α S T R) (hY : IsMoleculeIn P Y)
    (hp : P.IsPastingIn k (cond (!α) Y Z) (cond (!α) Z Y) T) :
    S ⊓ Y = S ⊓ T ∧ P.IsPastingAtIn k α S Y (S ⊔ Y) ∧
      P.IsPastingIn k (cond (!α) (S ⊔ Y) Z) (cond (!α) Z (S ⊔ Y)) R := by
  obtain ⟨hYZ, hi₁, hi₂⟩ := (isPastingIn_cond_iff (!α)).1 hp
  have hbT : P.boundary T k α = P.boundary Y k α := by
    have e := ((isPastingIn_cond_comm (!α)).1 hp).boundary_cond (!!α)
    rwa [Bool.not_not] at e
  have hST : S ⊓ T ≤ P.boundary Y k α := hbT ▸ h.inf_le_boundary
  have hSY : S ⊓ Y = S ⊓ T :=
    le_antisymm (inf_le_inf_left S (hYZ ▸ le_sup_left))
      fun x hx => ⟨hx.1, boundary_le Y k α (hST hx)⟩
  have hpY : P.IsPastingAtIn k α S Y (S ⊔ Y) :=
    ⟨h.isMoleculeIn_left, hY, rfl, hSY.trans h.inf_eq, by
      rw [hSY, ← hbT]; exact h.isSubmoleculeOf_inf⟩
  have hmeet : (S ⊔ Y) ⊓ Z = Y ⊓ Z := by
    refine le_antisymm ?_ (inf_le_inf_right Z le_sup_right)
    rintro x ⟨hxS | hxY, hxZ⟩
    · exact ⟨boundary_le Y k α (hST ⟨hxS, hYZ ▸ Or.inr hxZ⟩), hxZ⟩
    · exact ⟨hxY, hxZ⟩
  refine ⟨hSY, hpY, (isPastingIn_cond_iff (!α)).2 ⟨?_, hmeet.trans hi₁, ?_⟩⟩
  · rw [h.eq_sup, ← hYZ, sup_assoc]
  · rw [hmeet, hi₂, hpY.boundary_not]

theorem IsPastingAtIn.isPastingAtIn_boundary_and_isPastingIn_sup_boundary {P : OGP.{u}} {k : ℕ}
    {α : Bool} {S T R : LowerSet P} (h : P.IsPastingAtIn k α S T R) :
    P.IsPastingAtIn k α S (P.boundary T k α) (S ⊔ P.boundary T k α) ∧
      P.IsPastingIn k (cond α T (S ⊔ P.boundary T k α)) (cond α (S ⊔ P.boundary T k α) T) R := by
  have hSB : S ⊓ P.boundary T k α = S ⊓ T := h.inf_boundary_right
  have hBT : P.boundary T k α ≤ T := boundary_le T k α
  have hpB : P.IsPastingAtIn k α S (P.boundary T k α) (S ⊔ P.boundary T k α) :=
    ⟨h.isMoleculeIn_left, h.isMoleculeIn_right.boundary k α, rfl, hSB.trans h.inf_eq, by
      rw [hSB, boundary_boundary_of_le le_rfl]; exact h.isSubmoleculeOf_inf⟩
  have hmeet : T ⊓ (S ⊔ P.boundary T k α) = P.boundary T k α := by
    rw [inf_sup_left, inf_eq_right.2 hBT, inf_comm, sup_eq_right.2 h.inf_le_boundary]
  refine ⟨hpB, (isPastingIn_cond_iff α).2 ⟨?_, ?_, hmeet⟩⟩
  · rw [h.eq_sup]
    exact le_antisymm (sup_le le_sup_right (sup_le le_sup_left (hBT.trans le_sup_right)))
      (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
  · rw [hmeet, hpB.boundary_not, boundary_boundary_of_le le_rfl]

theorem IsPastingAtIn.swap_of_lt {P : OGP.{u}} {j n : ℕ} {α β : Bool}
    {U A R₁ Y R : LowerSet P} (h₁ : P.IsPastingAtIn n α U A R₁)
    (h₂ : P.IsPastingAtIn j β Y R₁ R) (hjn : j < n) (hdY : Order.krullDim Y ≤ n) :
    P.boundary A j β = P.boundary R₁ j β ∧ Y ⊓ A = Y ⊓ R₁ ∧
      P.IsPastingAtIn j β Y A (Y ⊔ A) ∧ P.IsPastingAtIn n α U (Y ⊔ A) R := by
  have hA := h₁.isMoleculeIn_right
  have hb : P.boundary A j β = P.boundary R₁ j β := by
    rw [← hA.isGlobular j n hjn β (!α), ← h₁.isMoleculeIn.isGlobular j n hjn β (!α),
      h₁.boundary_not]
  have hYA : Y ⊓ A = Y ⊓ R₁ :=
    le_antisymm (inf_le_inf_left Y h₁.right_le)
      fun x hx => ⟨hx.1, boundary_le A j β (hb ▸ h₂.inf_le_boundary hx)⟩
  have hp : P.IsPastingAtIn j β Y A (Y ⊔ A) :=
    ⟨h₂.isMoleculeIn_left, hA, rfl, hYA.trans h₂.inf_eq, by
      rw [hYA, hb]; exact h₂.isSubmoleculeOf_inf⟩
  have hUY : U ⊓ Y ≤ U ⊓ A := fun x hx =>
    ⟨hx.1, (hYA ▸ (⟨hx.2, h₁.left_le hx.1⟩ : x ∈ Y ⊓ R₁) : x ∈ Y ⊓ A).2⟩
  have hU : U ⊓ (Y ⊔ A) = U ⊓ A := by
    rw [inf_sup_left, sup_eq_right.2 hUY]
  refine ⟨hb, hYA, hp, ⟨h₁.isMoleculeIn_left, hp.isMoleculeIn, ?_, hU.trans h₁.inf_eq, ?_⟩⟩
  · rw [h₂.eq_sup, h₁.eq_sup]
    exact sup_left_comm _ _ _
  · rw [hU, hp.boundary_eq_sup_of_lt hjn hdY α]
    exact h₁.isSubmoleculeOf_inf.trans
      (hp.isPastingAtIn_boundary_of_lt hjn α).isSubmoleculeOf_right

namespace IsGenPastingIn

variable {V E : LowerSet P}

theorem isPastingAtIn_right_of_isPastingIn (hg : P.IsGenPastingIn k U V)
    (iV : V ⊓ P.boundary (U ⊔ V) k true ≤ P.boundary V k true) (hE : IsMoleculeIn P E)
    (hp : P.IsPastingIn k (U ⊔ V) E R) : P.IsPastingAtIn k false V E (V ⊔ E) := by
  have hVE : V ⊓ E = P.boundary V k true := by
    have h : V ⊓ E = V ⊓ ((U ⊔ V) ⊓ E) := by
      rw [← inf_assoc, inf_eq_left.2 (le_sup_right : V ≤ U ⊔ V)]
    rw [h, hp.inf_eq_output]
    exact le_antisymm iV (le_inf (boundary_le _ _ _) hg.boundary_isSubmoleculeOf_right.le)
  refine ⟨hg.isMoleculeIn_right, hE, rfl, hVE, ?_⟩
  rw [hVE, ← hp.inf_eq_input, hp.inf_eq_output]
  exact hg.boundary_isSubmoleculeOf_right

theorem isPastingAtIn_left_of_isPastingIn (hg : P.IsGenPastingIn k U V)
    (iU : U ⊓ P.boundary (U ⊔ V) k false ≤ P.boundary U k false)
    (iV : V ⊓ P.boundary (U ⊔ V) k true ≤ P.boundary V k true) (hE : IsMoleculeIn P E)
    (hp : P.IsPastingIn k (U ⊔ V) E R) (hkU : (k : WithBot ℕ∞) ≤ krullDim U) :
    P.IsPastingAtIn k false U (V ⊔ E) R := by
  have hM := hg.isMoleculeIn iU iV
  have c1 := hg.isPastingAtIn_right_of_isPastingIn iV hE hp
  have hUb : U ⊓ P.boundary (U ⊔ V) k false = P.boundary U k false :=
    le_antisymm iU (le_inf (boundary_le _ _ _) hg.boundary_isSubmoleculeOf_left.le)
  have cU : P.IsPastingAtIn k true U (P.boundary (U ⊔ V) k false)
      (U ⊔ P.boundary (U ⊔ V) k false) :=
    ⟨hg.isMoleculeIn_left, hM.boundary k false, rfl, hUb, by
      rw [hUb, boundary_eq_self (krullDim_boundary_le _ _ _)]
      exact hg.boundary_isSubmoleculeOf_left⟩
  have hkB : (k : WithBot ℕ∞) ≤ krullDim (P.boundary (U ⊔ V) k false) :=
    (hM.krullDim_boundary (hkU.trans (LowerSet.krullDim_mono le_sup_left)) false).ge
  have hU' := cU.inf_boundary_eq_left hkU hkB
  have hpc := isPastingIn_sup_boundary hg.inf_isSubmoleculeOf_left.le
    hg.inf_isSubmoleculeOf_right.le
  have hUE : U ⊓ E = U ⊓ P.boundary (U ⊔ V) k true := by
    rw [← hp.inf_eq_output, ← inf_assoc, inf_eq_left.2 (le_sup_left : U ≤ U ⊔ V)]
  have h1 : U ⊓ (V ⊔ P.boundary (U ⊔ V) k true) = U ⊓ ((U ⊔ P.boundary (U ⊔ V) k false) ⊓
      (V ⊔ P.boundary (U ⊔ V) k true)) := by
    rw [← inf_assoc, inf_eq_left.2 (le_sup_left : U ≤ U ⊔ P.boundary (U ⊔ V) k false)]
  have hinf : U ⊓ (V ⊔ E) = P.boundary U k true := by
    rw [inf_sup_left, hUE, ← inf_sup_left, h1, hpc.inf_eq_output, hU']
  refine ⟨hg.isMoleculeIn_left, c1.isMoleculeIn, by rw [← hp.sup_eq, sup_assoc], hinf, ?_⟩
  rw [hinf, c1.isMoleculeIn_sup.2.2.2.2, ← hp.inf_eq_input, hp.inf_eq_output,
    ← hpc.inf_eq_input, hpc.inf_eq_output]
  exact cU.isSubmoleculeOf_boundary_left

end IsGenPastingIn

end Atoms.Molecule.OGP
