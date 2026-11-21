import Atoms.Molecule.Rewritable.Basic
import Atoms.Molecule.Construction.GrayProductMolecule

universe u

open Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

variable {P Q : OGP.{u}}

theorem isSubmoleculeOf_prod_boundary_left {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (k : ℕ) (γ : Bool) :
    (grayProduct P Q).IsSubmoleculeOf (P.boundary U k γ ×ˢ V) (U ×ˢ V) := by
  obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
  obtain ⟨n, hn⟩ := hV.exists_krullDim_eq
  have h := isSubmoleculeOf_boundary_prod_boundary_left hU hV (m + n) k γ
  rwa [boundary_prod_eq_self hm.le hn.le le_rfl,
    boundary_prod_eq_self ((LowerSet.krullDim_mono (boundary_le U k γ)).trans hm.le)
      hn.le le_rfl] at h

theorem isSubmoleculeOf_prod_cond_left (α : Bool) {k : ℕ} {A B U : LowerSet P}
    {V : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B) (hV : IsMoleculeIn Q V)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    (grayProduct P Q).IsSubmoleculeOf (B ×ˢ V) (U ×ˢ V) := by
  have hU := hp.isMoleculeIn (Bool.cond_rec_prop α hA hB) (Bool.cond_rec_prop α hB hA)
  obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
  obtain ⟨n, hn⟩ := hV.exists_krullDim_eq
  rcases hp.lt_or_eq_boundary α with ⟨hAU, hBU⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · have h := isSubmoleculeOf_boundary_prod_cond_left α hA hB hAU hBU hV hp (m + n)
    rwa [boundary_prod_eq_self hm.le hn.le le_rfl,
      boundary_prod_eq_self ((LowerSet.krullDim_mono hBU.le).trans hm.le) hn.le le_rfl] at h
  · exact .refl (isMoleculeIn_prod hU hV)
  · exact isSubmoleculeOf_prod_boundary_left hU hV k α

theorem isSubmoleculeOf_prod_left {X U : LowerSet P} {V : LowerSet Q}
    (h : P.IsSubmoleculeOf X U) (hV : IsMoleculeIn Q V) :
    (grayProduct P Q).IsSubmoleculeOf (X ×ˢ V) (U ×ˢ V) := by
  have hX := h.isMoleculeIn
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact .refl (isMoleculeIn_prod hX hV)
  | tail _ hYU ih =>
    obtain ⟨k, α, W, hp, hY, hW⟩ := hYU
    exact ih.trans (isSubmoleculeOf_prod_cond_left α hW hY hV hp)

theorem isSubmoleculeOf_prod_right {U : LowerSet P} {X V : LowerSet Q}
    (hU : IsMoleculeIn P U) (h : Q.IsSubmoleculeOf X V) :
    (grayProduct P Q).IsSubmoleculeOf (U ×ˢ X) (U ×ˢ V) := by
  have h' := isSubmoleculeOf_prod_left ((isSubmoleculeOf_dual Nat.bodd).2 h)
    ((isMoleculeIn_dual Nat.bodd).2 hU)
  rwa [← isSubmoleculeOf_map_iff (grayProductSwap P Q).inv, map_grayProductSwap_inv_prod,
    map_grayProductSwap_inv_prod, isSubmoleculeOf_dual] at h'

theorem bdryFull_prod {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) :
    (grayProduct P Q).bdryFull (U ×ˢ V) = P.bdryFull U ×ˢ V ⊔ U ×ˢ Q.bdryFull V := by
  rw [← (isMoleculeIn_prod hU hV).properBoundary_eq_bdryFull, ← hU.properBoundary_eq_bdryFull,
    ← hV.properBoundary_eq_bdryFull]
  obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
  obtain ⟨n, hn⟩ := hV.exists_krullDim_eq
  have hmn := krullDim_prod hm hn
  refine SetLike.ext fun ⟨a, b⟩ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, hk, α, hab⟩ := mem_properBoundary.1 h
    have hk' : k < m + n := by exact_mod_cast hmn ▸ hk
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hU.isGlobular hV.isGlobular).1 hab
    by_cases him : i < m
    · exact Or.inl ⟨mem_properBoundary.2 ⟨i, hm ▸ Nat.cast_lt.2 him, α, ha⟩,
        boundary_le V _ _ hb⟩
    · exact Or.inr ⟨boundary_le U _ _ ha,
        mem_properBoundary.2 ⟨k - i, hn ▸ Nat.cast_lt.2 (by omega), _, hb⟩⟩
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨i, hi, α, ha⟩ := mem_properBoundary.1 ha
      have hi' : i < m := by exact_mod_cast hm ▸ hi
      refine mem_properBoundary.2 ⟨i + n, hmn ▸ Nat.cast_lt.2 (by omega), α,
        (mem_boundary_prod_of_isGlobular hU.isGlobular hV.isGlobular).2 ⟨i, by omega, ha, ?_⟩⟩
      rw [Nat.add_sub_cancel_left, boundary_eq_self hn.le]
      exact hb
    · obtain ⟨j, hj, γ, hb⟩ := mem_properBoundary.1 hb
      have hj' : j < n := by exact_mod_cast hn ▸ hj
      refine mem_properBoundary.2 ⟨m + j, hmn ▸ Nat.cast_lt.2 (by omega), xor m.bodd γ,
        (mem_boundary_prod_of_isGlobular hU.isGlobular hV.isGlobular).2 ⟨m, by omega, ?_, ?_⟩⟩
      · rw [boundary_eq_self hm.le]
        exact ha
      · rw [Nat.add_sub_cancel_left, Bool.xor_xor_cancel_left]
        exact hb

theorem interior_prod {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) :
    (grayProduct P Q).interior (U ×ˢ V) = P.interior U ×ˢ Q.interior V := by
  ext ⟨a, b⟩
  change ((a, b) : grayProduct P Q) ∈ (grayProduct P Q).interior (U ×ˢ V) ↔ _
  rw [OGP.mem_interior, Set.mem_prod, OGP.mem_interior, OGP.mem_interior,
    (isMoleculeIn_prod hU hV).properBoundary_eq_bdryFull, hU.properBoundary_eq_bdryFull,
    hV.properBoundary_eq_bdryFull, bdryFull_prod hU hV, LowerSet.mem_sup_iff,
    LowerSet.mem_prod, LowerSet.mem_prod, LowerSet.mem_prod]
  tauto

theorem mem_bdryFull_diff_interior_prod (hP : IsMolecule P) (hQ : IsMolecule Q)
    {X : LowerSet P} {Y : LowerSet Q} (hX : IsMoleculeIn P X) (hY : IsMoleculeIn Q Y) {a : P}
    {b : Q} :
    ((a, b) : grayProduct P Q) ∈ (grayProduct P Q).bdryFull ⊤ ∧
        ((a, b) : grayProduct P Q) ∉ (grayProduct P Q).interior (X ×ˢ Y) ↔
      (a ∈ P.bdryFull ⊤ ∨ b ∈ Q.bdryFull ⊤) ∧ ¬(a ∈ P.interior X ∧ b ∈ Q.interior Y) := by
  rw [interior_prod hX hY, ← LowerSet.top_prod_top, bdryFull_prod hP hQ]
  simp

theorem isSubmoleculeOf_boundary_prod_top (hP : IsMolecule P) (hQ : IsMolecule Q)
    {n k : ℕ} (hk : k ≤ n) (α : Bool) :
    (grayProduct P Q).IsSubmoleculeOf
      (P.boundary ⊤ k α ×ˢ Q.boundary ⊤ (n - k) (xor k.bodd α))
      ((grayProduct P Q).boundary ⊤ n α) := by
  have := isSubmoleculeOf_prod_boundary_boundary hP hQ hk α
  rwa [LowerSet.top_prod_top] at this

theorem isRewritableSubmolecule_prod_left (hP : IsAtom P) (hQ : IsAtom Q) {α : Bool}
    {W : LowerSet P} (hW : P.IsRewritableSubmolecule W (P.bdry ⊤ α)) :
    (grayProduct P Q).IsRewritableSubmolecule (W ×ˢ (⊤ : LowerSet Q))
      ((grayProduct P Q).bdry ⊤ α) := by
  have hp := krullDim_pos_of_isSubmoleculeOf_bdry hW.isSubmoleculeOf
  obtain ⟨m, hm⟩ := hP.isMoleculeIn.exists_krullDim_eq
  obtain ⟨n, hn⟩ := hQ.isMoleculeIn.exists_krullDim_eq
  have hm0 : 0 < m := by rw [hm] at hp; exact_mod_cast hp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hm' : krullDim (⊤ : LowerSet P) = k + 1 := by rw [hm]; push_cast; rfl
  have hmn : krullDim (⊤ : LowerSet (grayProduct P Q)) = ((k + n) + 1 : ℕ) := by
    rw [← LowerSet.top_prod_top, krullDim_prod hm hn]
    exact_mod_cast Nat.add_right_comm k 1 n
  have hmn' : krullDim (⊤ : LowerSet (grayProduct P Q)) = (k + n : ℕ) + 1 := by
    rw [hmn]; push_cast; rfl
  have hbdP := bdry_eq_boundary hm' α
  have hbdPQ := bdry_eq_boundary hmn' α
  have ht := isSubmoleculeOf_boundary_prod_top hP.isMoleculeIn hQ.isMoleculeIn
    (Nat.le_add_right k n) α
  rw [Nat.add_sub_cancel_left, boundary_eq_self hn.le] at ht
  refine ⟨?_, ?_, isRound_prod hW.isRound hQ.isRound⟩
  · rw [hbdPQ]
    exact (isSubmoleculeOf_prod_left (hbdP ▸ hW.isSubmoleculeOf) hQ.isMoleculeIn).trans ht
  · have hdW : krullDim W = k :=
      hW.krullDim_eq.trans (hP.isMoleculeIn.krullDim_bdry hm α)
    rw [krullDim_prod hdW hn,
      (isMolecule_grayProduct hP.isMoleculeIn hQ.isMoleculeIn).krullDim_bdry hmn α]

theorem isRewritableSubmolecule_prod_right {n : ℕ} (hQ : IsAtom Q) (hdQ : krullDim Q = n)
    (hP : IsAtom P) {α : Bool} {W : LowerSet P}
    (hW : P.IsRewritableSubmolecule W (P.bdry ⊤ α)) :
    (grayProduct Q P).IsRewritableSubmolecule ((⊤ : LowerSet Q) ×ˢ W)
      ((grayProduct Q P).bdry ⊤ (xor n.bodd α)) := by
  obtain ⟨m, hm⟩ := hP.isMoleculeIn.exists_krullDim_eq
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_add_one_of_ne_zero (by
    rintro rfl
    exact absurd (hm ▸ krullDim_pos_of_isSubmoleculeOf_bdry hW.isSubmoleculeOf) (lt_irrefl _))
  have hm' : krullDim (⊤ : LowerSet P) = k + 1 := by rw [hm]; push_cast; rfl
  have hnm : krullDim (⊤ : LowerSet (grayProduct Q P)) = (n + k : ℕ) + 1 := by
    rw [← LowerSet.top_prod_top, krullDim_prod (by rwa [LowerSet.krullDim_top]) hm]
    push_cast
    exact (add_assoc _ _ _).symm
  have h := isRewritableSubmolecule_prod_left ((isAtomIn_dual Nat.bodd).2 hP)
    ((isAtomIn_dual Nat.bodd).2 hQ)
    (α := xor (k + 1).bodd α) (by rwa [bdry_dual Nat.bodd hm', Bool.xor_xor_cancel_left,
      isRewritableSubmolecule_dual])
  rwa [← isRewritableSubmolecule_map_iff (grayProductSwap Q P).inv, map_bdry,
    map_grayProductSwap_inv_prod, ← LowerSet.top_prod_top, map_grayProductSwap_inv_prod,
    LowerSet.top_prod_top, bdry_dual Nat.bodd hnm, isRewritableSubmolecule_dual, add_assoc,
    Nat.bodd_add n, Bool.xor_assoc, Bool.xor_xor_cancel_left] at h

theorem hornSet_prod_left (hP : IsAtom P) (hQ : IsAtom Q) {α : Bool} {W : LowerSet P}
    (hW : P.IsRewritableSubmolecule W (P.bdry ⊤ α)) :
    (isRewritableSubmolecule_prod_left hP hQ hW).hornSet
        (isMolecule_grayProduct hP.isMoleculeIn hQ.isMoleculeIn)
        (isAtom_grayProduct hP hQ).isRound =
      hW.hornSet hP.isMoleculeIn hP.isRound ×ˢ (⊤ : LowerSet Q) ⊔
        (⊤ : LowerSet P) ×ˢ Q.bdryFull ⊤ := by
  refine SetLike.ext fun ⟨a, b⟩ => (mem_bdryFull_diff_interior_prod hP.isMoleculeIn
    hQ.isMoleculeIn hW.isSubmoleculeOf.isMoleculeIn hQ.isMoleculeIn).trans ?_
  change _ ↔ (a ∈ P.bdryFull ⊤ ∧ a ∉ P.interior W) ∧ b ∈ (⊤ : LowerSet Q) ∨
    a ∈ (⊤ : LowerSet P) ∧ b ∈ Q.bdryFull ⊤
  rw [OGP.mem_interior (P := Q), hQ.isMoleculeIn.properBoundary_eq_bdryFull]
  by_cases hq : b ∈ Q.bdryFull ⊤ <;> simp [hq]

theorem hornSet_prod_right {n : ℕ} (hQ : IsAtom Q) (hdQ : krullDim Q = n) (hP : IsAtom P)
    {α : Bool} {W : LowerSet P} (hW : P.IsRewritableSubmolecule W (P.bdry ⊤ α)) :
    (isRewritableSubmolecule_prod_right hQ hdQ hP hW).hornSet
        (isMolecule_grayProduct hQ.isMoleculeIn hP.isMoleculeIn)
        (isAtom_grayProduct hQ hP).isRound =
      Q.bdryFull ⊤ ×ˢ (⊤ : LowerSet P) ⊔
        (⊤ : LowerSet Q) ×ˢ hW.hornSet hP.isMoleculeIn hP.isRound := by
  refine SetLike.ext fun ⟨a, b⟩ => (mem_bdryFull_diff_interior_prod hQ.isMoleculeIn
    hP.isMoleculeIn hQ.isMoleculeIn hW.isSubmoleculeOf.isMoleculeIn).trans ?_
  change _ ↔ a ∈ Q.bdryFull ⊤ ∧ b ∈ (⊤ : LowerSet P) ∨
    a ∈ (⊤ : LowerSet Q) ∧ (b ∈ P.bdryFull ⊤ ∧ b ∉ P.interior W)
  rw [OGP.mem_interior (P := Q), hQ.isMoleculeIn.properBoundary_eq_bdryFull]
  by_cases hq : a ∈ Q.bdryFull ⊤ <;> simp [hq]

theorem isRewritableSubmolecule_globe_one (β : Bool) :
    (globe.{u} 1).IsRewritableSubmolecule (LowerSet.Iic (pole β))
      ((globe.{u} 1).bdry ⊤ β) := by
  rw [← bdry_globe_one]
  exact isRewritableSubmolecule_bdry_self (isAtom_globe 1).isMoleculeIn (isAtom_globe 1).isRound
    (by rw [LowerSet.krullDim_top, krullDim_globe]; rfl) β

theorem hornSet_globe_one (β : Bool) :
    (isRewritableSubmolecule_globe_one.{u} β).hornSet
        (isAtom_globe 1).isMoleculeIn (isAtom_globe 1).isRound =
      LowerSet.Iic (pole (!β)) := by
  have hn : krullDim (⊤ : LowerSet (globe.{u} 1)) = (0 : ℕ) + 1 := by
    rw [LowerSet.krullDim_top, krullDim_globe]; rfl
  have hB : (globe.{u} 1).IsSubmoleculeOf
      ((globe.{u} 1).bdry ⊤ (!!β)) ((globe.{u} 1).bdry ⊤ (!!β)) :=
    .refl ((isAtom_globe 1).isMoleculeIn.bdry (by rw [hn]; exact_mod_cast Nat.zero_lt_one) _)
  refine (SetLike.coe_injective (congrArg
      (fun V => ((globe.{u} 1).bdryFull ⊤ : Set (globe.{u} 1)) \ (globe.{u} 1).interior V)
      (by rw [Bool.not_not, bdry_globe_one]))).trans
    ((IsSubmoleculeOf.hornSet_bdry (isAtom_globe 1).isMoleculeIn (isAtom_globe 1).isRound
      hn hB rfl).trans (bdry_globe_one (!β)))

theorem bdryFull_globe_one :
    (globe.{u} 1).bdryFull ⊤ = LowerSet.Iic (pole false) ⊔ LowerSet.Iic (pole true) := by
  rw [bdryFull, bdry_globe_one, bdry_globe_one]

theorem isGenPastingIn_prod_pasteAt {k ℓ : ℕ} (α : Bool)
    {W U : LowerSet P} {V : LowerSet Q} (hW : IsMoleculeIn P W) (hU : IsMoleculeIn P U)
    (hV : IsMoleculeIn Q V) (hdW : Order.krullDim W ≤ (k + 1 : ℕ))
    (hc : P.IsPastingAtIn k α W U (W ⊔ U)) :
    (grayProduct P Q).IsGenPastingIn (k + ℓ)
      (cond α ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (!α))
        (W ×ˢ Q.boundary V ℓ (xor (k + 1).bodd (!α))))
      (cond α (W ×ˢ Q.boundary V ℓ (xor (k + 1).bodd (!α)))
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (!α))) := by
  set Y := Q.boundary V ℓ (xor (k + 1).bodd (!α)) with hY
  set M := W ⊔ P.boundary U k α with hMdef
  have mY : IsMoleculeIn Q Y := hV.boundary _ _
  have hU' := hc.isMoleculeIn
  have hsub := hc.isSubmoleculeOf_boundary
  have hWU := hc.inf_le_boundary
  have hWD : W ⊓ P.boundary U k α ≤ P.boundary W k (!α) :=
    (inf_le_inf_left W (boundary_le U k α)).trans hc.inf_eq.le
  have mM : IsMoleculeIn P M :=
    (hsub.isSubmoleculeOf_sup hW (krullDim_boundary_le U k α) hWD).isMoleculeIn_right
  have hp : P.IsPastingIn k (cond α U M) (cond α M U) (W ⊔ U) := by
    have hUM : U ⊓ M = P.boundary U k α := by
      rw [hMdef, inf_sup_left, inf_comm U W, inf_eq_right.2 (boundary_le U k α),
        sup_eq_right.2 hWU]
    refine (isPastingIn_cond_iff α).2 ⟨?_, hUM.trans (boundary_sup_eq_of_boundary_le
      (krullDim_boundary_le U k α) hWD hsub.le).symm, hUM⟩
    rw [hMdef, ← sup_assoc, sup_comm U W, sup_assoc, sup_eq_left.2 (boundary_le U k α)]
  have hN : k + ℓ < k + 1 + ℓ := by omega
  have hcover := boundary_prod_eq_prod_sup_of_le (ℓ := ℓ) (V := V) hU.isGlobular hU'.isGlobular
    hV.isGlobular (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · rw [← hU'.isGlobular i k hi (!α) (!α), hc.boundary_not, hU.isGlobular i k hi (!α) (!α)]
      · exact hc.boundary_not)
    (fun i hi => hc.boundary_eq_sup_of_lt hi (hdW.trans (by exact_mod_cast hi)) (!α))
  have hmeet := prod_inf_boundary_prod (ℓ := ℓ) (V := V) hU.isGlobular hV.isGlobular hWU
  rw [hc.inf_eq] at hmeet
  have hs : xor (k + 1).bodd (!α) = xor k.bodd α := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not]
  have hYe : Q.boundary Y (k + ℓ - k) (xor k.bodd (!α)) = Y := by
    rw [Nat.add_sub_cancel_left]; exact boundary_eq_self (krullDim_boundary_le V ℓ _) _
  have hglob (γ : Bool) : (grayProduct P Q).boundary
      ((grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + 1 + ℓ) (!α)) (k + ℓ) γ =
      (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + ℓ) γ :=
    isGlobular_prod hU'.isGlobular hV.isGlobular _ _ hN γ (!α)
  refine isGenPastingIn_cond α (isMoleculeIn_prod hW mY)
    ((isMoleculeIn_prod hU hV).boundary _ _) ?_ ?_ ?_ ?_
  · rw [hmeet]
    have h := isSubmoleculeOf_prod_boundary_boundary hW mY (Nat.le_add_right k ℓ) (!α)
    rwa [hYe] at h
  · rw [hmeet, isGlobular_prod hU.isGlobular hV.isGlobular _ _ hN α (!α)]
    have h := isSubmoleculeOf_prod_boundary_boundary hU hV (Nat.le_add_right k ℓ) α
    rw [Nat.add_sub_cancel_left, ← hs] at h
    exact (isSubmoleculeOf_prod_left hsub mY).trans h
  · rw [← hcover, hglob]
    have hr := isSubmoleculeOf_boundary_prod_boundary_right hU' hV (k + ℓ) ℓ α
    rw [show xor (k + ℓ + ℓ).bodd α = xor (k + 1).bodd (!α) by
      rw [hs, show k + ℓ + ℓ = k + 2 * ℓ by omega]; simp [Nat.bodd_add]] at hr
    exact ((isSubmoleculeOf_boundary_prod_sup_left hW (krullDim_boundary_le U k α)
      (le_antisymm hWD (le_inf (boundary_le W k (!α)) hsub.le)) hsub mY
      (krullDim_boundary_le V ℓ _) le_rfl α).trans
      (isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn α hU mM mY hp (k + ℓ))).trans hr
  · rw [← hcover, hglob, isGlobular_prod hU.isGlobular hV.isGlobular _ _ hN (!α) (!α)]
    exact isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn (!α) mM hU hV
      ((isPastingIn_cond_comm α).1 hp) (k + ℓ)

private theorem isSubmoleculeOf_boundary_prod_genPasting (α : Bool) {k d : ℕ}
    {A B : LowerSet P} {V : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B)
    (hV : IsMoleculeIn Q V) (hdV : Order.krullDim V ≤ d)
    (hAB : A ⊓ B ≤ P.boundary A k (!α)) (hBA : A ⊓ B ≤ P.boundary B k α)
    (sA : P.IsSubmoleculeOf (P.boundary A k α) (P.boundary (A ⊔ B) k α))
    (sB : P.IsSubmoleculeOf (P.boundary B k (!α)) (P.boundary (A ⊔ B) k (!α)))
    (iA : A ⊓ P.boundary (A ⊔ B) k α ≤ P.boundary A k α)
    (iB : B ⊓ P.boundary (A ⊔ B) k (!α) ≤ P.boundary B k (!α)) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (A ×ˢ V) (k + d) α)
      ((grayProduct P Q).boundary ((A ⊔ B) ×ˢ V) (k + d) α) := by
  have mA := (sA.isSubmoleculeOf_sup hA (krullDim_boundary_le _ k α) iA).isMoleculeIn_right
  have mB := (sB.isSubmoleculeOf_sup hB (krullDim_boundary_le _ k (!α)) iB).isMoleculeIn_right
  have hK := isSubmoleculeOf_boundary_prod_sup_left (α := !α) (X := V) (n := k + d) hA
    (krullDim_boundary_le _ k α)
    (by rw [Bool.not_not]; exact le_antisymm iA (le_inf (boundary_le A k α) sA.le))
    (by rw [Bool.not_not]; exact sA) hV hdV le_rfl α
  exact hK.trans (isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn α mB mA hV
    (isPastingIn_sup_boundary_cond α hAB hBA) (k + d))

theorem isGenPastingIn_prod_left {k d : ℕ} {A B : LowerSet P}
    {V : LowerSet Q} (hV : IsMoleculeIn Q V) (hdV : Order.krullDim V ≤ d)
    (h : P.IsGenPastingIn k A B) (iA : A ⊓ P.boundary (A ⊔ B) k false ≤ P.boundary A k false)
    (iB : B ⊓ P.boundary (A ⊔ B) k true ≤ P.boundary B k true) :
    (grayProduct P Q).IsGenPastingIn (k + d) (A ×ˢ V) (B ×ˢ V) := by
  have hVe (γ : Bool) : Q.boundary V (k + d - k) γ = V := by
    rw [Nat.add_sub_cancel_left]; exact boundary_eq_self hdV γ
  have term (C : LowerSet P) (hC : IsMoleculeIn P C) (γ : Bool)
      (hs : P.IsSubmoleculeOf (A ⊓ B) (P.boundary C k γ)) :
      (grayProduct P Q).IsSubmoleculeOf ((A ×ˢ V) ⊓ (B ×ˢ V))
        ((grayProduct P Q).boundary (C ×ˢ V) (k + d) γ) := by
    have t := isSubmoleculeOf_prod_boundary_boundary hC hV (Nat.le_add_right k d) γ
    rw [hVe] at t
    rw [← LowerSet.inf_prod]
    exact (isSubmoleculeOf_prod_left hs hV).trans t
  have hm := h.isMoleculeIn_left
  have hm' := h.isMoleculeIn_right
  refine ⟨isMoleculeIn_prod hm hV, isMoleculeIn_prod hm' hV,
    term A hm true h.inf_isSubmoleculeOf_left, term B hm' false h.inf_isSubmoleculeOf_right, ?_, ?_⟩
  · rw [← LowerSet.sup_prod]
    exact isSubmoleculeOf_boundary_prod_genPasting false hm hm' hV hdV
      h.inf_isSubmoleculeOf_left.le h.inf_isSubmoleculeOf_right.le h.boundary_isSubmoleculeOf_left
      h.boundary_isSubmoleculeOf_right iA iB
  · rw [← LowerSet.sup_prod, sup_comm A B]
    rw [sup_comm A B] at iA iB
    have hs := h.boundary_isSubmoleculeOf_right
    have hs' := h.boundary_isSubmoleculeOf_left
    rw [sup_comm A B] at hs hs'
    exact isSubmoleculeOf_boundary_prod_genPasting true hm' hm hV hdV
      ((inf_comm B A).trans_le h.inf_isSubmoleculeOf_right.le)
      ((inf_comm B A).trans_le h.inf_isSubmoleculeOf_left.le) hs hs' iB iA

theorem isGenPastingIn_prod_right {k d : ℕ} {A B : LowerSet Q}
    {U : LowerSet P} (hU : IsMoleculeIn P U) (hdU : Order.krullDim U ≤ d)
    (h : Q.IsGenPastingIn k A B) (iA : A ⊓ Q.boundary (A ⊔ B) k false ≤ Q.boundary A k false)
    (iB : B ⊓ Q.boundary (A ⊔ B) k true ≤ Q.boundary B k true) :
    (grayProduct P Q).IsGenPastingIn (k + d) (cond d.bodd (U ×ˢ B) (U ×ˢ A))
      (cond d.bodd (U ×ˢ A) (U ×ˢ B)) := by
  set c := (k + 1).bodd with hc
  clear_value c
  have hd : d.bodd = xor c (k + d + 1).bodd := by
    rw [hc, show k + d + 1 = k + 1 + d by omega, Nat.bodd_add (k + 1) d]
    cases (k + 1).bodd <;> simp
  have h' : (OGP.dual Q Nat.bodd).IsGenPastingIn k (cond c B A) (cond c A B) :=
    (isGenPastingIn_dual_iff Nat.bodd).2 (by rw [← hc]; cases c <;> exact h)
  have iA' : cond c B A ⊓ (OGP.dual Q Nat.bodd).boundary (cond c B A ⊔ cond c A B) k false ≤
      (OGP.dual Q Nat.bodd).boundary (cond c B A) k false := by
    rw [boundary_dual, boundary_dual, ← hc]
    cases c
    · exact iA
    · rw [cond_true, cond_true, sup_comm]; exact iB
  have iB' : cond c A B ⊓ (OGP.dual Q Nat.bodd).boundary (cond c B A ⊔ cond c A B) k true ≤
      (OGP.dual Q Nat.bodd).boundary (cond c A B) k true := by
    rw [boundary_dual, boundary_dual, ← hc]
    cases c
    · exact iB
    · rw [cond_true, cond_true, sup_comm]; exact iA
  have hp := OGP.IsGenPastingIn.map (grayProductSwap P Q).inv (isGenPastingIn_prod_left
    ((isMoleculeIn_dual Nat.bodd).2 hU) hdU h' iA' iB')
  rw [map_grayProductSwap_inv_prod, map_grayProductSwap_inv_prod, isGenPastingIn_dual_iff] at hp
  rw [hd]
  generalize (k + d + 1).bodd = c' at hp ⊢
  cases c <;> cases c' <;> exact hp

private theorem cond_cond_xor {β : Type*} (c a : Bool) (x y : β) :
    cond c (cond a y x) (cond a x y) = cond (xor c a) x y := by
  cases c <;> cases a <;> rfl

theorem isGenPastingIn_prod_pasteAt_right {k ℓ : ℕ} (α : Bool)
    {W V : LowerSet Q} {U : LowerSet P} (hW : IsMoleculeIn Q W) (hV : IsMoleculeIn Q V)
    (hU : IsMoleculeIn P U) (hdW : Order.krullDim W ≤ (k + 1 : ℕ))
    (hc : Q.IsPastingAtIn k α W V (W ⊔ V)) :
    (grayProduct P Q).IsGenPastingIn (k + ℓ)
      (cond (xor ℓ.bodd α) ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (xor ℓ.bodd α))
        (P.boundary U ℓ (xor ℓ.bodd α) ×ˢ W))
      (cond (xor ℓ.bodd α) (P.boundary U ℓ (xor ℓ.bodd α) ×ˢ W)
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (xor ℓ.bodd α))) := by
  have h := OGP.IsGenPastingIn.map (grayProductSwap P Q).inv (isGenPastingIn_prod_pasteAt (ℓ := ℓ)
    (xor (k + 1).bodd α) ((isMoleculeIn_dual Nat.bodd).2 hW) ((isMoleculeIn_dual Nat.bodd).2 hV)
    ((isMoleculeIn_dual Nat.bodd).2 hU) hdW (isPastingAtIn_dual_bodd hc))
  rw [Bool.apply_cond (OGP.map _), Bool.apply_cond (OGP.map _), isGenPastingIn_dual_iff,
    cond_cond_xor, cond_cond_xor, map_grayProductSwap_inv_boundary_prod,
    map_grayProductSwap_inv_prod, boundary_dual] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

end Atoms.Molecule.OGP
