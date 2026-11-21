import Atoms.Molecule.Construction.Suspension
import Atoms.Molecule.RegularComplex.Comap

universe u v

open Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

def globeFace : (n k : ℕ) → k < n → Bool → globe.{u} n
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, α => pole α
  | n + 1, k + 1, h, α => susp (globeFace n k (Nat.lt_of_succ_lt_succ h) α)

@[simp] theorem globeFace_zero {n : ℕ} (h : 0 < n + 1) (α : Bool) :
    globeFace.{u} (n + 1) 0 h α = pole α :=
  rfl

@[simp] theorem globeFace_succ {n k : ℕ} (h : k + 1 < n + 1) (α : Bool) :
    globeFace.{u} (n + 1) (k + 1) h α = susp (globeFace n k (Nat.lt_of_succ_lt_succ h) α) :=
  rfl

theorem grade_globeFace : (n k : ℕ) → (hk : k < n) → (α : Bool) →
    grade ℕ (globeFace.{u} n k hk α) = k
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, α => grade_pole α
  | n + 1, k + 1, h, α => by
    rw [globeFace_succ]
    exact congrArg (· + 1) (grade_globeFace n k _ α)

theorem boundary_globe : (n k : ℕ) → (hk : k < n) → (α : Bool) →
    (globe.{u} n).boundary ⊤ k α = .Iic (globeFace n k hk α)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _, α => by
    rw [globeFace_zero, ← susp_top]
    exact boundary_susp_zero (P := globe n) ⟨⊤, LowerSet.mem_top⟩ α
  | n + 1, k + 1, h, α => by
    have ih := boundary_globe n k (Nat.lt_of_succ_lt_succ h) α
    rw [globeFace_succ, ← susp_top, ← susp_Iic, ← ih]
    exact boundary_susp_succ (P := globe n) (by rw [ih]; exact ⟨_, le_rfl⟩)

theorem globeFace_le_globeFace_iff : (n j k : ℕ) → (hj : j < n) → (hk : k < n) → (β α : Bool) →
    (globeFace.{u} n j hj β ≤ globeFace n k hk α ↔ j < k ∨ j = k ∧ β = α)
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, 0, _, _, β, α => (pole_le_pole (X := globe n)).trans (by simp)
  | n + 1, 0, _ + 1, _, _, β, _ =>
    iff_of_true (pole_le_susp (X := globe n) β _) (Or.inl (Nat.succ_pos _))
  | n + 1, _ + 1, 0, _, _, _, α =>
    iff_of_false (not_susp_le_pole (X := globe n) _ α) (by omega)
  | n + 1, j + 1, k + 1, hj, hk, β, α => by
    rw [globeFace_succ, globeFace_succ, susp_le_susp, globeFace_le_globeFace_iff n j k,
      Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

theorem not_top_le_globeFace {n k : ℕ} (hk : k < n) (α : Bool) :
    ¬ (⊤ : globe.{u} n) ≤ globeFace n k hk α := fun h => by
  have := grade_mono (𝕆 := ℕ) h
  rw [grade_top_globe, grade_globeFace] at this
  omega

theorem eq_top_or_exists_eq_globeFace : (n : ℕ) → (y : globe.{u} n) →
    y = ⊤ ∨ ∃ (k : ℕ) (hk : k < n) (α : Bool), y = globeFace n k hk α
  | 0, y => Or.inl (le_antisymm le_top (isMin_point ⊤ le_top))
  | n + 1, pole α => Or.inr ⟨0, n.succ_pos, α, rfl⟩
  | n + 1, susp z => by
    rcases eq_top_or_exists_eq_globeFace n z with rfl | ⟨k, hk, α, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, α, rfl⟩

theorem interior_globe (n : ℕ) : (globe.{u} n).interior ⊤ = {⊤} := by
  rw [← LowerSet.Iic_top]
  exact (isRDC_of_isMolecule (isAtom_globe n).isMoleculeIn ⊤).interior_Iic

theorem interior_boundary_globe {n k : ℕ} (hk : k < n) (α : Bool) :
    (globe.{u} n).interior ((globe n).boundary ⊤ k α) = {globeFace n k hk α} := by
  rw [boundary_globe n k hk α]
  exact (isRDC_of_isMolecule (isAtom_globe n).isMoleculeIn _).interior_Iic

variable {P : OGP.{u}}

private theorem isComap_of_le_globeFace_iff {n : ℕ} (hP : IsMolecule P)
    (hd : krullDim (⊤ : LowerSet P) = n) {c : P → globe.{v} n}
    (hkey : ∀ x k (hk : k < n) α, c x ≤ globeFace n k hk α ↔ x ∈ P.boundary ⊤ k α) :
    IsComap c := by
  have hG : krullDim (⊤ : LowerSet (globe.{v} n)) = n := by
    rw [LowerSet.krullDim_top, krullDim_globe]
  have hmono : Monotone c := fun x y hxy => by
    rcases eq_top_or_exists_eq_globeFace n (c y) with h | ⟨k, hk, α, h⟩
    · rw [h]
      exact le_top
    · rw [h, hkey]
      exact (P.boundary ⊤ k α).lower hxy ((hkey y k hk α).1 h.le)
  have hL (k : ℕ) (α : Bool) :
      lowerPreimage hmono ((globe n).boundary ⊤ k α) = P.boundary ⊤ k α := by
    rcases lt_or_ge k n with hk | hk
    · rw [boundary_globe n k hk α]
      exact SetLike.ext fun x => hkey x k hk α
    · rw [boundary_eq_self (hG.trans_le (by exact_mod_cast hk)),
        boundary_eq_self (hd.trans_le (by exact_mod_cast hk)), lowerPreimage_top]
  have hIic (y : globe n) : ∃ k α, LowerSet.Iic y = (globe n).boundary ⊤ k α := by
    rcases eq_top_or_exists_eq_globeFace n y with rfl | ⟨k, hk, α, rfl⟩
    · exact ⟨n, true, by rw [LowerSet.Iic_top, boundary_eq_self hG.le]⟩
    · exact ⟨k, α, (boundary_globe n k hk α).symm⟩
  have hgG := (isAtom_globe.{v} n).isMoleculeIn.isGlobular
  refine ⟨hmono, fun y => ?_, fun y m β => ?_⟩
  · obtain ⟨k, α, h⟩ := hIic y
    rw [h, hL]
    exact hP.boundary k α
  · obtain ⟨k, α, h⟩ := hIic y
    rw [h, hL]
    rcases lt_or_ge m k with hmk | hkm
    · rw [hgG m k hmk β α, hP.isGlobular m k hmk β α, hL]
    · rw [boundary_boundary_of_le hkm, boundary_boundary_of_le hkm, hL]

private theorem exists_mem_boundary_of_mem_boundary_not (hP : IsMolecule P) (hr : P.IsRound ⊤)
    {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim (⊤ : LowerSet P)) {α : Bool} {x : P}
    (hx : x ∈ P.boundary ⊤ k α) (hx' : x ∈ P.boundary ⊤ k (!α)) :
    ∃ j < k, ∃ β, x ∈ P.boundary ⊤ j β := by
  have hxb : x ∈ P.properBoundary (P.boundary ⊤ k α) := by
    rw [← hr.inf_boundary_eq_properBoundary hP hk α]
    exact ⟨hx, hx'⟩
  obtain ⟨j, hj, β, hxj⟩ := mem_properBoundary.1 hxb
  have hjk : j < k := by exact_mod_cast hj.trans_le (krullDim_boundary_le _ k α)
  exact ⟨j, hjk, β, hP.isGlobular j k hjk β α ▸ hxj⟩

private theorem exists_le_globeFace_iff {n : ℕ} (hP : IsMolecule P) (hr : P.IsRound ⊤)
    (hd : krullDim (⊤ : LowerSet P) = n) :
    ∃ c : P → globe.{v} n,
      ∀ x k (hk : k < n) α, c x ≤ globeFace n k hk α ↔ x ∈ P.boundary ⊤ k α := by
  have hy (x : P) : ∃ y : globe.{v} n,
      ∀ k (hk : k < n) α, y ≤ globeFace n k hk α ↔ x ∈ P.boundary ⊤ k α := by
    classical
    have hex : ∃ k, ∃ α, x ∈ P.boundary ⊤ k α :=
      ⟨n, true, by rw [boundary_eq_self hd.le]; exact LowerSet.mem_top⟩
    obtain ⟨m, ⟨s, hs⟩, hmin⟩ : ∃ m, (∃ α, x ∈ P.boundary ⊤ m α) ∧
        ∀ j < m, ∀ β, x ∉ P.boundary ⊤ j β :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj β h => Nat.find_min hex hj ⟨β, h⟩⟩
    have hle {k : ℕ} {α : Bool} (hx : x ∈ P.boundary ⊤ k α) : m ≤ k :=
      not_lt.1 fun hkm => hmin k hkm α hx
    by_cases hmn : m < n
    · refine ⟨globeFace n m hmn s, fun k hk α => ?_⟩
      rw [globeFace_le_globeFace_iff]
      refine ⟨fun h => ?_, fun hx => ?_⟩
      · rcases h with hlt | ⟨rfl, rfl⟩
        · exact hP.isGlobular.boundary_le_boundary hlt s α hs
        · exact hs
      · rcases (hle hx).lt_or_eq with hlt | rfl
        · exact Or.inl hlt
        · refine Or.inr ⟨rfl, by_contra fun hne => ?_⟩
          rw [Bool.eq_not_of_ne (Ne.symm hne)] at hx
          obtain ⟨j, hj, β, hxj⟩ := exists_mem_boundary_of_mem_boundary_not hP hr
            (by rw [hd]; exact_mod_cast hmn) hs hx
          exact hmin j hj β hxj
    · exact ⟨⊤, fun k hk α =>
        iff_of_false (not_top_le_globeFace hk α) fun hx => hmn ((hle hx).trans_lt hk)⟩
  exact ⟨fun x => (hy x).choose, fun x => (hy x).choose_spec⟩

theorem exists_isComap_globe_iff (n : ℕ) :
    (∃ c : P → globe.{v} n, IsComap c) ↔
      IsMolecule P ∧ P.IsRound ⊤ ∧ krullDim (⊤ : LowerSet P) = n := by
  have hG := (isAtom_globe.{v} n).isMoleculeIn
  refine ⟨fun ⟨c, hc⟩ => ⟨hc.isMolecule hG, ?_, ?_⟩, fun ⟨hP, hr, hd⟩ => ?_⟩
  · exact hc.isRound_lowerPreimage hG (isAtom_globe n).isRound
  · rw [← lowerPreimage_top hc.monotone, hc.krullDim_lowerPreimage hG, LowerSet.krullDim_top,
      krullDim_globe]
  · obtain ⟨c, hkey⟩ := exists_le_globeFace_iff.{u, v} hP hr hd
    exact ⟨c, isComap_of_le_globeFace_iff hP hd hkey⟩

theorem IsComap.eq_of_globe {n : ℕ} {c c' : P → globe.{v} n} (hc : IsComap c)
    (hc' : IsComap c') : c = c' := by
  have hG := (isAtom_globe.{v} n).isMoleculeIn
  have hn : krullDim (⊤ : LowerSet P) = n := by
    rw [← lowerPreimage_top hc.monotone, hc.krullDim_lowerPreimage hG, LowerSet.krullDim_top,
      krullDim_globe]
  funext x
  rcases (hc.isMolecule hG).isGlobular.mem_interior_or_exists_mem_interior_boundary
    (LowerSet.mem_top (a := x)) with hx | ⟨k, hk, α, hx⟩
  · have h (d : P → globe.{v} n) (hd : IsComap d) : d x = ⊤ := by
      have e := hd.preimage_interior hG
      rw [interior_globe, lowerPreimage_top] at e
      have hx' : x ∈ d ⁻¹' {⊤} := by rw [e]; exact hx
      exact hx'
    rw [h c hc, h c' hc']
  · have hkn : k < n := by rw [hn] at hk; exact_mod_cast hk
    have h (d : P → globe.{v} n) (hd : IsComap d) : d x = globeFace n k hkn α := by
      have e := hd.preimage_interior_boundary hG k α
      rw [interior_boundary_globe hkn, lowerPreimage_top] at e
      have hx' : x ∈ d ⁻¹' {globeFace n k hkn α} := by rw [e]; exact hx
      exact hx'
    rw [h c hc, h c' hc']

end Atoms.Molecule.OGP
