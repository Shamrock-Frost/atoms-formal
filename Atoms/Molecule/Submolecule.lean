import Atoms.ForMathlib.Data.Bool.Basic
import Atoms.Molecule.Decidable

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable (P : OGP.{u})

def IsAtomIn (U : LowerSet P) : Prop :=
  IsMoleculeIn P U ∧ ∃ t, U = LowerSet.Iic t

def IsAtom : Prop := P.IsAtomIn ⊤

variable {P} {U V W X Y : LowerSet P} {k : ℕ}

theorem IsAtomIn.isMoleculeIn (h : P.IsAtomIn U) : IsMoleculeIn P U := h.1

theorem IsAtomIn.exists_eq_Iic (h : P.IsAtomIn U) : ∃ t, U = LowerSet.Iic t := h.2

theorem isRound_of_krullDim_le_zero (h : krullDim U ≤ 0) : P.IsRound U where
  isGlobular k n _ α β := by
    rw [boundary_eq_self (h.trans (by exact_mod_cast Nat.zero_le n)),
      boundary_eq_self (h.trans (by exact_mod_cast Nat.zero_le k))]
  inf_boundary_zero h' := absurd h (not_le.2 h')
  inf_boundary_succ n h' := absurd h (not_le.2 ((by exact_mod_cast Nat.zero_le _ :
    (0 : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞)).trans_lt h'))

theorem IsPastingIn.ne_Iic (hp : P.IsPastingIn k V W U)
    (hk : (k : WithBot ℕ∞) < min (krullDim V) (krullDim W)) (t : P) : U ≠ LowerSet.Iic t := by
  rintro rfl
  rcases LowerSet.mem_sup_iff.1 (hp.sup_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl) with htV | htW
  · exact (hp.lt_cond false (hk.trans_le (min_le_right _ _))).not_ge (LowerSet.Iic_le.2 htV)
  · exact (hp.lt_cond true (hk.trans_le (min_le_left _ _))).not_ge (LowerSet.Iic_le.2 htW)

theorem isAtomIn_iff : P.IsAtomIn U ↔ (∃ x, IsMin x ∧ U = LowerSet.Iic x) ∨
    ∃ t, P.IsRound (LowerSet.Iic t) ∧ (∀ α, IsMoleculeIn P (P.bdry (LowerSet.Iic t) α)) ∧
      U = LowerSet.Iic t := by
  constructor
  · rintro ⟨hm, t, ht⟩
    cases hm with
    | point x hx => exact Or.inl ⟨x, hx, rfl⟩
    | atom t' hr hb => exact Or.inr ⟨t', hr, hb, rfl⟩
    | paste k V W U hp _ _ hk => exact absurd ht (hp.ne_Iic hk t)
  · rintro (⟨x, hx, rfl⟩ | ⟨t, hr, hb, rfl⟩)
    · exact ⟨.point x hx, x, rfl⟩
    · exact ⟨.atom t hr hb, t, rfl⟩

theorem IsAtomIn.isRound (h : P.IsAtomIn U) : P.IsRound U := by
  rcases isAtomIn_iff.1 h with ⟨x, hx, rfl⟩ | ⟨t, hr, -, rfl⟩
  · exact isRound_of_krullDim_le_zero (LowerSet.krullDim_Iic_of_isMin hx).le
  · exact hr

theorem IsMoleculeIn.isAtomIn_Iic (h : IsMoleculeIn P U) {x : P} (hx : x ∈ U) :
    P.IsAtomIn (LowerSet.Iic x) := by
  induction h with
  | point y hy =>
    obtain rfl : x = y := le_antisymm hx (hy hx)
    exact ⟨.point x hy, x, rfl⟩
  | atom t hr hb ih =>
    rcases (LowerSet.mem_Iic_iff.1 hx).eq_or_lt with rfl | hlt
    · exact ⟨.atom x hr hb, x, rfl⟩
    · rw [← Set.mem_Iio, ← coe_bdry_Iic_sup, SetLike.mem_coe, LowerSet.mem_sup_iff] at hlt
      exact hlt.elim (ih false) (ih true)
  | paste k V W U hp _ _ _ ihV ihW => exact (LowerSet.mem_sup_iff.1 (hp.sup_eq ▸ hx)).elim ihV ihW

theorem IsMoleculeIn.bdry (h : IsMoleculeIn P U) (hd : 0 < krullDim U) (α : Bool) :
    IsMoleculeIn P (P.bdry U α) := by
  obtain ⟨n, hn⟩ := h.exists_krullDim_eq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by rintro rfl; simp [hn] at hd)
  rw [bdry_eq_boundary (by rw [hn]; push_cast; rfl)]
  exact h.boundary m α

theorem IsMoleculeIn.nonempty_faces (h : IsMoleculeIn P U) {x : P} (hx : x ∈ U)
    (hd : 0 < grade ℕ x) (α : Bool) : (P.faces α x).Nonempty := by
  have hb := (h.isAtomIn_Iic hx).isMoleculeIn.bdry
    (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hd) α
  obtain ⟨y, hy⟩ := hb.nonempty
  rw [bdry_Iic, SetLike.mem_coe, mem_lowerClosure] at hy
  obtain ⟨z, hz, -⟩ := hy
  exact ⟨z, hz⟩

variable (P) in
def IsPastingFactorOf (X U : LowerSet P) : Prop :=
  ∃ (k : ℕ) (α : Bool) (Y : LowerSet P), P.IsPastingIn k (cond α Y X) (cond α X Y) U ∧
    IsMoleculeIn P X ∧ IsMoleculeIn P Y

variable (P) in
def IsSubmoleculeOf (X U : LowerSet P) : Prop :=
  IsMoleculeIn P U ∧ Relation.ReflTransGen (P.IsPastingFactorOf) X U

theorem IsPastingIn.isPastingFactorOf (α : Bool) {A B : LowerSet P} (hB : IsMoleculeIn P B)
    (hA : IsMoleculeIn P A) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    P.IsPastingFactorOf B U :=
  ⟨k, α, A, hp, hB, hA⟩

namespace IsPastingFactorOf

theorem isMoleculeIn_left (h : P.IsPastingFactorOf X U) : IsMoleculeIn P X := by
  obtain ⟨-, -, -, -, hX, -⟩ := h
  exact hX

theorem isMoleculeIn_right (h : P.IsPastingFactorOf X U) : IsMoleculeIn P U := by
  obtain ⟨_, α, _, hp, hX, hY⟩ := h
  exact hp.isMoleculeIn (Bool.cond_rec_prop α hY hX) (Bool.cond_rec_prop α hX hY)

theorem le (h : P.IsPastingFactorOf X U) : X ≤ U := by
  obtain ⟨_, α, _, hp, -⟩ := h
  exact ((isPastingIn_cond_iff α).1 hp).1 ▸ le_sup_right

theorem isSubmoleculeOf (h : P.IsPastingFactorOf X U) : P.IsSubmoleculeOf X U :=
  ⟨h.isMoleculeIn_right, .single h⟩

end IsPastingFactorOf

namespace IsSubmoleculeOf

theorem refl (h : IsMoleculeIn P U) : P.IsSubmoleculeOf U U := ⟨h, .refl⟩

theorem trans (hXV : P.IsSubmoleculeOf X V) (hVU : P.IsSubmoleculeOf V U) :
    P.IsSubmoleculeOf X U :=
  ⟨hVU.1, hXV.2.trans hVU.2⟩

theorem isMoleculeIn_right (h : P.IsSubmoleculeOf X U) : IsMoleculeIn P U := h.1

theorem isMoleculeIn (h : P.IsSubmoleculeOf X U) : IsMoleculeIn P X := by
  rcases h.2.cases_head with rfl | ⟨Y, hXY, -⟩
  · exact h.1
  · exact hXY.isMoleculeIn_left

theorem le (h : P.IsSubmoleculeOf X U) : X ≤ U :=
  Relation.reflTransGen_le_of_le (r := (· ≤ ·)) (fun _ _ h => h.le) _ _ h.2

theorem tail (hXY : P.IsSubmoleculeOf X Y) (hYU : P.IsPastingFactorOf Y U) :
    P.IsSubmoleculeOf X U :=
  hXY.trans hYU.isSubmoleculeOf

theorem exists_isPastingFactorOf_of_ne (h : P.IsSubmoleculeOf X U) (hXU : X ≠ U) :
    ∃ Y, P.IsPastingFactorOf Y U ∧ Y ≠ U ∧ P.IsSubmoleculeOf X Y := by
  obtain ⟨hU, hr⟩ := h
  induction hr with
  | refl => exact absurd rfl hXU
  | @tail Y U hXY hYU ih =>
    by_cases hY : Y = U
    · subst hY
      exact ih hXU hU
    · exact ⟨Y, hYU, hY, hYU.isMoleculeIn_left, hXY⟩

end IsSubmoleculeOf

theorem IsMoleculeIn.boundary_isSubmoleculeOf (h : IsMoleculeIn P U) (n : ℕ) (α : Bool) :
    P.IsSubmoleculeOf (P.boundary U n α) U := by
  have hle := boundary_le U n α
  have hb (β : Bool) : P.boundary (P.boundary U n α) n β = P.boundary U n α :=
    boundary_eq_self (krullDim_boundary_le U n α) β
  exact (IsPastingIn.isPastingFactorOf α (h.boundary n α) h ((isPastingIn_cond_iff α).2
    ⟨sup_eq_left.2 hle, by rw [inf_eq_right.2 hle, hb], inf_eq_right.2 hle⟩)).isSubmoleculeOf

theorem IsMoleculeIn.Iic_isSubmoleculeOf (h : IsMoleculeIn P U) {x : P} (hx : x ∈ U) :
    P.IsSubmoleculeOf (LowerSet.Iic x) U := by
  induction h with
  | point y hy =>
    obtain rfl : x = y := le_antisymm hx (hy hx)
    exact .refl (.point x hy)
  | atom t hround hbdry ih =>
    have hU := IsMoleculeIn.atom t hround hbdry
    rcases (LowerSet.mem_Iic_iff.1 hx).eq_or_lt with rfl | hlt
    · exact .refl hU
    obtain ⟨m, hm⟩ : ∃ m, grade ℕ t = m + 1 :=
      ⟨grade ℕ t - 1, by have := grade_strictMono (𝕆 := ℕ) hlt; omega⟩
    obtain ⟨α, hα⟩ : ∃ α, x ∈ P.bdry (.Iic t) α := by
      rw [Bool.exists_bool, ← LowerSet.mem_sup_iff, ← SetLike.mem_coe, coe_bdry_Iic_sup]
      exact hlt
    refine (ih α hα).trans ?_
    rw [bdry_eq_boundary (by rw [LowerSet.krullDim_Iic, hm]; push_cast; rfl)]
    exact hU.boundary_isSubmoleculeOf m α
  | paste k V W U hp hV hW _ ihV ihW =>
    rcases LowerSet.mem_sup_iff.1 (hp.sup_eq ▸ hx) with hx | hx
    · exact (ihV hx).tail (hp.isPastingFactorOf false hV hW)
    · exact (ihW hx).tail (hp.isPastingFactorOf true hW hV)

theorem IsPastingIn.lt_krullDim (hp : P.IsPastingIn k V W U) (hVW : V ≠ W) :
    (k : WithBot ℕ∞) < krullDim U := by
  refine lt_of_not_ge fun hU => hVW ?_
  rw [← boundary_eq_self ((LowerSet.krullDim_mono hp.left_le).trans hU) true,
    ← hp.inf_eq_output, hp.inf_eq_input,
    boundary_eq_self ((LowerSet.krullDim_mono hp.right_le).trans hU) false]

section Decide

variable [Fintype P] [DecidableEq P] [DecidableLE P]

variable (P) in
def submoleculeTest (X : LowerSet P) [DecidablePred (· ∈ X)] (s : Finset P)
    (hs : IsLowerSet (s : Set P)) : Bool :=
  decide (X = ⟨s, hs⟩ ∧ IsMoleculeIn P ⟨s, hs⟩) ||
  decide (∃ k < P.gradeBound, ∃ S ∈ (P.finsetTopsAbove s k).powerset,
    (if h : P.IsPastingIn k (P.pastingPart s hs k S false)
        (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) ⟨s, hs⟩ ∧
      IsMoleculeIn P (P.pastingPart s hs k S false) ∧
      IsMoleculeIn P (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) then
      (if hV : P.pastingPart s hs k S false = ⟨s, hs⟩ then false else
        have := Finset.card_lt_card (filter_mem_ssubset (lt_of_le_of_ne h.1.left_le hV))
        submoleculeTest X (Finset.univ.filter (· ∈ P.pastingPart s hs k S false))
          (isLowerSet_filter_mem _)) ||
      (if hW : P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true = ⟨s, hs⟩ then false else
        have := Finset.card_lt_card (filter_mem_ssubset (lt_of_le_of_ne h.1.right_le hW))
        submoleculeTest X (Finset.univ.filter
          (· ∈ P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true))
          (isLowerSet_filter_mem _))
    else false) = true)
termination_by s.card

theorem isSubmoleculeOf_of_submoleculeTest (X : LowerSet P) [DecidablePred (· ∈ X)]
    (s : Finset P) (hs : IsLowerSet (s : Set P)) (h : P.submoleculeTest X s hs = true) :
    P.IsSubmoleculeOf X ⟨s, hs⟩ := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rw [submoleculeTest] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.dite_else_false, Bool.dite_then_false] at h
  rcases h with ⟨rfl, hm⟩ | ⟨k, -, S, -, ⟨hp, hV, hW⟩, ⟨hne, h⟩ | ⟨hne, h⟩⟩
  · exact .refl hm
  · have hX := ih _ (filter_mem_ssubset (lt_of_le_of_ne hp.left_le hne)) _ h
    rw [mk_filter_mem] at hX
    exact hX.tail (hp.isPastingFactorOf false hV hW)
  · have hX := ih _ (filter_mem_ssubset (lt_of_le_of_ne hp.right_le hne)) _ h
    rw [mk_filter_mem] at hX
    exact hX.tail (hp.isPastingFactorOf true hW hV)

theorem submoleculeTest_of_isSubmoleculeOf {X U : LowerSet P} [DecidablePred (· ∈ X)]
    (h : P.IsSubmoleculeOf X U) (s : Finset P) (hs : IsLowerSet (s : Set P))
    (hsU : (⟨s, hs⟩ : LowerSet P) = U) : P.submoleculeTest X s hs = true := by
  obtain ⟨hU, hr⟩ := h
  induction hr generalizing s with
  | refl =>
    rw [submoleculeTest]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨hsU.symm, by rw [hsU]; exact hU⟩
  | @tail Y U _ hYU ih =>
    by_cases hYU' : Y = U
    · subst hYU'
      exact ih s hs hsU hU
    subst hsU
    classical
    obtain ⟨k, α, Z, hp, hY, hZ⟩ := hYU
    obtain ⟨V, W, hp, hV, hW, hYVW⟩ : ∃ V W, P.IsPastingIn k V W ⟨s, hs⟩ ∧ IsMoleculeIn P V ∧
        IsMoleculeIn P W ∧ (Y = V ∨ Y = W) := by
      cases α
      · exact ⟨Y, Z, hp, hY, hZ, Or.inl rfl⟩
      · exact ⟨Z, Y, hp, hZ, hY, Or.inr rfl⟩
    have hVW : V ≠ W := fun h => hYU' (by
      rw [← hp.sup_eq, ← h, sup_idem]
      exact hYVW.elim id (·.trans h.symm))
    have hkb : k < P.gradeBound := by
      exact_mod_cast (hp.lt_krullDim hVW).trans_le (krullDim_le_gradeBound _)
    rw [submoleculeTest]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.dite_else_false, Bool.dite_then_false]
    refine Or.inr ⟨k, hkb, (P.finsetTopsAbove s k).filter (· ∈ V),
      Finset.mem_powerset.2 (Finset.filter_subset _ _), by
        rw [hp.pastingPart_filter_cond false, hp.pastingPart_sdiff_filter]; exact ⟨hp, hV, hW⟩, ?_⟩
    rcases hYVW with rfl | rfl
    · exact .inl ⟨by rwa [hp.pastingPart_filter_cond false],
        ih _ _ (by rw [mk_filter_mem, hp.pastingPart_filter_cond false]) hY⟩
    · exact .inr ⟨by rwa [hp.pastingPart_sdiff_filter],
        ih _ _ (by rw [mk_filter_mem, hp.pastingPart_sdiff_filter]) hY⟩

theorem submoleculeTest_eq_true_iff (X : LowerSet P) [DecidablePred (· ∈ X)] (s : Finset P)
    (hs : IsLowerSet (s : Set P)) :
    P.submoleculeTest X s hs = true ↔ P.IsSubmoleculeOf X ⟨s, hs⟩ :=
  ⟨isSubmoleculeOf_of_submoleculeTest X s hs,
    fun h => submoleculeTest_of_isSubmoleculeOf h s hs rfl⟩

variable (P) in
def isSplitFinset (k : ℕ) (v w s : Finset P) : Bool :=
  decide (v ∪ w = s ∧ v ∩ w = P.boundaryFinset v k true ∧ v ∩ w = P.boundaryFinset w k false)

theorem isSplitFinset_eq_true_iff {k : ℕ} {v w s : Finset P} (hv : IsLowerSet (v : Set P))
    (hw : IsLowerSet (w : Set P)) (hs : IsLowerSet (s : Set P)) :
    P.isSplitFinset k v w s = true ↔ P.IsPastingIn k ⟨v, hv⟩ ⟨w, hw⟩ ⟨s, hs⟩ := by
  have hsup : v ∪ w = s ↔ (⟨v, hv⟩ ⊔ ⟨w, hw⟩ : LowerSet P) = ⟨s, hs⟩ := by
    rw [SetLike.ext'_iff (A := LowerSet P), LowerSet.coe_sup, ← Finset.coe_inj, Finset.coe_union]
    rfl
  have hinf {u : Finset P} (hu : IsLowerSet (u : Set P)) (α : Bool) :
      v ∩ w = P.boundaryFinset u k α ↔
        (⟨v, hv⟩ ⊓ ⟨w, hw⟩ : LowerSet P) = P.boundary ⟨u, hu⟩ k α := by
    rw [SetLike.ext'_iff (A := LowerSet P), LowerSet.coe_inf, ← Finset.coe_inj, Finset.coe_inter,
      coe_boundaryFinset hu]
    rfl
  rw [isSplitFinset, decide_eq_true_iff, hsup, hinf hv, hinf hw]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun h => ⟨h.sup_eq, h.inf_eq_output, h.inf_eq_input⟩⟩

variable (P) in
def fastSubmoleculeTestAux (X : LowerSet P) [DecidablePred (· ∈ X)] : ℕ → Finset P → Bool
  | 0, _ => false
  | n + 1, s =>
    (decide (∀ x, x ∈ X ↔ x ∈ s) && P.fastMoleculeTest s) ||
    decide (∃ k < P.gradeBound, ∃ S ∈ (P.finsetTopsAbove s k).powerset,
      (P.isSplitFinset k (P.pastingPartFinset s k S false)
          (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) s &&
        ((decide (P.pastingPartFinset s k S false ≠ s) &&
            decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k S false)) ||
          (decide (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true ≠ s) &&
            decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true))) &&
        P.fastMoleculeTest (P.pastingPartFinset s k S false) &&
        P.fastMoleculeTest (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) &&
        ((decide (P.pastingPartFinset s k S false ≠ s) &&
            (decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k S false) &&
              fastSubmoleculeTestAux X n (P.pastingPartFinset s k S false))) ||
          (decide (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true ≠ s) &&
            (decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) &&
              fastSubmoleculeTestAux X n
                (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true))))) = true)

theorem fastSubmoleculeTestAux_eq_submoleculeTest (X : LowerSet P) [DecidablePred (· ∈ X)]
    {n : ℕ} {s : Finset P} (hs : IsLowerSet (s : Set P)) (hn : s.card < n) :
    P.fastSubmoleculeTestAux X n s = P.submoleculeTest X s hs := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
  have hrec {t : Finset P} (ht : IsLowerSet (t : Set P)) (hts : t ⊂ s) :
      P.fastSubmoleculeTestAux X n t = P.submoleculeTest X t ht :=
    ih ht (by have := Finset.card_lt_card hts; omega)
  have hne (V : LowerSet P) [DecidablePred (· ∈ V)] :
      decide (Finset.univ.filter (· ∈ V) ≠ s) = decide (V ≠ ⟨s, hs⟩) := by
    simp [SetLike.ext_iff]
  have hwhole : (decide (∀ x, x ∈ X ↔ x ∈ s) && P.fastMoleculeTest s) =
      decide (X = ⟨s, hs⟩ ∧ IsMoleculeIn P ⟨s, hs⟩) := by
    rw [Bool.decide_and]
    congr 1
    · exact decide_eq_decide.2 (SetLike.ext_iff (p := X) (q := (⟨s, hs⟩ : LowerSet P))).symm
    · exact Bool.eq_iff_iff.2 ((fastMoleculeTest_eq_true_iff s hs).trans decide_eq_true_iff.symm)
  have hpaste (k : ℕ) (S : Finset P) :
      (P.isSplitFinset k (P.pastingPartFinset s k S false)
          (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) s &&
        ((decide (P.pastingPartFinset s k S false ≠ s) &&
            decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k S false)) ||
          (decide (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true ≠ s) &&
            decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true))) &&
        P.fastMoleculeTest (P.pastingPartFinset s k S false) &&
        P.fastMoleculeTest (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) &&
        ((decide (P.pastingPartFinset s k S false ≠ s) &&
            (decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k S false) &&
              P.fastSubmoleculeTestAux X n (P.pastingPartFinset s k S false))) ||
          (decide (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true ≠ s) &&
            (decide (∀ y ∈ X, y ∈ P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) &&
              P.fastSubmoleculeTestAux X n
                (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true))))) =
      if h : P.IsPastingIn k (P.pastingPart s hs k S false)
          (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) ⟨s, hs⟩ ∧
        IsMoleculeIn P (P.pastingPart s hs k S false) ∧
        IsMoleculeIn P (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) then
        (if hV : P.pastingPart s hs k S false = ⟨s, hs⟩ then false else
          P.submoleculeTest X (Finset.univ.filter (· ∈ P.pastingPart s hs k S false))
            (isLowerSet_filter_mem _)) ||
        (if hW : P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true = ⟨s, hs⟩ then false else
          P.submoleculeTest X (Finset.univ.filter
            (· ∈ P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true))
            (isLowerSet_filter_mem _))
      else false := by
    have hb (p a₁ a₂ b₁ b₂ m₁ m₂ c d : Bool) :
        (p && (a₁ && a₂ || b₁ && b₂) && m₁ && m₂ && (a₁ && (a₂ && c) || b₁ && (b₂ && d))) =
          (p && m₁ && m₂ && (a₁ && (a₂ && c) || b₁ && (b₂ && d))) := by
      cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp
    have hguard (V : LowerSet P) [DecidablePred (· ∈ V)] :
        (decide (∀ y ∈ X, y ∈ Finset.univ.filter (· ∈ V)) &&
          P.submoleculeTest X (Finset.univ.filter (· ∈ V)) (isLowerSet_filter_mem V)) =
        P.submoleculeTest X (Finset.univ.filter (· ∈ V)) (isLowerSet_filter_mem V) := by
      cases h : P.submoleculeTest X _ (isLowerSet_filter_mem V)
      · exact Bool.and_false _
      · have hle := (isSubmoleculeOf_of_submoleculeTest X _ _ h).le
        rw [mk_filter_mem] at hle
        rw [Bool.and_true, decide_eq_true_iff]
        exact fun y hy => (Finset.mem_filter_univ y).2 (hle hy)
    rw [hb, ← filter_mem_pastingPart hs, ← filter_mem_pastingPart hs]
    have hC := isSplitFinset_eq_true_iff (k := k) (isLowerSet_filter_mem
      (P.pastingPart s hs k S false)) (isLowerSet_filter_mem
        (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true)) hs
    rw [mk_filter_mem, mk_filter_mem] at hC
    have hM (V : LowerSet P) [DecidablePred (· ∈ V)] :
        P.fastMoleculeTest (Finset.univ.filter (· ∈ V)) = true ↔ IsMoleculeIn P V := by
      rw [fastMoleculeTest_eq_true_iff _ (isLowerSet_filter_mem V), mk_filter_mem]
    split_ifs with h hV hW hW
    · rw [hC.2 h.1, (hM _).2 h.2.1, (hM _).2 h.2.2, hne, hne]
      simp [hV, hW]
    · rw [hC.2 h.1, (hM _).2 h.2.1, (hM _).2 h.2.2, hne, hne,
        hrec (isLowerSet_filter_mem _) (filter_mem_ssubset (lt_of_le_of_ne h.1.right_le hW)),
        hguard]
      simp [hV, hW]
    · rw [hC.2 h.1, (hM _).2 h.2.1, (hM _).2 h.2.2, hne, hne,
        hrec (isLowerSet_filter_mem _) (filter_mem_ssubset (lt_of_le_of_ne h.1.left_le hV)),
        hguard]
      simp [hV, hW]
    · rw [hC.2 h.1, (hM _).2 h.2.1, (hM _).2 h.2.2, hne, hne,
        hrec (isLowerSet_filter_mem _) (filter_mem_ssubset (lt_of_le_of_ne h.1.left_le hV)),
        hrec (isLowerSet_filter_mem _) (filter_mem_ssubset (lt_of_le_of_ne h.1.right_le hW)),
        hguard, hguard]
      simp [hV, hW]
    · rw [Bool.eq_false_iff]
      intro h'
      simp only [Bool.and_eq_true] at h'
      obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, -⟩ := h'
      exact h ⟨hC.1 h₁, (hM _).1 h₂, (hM _).1 h₃⟩
  rw [fastSubmoleculeTestAux, submoleculeTest, hwhole]
  congr 1
  exact decide_eq_decide.2 (exists_congr fun k => and_congr_right' (exists_congr fun S =>
    and_congr_right' (by rw [hpaste k S])))

variable (P) in
def fastSubmoleculeTest (X : LowerSet P) [DecidablePred (· ∈ X)] (s : Finset P) : Bool :=
  P.fastSubmoleculeTestAux X (s.card + 1) s

theorem fastSubmoleculeTest_eq_submoleculeTest (X : LowerSet P) [DecidablePred (· ∈ X)]
    (s : Finset P) (hs : IsLowerSet (s : Set P)) :
    P.fastSubmoleculeTest X s = P.submoleculeTest X s hs :=
  fastSubmoleculeTestAux_eq_submoleculeTest X hs (Nat.lt_succ_self _)

theorem fastSubmoleculeTest_eq_true_iff (X : LowerSet P) [DecidablePred (· ∈ X)]
    (s : Finset P) (hs : IsLowerSet (s : Set P)) :
    P.fastSubmoleculeTest X s = true ↔ P.IsSubmoleculeOf X ⟨s, hs⟩ := by
  rw [fastSubmoleculeTest_eq_submoleculeTest X s hs, submoleculeTest_eq_true_iff]

instance decidableIsSubmoleculeOf (X U : LowerSet P) [DecidablePred (· ∈ X)]
    [DecidablePred (· ∈ U)] : Decidable (P.IsSubmoleculeOf X U) :=
  decidable_of_iff (P.fastSubmoleculeTest X (Finset.univ.filter (· ∈ U)) = true)
    (by rw [fastSubmoleculeTest_eq_true_iff _ _ (isLowerSet_filter_mem U),
      mk_filter_mem])

instance decidableIsAtomIn (U : LowerSet P) [DecidablePred (· ∈ U)] : Decidable (P.IsAtomIn U) :=
  inferInstanceAs (Decidable (IsMoleculeIn P U ∧ ∃ t, U = LowerSet.Iic t))

instance decidableIsAtom : Decidable P.IsAtom := decidableIsAtomIn ⊤

end Decide

end Atoms.Molecule.OGP
