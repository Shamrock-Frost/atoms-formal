import Atoms.Molecule.Boundary
import Atoms.Molecule.Category

universe u

open Order

namespace Atoms.Molecule.OGP

variable (P : OGP.{u})

def IsGlobular (U : LowerSet P) : Prop :=
  ∀ k n : ℕ, k < n → ∀ α β : Bool, P.boundary (P.boundary U n β) k α = P.boundary U k α

structure IsRound (U : LowerSet P) : Prop where
  isGlobular : P.IsGlobular U
  inf_boundary_zero : 0 < krullDim U → P.boundary U 0 false ⊓ P.boundary U 0 true = ⊥
  inf_boundary_succ : ∀ n : ℕ, ((n + 1 : ℕ) : WithBot ℕ∞) < krullDim U →
    P.boundary U (n + 1) false ⊓ P.boundary U (n + 1) true = P.boundaryFull U n

structure IsPastingIn (k : ℕ) (V W U : LowerSet P) : Prop where
  sup_eq : V ⊔ W = U
  inf_eq_output : V ⊓ W = P.boundary V k true
  inf_eq_input : V ⊓ W = P.boundary W k false

variable {P} in
theorem isPastingIn_cond_iff (β : Bool) {k : ℕ} {A B U : LowerSet P} :
    P.IsPastingIn k (cond β A B) (cond β B A) U ↔
      A ⊔ B = U ∧ A ⊓ B = P.boundary B k (!β) ∧ A ⊓ B = P.boundary A k β := by
  cases β
  · exact ⟨fun h => ⟨(sup_comm A B).trans h.sup_eq, (inf_comm A B).trans h.inf_eq_output,
      (inf_comm A B).trans h.inf_eq_input⟩,
    fun ⟨h1, h2, h3⟩ => ⟨(sup_comm B A).trans h1, (inf_comm B A).trans h2,
      (inf_comm B A).trans h3⟩⟩
  · exact ⟨fun h => ⟨h.sup_eq, h.inf_eq_input, h.inf_eq_output⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩

variable {P} in
theorem isPastingIn_cond_comm (β : Bool) {k : ℕ} {A B U : LowerSet P} :
    P.IsPastingIn k (cond β A B) (cond β B A) U ↔
      P.IsPastingIn k (cond (!β) B A) (cond (!β) A B) U := by
  rw [Bool.cond_not, Bool.cond_not]

variable {P} in
theorem IsPastingIn.le_cond (β : Bool) {k : ℕ} {A B U : LowerSet P}
    (hp : P.IsPastingIn k (cond β A B) (cond β B A) U) : B ≤ U :=
  ((isPastingIn_cond_iff β).1 hp).1 ▸ le_sup_right

variable {P} in
theorem IsPastingIn.left_le {k : ℕ} {V W U : LowerSet P} (hp : P.IsPastingIn k V W U) : V ≤ U :=
  hp.le_cond false

variable {P} in
theorem IsPastingIn.right_le {k : ℕ} {V W U : LowerSet P} (hp : P.IsPastingIn k V W U) :
    W ≤ U :=
  hp.le_cond true

inductive IsMoleculeIn (P : OGP.{u}) : LowerSet P → Prop
  | point (x : P) (hx : IsMin x) : IsMoleculeIn P (LowerSet.Iic x)
  | atom (t : P) (hround : P.IsRound (LowerSet.Iic t))
      (hbdry : ∀ α, IsMoleculeIn P (P.bdry (LowerSet.Iic t) α)) : IsMoleculeIn P (LowerSet.Iic t)
  | paste (k : ℕ) (V W U : LowerSet P) (hpaste : P.IsPastingIn k V W U) (hV : IsMoleculeIn P V)
      (hW : IsMoleculeIn P W) (hk : (k : WithBot ℕ∞) < min (krullDim V) (krullDim W)) :
      IsMoleculeIn P U

def IsMolecule : Prop := IsMoleculeIn P ⊤

def IsPasting (U V : OGP.{u}) (k : ℕ) (W : OGP.{u}) : Prop :=
  ∃ (i : U ⟶ W) (j : V ⟶ W), IsInclusion i ∧ IsInclusion j ∧ W.IsPastingIn k (map i ⊤) (map j ⊤) ⊤

variable {P} {U V W : LowerSet P} {n : ℕ}

theorem IsGlobular.boundary_le_boundary (hU : P.IsGlobular U) {k : ℕ} (hk : k < n) (α β : Bool) :
    P.boundary U k α ≤ P.boundary U n β :=
  hU k n hk α β ▸ boundary_le _ k α

theorem IsGlobular.boundary (hU : P.IsGlobular U) (n : ℕ) (β : Bool) :
    P.IsGlobular (P.boundary U n β) := by
  intro k m hkm α γ
  rcases lt_or_ge m n with hmn | hnm
  · rw [hU m n hmn γ β, hU k m hkm α γ, hU k n (hkm.trans hmn) α β]
  · rw [boundary_boundary_of_le hnm]

theorem IsGlobular.boundary_boundary_eq_of_le (hU : P.IsGlobular U) {k : ℕ} (hk : k ≤ n)
    {α β : Bool} (h : k < n ∨ α = β) : P.boundary (P.boundary U n β) k α = P.boundary U k α := by
  rcases hk.lt_or_eq with hlt | rfl
  · exact hU k n hlt α β
  · obtain rfl := h.resolve_left (lt_irrefl k)
    exact boundary_boundary_of_le le_rfl α α

theorem IsGlobular.boundaryFull_le_bdryFull (hU : P.IsGlobular U) (hd : krullDim U = n + 1) {k : ℕ}
    (hk : k ≤ n) : P.boundaryFull U k ≤ P.bdryFull U := by
  rw [bdryFull, bdry_eq_boundary hd, bdry_eq_boundary hd, boundaryFull]
  rcases hk.lt_or_eq with hk | rfl
  · exact sup_le_sup (hU.boundary_le_boundary hk _ _) (hU.boundary_le_boundary hk _ _)
  · exact le_rfl

theorem IsRound.grade_eq_of_maximal (hr : P.IsRound U) (hU : krullDim U = n) {x : P}
    (hx : Maximal (· ∈ U) x) : grade ℕ x = n := by
  have hle : grade ℕ x ≤ n := krullDim_le_coe_iff.1 hU.le ⟨x, hx.prop⟩
  by_contra hne
  have hlt : grade ℕ x < n := lt_of_le_of_ne hle hne
  have hmem : x ∈ P.boundary U (grade ℕ x) false ⊓ P.boundary U (grade ℕ x) true :=
    ⟨mem_boundary_of_mem_facesIn (maximal_mem_iff_forall_mem_facesIn.1 hx false) le_rfl,
      mem_boundary_of_mem_facesIn (maximal_mem_iff_forall_mem_facesIn.1 hx true) le_rfl⟩
  cases hk : grade ℕ x with
  | zero =>
    rw [hk, hr.inf_boundary_zero (by rw [hU]; exact_mod_cast (by omega : 0 < n))] at hmem
    exact hmem
  | succ m =>
    rw [hk, hr.inf_boundary_succ m (by rw [hU]; exact_mod_cast (hk ▸ hlt))] at hmem
    have := hmem.elim grade_le_of_mem_boundary grade_le_of_mem_boundary
    omega

theorem IsRound.boundary (hr : P.IsRound U) (n : ℕ) (β : Bool) : P.IsRound (P.boundary U n β) where
  isGlobular := hr.isGlobular.boundary n β
  inf_boundary_zero h := by
    have hn : 0 < n := by exact_mod_cast h.trans_le (krullDim_boundary_le U n β)
    rw [hr.isGlobular 0 n hn false β, hr.isGlobular 0 n hn true β]
    exact hr.inf_boundary_zero (h.trans_le (LowerSet.krullDim_mono (boundary_le U n β)))
  inf_boundary_succ m h := by
    have hn : m + 1 < n := by exact_mod_cast h.trans_le (krullDim_boundary_le U n β)
    rw [hr.isGlobular _ n hn false β, hr.isGlobular _ n hn true β, boundaryFull,
      hr.isGlobular m n (by omega) false β, hr.isGlobular m n (by omega) true β]
    exact hr.inf_boundary_succ m (h.trans_le (LowerSet.krullDim_mono (boundary_le U n β)))

section Closure

variable {t : P}

theorem krullDim_bdry_Iic (ht : grade ℕ t = n + 1) {α : Bool}
    (hne : (P.bdry (.Iic t) α : Set P).Nonempty) : krullDim (P.bdry (.Iic t) α) = n := by
  have hU : krullDim (LowerSet.Iic t) = n + 1 := by rw [LowerSet.krullDim_Iic, ht]; push_cast; rfl
  refine le_antisymm (bdry_eq_boundary hU α ▸ krullDim_boundary_le _ n α) ?_
  obtain ⟨y, hy⟩ := hne
  rw [bdry_Iic] at hy
  obtain ⟨z, hz, -⟩ := mem_lowerClosure.1 hy
  have hzn : grade ℕ z = n := by have := Nat.covBy_iff_add_one_eq.1 (hz.1.grade ℕ); omega
  have hzU : z ∈ P.bdry (.Iic t) α := by
    rw [bdry_Iic]
    exact subset_lowerClosure hz
  exact hzn ▸ grade_le_krullDim (⟨z, hzU⟩ : ↥(P.bdry (.Iic t) α))

theorem IsGlobular.bdry_bdry_eq (hg : P.IsGlobular U) (hU : krullDim U = n + 1)
    (hd : ∀ β, krullDim (P.bdry U β) = n) (α : Bool) :
    P.bdry (P.bdry U false) α = P.bdry (P.bdry U true) α := by
  cases n with
  | zero => rw [bdry_eq_bot (hd false).le, bdry_eq_bot (hd true).le]
  | succ m =>
    have hd' (β : Bool) : krullDim (P.bdry U β) = m + 1 := by rw [hd]; push_cast; rfl
    rw [bdry_eq_boundary (hd' false), bdry_eq_boundary (hd' true), bdry_eq_boundary hU,
      bdry_eq_boundary hU, hg m _ (by omega), hg m _ (by omega)]

theorem IsRound.bdry_inf_bdry (hr : P.IsRound U) (hU : krullDim U = n + 1)
    (hd : krullDim (P.bdry U false) = n) :
    P.bdry U false ⊓ P.bdry U true = P.bdryFull (P.bdry U false) := by
  have hb (β : Bool) := bdry_eq_boundary hU β
  cases n with
  | zero =>
    rw [bdryFull, bdry_eq_bot hd.le, bdry_eq_bot hd.le, sup_bot_eq, hb, hb]
    exact hr.inf_boundary_zero (by rw [hU]; exact_mod_cast Nat.zero_lt_one)
  | succ m =>
    have hd' : krullDim (P.bdry U false) = m + 1 := by rw [hd]; push_cast; rfl
    rw [bdryFull, bdry_eq_boundary hd', bdry_eq_boundary hd', hb, hb,
      hr.isGlobular m _ (by omega), hr.isGlobular m _ (by omega),
      hr.inf_boundary_succ m (by rw [hU]; exact_mod_cast (by omega : m + 1 < m + 1 + 1))]
    rfl

theorem IsRound.halves (hr : P.IsRound (.Iic t)) (ht : grade ℕ t = n + 1)
    (hne : ∀ α, (P.bdry (.Iic t) α : Set P).Nonempty) :
    (∀ α, P.IsRound (P.bdry (.Iic t) α)) ∧
      (∀ α, P.bdry (P.bdry (.Iic t) false) α = P.bdry (P.bdry (.Iic t) true) α) ∧
      P.bdry (.Iic t) false ⊓ P.bdry (.Iic t) true = P.bdryFull (P.bdry (.Iic t) false) := by
  have hU : krullDim (LowerSet.Iic t) = n + 1 := by rw [LowerSet.krullDim_Iic, ht]; push_cast; rfl
  have hd (β : Bool) := krullDim_bdry_Iic ht (hne β)
  exact ⟨fun β => bdry_eq_boundary hU β ▸ hr.boundary n β, hr.isGlobular.bdry_bdry_eq hU hd,
    hr.bdry_inf_bdry hU (hd false)⟩

private theorem boundary_halves_eq (hr : ∀ α, P.IsRound (P.bdry (.Iic t) α))
    (hb : ∀ α, P.bdry (P.bdry (.Iic t) false) α = P.bdry (P.bdry (.Iic t) true) α)
    (hd : ∀ α, krullDim (P.bdry (.Iic t) α) = n + 1) {j : ℕ} (hj : j ≤ n) (α : Bool) :
    P.boundary (P.bdry (.Iic t) false) j α = P.boundary (P.bdry (.Iic t) true) j α := by
  rcases hj.lt_or_eq with hj | rfl
  · rw [← (hr false).isGlobular j n hj α α, ← (hr true).isGlobular j n hj α α,
      ← bdry_eq_boundary (hd false), ← bdry_eq_boundary (hd true), hb]
  · rw [← bdry_eq_boundary (hd false), ← bdry_eq_boundary (hd true), hb]

private theorem boundary_Iic_eq_boundary_bdry (ht : grade ℕ t = n + 1)
    (hne : ∀ α, (P.bdry (.Iic t) α : Set P).Nonempty) (hr : ∀ α, P.IsRound (P.bdry (.Iic t) α))
    (hb : ∀ α, P.bdry (P.bdry (.Iic t) false) α = P.bdry (P.bdry (.Iic t) true) α)
    {j : ℕ} (hj : j < n) (α β : Bool) :
    P.boundary (.Iic t) j α = P.boundary (P.bdry (.Iic t) β) j α := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  have hd (γ : Bool) : krullDim (P.bdry (.Iic t) γ) = m + 1 := by
    rw [krullDim_bdry_Iic ht (hne γ), hm]; push_cast; rfl
  have hd' (γ : Bool) : krullDim (P.bdry (.Iic t) γ) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hd]; push_cast; rfl
  have hVW (γ : Bool) := boundary_halves_eq hr hb hd (by omega : j ≤ m) γ
  have hmem (c : P) (hc : grade ℕ c ≤ j + 1) :
      c ∈ (LowerSet.Iic t : Set P) ↔ c ∈ ((P.bdry (.Iic t) false ⊔ P.bdry (.Iic t) true :
        LowerSet P) : Set P) := by
    rw [coe_bdry_Iic_sup, LowerSet.coe_Iic, Set.mem_Iic, Set.mem_Iio]
    refine ⟨fun h => h.lt_of_ne fun hct => ?_, le_of_lt⟩
    rw [hct, ht] at hc
    omega
  have hmax (x : P) (hx : grade ℕ x < j) : Maximal (· ∈ LowerSet.Iic t) x ↔
      Maximal (· ∈ P.bdry (.Iic t) false ⊔ P.bdry (.Iic t) true) x := by
    refine iff_of_false (fun h => ?_) fun h => ?_
    · obtain rfl := h.eq_of_le (le_refl t) h.prop
      omega
    · obtain ⟨hx', hV', hW'⟩ := LowerSet.maximal_mem_sup_iff.1 h
      have := hx'.elim (fun h' => (hr false).grade_eq_of_maximal (hd' false) (hV' h'))
        fun h' => (hr true).grade_eq_of_maximal (hd' true) (hW' h')
      omega
  rw [boundary_congr (facesIn_congr hmem) hmax, boundary_sup_of_boundary_eq (hVW α)]
  cases β
  · rfl
  · exact hVW α

theorem isRound_Iic_of_halves (ht : grade ℕ t = n + 1)
    (hne : ∀ α, (P.bdry (.Iic t) α : Set P).Nonempty) (hr : ∀ α, P.IsRound (P.bdry (.Iic t) α))
    (hb : ∀ α, P.bdry (P.bdry (.Iic t) false) α = P.bdry (P.bdry (.Iic t) true) α)
    (hi : P.bdry (.Iic t) false ⊓ P.bdry (.Iic t) true = P.bdryFull (P.bdry (.Iic t) false)) :
    P.IsRound (.Iic t) := by
  have hU : krullDim (LowerSet.Iic t) = n + 1 := by rw [LowerSet.krullDim_Iic, ht]; push_cast; rfl
  have hd (β : Bool) := krullDim_bdry_Iic ht (hne β)
  have hbe {j : ℕ} (hj : j < n) (α β : Bool) := boundary_Iic_eq_boundary_bdry ht hne hr hb hj α β
  have hglob : P.IsGlobular (.Iic t) := by
    intro k m hkm α β
    rcases le_or_gt m n with hm | hm
    · have e : P.boundary (.Iic t) m β = P.boundary (P.bdry (.Iic t) β) m β := by
        rcases hm.lt_or_eq with hm | rfl
        · exact hbe hm β β
        · rw [← bdry_eq_boundary hU, boundary_eq_self (hd β).le]
      rw [e, (hr β).isGlobular k m hkm α β, hbe (by omega) α β]
    · rw [boundary_eq_self (U := .Iic t) (n := m) (by rw [hU]; exact_mod_cast hm)]
  refine ⟨hglob, fun _ => ?_, fun m hm => ?_⟩
  · cases n with
    | zero =>
      rw [← bdry_eq_boundary hU, ← bdry_eq_boundary hU, hi, bdryFull,
        bdry_eq_bot (hd false).le, bdry_eq_bot (hd false).le, sup_bot_eq]
    | succ m =>
      rw [hbe (by omega) false false, hbe (by omega) true false]
      exact (hr false).inf_boundary_zero (by rw [hd]; exact_mod_cast Nat.succ_pos m)
  · have hmn : m + 1 ≤ n := by rw [hU] at hm; norm_cast at hm; omega
    rcases hmn.lt_or_eq with h | rfl
    · rw [hbe h false false, hbe h true false, boundaryFull, hbe (by omega) false false,
        hbe (by omega) true false]
      exact (hr false).inf_boundary_succ m (by rw [hd]; exact_mod_cast h)
    · have hV' : krullDim (P.bdry (.Iic t) false) = m + 1 := by rw [hd]; push_cast; rfl
      rw [← bdry_eq_boundary hU, ← bdry_eq_boundary hU, hi, bdryFull, bdry_eq_boundary hV',
        bdry_eq_boundary hV', boundaryFull, hbe (by omega) false false,
        hbe (by omega) true false]

theorem isRound_Iic_iff (ht : grade ℕ t = n + 1)
    (hne : ∀ α, (P.bdry (.Iic t) α : Set P).Nonempty) :
    P.IsRound (.Iic t) ↔ (∀ α, P.IsRound (P.bdry (.Iic t) α)) ∧
      (∀ α, P.bdry (P.bdry (.Iic t) false) α = P.bdry (P.bdry (.Iic t) true) α) ∧
      P.bdry (.Iic t) false ⊓ P.bdry (.Iic t) true = P.bdryFull (P.bdry (.Iic t) false) :=
  ⟨fun hr => hr.halves ht hne, fun ⟨hr, hb, hi⟩ => isRound_Iic_of_halves ht hne hr hb hi⟩

end Closure

namespace IsPastingIn

variable {k : ℕ} {A B : LowerSet P}

theorem boundary_cond (α : Bool) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    P.boundary U k α = P.boundary B k α := by
  obtain ⟨hs, -, hi⟩ := (isPastingIn_cond_iff α).1 hp
  rw [← hs, sup_comm]
  exact boundary_sup_of_inf_eq_boundary ((inf_comm B A).trans hi)

theorem boundary_input (hp : P.IsPastingIn k V W U) :
    P.boundary U k false = P.boundary V k false :=
  boundary_cond false hp

theorem boundary_output (hp : P.IsPastingIn k V W U) :
    P.boundary U k true = P.boundary W k true :=
  boundary_cond true hp

theorem inf_boundary_le (hp : P.IsPastingIn k V W U) :
    P.boundary U k false ⊓ P.boundary U k true ≤
      (P.boundary V k false ⊓ P.boundary V k true) ⊓
        (P.boundary W k false ⊓ P.boundary W k true) := by
  rw [hp.boundary_input, hp.boundary_output]
  rintro x ⟨h₁, h₂⟩
  have hx : x ∈ V ⊓ W := ⟨boundary_le V k false h₁, boundary_le W k true h₂⟩
  exact ⟨⟨h₁, hp.inf_eq_output ▸ hx⟩, ⟨hp.inf_eq_input ▸ hx, h₂⟩⟩

theorem boundary_eq_boundary_of_lt_cond (α : Bool) (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {j : ℕ} (hj : j < k) (δ : Bool) :
    P.boundary A j δ = P.boundary B j δ := by
  obtain ⟨-, hiB, hiA⟩ := (isPastingIn_cond_iff α).1 hp
  rw [← hA j k hj δ α, ← hiA, hiB, hB j k hj δ (!α)]

theorem boundary_eq_of_lt_cond (α : Bool) (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {j : ℕ} (hj : j < k) (δ : Bool) :
    P.boundary U j δ = P.boundary B j δ := by
  have h := hp.boundary_eq_boundary_of_lt_cond α hA hB hj δ
  rw [← ((isPastingIn_cond_iff α).1 hp).1, boundary_sup_of_boundary_eq h, h]

theorem boundary_eq_of_le_cond (α : Bool) (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {i : ℕ} (hi : i ≤ k) :
    P.boundary U i α = P.boundary B i α := by
  rcases hi.lt_or_eq with hi | rfl
  · exact hp.boundary_eq_of_lt_cond α hA hB hi α
  · exact hp.boundary_cond α

theorem boundary_of_lt (hp : P.IsPastingIn k V W U) (hV : P.IsGlobular V) (hW : P.IsGlobular W)
    (hkn : k < n) (α : Bool) :
    P.IsPastingIn k (P.boundary V n α) (P.boundary W n α) (P.boundary U n α) := by
  have hVn : V ⊓ W ≤ P.boundary V n α := hp.inf_eq_output ▸ hV.boundary_le_boundary hkn true α
  have hWn : V ⊓ W ≤ P.boundary W n α := hp.inf_eq_input ▸ hW.boundary_le_boundary hkn false α
  have hd (x : P) (hx : x ∈ V ⊓ W) : grade ℕ x < n :=
    (grade_le_of_mem_boundary (hp.inf_eq_output ▸ hx)).trans_lt hkn
  have hinf : P.boundary V n α ⊓ P.boundary W n α = V ⊓ W :=
    le_antisymm (inf_le_inf (boundary_le _ _ _) (boundary_le _ _ _)) (le_inf hVn hWn)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hp.sup_eq]
    refine le_antisymm (sup_le (boundary_le_boundary_sup hWn hd) ?_) (boundary_sup_le V W n α)
    exact sup_comm W V ▸ boundary_le_boundary_sup (inf_comm V W ▸ hVn)
      fun x hx => hd x ⟨hx.2, hx.1⟩
  · rw [hinf, hp.inf_eq_output, hV k n hkn true α]
  · rw [hinf, hp.inf_eq_input, hW k n hkn false α]

theorem boundary_of_lt_cond (α : Bool) (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (hkn : k < n) (δ : Bool) :
    P.IsPastingIn k (cond α (P.boundary A n δ) (P.boundary B n δ))
      (cond α (P.boundary B n δ) (P.boundary A n δ)) (P.boundary U n δ) := by
  cases α
  · exact hp.boundary_of_lt hB hA hkn δ
  · exact hp.boundary_of_lt hA hB hkn δ

theorem boundary_eq_sup_of_lt_cond (α : Bool) (hA : P.IsGlobular A) (hB : P.IsGlobular B)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (hkn : k < n) (δ : Bool) :
    P.boundary U n δ = P.boundary A n δ ⊔ P.boundary B n δ :=
  ((isPastingIn_cond_iff α).1 (hp.boundary_of_lt_cond α hA hB hkn δ)).1.symm

theorem isGlobular (hp : P.IsPastingIn k V W U) (hV : P.IsGlobular V) (hW : P.IsGlobular W) :
    P.IsGlobular U := by
  intro m n hmn α β
  rcases lt_trichotomy n k with hnk | rfl | hkn
  · rw [hp.boundary_eq_of_lt_cond false hW hV hnk, hV m n hmn,
      hp.boundary_eq_of_lt_cond false hW hV (hmn.trans hnk)]
  · cases β
    · rw [hp.boundary_input, hV m _ hmn, hp.boundary_eq_of_lt_cond false hW hV hmn]
    · rw [hp.boundary_output, hW m _ hmn, hp.boundary_eq_of_lt_cond true hV hW hmn]
  · have hp' := hp.boundary_of_lt hV hW hkn β
    have hV' := hV.boundary n β
    have hW' := hW.boundary n β
    rcases lt_trichotomy m k with hmk | rfl | hkm
    · rw [hp'.boundary_eq_of_lt_cond false hW' hV' hmk, hV m n hmn,
        hp.boundary_eq_of_lt_cond false hW hV hmk]
    · cases α
      · rw [hp'.boundary_input, hV m n hmn, hp.boundary_input]
      · rw [hp'.boundary_output, hW m n hmn, hp.boundary_output]
    · rw [← (hp'.boundary_of_lt hV' hW' hkm α).sup_eq, hV m n hmn, hW m n hmn,
        (hp.boundary_of_lt hV hW hkm α).sup_eq]

theorem lt_cond (α : Bool) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U)
    (hk : (k : WithBot ℕ∞) < krullDim A) : B < U := by
  obtain ⟨hs, -, hiA⟩ := (isPastingIn_cond_iff α).1 hp
  refine (hp.le_cond α).lt_of_ne fun h => hk.not_ge (boundary_eq_self_iff (α := α).1 ?_)
  rw [← hiA, inf_eq_left.2 (le_sup_left.trans_eq (hs.trans h.symm))]

theorem le_of_krullDim_le_cond (β : Bool) (hp : P.IsPastingIn k (cond β A B) (cond β B A) U)
    (hk : krullDim B ≤ k) : B ≤ A :=
  inf_eq_right.1 (((isPastingIn_cond_iff β).1 hp).2.1.trans (boundary_eq_self hk _))

private theorem grade_le_of_maximal_of_not_maximal {X Y : LowerSet P} (hXY : X ⊔ Y = U)
    {α : Bool} (hb : X ⊓ Y = P.boundary X k α) {z : P} (hz : Maximal (· ∈ X) z)
    (hzU : ¬ Maximal (· ∈ U) z) : grade ℕ z ≤ k := by
  obtain ⟨y, hzy, hy⟩ := (not_maximal_iff_exists_gt (hXY ▸ Or.inl hz.prop)).1 hzU
  rw [← hXY] at hy
  have hyY : y ∈ Y := hy.resolve_left fun hyX => hzy.not_ge (hz.2 hyX hzy.le)
  have hzXY : z ∈ X ⊓ Y := ⟨hz.prop, Y.lower hzy.le hyY⟩
  rw [hb] at hzXY
  exact grade_le_of_mem_boundary hzXY

private theorem eq_lowerClosure_sup_boundary {X : LowerSet P} {α : Bool} (hXU : X ≤ U)
    (hb : P.boundary U k α = P.boundary X k α)
    (hlow : ∀ z, Maximal (· ∈ X) z → ¬ Maximal (· ∈ U) z → grade ℕ z ≤ k)
    (hU : krullDim U ≤ n) :
    X = lowerClosure {x | Maximal (· ∈ U) x ∧ k < grade ℕ x ∧ x ∈ X} ⊔ P.boundary U k α := by
  refine le_antisymm (fun x hx => ?_) (sup_le (lowerClosure_le.2 fun _ hx => hx.2.2) ?_)
  · obtain ⟨z, hxz, hz⟩ := GradeOrder.exists_le_maximal
      (fun y hy => krullDim_le_coe_iff.1 hU ⟨y, hXU hy⟩) hx
    refine LowerSet.lower _ hxz (LowerSet.mem_sup_iff.2 ?_)
    by_cases hzU : Maximal (· ∈ U) z
    · rcases lt_or_ge k (grade ℕ z) with hk | hk
      · exact Or.inl (subset_lowerClosure ⟨hzU, hk, hz.prop⟩)
      · exact Or.inr (mem_boundary_of_maximal_of_grade_le hzU hk α)
    · rw [hb]
      exact Or.inr (mem_boundary_of_maximal_of_grade_le hz (hlow z hz hzU) α)
  · rw [hb]
    exact boundary_le X k α

theorem eq_cond (α : Bool) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U)
    (hU : krullDim U ≤ n) :
    B = lowerClosure {x | Maximal (· ∈ U) x ∧ k < grade ℕ x ∧ x ∈ B} ⊔ P.boundary U k α := by
  obtain ⟨hs, hiB, -⟩ := (isPastingIn_cond_iff α).1 hp
  exact eq_lowerClosure_sup_boundary (hp.le_cond α) (hp.boundary_cond α)
    (fun _ hz hzU => grade_le_of_maximal_of_not_maximal ((sup_comm B A).trans hs)
      ((inf_comm B A).trans hiB) hz hzU) hU

theorem mem_right_iff_notMem_left (hp : P.IsPastingIn k V W U) {x : P} (hx : x ∈ U)
    (hk : k < grade ℕ x) : x ∈ W ↔ x ∉ V := by
  refine ⟨fun hxW hxV => ?_, fun hxV => ?_⟩
  · have hxVW : x ∈ V ⊓ W := ⟨hxV, hxW⟩
    rw [hp.inf_eq_output] at hxVW
    exact (grade_le_of_mem_boundary hxVW).not_gt hk
  · rw [← hp.sup_eq] at hx
    exact hx.resolve_left hxV

theorem isMoleculeIn (hp : P.IsPastingIn k V W U)
    (hV : IsMoleculeIn P V) (hW : IsMoleculeIn P W) : IsMoleculeIn P U := by
  by_cases hkV : (k : WithBot ℕ∞) < krullDim V
  · by_cases hkW : (k : WithBot ℕ∞) < krullDim W
    · exact .paste k V W U hp hV hW (lt_min hkV hkW)
    · rwa [← hp.sup_eq, sup_eq_left.2 (hp.le_of_krullDim_le_cond true (not_lt.1 hkW))]
  · rwa [← hp.sup_eq, sup_eq_right.2 (hp.le_of_krullDim_le_cond false (not_lt.1 hkV))]

theorem lt_or_eq_boundary (α : Bool) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    (A < U ∧ B < U) ∨ (A = P.boundary U k (!α) ∧ B = U) ∨ (A = U ∧ B = P.boundary U k α) := by
  have deg (β : Bool) {X Y : LowerSet P} (hq : P.IsPastingIn k (cond β X Y) (cond β Y X) U)
      (hY : krullDim Y ≤ k) : X = U ∧ Y = P.boundary U k β :=
    ⟨(sup_eq_left.2 (hq.le_of_krullDim_le_cond β hY)).symm.trans
      ((isPastingIn_cond_iff β).1 hq).1, ((hq.boundary_cond β).trans (boundary_eq_self hY β)).symm⟩
  have hq := (isPastingIn_cond_comm α).1 hp
  by_cases hkA : (k : WithBot ℕ∞) < krullDim A
  · by_cases hkB : (k : WithBot ℕ∞) < krullDim B
    · exact Or.inl ⟨hq.lt_cond (!α) hkB, hp.lt_cond α hkA⟩
    · exact Or.inr (Or.inr (deg α hp (not_lt.1 hkB)))
  · exact Or.inr (Or.inl (deg (!α) hq (not_lt.1 hkA)).symm)

end IsPastingIn

namespace IsMoleculeIn

theorem nonempty (h : IsMoleculeIn P U) : (U : Set P).Nonempty := by
  induction h with
  | point x _ => exact ⟨x, le_refl x⟩
  | atom t _ _ _ => exact ⟨t, le_refl t⟩
  | paste k V W U hp _ _ _ ihV _ => exact ihV.mono hp.left_le

theorem finite (h : IsMoleculeIn P U) : (U : Set P).Finite := by
  induction h with
  | point x hx => exact (Set.finite_singleton x).subset fun y hy => le_antisymm hy (hx hy)
  | atom t _ _ ih =>
    refine ((ih false).union (ih true)).insert t |>.subset fun y hy => ?_
    rcases (LowerSet.mem_Iic_iff.1 hy).eq_or_lt with rfl | hlt
    · exact Set.mem_insert y _
    · refine Set.mem_insert_of_mem t ?_
      rw [← LowerSet.coe_sup, coe_bdry_Iic_sup]
      exact hlt
  | paste k V W U hp _ _ _ ihV ihW =>
    rw [← hp.sup_eq, LowerSet.coe_sup]
    exact ihV.union ihW

theorem exists_krullDim_eq (h : IsMoleculeIn P U) : ∃ n : ℕ, krullDim U = n := by
  induction h with
  | point x hx => exact ⟨0, (LowerSet.krullDim_Iic_of_isMin hx).trans Nat.cast_zero.symm⟩
  | atom t _ _ _ => exact ⟨grade ℕ t, LowerSet.krullDim_Iic t⟩
  | paste k V W U hp _ _ _ ihV ihW =>
    obtain ⟨a, ha⟩ := ihV
    obtain ⟨b, hb⟩ := ihW
    exact ⟨max a b, by
      rw [← hp.sup_eq, LowerSet.krullDim_sup, ha, hb, ← Nat.mono_cast.map_max]⟩

theorem exists_le_maximal (h : IsMoleculeIn P U) {x : P} (hx : x ∈ U) :
    ∃ z, x ≤ z ∧ Maximal (· ∈ U) z := by
  obtain ⟨n, hn⟩ := h.exists_krullDim_eq
  exact GradeOrder.exists_le_maximal (fun y hy => krullDim_le_coe_iff.1 hn.le ⟨y, hy⟩) hx

theorem exists_eq_Iic_of_krullDim_eq_zero (h : IsMoleculeIn P U) (h0 : krullDim U = 0) :
    ∃ x, IsMin x ∧ U = LowerSet.Iic x := by
  cases h with
  | point x hx => exact ⟨x, hx, rfl⟩
  | atom t _ _ =>
    rw [LowerSet.krullDim_Iic] at h0
    have ht : grade ℕ t = 0 := by exact_mod_cast h0
    exact ⟨t, isMin_grade_iff.1 (isMin_iff_eq_bot.2 ht), rfl⟩
  | paste k V W U hp _ _ hk =>
    have : (k : WithBot ℕ∞) < krullDim U :=
      (hk.trans_le (min_le_left _ _)).trans_le (LowerSet.krullDim_mono hp.left_le)
    rw [h0] at this
    exact absurd this (not_lt.2 (by exact_mod_cast Nat.zero_le k))

end IsMoleculeIn

open CategoryTheory in
theorem nonempty_iso_of_krullDim_eq_zero {Q : OGP.{u}} (hP : IsMolecule P) (hQ : IsMolecule Q)
    (hP0 : krullDim (⊤ : LowerSet P) = 0) (hQ0 : krullDim (⊤ : LowerSet Q) = 0) :
    Nonempty (P ≅ Q) := by
  obtain ⟨x, hx, hPx⟩ := hP.exists_eq_Iic_of_krullDim_eq_zero hP0
  obtain ⟨y, hy, hQy⟩ := hQ.exists_eq_Iic_of_krullDim_eq_zero hQ0
  have hPx' : ∀ a : P, a = x := fun a =>
    hx.eq_of_le (LowerSet.mem_Iic_iff.1 (hPx ▸ LowerSet.mem_top))
  have hQy' : ∀ b : Q, b = y := fun b =>
    hy.eq_of_le (LowerSet.mem_Iic_iff.1 (hQy ▸ LowerSet.mem_top))
  exact ⟨isoMk
    { toEquiv := ⟨fun _ => y, fun _ => x, fun a => (hPx' a).symm, fun b => (hQy' b).symm⟩
      map_rel_iff' := fun {a b} =>
        ⟨fun _ => (hPx' a).trans (hPx' b).symm ▸ le_rfl, fun _ => le_rfl⟩ }
    fun {a b} hab => absurd ((hPx' a).trans (hPx' b).symm) hab.ne.symm⟩

namespace IsMoleculeIn

private theorem isGlobular_and_boundary (h : IsMoleculeIn P U) :
    P.IsGlobular U ∧ ∀ (n : ℕ) (α : Bool), IsMoleculeIn P (P.boundary U n α) ∧
      ((n : WithBot ℕ∞) ≤ krullDim U → krullDim (P.boundary U n α) = n) := by
  induction h with
  | point x hx =>
    have h0 : krullDim (LowerSet.Iic x) = 0 := LowerSet.krullDim_Iic_of_isMin hx
    have hself (n : ℕ) (α : Bool) : P.boundary (LowerSet.Iic x) n α = LowerSet.Iic x :=
      boundary_eq_self (h0.trans_le (by exact_mod_cast Nat.zero_le n)) α
    refine ⟨fun k n _ α β => by rw [hself, hself], fun n α => ⟨by rw [hself]; exact .point x hx,
      fun hn => ?_⟩⟩
    rw [hself, h0] at *
    have : n = 0 := by exact_mod_cast le_antisymm hn (by exact_mod_cast Nat.zero_le n)
    rw [this]
    rfl
  | atom t hround hbdry ih =>
    have hne (β : Bool) := (hbdry β).nonempty
    obtain ⟨n, ht⟩ : ∃ n, grade ℕ t = n + 1 := by
      refine ⟨grade ℕ t - 1, ?_⟩
      by_contra h
      have h0 : grade ℕ t = 0 := by omega
      obtain ⟨y, hy⟩ := hne false
      rw [bdry_eq_bot (by rw [LowerSet.krullDim_Iic, h0]; rfl)] at hy
      simp at hy
    have hU : krullDim (LowerSet.Iic t) = n + 1 := by
      rw [LowerSet.krullDim_Iic, ht]; push_cast; rfl
    have hd (β : Bool) := krullDim_bdry_Iic ht (hne β)
    refine ⟨hround.isGlobular, fun m α => ?_⟩
    rcases lt_trichotomy m n with hm | rfl | hm
    · have e : P.boundary (.Iic t) m α = P.boundary (P.bdry (.Iic t) false) m α := by
        rw [bdry_eq_boundary hU, hround.isGlobular m n hm α false]
      rw [e]
      exact ⟨((ih false).2 m α).1, fun _ => ((ih false).2 m α).2
        (by rw [hd]; exact_mod_cast hm.le)⟩
    · rw [← bdry_eq_boundary hU]
      exact ⟨hbdry α, fun _ => hd α⟩
    · rw [boundary_eq_self (by rw [hU]; exact_mod_cast hm)]
      refine ⟨.atom t hround hbdry, fun h' => ?_⟩
      rw [hU] at h' ⊢
      norm_cast at h' ⊢
      omega
  | paste k V W U hp hVm hWm hk ihV ihW =>
    obtain ⟨a, ha⟩ := hVm.exists_krullDim_eq
    obtain ⟨b, hb⟩ := hWm.exists_krullDim_eq
    have hU : krullDim U = (max a b : ℕ) := by
      rw [← hp.sup_eq, LowerSet.krullDim_sup, ha, hb, ← Nat.mono_cast.map_max]
    rw [ha, hb] at hk
    have hka : k < a := by exact_mod_cast (lt_min_iff.1 hk).1
    have hkb : k < b := by exact_mod_cast (lt_min_iff.1 hk).2
    refine ⟨hp.isGlobular ihV.1 ihW.1, fun n α => ?_⟩
    by_cases hn : max a b ≤ n
    · rw [boundary_eq_self (by rw [hU]; exact_mod_cast hn)]
      refine ⟨.paste k V W U hp hVm hWm (by rw [ha, hb]; exact hk), fun h' => ?_⟩
      rw [hU] at h' ⊢
      norm_cast at h' ⊢
      omega
    rcases lt_trichotomy n k with hnk | rfl | hkn
    · rw [hp.boundary_eq_of_lt_cond false ihW.1 ihV.1 hnk]
      exact ⟨(ihV.2 n α).1, fun _ => (ihV.2 n α).2 (by rw [ha]; exact_mod_cast (by omega))⟩
    · cases α
      · rw [hp.boundary_input]
        exact ⟨(ihV.2 _ false).1, fun _ => (ihV.2 _ false).2 (by rw [ha]; exact_mod_cast hka.le)⟩
      · rw [hp.boundary_output]
        exact ⟨(ihW.2 _ true).1, fun _ => (ihW.2 _ true).2 (by rw [hb]; exact_mod_cast hkb.le)⟩
    · have hdim (X : LowerSet P) (c : ℕ) (hc : krullDim X = c)
          (ihX : ∀ (n : ℕ) (α : Bool), IsMoleculeIn P (P.boundary X n α) ∧
            ((n : WithBot ℕ∞) ≤ krullDim X → krullDim (P.boundary X n α) = n)) :
          krullDim (P.boundary X n α) = (min c n : ℕ) := by
        rcases le_total n c with h | h
        · rw [(ihX n α).2 (by rw [hc]; exact_mod_cast h), min_eq_right h]
        · rw [boundary_eq_self (by rw [hc]; exact_mod_cast h), hc, min_eq_left h]
      have hp' := hp.boundary_of_lt ihV.1 ihW.1 hkn α
      refine ⟨.paste k _ _ _ hp' (ihV.2 n α).1 (ihW.2 n α).1 ?_, fun _ => ?_⟩
      · rw [hdim V a ha ihV.2, hdim W b hb ihW.2]
        exact lt_min (by exact_mod_cast lt_min hka hkn) (by exact_mod_cast lt_min hkb hkn)
      · rw [← hp'.sup_eq, LowerSet.krullDim_sup, hdim V a ha ihV.2, hdim W b hb ihW.2,
          ← Nat.mono_cast.map_max]
        congr 1
        omega

theorem isGlobular (h : IsMoleculeIn P U) : P.IsGlobular U :=
  h.isGlobular_and_boundary.1

theorem boundary (h : IsMoleculeIn P U) (n : ℕ) (α : Bool) :
    IsMoleculeIn P (P.boundary U n α) :=
  (h.isGlobular_and_boundary.2 n α).1

theorem krullDim_boundary (h : IsMoleculeIn P U) (hn : (n : WithBot ℕ∞) ≤ krullDim U)
    (α : Bool) : krullDim (P.boundary U n α) = n :=
  (h.isGlobular_and_boundary.2 n α).2 hn

theorem krullDim_bdry (h : IsMoleculeIn P U) (hn : krullDim U = (n + 1 : ℕ)) (α : Bool) :
    krullDim (P.bdry U α) = n := by
  rw [bdry_eq_boundary (by exact_mod_cast hn)]
  exact h.krullDim_boundary (by rw [hn]; exact_mod_cast n.le_succ) α

end IsMoleculeIn

end Atoms.Molecule.OGP
