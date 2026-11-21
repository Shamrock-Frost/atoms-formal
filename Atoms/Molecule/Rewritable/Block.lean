import Atoms.Molecule.Rewritable.Basic

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {n k : ℕ} {U V A B : LowerSet P}

structure RewritableBlock (P : OGP.{u}) (n : ℕ) (U V : LowerSet P) where
  left : LowerSet P
  middle : LowerSet P
  right : LowerSet P
  isMoleculeIn_left : IsMoleculeIn P left
  isMoleculeIn_middle : IsMoleculeIn P middle
  isMoleculeIn_right : IsMoleculeIn P right
  paste_left : P.IsPastingIn n left middle (left ⊔ middle)
  paste_right : P.IsPastingIn n (left ⊔ middle) right U
  middle_eq : ∀ α, middle = P.boundary middle n α ⊔ V
  meet : ∀ α, P.boundary middle n α ⊓ V = P.bdry V α
  rewritable : ∀ α, P.IsRewritableSubmolecule (P.bdry V α) (P.boundary middle n α)

def RewritableBlock.dual (b : RewritableBlock P n U V) : RewritableBlock (dual P ⊤) n U V where
  left := b.right
  middle := b.middle
  right := b.left
  isMoleculeIn_left := (isMoleculeIn_dual ⊤).2 b.isMoleculeIn_right
  isMoleculeIn_middle := (isMoleculeIn_dual ⊤).2 b.isMoleculeIn_middle
  isMoleculeIn_right := (isMoleculeIn_dual ⊤).2 b.isMoleculeIn_left
  paste_left := (isPastingIn_dual ⊤).2 (by
    have h := b.paste_left.isPastingIn_right_sup b.paste_right
    rwa [sup_comm] at h)
  paste_right := (isPastingIn_dual ⊤).2 (by
    have h := b.paste_left.assoc b.paste_right
    rwa [sup_comm b.middle] at h)
  middle_eq α := by simpa only [boundary_dual_top] using b.middle_eq (!α)
  meet α := by simpa only [boundary_dual_top, bdry_dual_top] using b.meet (!α)
  rewritable α := by
    simpa only [isRewritableSubmolecule_dual, boundary_dual_top, bdry_dual_top] using
      b.rewritable (!α)

theorem nonempty_rewritableBlock_dual :
    Nonempty (RewritableBlock (dual P ⊤) n U V) ↔ Nonempty (RewritableBlock P n U V) :=
  ⟨fun ⟨b⟩ => (congrArg (fun o => Nonempty (RewritableBlock { P with orient := o } n U V))
    (orient_dual_dual P ⊤)).mp ⟨b.dual⟩, fun ⟨b⟩ => ⟨b.dual⟩⟩

theorem nonempty_rewritableBlock_self (hV : IsMoleculeIn P V) (hr : P.IsRound V)
    (hn : krullDim V = n + 1) : Nonempty (RewritableBlock P n V V) := by
  have hs (α : Bool) := boundary_le V n α
  have hun (α : Bool) : P.boundary V n α ⊔ V = V := sup_eq_right.2 (hs α)
  refine ⟨⟨P.boundary V n false, V, P.boundary V n true, hV.boundary n false, hV,
    hV.boundary n true, ?_, ?_, fun α => (hun α).symm, fun α => ?_, fun α => ?_⟩⟩
  · rw [hun false]
    exact isPastingIn_boundary_false_self V n
  · rw [hun false]
    exact isPastingIn_self_boundary_true V n
  · rw [inf_eq_left.2 (hs α), bdry_eq_boundary hn]
  · rw [bdry_eq_boundary hn]
    exact ⟨.refl (hV.boundary n α), rfl, hr.boundary n α⟩

private theorem nonempty_rewritableBlock_of_isPastingIn_left_eq (b : RewritableBlock P n A V)
    (hB : IsMoleculeIn P B) (hp : P.IsPastingIn n A B U) : Nonempty (RewritableBlock P n U V) :=
  ⟨⟨b.left, b.middle, b.right ⊔ B, b.isMoleculeIn_left, b.isMoleculeIn_middle,
    (b.paste_right.isPastingIn_right_sup hp).isMoleculeIn b.isMoleculeIn_right hB, b.paste_left,
    b.paste_right.assoc hp, b.middle_eq, b.meet, b.rewritable⟩⟩

theorem nonempty_rewritableBlock_of_isPastingIn_eq_cond (α : Bool) (b : RewritableBlock P n A V)
    (hB : IsMoleculeIn P B) (hp : P.IsPastingIn n (cond α A B) (cond α B A) U) :
    Nonempty (RewritableBlock P n U V) := by
  cases α
  · exact nonempty_rewritableBlock_dual.1 (nonempty_rewritableBlock_of_isPastingIn_left_eq
      (P := dual P ⊤) b.dual ((isMoleculeIn_dual ⊤).2 hB) ((isPastingIn_dual ⊤).2 hp))
  · exact nonempty_rewritableBlock_of_isPastingIn_left_eq b hB hp

private theorem nonempty_rewritableBlock_of_isPastingIn_left_lt (b : RewritableBlock P n A V)
    (hB : IsMoleculeIn P B) (hVA : P.IsSubmoleculeOf V A) (hr : P.IsRound V)
    (hVU : krullDim V = krullDim U) (hn : krullDim U = n + 1) (hk : k < n)
    (hp : P.IsPastingIn k A B U) : Nonempty (RewritableBlock P n U V) := by
  obtain ⟨L, Q, R, hL, hQ, hR, h1, h2, h3, h4, h5⟩ := b
  set D := P.boundary B n false with hDdef
  have hD : IsMoleculeIn P D := hB.boundary n false
  have hDle : krullDim D ≤ n := krullDim_boundary_le B n false
  have hDs (α : Bool) : P.boundary D n α = D := boundary_eq_self hDle α
  have hDB : P.IsPastingIn n D B B := isPastingIn_boundary_false_self B n
  have hDD : P.IsPastingIn n D D D := by
    have := isPastingIn_boundary_false_self D n
    rwa [hDs] at this
  have hLQ := h1.isMoleculeIn hL hQ
  have hU := isPastingIn_interchange hk hLQ.isGlobular hR.isGlobular hD.isGlobular hB.isGlobular
    h2 hDB hp
  have hk1 := isPastingIn_interchange_left hk hLQ.isGlobular hR.isGlobular hD.isGlobular
    hB.isGlobular h2 hDB hp
  have hk2 := isPastingIn_interchange_right hk hLQ.isGlobular hR.isGlobular hD.isGlobular
    hB.isGlobular h2 hDB hp
  have hk3 := isPastingIn_interchange_left hk hL.isGlobular hQ.isGlobular hD.isGlobular
    hD.isGlobular h1 hDD hk1
  have hk4 := isPastingIn_interchange_right hk hL.isGlobular hQ.isGlobular hD.isGlobular
    hD.isGlobular h1 hDD hk1
  have hLQD := isPastingIn_interchange hk hL.isGlobular hQ.isGlobular hD.isGlobular hD.isGlobular
    h1 hDD hk1
  have heq : (L ⊔ D) ⊔ (Q ⊔ D) = (L ⊔ Q) ⊔ D := by rw [sup_sup_sup_comm, sup_idem]
  rw [← heq] at hU hLQD
  have hpk (α : Bool) : P.IsPastingIn k (P.boundary Q n α) D (P.boundary (Q ⊔ D) n α) := by
    have := hk4.boundary_of_lt hQ.isGlobular hD.isGlobular hk α
    rwa [hDs] at this
  have hmid (α : Bool) : P.boundary (Q ⊔ D) n α = P.boundary Q n α ⊔ D := (hpk α).sup_eq.symm
  have hVmol := hVA.isMoleculeIn
  have hVn : krullDim V = n + 1 := hVU.trans hn
  have hbV (α : Bool) : P.bdry V α = P.boundary V n α := bdry_eq_boundary hVn α
  have hDV (α : Bool) : D ⊓ V ≤ P.bdry V α := by
    rintro x ⟨hxD, hxV⟩
    have hxAB : x ∈ A ⊓ B := ⟨hVA.le hxV, boundary_le B n false hxD⟩
    rw [hp.inf_eq_output] at hxAB
    rw [hbV]
    exact hr.isGlobular.boundary_le_boundary hk true α (hVA.inf_boundary_le k true ⟨hxV, hxAB⟩)
  have hdV (α : Bool) : krullDim (P.bdry V α) = n := by
    rw [hbV]
    exact hVmol.krullDim_boundary (by rw [hVn]; exact_mod_cast n.le_succ) α
  have hin (α : Bool) (h : Q = P.boundary Q n α ⊔ V) :
      Q ⊔ D = P.boundary (Q ⊔ D) n α ⊔ V := by
    rw [hmid, sup_right_comm, ← h]
  have hmeet (α : Bool) (h : P.boundary Q n α ⊓ V = P.bdry V α) :
      P.boundary (Q ⊔ D) n α ⊓ V = P.bdry V α := by
    rw [hmid, inf_sup_right, h, sup_eq_left.2 (hDV α)]
  have hrw (α : Bool) (h : P.IsRewritableSubmolecule (P.bdry V α) (P.boundary Q n α)) :
      P.IsRewritableSubmolecule (P.bdry V α) (P.boundary (Q ⊔ D) n α) := by
    refine ⟨h.isSubmoleculeOf.tail ((hpk α).isPastingFactorOf false (hQ.boundary n α) hD), ?_,
      h.isRound⟩
    rw [hmid, LowerSet.krullDim_sup, ← h.krullDim_eq, hdV]
    exact (sup_eq_left.2 hDle).symm
  exact ⟨⟨L ⊔ D, Q ⊔ D, R ⊔ B, hk3.isMoleculeIn hL hD, hk4.isMoleculeIn hQ hD,
    hk2.isMoleculeIn hR hB, hLQD, hU, fun α => hin α (h3 α), fun α => hmeet α (h4 α),
    fun α => hrw α (h5 α)⟩⟩

theorem nonempty_rewritableBlock_of_isPastingIn_lt_cond (α : Bool) (b : RewritableBlock P n A V)
    (hB : IsMoleculeIn P B) (hVA : P.IsSubmoleculeOf V A) (hr : P.IsRound V)
    (hVU : krullDim V = krullDim U) (hn : krullDim U = n + 1) (hk : k < n)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) : Nonempty (RewritableBlock P n U V) := by
  cases α
  · exact nonempty_rewritableBlock_dual.1 (nonempty_rewritableBlock_of_isPastingIn_left_lt
      (P := dual P ⊤) b.dual ((isMoleculeIn_dual ⊤).2 hB) ((isSubmoleculeOf_dual ⊤).2 hVA)
      ((isRound_dual ⊤).2 hr) hVU hn hk ((isPastingIn_dual ⊤).2 hp))
  · exact nonempty_rewritableBlock_of_isPastingIn_left_lt b hB hVA hr hVU hn hk hp

theorem nonempty_rewritableBlock (hV : P.IsRewritableSubmolecule V U) (hn : krullDim U = n + 1) :
    Nonempty (RewritableBlock P n U V) := by
  obtain ⟨h, hd, hr⟩ := hV
  revert hn hd hr
  refine IsSubmoleculeOf.induction_paste (motive := fun V U => krullDim U = n + 1 →
      krullDim V = krullDim U → P.IsRound V → Nonempty (RewritableBlock P n U V))
    (fun U hU hn hd hr => nonempty_rewritableBlock_self hU hr hn) ?_ h
  intro α k A B U X hp _ hB hkB hAU hBU hXA ih hn hd hr
  have hdAU : krullDim A = krullDim U :=
    le_antisymm (LowerSet.krullDim_mono hAU) (hd ▸ LowerSet.krullDim_mono hXA.le)
  obtain ⟨b⟩ := ih (hdAU.trans hn) (hd.trans hdAU.symm) hr
  have hkn : k ≤ n := by
    have := hkB.trans_le ((LowerSet.krullDim_mono hBU).trans hn.le)
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hdXU : krullDim X = krullDim U := hd
  rcases hkn.lt_or_eq with hk | rfl
  · exact nonempty_rewritableBlock_of_isPastingIn_lt_cond α b hB hXA hr hdXU hn hk hp
  · exact nonempty_rewritableBlock_of_isPastingIn_eq_cond α b hB hp

namespace RewritableBlock

variable (b : RewritableBlock P n U V)

theorem boundary_boundary_middle {j : ℕ} (hj : j < n) (α : Bool) :
    P.boundary (P.boundary b.middle n false) j α = P.boundary U j α := by
  have gL := b.isMoleculeIn_left.isGlobular
  have gQ := b.isMoleculeIn_middle.isGlobular
  have gR := b.isMoleculeIn_right.isGlobular
  have gLQ := (b.paste_left.isMoleculeIn b.isMoleculeIn_left b.isMoleculeIn_middle).isGlobular
  rw [gQ j n hj α false, b.paste_right.boundary_eq_of_lt_cond false gR gLQ hj α,
    b.paste_left.boundary_eq_of_lt_cond true gL gQ hj α]

theorem isRound_input (hr : P.IsRound U) (hn : krullDim U = n + 1) :
    P.IsRound (P.boundary b.middle n false) := by
  have hA := b.isMoleculeIn_middle.boundary n false
  have hdA : krullDim (P.boundary b.middle n false) ≤ n := krullDim_boundary_le b.middle n false
  refine ⟨hA.isGlobular, fun h0 => ?_, fun j hj => ?_⟩
  · have hn0 : 0 < n := by exact_mod_cast h0.trans_le hdA
    rw [b.boundary_boundary_middle hn0, b.boundary_boundary_middle hn0]
    exact hr.inf_boundary_zero (by rw [hn]; exact_mod_cast n.succ_pos)
  · have hjn : j + 1 < n := by exact_mod_cast hj.trans_le hdA
    rw [b.boundary_boundary_middle hjn, b.boundary_boundary_middle hjn, boundaryFull,
      b.boundary_boundary_middle (by omega), b.boundary_boundary_middle (by omega),
      hr.inf_boundary_succ j (by rw [hn]; exact_mod_cast hjn.trans n.lt_succ_self), boundaryFull]

theorem sup_inf_right : (b.left ⊔ b.middle) ⊓ b.right = P.boundary b.middle n true := by
  rw [b.paste_right.inf_eq_output, b.paste_left.boundary_output]

theorem input_le_left : P.boundary b.middle n false ≤ b.left := by
  rw [← b.paste_left.inf_eq_input]
  exact inf_le_left

theorem output_le_right : P.boundary b.middle n true ≤ b.right :=
  (boundary_dual_top b.middle n false).symm.trans_le b.dual.input_le_left

theorem le_middle : V ≤ b.middle :=
  calc V ≤ P.boundary b.middle n false ⊔ V := le_sup_right
    _ = b.middle := (b.middle_eq false).symm

theorem left_le : b.left ≤ U := (le_sup_left.trans le_sup_left).trans b.paste_right.sup_eq.le

theorem right_le : b.right ≤ U := b.dual.left_le

theorem left_inf_right :
    b.left ⊓ b.right = P.boundary b.middle n false ⊓ P.boundary b.middle n true := by
  refine le_antisymm ?_ (inf_le_inf b.input_le_left b.output_le_right)
  rintro x ⟨hl, hr⟩
  have hB : x ∈ P.boundary b.middle n true := b.sup_inf_right ▸ ⟨Or.inl hl, hr⟩
  refine ⟨?_, hB⟩
  rw [← b.paste_left.inf_eq_input]
  exact ⟨hl, boundary_le b.middle n true hB⟩

theorem left_inf_self : b.left ⊓ V = P.bdry V false := by
  rw [← b.meet false]
  refine le_antisymm ?_ (inf_le_inf_right V b.input_le_left)
  rintro x ⟨hl, hv⟩
  refine ⟨?_, hv⟩
  rw [← b.paste_left.inf_eq_input]
  exact ⟨hl, b.le_middle hv⟩

theorem right_inf_self : b.right ⊓ V = P.bdry V true :=
  b.dual.left_inf_self.trans (bdry_dual_top V false)

theorem coe_sup_eq_complement (hV : IsMoleculeIn P V) :
    ((b.left ⊔ b.right : LowerSet P) : Set P) = (U : Set P) \ P.interior V := by
  have hpb : P.properBoundary V = P.bdryFull V := hV.properBoundary_eq_bdryFull
  have hs : (b.left ⊔ b.right) ⊓ V = P.bdryFull V := by
    rw [inf_sup_right, b.left_inf_self, b.right_inf_self, bdryFull]
  ext x
  constructor
  · exact fun hx => ⟨sup_le b.left_le b.right_le hx, fun ⟨hv, hnb⟩ => hnb (hpb ▸ hs ▸ ⟨hx, hv⟩)⟩
  · rintro ⟨hu, hni⟩
    have hu' : x ∈ (b.left ⊔ b.middle) ⊔ b.right := by
      rw [b.paste_right.sup_eq]
      exact hu
    rcases hu' with (hl | hq) | hr
    · exact Or.inl hl
    · have hq' : x ∈ P.boundary b.middle n false ⊔ V := by
        rw [← b.middle_eq false]
        exact hq
      rcases hq' with ha | hv
      · exact Or.inl (b.input_le_left ha)
      · by_cases hbd : x ∈ P.bdryFull V
        · exact (hs ▸ hbd : x ∈ (b.left ⊔ b.right) ⊓ V).1
        · exact absurd ⟨hv, hpb ▸ hbd⟩ hni
    · exact Or.inr hr

theorem coe_inf_eq_complement (hV : P.IsRewritableSubmolecule V U) (hn : krullDim U = n + 1) :
    ((b.left ⊓ b.right : LowerSet P) : Set P) =
      (P.boundary b.middle n false : Set P) \ P.interior (P.bdry V false) := by
  have hVmol := hV.isSubmoleculeOf.isMoleculeIn
  have hVn : krullDim V = n + 1 := hV.krullDim_eq.trans hn
  have hpos : 0 < krullDim V := by rw [hVn]; exact_mod_cast n.succ_pos
  have hround : P.bdry V false ⊓ P.bdry V true = P.bdryFull (P.bdry V false) :=
    hV.isRound.bdry_inf_bdry hVn (by
      rw [bdry_eq_boundary hVn]
      exact hVmol.krullDim_boundary (by rw [hVn]; exact_mod_cast n.le_succ) false)
  have hpb : P.properBoundary (P.bdry V false) = P.bdryFull (P.bdry V false) :=
    (hVmol.bdry hpos false).properBoundary_eq_bdryFull
  rw [b.left_inf_right]
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, fun ⟨hvf, hnb⟩ => hnb ?_⟩
    have hv : x ∈ V := (b.meet false ▸ hvf : x ∈ P.boundary b.middle n false ⊓ V).2
    rw [hpb, ← hround]
    exact ⟨hvf, b.meet true ▸ (⟨hb, hv⟩ : x ∈ P.boundary b.middle n true ⊓ V)⟩
  · rintro ⟨ha, hni⟩
    refine ⟨ha, ?_⟩
    by_cases hv : x ∈ V
    · have hvf : x ∈ P.bdry V false :=
        b.meet false ▸ (⟨ha, hv⟩ : x ∈ P.boundary b.middle n false ⊓ V)
      have hbf : x ∈ P.bdryFull (P.bdry V false) := by
        by_contra hc
        exact hni ⟨hvf, hpb ▸ hc⟩
      rw [← hround] at hbf
      exact (b.meet true ▸ hbf.2 : x ∈ P.boundary b.middle n true ⊓ V).1
    · have hq : x ∈ P.boundary b.middle n true ⊔ V :=
        b.middle_eq true ▸ boundary_le b.middle n false ha
      exact hq.resolve_right hv

theorem outer_boundary (hr : P.IsRound U) (hV : P.IsRewritableSubmolecule V U)
    (hn : krullDim U = n + 1) :
    P.bdry U false ≤ b.left ∧ P.bdry U true ≤ b.right ∧
      P.bdry U false ⊓ P.bdry U true = P.bdryFull (P.boundary b.middle n false) ∧
      krullDim (P.boundary b.middle n false) = n := by
  have hQdim : (n : WithBot ℕ∞) ≤ krullDim b.middle := by
    have h : krullDim V ≤ krullDim b.middle := LowerSet.krullDim_mono b.le_middle
    rw [hV.krullDim_eq, hn] at h
    exact (by exact_mod_cast n.le_succ : (n : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞)).trans h
  have hdA : krullDim (P.boundary b.middle n false) = n :=
    b.isMoleculeIn_middle.krullDim_boundary hQdim false
  refine ⟨?_, ?_, ?_, hdA⟩
  · rw [bdry_eq_boundary hn, b.paste_right.boundary_input, b.paste_left.boundary_input]
    exact boundary_le _ _ _
  · rw [bdry_eq_boundary hn, b.paste_right.boundary_output]
    exact boundary_le _ _ _
  · rw [bdry_eq_boundary hn, bdry_eq_boundary hn]
    cases n with
    | zero =>
      rw [bdryFull, bdry_eq_bot hdA.le, bdry_eq_bot hdA.le, sup_bot_eq]
      exact hr.inf_boundary_zero (by rw [hn]; exact_mod_cast Nat.zero_lt_one)
    | succ m =>
      rw [hr.inf_boundary_succ m (by rw [hn]; exact_mod_cast Nat.lt_succ_self (m + 1)), bdryFull,
        bdry_eq_boundary hdA, bdry_eq_boundary hdA, b.boundary_boundary_middle m.lt_succ_self,
        b.boundary_boundary_middle m.lt_succ_self, boundaryFull]

end RewritableBlock

end Atoms.Molecule.OGP
