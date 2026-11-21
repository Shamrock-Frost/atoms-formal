import Atoms.Molecule.Pasting.AtSubmolecule
import Atoms.Molecule.Rewritable.Block

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {U V W R S T : LowerSet P} {k n : ℕ} {α : Bool} {x : P}

variable (P) in
structure IsSubstitutionIn (U V W R : LowerSet P) : Prop where
  rewritable : P.IsRewritableSubmolecule V U
  isMoleculeIn_target : IsMoleculeIn P W
  isRound_target : P.IsRound W
  krullDim_target : krullDim W = krullDim V
  inf_eq : U ⊓ W = P.bdryFull V
  bdry_eq : ∀ β : Bool, P.bdry W β = P.bdry V β
  eq_sup : R = rewritable.complement ⊔ W

namespace IsSubstitutionIn

variable (h : P.IsSubstitutionIn U V W R)
include h

theorem bdryFull_target : P.bdryFull W = P.bdryFull V := by
  rw [bdryFull, bdryFull, h.bdry_eq, h.bdry_eq]

theorem target_le : W ≤ R := le_sup_right.trans h.eq_sup.ge

theorem complement_le : h.rewritable.complement ≤ R := le_sup_left.trans h.eq_sup.ge

theorem bdryFull_le_complement : P.bdryFull V ≤ h.rewritable.complement := fun _ hx =>
  ⟨h.rewritable.isSubmoleculeOf.le (properBoundary_le V (bdryFull_le_properBoundary V hx)),
    fun hi => hi.2 (bdryFull_le_properBoundary V hx)⟩

theorem bdryFull_le_target : P.bdryFull V ≤ W := by
  rw [← h.bdryFull_target]
  exact (bdryFull_le_properBoundary W).trans (properBoundary_le W)

theorem disjoint_interior_target_complement :
    Disjoint (P.interior W) (h.rewritable.complement : Set P) :=
  disjoint_left.2 fun x hxi hxs => hxi.2 (by
    have hxb : x ∈ P.bdryFull W := by
      rw [h.bdryFull_target, ← h.inf_eq]
      exact ⟨hxs.1, hxi.1⟩
    exact bdryFull_le_properBoundary W hxb)

theorem eq_target_of_krullDim_eq_zero (hn : krullDim U = 0) : R = W := by
  rw [h.eq_sup, sup_eq_right]
  intro x hx
  obtain ⟨t, ht, rfl⟩ :=
    h.rewritable.isSubmoleculeOf.isMoleculeIn_right.exists_eq_Iic_of_krullDim_eq_zero hn
  obtain ⟨y, hy⟩ := h.rewritable.isSubmoleculeOf.isMoleculeIn.nonempty
  have hyt : y ≤ t := LowerSet.mem_Iic_iff.1 (h.rewritable.isSubmoleculeOf.le hy)
  have hxV : x ∈ V := V.lower (LowerSet.mem_Iic_iff.1 hx.1) (hyt.antisymm (ht hyt) ▸ hy)
  refine absurd ?_ hx.2
  rw [interior_eq_self (by rw [h.rewritable.krullDim_eq, hn])]
  exact hxV

theorem eq_sup_sup_of_disjoint {X Y : LowerSet P} (hU : U = X ⊔ Y)
    (hd : Disjoint (P.interior V) (Y : Set P)) (hVX : P.IsRewritableSubmolecule V X) :
    R = (hVX.complement ⊔ W) ⊔ Y := by
  refine SetLike.coe_injective ?_
  rw [h.eq_sup, LowerSet.coe_sup, LowerSet.coe_sup, LowerSet.coe_sup,
    IsSubmoleculeOf.coe_complement, IsSubmoleculeOf.coe_complement, hU, LowerSet.coe_sup,
    union_sdiff_distrib, sdiff_eq_left.2 hd.symm, union_right_comm]

theorem sup_inf_eq_of_disjoint {X Y : LowerSet P} (hVX : P.IsRewritableSubmolecule V X)
    (hY : Y ≤ U) (hd : Disjoint (P.interior V) (Y : Set P)) :
    (hVX.complement ⊔ W) ⊓ Y = X ⊓ Y := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxM | hxW, hxY⟩
    · exact ⟨hxM.1, hxY⟩
    · have hxb : x ∈ P.bdryFull V := h.inf_eq ▸ (⟨hY hxY, hxW⟩ : x ∈ U ⊓ W)
      exact ⟨hVX.isSubmoleculeOf.le (properBoundary_le V (bdryFull_le_properBoundary V hxb)),
        hxY⟩
  · rintro x ⟨hxX, hxY⟩
    exact ⟨Or.inl ⟨hxX, fun hi => disjoint_left.1 hd hi hxY⟩, hxY⟩

theorem ofIsSubmoleculeOf {B : LowerSet P} (hB : P.IsSubmoleculeOf B U)
    (hVB : P.IsRewritableSubmolecule V B) :
    P.IsSubstitutionIn B V W (hVB.complement ⊔ W) where
  rewritable := hVB
  isMoleculeIn_target := h.isMoleculeIn_target
  isRound_target := h.isRound_target
  krullDim_target := h.krullDim_target
  inf_eq := le_antisymm (fun x hx => h.inf_eq ▸ (⟨hB.le hx.1, hx.2⟩ : x ∈ U ⊓ W))
    (le_inf ((bdryFull_le_properBoundary V).trans
      ((properBoundary_le V).trans hVB.isSubmoleculeOf.le)) h.bdryFull_le_target)
  bdry_eq := h.bdry_eq
  eq_sup := rfl

theorem dual (J : ℕ → Bool) : (OGP.dual P J).IsSubstitutionIn U V W R where
  rewritable := (isRewritableSubmolecule_dual J).2 h.rewritable
  isMoleculeIn_target := (isMoleculeIn_dual J).2 h.isMoleculeIn_target
  isRound_target := (isRound_dual J).2 h.isRound_target
  krullDim_target := h.krullDim_target
  inf_eq := by
    rw [bdryFull_dual]
    exact h.inf_eq
  bdry_eq β := by
    obtain ⟨m, hm⟩ := h.isMoleculeIn_target.exists_krullDim_eq
    cases m with
    | zero =>
      have h0 : krullDim W ≤ 0 := by rw [hm, Nat.cast_zero]
      rw [bdry_eq_bot (P := OGP.dual P J) h0, bdry_eq_bot (P := OGP.dual P J)
        (h.krullDim_target ▸ h0)]
    | succ m =>
      have hm' : krullDim W = m + 1 := by rw [hm]; push_cast; rfl
      rw [bdry_dual J hm', bdry_dual J (h.krullDim_target ▸ hm'), h.bdry_eq]
  eq_sup := by
    rw [h.rewritable.complement_dual J]
    exact h.eq_sup

end IsSubstitutionIn

theorem IsPastingAtIn.isSubstitutionIn_boundary (h : P.IsPastingAtIn k α S T R) (hr : P.IsRound S)
    (hdS : krullDim S = k + 1) (hkT : (k : WithBot ℕ∞) ≤ krullDim T) :
    P.IsSubstitutionIn (P.boundary T k α) (S ⊓ T) (P.boundary S k α) (P.boundary R k α) := by
  have hS := h.isMoleculeIn_left
  have hT := h.isMoleculeIn_right
  have hkS : (k : WithBot ℕ∞) ≤ krullDim S := by rw [hdS]; exact_mod_cast k.le_succ
  have hkS' : (k : WithBot ℕ∞) < krullDim S := by rw [hdS]; exact_mod_cast k.lt_succ_self
  have hdV : krullDim (S ⊓ T : LowerSet P) = k := by
    rw [h.inf_eq]
    exact hS.krullDim_boundary hkS (!α)
  have hdW : krullDim (P.boundary S k α) = k := hS.krullDim_boundary hkS α
  have hdU : krullDim (P.boundary T k α) = k := hT.krullDim_boundary hkT α
  have hmeet : P.bdryFull (P.boundary S k (!α)) = P.boundary S k (!α) ⊓ P.boundary S k α := by
    rw [← (hS.boundary k (!α)).properBoundary_eq_bdryFull,
      ← hr.inf_boundary_eq_properBoundary hS hkS' (!α), Bool.not_not]
  refine ⟨⟨h.isSubmoleculeOf_inf, hdV.trans hdU.symm, by rw [h.inf_eq]; exact hr.boundary k (!α)⟩,
    hS.boundary k α, hr.boundary k α, hdW.trans hdV.symm, ?_, ?_, SetLike.coe_injective (by
      rw [h.coe_boundary_eq hkS hkT, LowerSet.coe_sup, IsSubmoleculeOf.coe_complement])⟩
  · rw [h.inf_eq, hmeet]
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxT, hxS⟩
      exact ⟨h.inf_eq ▸ (⟨boundary_le S k α hxS, boundary_le T k α hxT⟩ : x ∈ S ⊓ T), hxS⟩
    · rintro x ⟨hx1, hx2⟩
      rw [← h.inf_eq] at hx1
      exact ⟨h.inf_le_boundary hx1, hx2⟩
  · intro β
    rw [h.inf_eq]
    cases k with
    | zero =>
      rw [bdry_eq_bot (by exact_mod_cast krullDim_boundary_le S 0 α),
        bdry_eq_bot (by exact_mod_cast krullDim_boundary_le S 0 (!α))]
    | succ m =>
      have hdW' : krullDim (P.boundary S (m + 1) α) = m + 1 := by rw [hdW]; push_cast; rfl
      have hdV' : krullDim (P.boundary S (m + 1) (!α)) = m + 1 := by
        rw [hS.krullDim_boundary hkS (!α)]; push_cast; rfl
      rw [bdry_eq_boundary hdW', bdry_eq_boundary hdV', hS.isGlobular m (m + 1) m.lt_succ_self β α,
        hS.isGlobular m (m + 1) m.lt_succ_self β (!α)]

theorem boundary_eq_of_isPastingIn_replace_middle {L Q Q' R' : LowerSet P} (gL : P.IsGlobular L)
    (gQ : P.IsGlobular Q) (gR : P.IsGlobular R') (gQ' : P.IsGlobular Q')
    (pl : P.IsPastingIn k L Q (L ⊔ Q)) (pr : P.IsPastingIn k (L ⊔ Q) R' U)
    (p1 : P.IsPastingIn k L Q' (L ⊔ Q')) (p2 : P.IsPastingIn k (L ⊔ Q') R' R) {m : ℕ}
    (hm : m ≤ k) (β : Bool) : P.boundary R m β = P.boundary U m β := by
  have gLQ := pl.isGlobular gL gQ
  have gLQ' := p1.isGlobular gL gQ'
  rcases hm.lt_or_eq with hlt | rfl
  · rw [p2.boundary_eq_of_lt_cond false gR gLQ' hlt β, p1.boundary_eq_of_lt_cond false gQ' gL hlt β,
      pr.boundary_eq_of_lt_cond false gR gLQ hlt β, pl.boundary_eq_of_lt_cond false gQ gL hlt β]
  · cases β
    · rw [p2.boundary_input, p1.boundary_input, pr.boundary_input, pl.boundary_input]
    · rw [p2.boundary_output, pr.boundary_output]

private theorem isPastingAtIn_source_middle (hV : P.IsRewritableSubmolecule V U)
    (hn : krullDim U = n + 1) (b : RewritableBlock P n U V) :
    P.IsPastingAtIn n true V (P.boundary b.middle n false) b.middle where
  isMoleculeIn_left := hV.isSubmoleculeOf.isMoleculeIn
  isMoleculeIn_right := b.isMoleculeIn_middle.boundary n false
  eq_sup := (b.middle_eq false).trans (sup_comm _ _)
  inf_eq := by
    rw [Bool.not_true, inf_comm, b.meet false, bdry_eq_boundary (hV.krullDim_eq.trans hn)]
  isSubmoleculeOf_inf := by
    rw [inf_comm, b.meet false, boundary_eq_self (krullDim_boundary_le b.middle n false)]
    exact (b.rewritable false).isSubmoleculeOf

namespace IsSubstitutionIn

variable (h : P.IsSubstitutionIn U V W R)
include h

theorem isPastingAtIn_target {A B : LowerSet P} (hdV : krullDim V = k + 1) (hdA : krullDim A = k)
    (hAU : A ≤ U) (cV : P.IsPastingAtIn k true V A B) : P.IsPastingAtIn k true W A (W ⊔ A) := by
  have hdW : krullDim W = k + 1 := h.krullDim_target.trans hdV
  have hAself (β : Bool) : P.boundary A k β = A := boundary_eq_self hdA.le β
  have hbV (β : Bool) : P.bdry V β = P.boundary V k β := bdry_eq_boundary hdV β
  have hbW (β : Bool) : P.bdry W β = P.boundary W k β := bdry_eq_boundary hdW β
  have hWV (β : Bool) : P.boundary W k β = P.boundary V k β := by rw [← hbW, ← hbV, h.bdry_eq]
  have hWU : W ⊓ U = P.bdryFull V := by rw [inf_comm, h.inf_eq]
  have hbdryV : P.bdryFull V = P.boundary V k false ⊔ P.boundary V k true := by
    rw [bdryFull, hbV, hbV]
  have hVA : V ⊓ A = P.boundary V k false := cV.inf_eq
  have hWA : W ⊓ A = P.boundary W k false := by
    rw [hWV]
    refine le_antisymm ?_ (le_inf ?_ ?_)
    · rintro x ⟨hxW, hxA⟩
      have hxb : x ∈ P.bdryFull V := hWU ▸ (⟨hxW, hAU hxA⟩ : x ∈ W ⊓ U)
      rw [hbdryV] at hxb
      rcases hxb with hxb | hxb
      · exact hxb
      · exact hVA ▸ (⟨boundary_le V k true hxb, hxA⟩ : x ∈ V ⊓ A)
    · rw [← hWV]
      exact boundary_le W k false
    · rw [← hVA]
      exact inf_le_right
  refine ⟨h.isMoleculeIn_target, cV.isMoleculeIn_right, rfl, hWA, ?_⟩
  have hsub := cV.isSubmoleculeOf_inf
  rw [hVA, hAself] at hsub
  rw [hWA, hAself, hWV]
  exact hsub

theorem isMoleculeIn_and_boundary_of_pos (hn : krullDim U = n + 1) :
    IsMoleculeIn P R ∧ P.IsSubmoleculeOf W R ∧
      ∀ m ≤ n, ∀ β : Bool, P.boundary R m β = P.boundary U m β := by
  have hV := h.rewritable.isSubmoleculeOf.isMoleculeIn
  obtain ⟨b⟩ := nonempty_rewritableBlock h.rewritable hn
  have pl := b.paste_left
  have pr := b.paste_right
  have lim : b.left ⊓ b.middle = P.boundary b.middle n false := pl.inf_eq_input
  have uir := b.sup_inf_right
  have isl := b.input_le_left
  have lis := b.left_inf_self
  have ris := b.right_inf_self
  have uec := b.coe_sup_eq_complement hV
  have iec := b.coe_inf_eq_complement h.rewritable hn
  have hdV : krullDim V = n + 1 := h.rewritable.krullDim_eq.trans hn
  have hdW : krullDim W = n + 1 := h.krullDim_target.trans hdV
  have hkV : (n : WithBot ℕ∞) ≤ krullDim V := by rw [hdV]; exact_mod_cast n.le_succ
  have hkW : (n : WithBot ℕ∞) ≤ krullDim W := by rw [hdW]; exact_mod_cast n.le_succ
  have hmidU : b.middle ≤ U := le_sup_right.trans (le_sup_left.trans pr.sup_eq.le)
  have hQdim : (n : WithBot ℕ∞) ≤ krullDim b.middle :=
    hkV.trans (LowerSet.krullDim_mono b.le_middle)
  set A := P.boundary b.middle n false with hA
  have hAmol : IsMoleculeIn P A := b.isMoleculeIn_middle.boundary n false
  have hdA : krullDim A = n := b.isMoleculeIn_middle.krullDim_boundary hQdim false
  have hAself (β : Bool) : P.boundary A n β = A := boundary_eq_self hdA.le β
  have hAU : A ≤ U := (boundary_le b.middle n false).trans hmidU
  have hbV (β : Bool) : P.bdry V β = P.boundary V n β := bdry_eq_boundary hdV β
  have hbW (β : Bool) : P.bdry W β = P.boundary W n β := bdry_eq_boundary hdW β
  have hWV (β : Bool) : P.boundary W n β = P.boundary V n β := by rw [← hbW, ← hbV, h.bdry_eq]
  have hWU : W ⊓ U = P.bdryFull V := by rw [inf_comm, h.inf_eq]
  have hbdryV : P.bdryFull V = P.boundary V n false ⊔ P.boundary V n true := by
    rw [bdryFull, hbV, hbV]
  have cV : P.IsPastingAtIn n true V A b.middle := isPastingAtIn_source_middle h.rewritable hn b
  have hVA : V ⊓ A = P.boundary V n false := cV.inf_eq
  have cW : P.IsPastingAtIn n true W A (W ⊔ A) := h.isPastingAtIn_target hdV hdA hAU cV
  have hWA : W ⊓ A = P.boundary W n false := cW.inf_eq
  have uW := cW.isMoleculeIn_sup
  have hM'mol : IsMoleculeIn P (W ⊔ A) := uW.1
  have hin : P.boundary (W ⊔ A) n false = A := by
    have := uW.2.2.2.1
    rwa [hAself] at this
  have hleftW : b.left ⊓ W ≤ A := by
    rintro x ⟨hxL, hxW⟩
    have hxb : x ∈ P.bdryFull V := hWU ▸ (⟨hxW, b.left_le hxL⟩ : x ∈ W ⊓ U)
    rw [hbdryV] at hxb
    rcases hxb with hxb | hxb
    · rw [← hVA] at hxb
      exact hxb.2
    · have hxV : x ∈ b.left ⊓ V := ⟨hxL, boundary_le V n true hxb⟩
      rw [lis, hbV, ← hVA] at hxV
      exact hxV.2
  have hleftM : b.left ⊓ (W ⊔ A) = A := by
    refine le_antisymm ?_ (le_inf isl le_sup_right)
    rintro x ⟨hxL, hxW | hxA⟩
    · exact hleftW ⟨hxL, hxW⟩
    · exact hxA
  have hbl : P.boundary b.left n true = A := pl.inf_eq_output.symm.trans lim
  have p1 : P.IsPastingIn n b.left (W ⊔ A) (b.left ⊔ (W ⊔ A)) :=
    ⟨rfl, hleftM.trans hbl.symm, hleftM.trans hin.symm⟩
  have hM''mol : IsMoleculeIn P (b.left ⊔ (W ⊔ A)) := p1.isMoleculeIn b.isMoleculeIn_left hM'mol
  have hRe : R = (b.left ⊔ (W ⊔ A)) ⊔ b.right := by
    refine SetLike.coe_injective ?_
    rw [h.eq_sup, LowerSet.coe_sup, IsSubmoleculeOf.coe_complement, ← uec, LowerSet.coe_sup,
      LowerSet.coe_sup, LowerSet.coe_sup, LowerSet.coe_sup]
    ext x
    have hAL : x ∈ A → x ∈ b.left := fun hx => isl hx
    simp only [mem_union, SetLike.mem_coe]
    tauto
  have hrightW : W ⊓ b.right = P.boundary V n true := by
    refine le_antisymm ?_ (le_inf ?_ ?_)
    · rintro x ⟨hxW, hxR⟩
      have hxb : x ∈ P.bdryFull V := hWU ▸ (⟨hxW, b.right_le hxR⟩ : x ∈ W ⊓ U)
      rw [hbdryV] at hxb
      rcases hxb with hxb | hxb
      · have hxV : x ∈ b.right ⊓ V := ⟨hxR, boundary_le V n false hxb⟩
        rw [ris, hbV] at hxV
        exact hxV
      · exact hxb
    · rw [← hWV]
      exact boundary_le W n true
    · rw [← hbV, ← ris]
      exact inf_le_left
  have hlr : ((b.left ⊓ b.right : LowerSet P) : Set P) =
      (A : Set P) \ P.interior (P.boundary V n false) := by
    rw [iec, hbV]
  have hLMR : (((b.left ⊔ (W ⊔ A)) ⊓ b.right : LowerSet P) : Set P) =
      ((A : Set P) \ P.interior (P.boundary V n false)) ∪ P.boundary V n true := by
    refine subset_antisymm ?_ ?_
    · rintro x ⟨hxM, hxR⟩
      rcases hxM with hxL | hxW | hxA
      · refine Or.inl ?_
        rw [← hlr]
        exact ⟨hxL, hxR⟩
      · refine Or.inr ?_
        rw [← hrightW]
        exact ⟨hxW, hxR⟩
      · refine Or.inl ?_
        rw [← hlr]
        exact ⟨isl hxA, hxR⟩
    · rintro x (hx | hx)
      · rw [← hlr] at hx
        exact ⟨Or.inl hx.1, hx.2⟩
      · rw [← hrightW] at hx
        exact ⟨Or.inr (Or.inl hx.1), hx.2⟩
  have hbM' : ((P.boundary (b.left ⊔ (W ⊔ A)) n true : LowerSet P) : Set P) =
      ((A : Set P) \ P.interior (P.boundary V n false)) ∪ P.boundary V n true := by
    rw [p1.boundary_output, cW.coe_boundary_eq hkW hdA.ge, hAself, hWA, hWV, hWV]
  have hbr : ((P.boundary b.right n false : LowerSet P) : Set P) =
      ((A : Set P) \ P.interior (P.boundary V n false)) ∪ P.boundary V n true := by
    rw [← pr.inf_eq_input, uir, cV.coe_boundary_eq hkV hdA.ge, hAself, hVA]
  have p2 : P.IsPastingIn n (b.left ⊔ (W ⊔ A)) b.right R :=
    ⟨hRe.symm, SetLike.coe_injective (hLMR.trans hbM'.symm),
      SetLike.coe_injective (hLMR.trans hbr.symm)⟩
  refine ⟨p2.isMoleculeIn hM''mol b.isMoleculeIn_right, ?_, fun m hm β => ?_⟩
  · exact (uW.2.1.tail (p1.isPastingFactorOf true hM'mol b.isMoleculeIn_left)).tail
      (p2.isPastingFactorOf false hM''mol b.isMoleculeIn_right)
  · exact boundary_eq_of_isPastingIn_replace_middle b.isMoleculeIn_left.isGlobular
      b.isMoleculeIn_middle.isGlobular b.isMoleculeIn_right.isGlobular hM'mol.isGlobular pl pr p1
      p2 hm β

theorem isMoleculeIn : IsMoleculeIn P R := by
  obtain ⟨m, hm⟩ := h.rewritable.isSubmoleculeOf.isMoleculeIn_right.exists_krullDim_eq
  cases m with
  | zero =>
    rw [h.eq_target_of_krullDim_eq_zero (by rw [hm, Nat.cast_zero])]
    exact h.isMoleculeIn_target
  | succ n => exact (h.isMoleculeIn_and_boundary_of_pos (by rw [hm]; push_cast; rfl)).1

theorem isSubmoleculeOf_target : P.IsSubmoleculeOf W R := by
  obtain ⟨m, hm⟩ := h.rewritable.isSubmoleculeOf.isMoleculeIn_right.exists_krullDim_eq
  cases m with
  | zero =>
    rw [h.eq_target_of_krullDim_eq_zero (by rw [hm, Nat.cast_zero])]
    exact .refl h.isMoleculeIn_target
  | succ n => exact (h.isMoleculeIn_and_boundary_of_pos (by rw [hm]; push_cast; rfl)).2.1

theorem boundary_eq {m : ℕ} (hm : (m : WithBot ℕ∞) < krullDim U) (β : Bool) :
    P.boundary R m β = P.boundary U m β := by
  obtain ⟨d, hd⟩ := h.rewritable.isSubmoleculeOf.isMoleculeIn_right.exists_krullDim_eq
  rw [hd] at hm
  cases d with
  | zero => exact absurd (by exact_mod_cast hm : m < 0) (Nat.not_lt_zero m)
  | succ n =>
    exact (h.isMoleculeIn_and_boundary_of_pos (by rw [hd]; push_cast; rfl)).2.2 m
      (Nat.lt_succ_iff.1 (by exact_mod_cast hm)) β

theorem krullDim_eq : krullDim R = krullDim U := by
  refine le_antisymm ?_ ?_
  · rw [h.eq_sup, LowerSet.krullDim_sup]
    exact sup_le (LowerSet.krullDim_mono fun _ hx => hx.1)
      (h.krullDim_target.trans h.rewritable.krullDim_eq).le
  · rw [← h.krullDim_target.trans h.rewritable.krullDim_eq]
    exact LowerSet.krullDim_mono h.target_le

theorem isRewritableSubmolecule_target : P.IsRewritableSubmolecule W R :=
  ⟨h.isSubmoleculeOf_target,
    (h.krullDim_target.trans h.rewritable.krullDim_eq).trans h.krullDim_eq.symm, h.isRound_target⟩

theorem symm : P.IsSubstitutionIn R W V U where
  rewritable := h.isRewritableSubmolecule_target
  isMoleculeIn_target := h.rewritable.isSubmoleculeOf.isMoleculeIn
  isRound_target := h.rewritable.isRound
  krullDim_target := h.krullDim_target.symm
  inf_eq := by
    rw [h.bdryFull_target]
    refine le_antisymm ?_ (le_inf (h.bdryFull_le_complement.trans h.complement_le)
      ((bdryFull_le_properBoundary V).trans (properBoundary_le V)))
    rintro x ⟨hxR, hxV⟩
    rw [h.eq_sup] at hxR
    rcases hxR with hxs | hxW
    · rw [← h.rewritable.isSubmoleculeOf.isMoleculeIn.properBoundary_eq_bdryFull]
      exact mem_properBoundary_of_notMem_interior hxV hxs.2
    · exact h.inf_eq ▸ (⟨h.rewritable.isSubmoleculeOf.le hxV, hxW⟩ : x ∈ U ⊓ W)
  bdry_eq β := (h.bdry_eq β).symm
  eq_sup := by
    refine le_antisymm (fun x hxU => ?_) ?_
    · by_cases hxV : x ∈ V
      · exact Or.inr hxV
      · have hxs : x ∈ h.rewritable.complement := ⟨hxU, fun hi => hxV hi.1⟩
        exact Or.inl ⟨h.complement_le hxs,
          fun hi => disjoint_left.1 h.disjoint_interior_target_complement hi hxs⟩
    · rintro x (hx | hx)
      · obtain ⟨hxR, hxi⟩ := hx
        rw [h.eq_sup] at hxR
        rcases hxR with hxs | hxW
        · exact hxs.1
        · have hxb : x ∈ P.bdryFull W := by
            rw [← h.isMoleculeIn_target.properBoundary_eq_bdryFull]
            exact mem_properBoundary_of_notMem_interior hxW hxi
          rw [h.bdryFull_target] at hxb
          exact h.rewritable.isSubmoleculeOf.le
            (properBoundary_le V (bdryFull_le_properBoundary V hxb))
      · exact h.rewritable.isSubmoleculeOf.le hx

theorem isPastingIn_cond (α : Bool) {A B : LowerSet P} (hA : IsMoleculeIn P A)
    (hB : IsMoleculeIn P B) (hVB : P.IsRewritableSubmolecule V B)
    (hk : (k : WithBot ℕ∞) < krullDim B) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    P.IsPastingIn k (cond α A (hVB.complement ⊔ W)) (cond α (hVB.complement ⊔ W) A) R := by
  obtain ⟨hs, hiB, hiA⟩ := (isPastingIn_cond_iff α).1 hp
  have h₁ : P.IsSubstitutionIn B V W (hVB.complement ⊔ W) :=
    h.ofIsSubmoleculeOf (hp.isPastingFactorOf α hB hA).isSubmoleculeOf hVB
  have hdisj : Disjoint (P.interior V) (A : Set P) :=
    hVB.isSubmoleculeOf.disjoint_interior_of_inf_le_boundary hVB.krullDim_eq hk
      ((inf_comm B A).trans hiB).le
  have hinter := h.sup_inf_eq_of_disjoint hVB (le_sup_left.trans hs.le) hdisj
  have hR := h.eq_sup_sup_of_disjoint (hs.symm.trans (sup_comm A B)) hdisj hVB
  refine (isPastingIn_cond_iff α).2 ⟨(sup_comm _ _).trans hR.symm, ?_, ?_⟩
  · rw [inf_comm, hinter, inf_comm, hiB, h₁.boundary_eq hk]
  · rw [inf_comm, hinter, inf_comm, hiA]

theorem eq_of_isPastingIn_of_le_cond (α : Bool) {A B : LowerSet P} (hVB : V ≤ B)
    (hk : krullDim B ≤ k) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) : B = U := by
  have hdU : krullDim U ≤ k := by
    rw [← h.rewritable.krullDim_eq]
    exact (LowerSet.krullDim_mono hVB).trans hk
  have hq := (isPastingIn_cond_comm α).1 hp
  have hdA : krullDim A ≤ k := (LowerSet.krullDim_mono (hq.le_cond (!α))).trans hdU
  rw [← ((isPastingIn_cond_iff α).1 hp).1, sup_eq_right.2 (hq.le_of_krullDim_le_cond (!α) hdA)]

theorem complement_sup_target_self (hVV : P.IsRewritableSubmolecule V V) :
    hVV.complement ⊔ W = W :=
  sup_eq_right.2 fun _ hx => h.bdryFull_le_target
    (h.rewritable.isSubmoleculeOf.isMoleculeIn.properBoundary_eq_bdryFull ▸
      mem_properBoundary_of_notMem_interior hx.1 hx.2)

theorem isPastingIn_self_cond (α : Bool) {A : LowerSet P} (hA : IsMoleculeIn P A)
    (hk : (k : WithBot ℕ∞) < krullDim V) (hp : P.IsPastingIn k (cond α A V) (cond α V A) U) :
    P.IsPastingIn k (cond α A W) (cond α W A) R := by
  have hV := h.rewritable.isSubmoleculeOf.isMoleculeIn
  have h' := h.isPastingIn_cond α hA hV ⟨.refl hV, rfl, h.rewritable.isRound⟩ hk hp
  rwa [h.complement_sup_target_self] at h'

theorem isRound (hU : P.IsRound U) : P.IsRound R where
  isGlobular := h.isMoleculeIn.isGlobular
  inf_boundary_zero hpos := by
    rw [h.krullDim_eq] at hpos
    have h0 : ((0 : ℕ) : WithBot ℕ∞) < krullDim U := by exact_mod_cast hpos
    rw [h.boundary_eq h0, h.boundary_eq h0]
    exact hU.inf_boundary_zero hpos
  inf_boundary_succ m hm := by
    rw [h.krullDim_eq] at hm
    have hm' : (m : WithBot ℕ∞) < krullDim U :=
      (by exact_mod_cast m.lt_succ_self : (m : WithBot ℕ∞) < ((m + 1 : ℕ) : WithBot ℕ∞)).trans hm
    rw [h.boundary_eq hm, h.boundary_eq hm, hU.inf_boundary_succ m hm, boundaryFull, boundaryFull,
      h.boundary_eq hm', h.boundary_eq hm']

theorem eq_target_of_eq_source (hU : U = V) : R = W := by
  obtain rfl := hU
  rw [h.eq_sup]
  exact h.complement_sup_target_self _

end IsSubstitutionIn

theorem IsSubstitutionIn.isSubmoleculeOf_of_isSubmoleculeOf {B : LowerSet P}
    (hB : P.IsSubmoleculeOf B U) (h : P.IsSubstitutionIn U V W R)
    (hVB : P.IsRewritableSubmolecule V B) : P.IsSubmoleculeOf (hVB.complement ⊔ W) R := by
  refine IsSubmoleculeOf.induction_paste (motive := fun X U => ∀ R, P.IsSubstitutionIn U V W R →
      ∀ hVX : P.IsRewritableSubmolecule V X, P.IsSubmoleculeOf (hVX.complement ⊔ W) R)
    (fun U _ R h hVX => ?_) ?_ hB R h hVB
  · rw [h.eq_sup]
    exact .refl (h.eq_sup ▸ h.isMoleculeIn)
  intro α k A B U X hp hA hB hkB hAU hBU hXA ih R h hVX
  have hdA : krullDim V = krullDim A :=
    le_antisymm (LowerSet.krullDim_mono (hVX.isSubmoleculeOf.le.trans hXA.le))
      ((LowerSet.krullDim_mono hAU).trans h.rewritable.krullDim_eq.ge)
  have hVA : P.IsRewritableSubmolecule V A := ⟨hVX.isSubmoleculeOf.trans hXA, hdA, hVX.isRound⟩
  have hq := (isPastingIn_cond_comm α).1 hp
  have hA' : P.IsSubstitutionIn A V W (hVA.complement ⊔ W) :=
    h.ofIsSubmoleculeOf (hq.isPastingFactorOf (!α) hA hB).isSubmoleculeOf hVA
  have hsub := ih _ hA' hVX
  by_cases hk : (k : WithBot ℕ∞) < krullDim A
  · exact hsub.trans ((h.isPastingIn_cond (!α) hB hA hVA hk hq).isPastingFactorOf (!α)
      hA'.isMoleculeIn hB).isSubmoleculeOf
  · obtain rfl := h.eq_of_isPastingIn_of_le_cond (!α) (hVX.isSubmoleculeOf.le.trans hXA.le)
      (not_lt.1 hk) hq
    rw [h.eq_sup]
    exact hsub

theorem IsSubstitutionIn.map (f : P ⟶ Q) [IsInclusion f] (h : P.IsSubstitutionIn U V W R) :
    Q.IsSubstitutionIn (map f U) (map f V) (map f W) (map f R) where
  rewritable := (isRewritableSubmolecule_map_iff f V U).2 h.rewritable
  isMoleculeIn_target := (isMoleculeIn_map_iff f W).2 h.isMoleculeIn_target
  isRound_target := (isRound_map_iff f W).2 h.isRound_target
  krullDim_target := by rw [krullDim_map, krullDim_map, h.krullDim_target]
  inf_eq := by rw [← map_inf, h.inf_eq, map_bdryFull]
  bdry_eq β := by rw [← map_bdry, ← map_bdry, h.bdry_eq]
  eq_sup := by
    have hr := (isRewritableSubmolecule_map_iff f V U).2 h.rewritable
    refine (congrArg (fun X : LowerSet P => OGP.map f X) h.eq_sup).trans ?_
    rw [map_sup, IsSubmoleculeOf.map_complement f h.rewritable.isSubmoleculeOf
      h.rewritable.krullDim_eq hr.isSubmoleculeOf hr.krullDim_eq]

end Atoms.Molecule.OGP
