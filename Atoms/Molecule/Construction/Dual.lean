import Atoms.Molecule.Construction.Basic

universe u

open Order
open scoped symmDiff

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} (J : ℕ → Bool)

@[simp] theorem orient_dual {x y : P} (h : y ⋖ x) :
    (dual P J).orient h = xor (J (grade ℕ x)) (P.orient h) :=
  rfl

variable (P) in
@[simp] theorem dual_bot : dual P ⊥ = P := by
  cases P
  simp only [dual, OGP.mk.injEq, heq_eq_eq, true_and]
  funext x y h
  simp

variable (P) in
theorem dual_dual (I : ℕ → Bool) : dual (dual P J) I = dual P (I ∆ J) := by
  cases P
  simp only [dual, OGP.mk.injEq, heq_eq_eq, true_and]
  funext x y h
  simp [Pi.symmDiff_apply, Bool.symmDiff_eq_xor]

theorem dual_involutive : Function.Involutive fun P : OGP.{u} => dual P J := fun P =>
  (dual_dual P J J).trans (by rw [symmDiff_self, dual_bot])

variable (P) in
theorem orient_dual_dual : @OGP.orient (dual (dual P J) J) = @OGP.orient P :=
  eq_of_heq (congr_arg_heq (@OGP.orient) (dual_involutive J P))

variable (P) in
theorem dual_iff_of_forall {Φ : ∀ Q : OGP.{u}, LowerSet Q → Prop}
    (h : ∀ (Q : OGP.{u}) (U : LowerSet Q), Φ Q U → Φ (dual Q J) U) (U : LowerSet P) :
    Φ (dual P J) U ↔ Φ P U :=
  ⟨fun hU => (congrArg (fun o => Φ { P with orient := o } U) (orient_dual_dual P J)).mp
    (h (dual P J) U hU), h P U⟩

abbrev topDim (n : ℕ) : ℕ → Bool := fun d => decide (d = n)

@[simp] theorem cofaces_dual (α : Bool) (x : P) :
    (dual P J).cofaces α x = P.cofaces (xor (J (grade ℕ x + 1)) α) x := by
  ext y
  refine exists_congr fun h => ?_
  rw [orient_dual, Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)]
  cases J (grade ℕ y) <;> cases P.orient h <;> cases α <;> decide

theorem facesIn_dual (U : Set P) (n : ℕ) (α : Bool) :
    (dual P J).facesIn U n α = P.facesIn U n (xor (J (n + 1)) α) := by
  ext x
  refine and_congr_right fun _ => and_congr_right fun hn => ?_
  rw [cofaces_dual, hn, Bool.xor_not]

theorem boundary_dual (U : LowerSet P) (n : ℕ) (α : Bool) :
    (dual P J).boundary U n α = P.boundary U n (xor (J (n + 1)) α) :=
  SetLike.ext fun x => by rw [mem_boundary, mem_boundary, facesIn_dual]

theorem boundaryFull_dual (U : LowerSet P) (n : ℕ) :
    (dual P J).boundaryFull U n = P.boundaryFull U n := by
  rw [boundaryFull, boundaryFull, boundary_dual, boundary_dual]
  cases J (n + 1)
  · rfl
  · exact sup_comm _ _

private theorem inf_boundary_dual (U : LowerSet P) (n : ℕ) :
    (dual P J).boundary U n false ⊓ (dual P J).boundary U n true =
      P.boundary U n false ⊓ P.boundary U n true := by
  rw [boundary_dual, boundary_dual]
  cases J (n + 1)
  · rfl
  · exact inf_comm _ _

theorem bdry_dual {U : LowerSet P} {n : ℕ} (hU : krullDim U = n + 1) (α : Bool) :
    (dual P J).bdry U α = P.bdry U (xor (J (n + 1)) α) := by
  rw [bdry_eq_boundary (P := dual P J) hU, bdry_eq_boundary hU, boundary_dual]

theorem boundary_dual_top (U : LowerSet P) (n : ℕ) (α : Bool) :
    (dual P ⊤).boundary U n α = P.boundary U n (!α) := by
  simp only [boundary_dual, Pi.top_apply, top_eq_true, Bool.true_bne]

theorem bdry_dual_top (U : LowerSet P) (α : Bool) : (dual P ⊤).bdry U α = P.bdry U (!α) := by
  simp only [bdry, boundary_dual_top]

theorem bdryFull_dual (U : LowerSet P) : (dual P J).bdryFull U = P.bdryFull U := by
  by_cases h : ∃ n : ℕ, krullDim U = n + 1
  · obtain ⟨n, hn⟩ := h
    rw [bdryFull, bdryFull, bdry_dual J hn, bdry_dual J hn]
    cases J (n + 1)
    · rfl
    · exact sup_comm _ _
  · have hb (Q : OGP.{u}) (V : LowerSet Q) (hV : ¬∃ n : ℕ, krullDim V = n + 1) (α : Bool) :
        Q.bdry V α = ⊥ :=
      iSup_eq_bot.2 fun n => iSup_eq_bot.2 fun hn => (hV ⟨n, hn⟩).elim
    rw [bdryFull, bdryFull, hb (dual P J) U h, hb (dual P J) U h, hb P U h, hb P U h]

theorem isGlobular_dual {U : LowerSet P} : (dual P J).IsGlobular U ↔ P.IsGlobular U :=
  dual_iff_of_forall P J (Φ := IsGlobular) (fun _ _ h k n hkn α β => by
    simp only [boundary_dual]
    exact h k n hkn _ _) U

theorem isRound_dual {U : LowerSet P} : (dual P J).IsRound U ↔ P.IsRound U :=
  dual_iff_of_forall P J (Φ := IsRound) (fun _ U h =>
    { isGlobular := (isGlobular_dual J).2 h.isGlobular
      inf_boundary_zero := fun hd => (inf_boundary_dual J U 0).trans (h.inf_boundary_zero hd)
      inf_boundary_succ := fun n hn => (inf_boundary_dual J U (n + 1)).trans
        ((h.inf_boundary_succ n hn).trans (boundaryFull_dual J U n).symm) }) U

theorem bdry_Iic_dual (t : P) (α : Bool) :
    (dual P J).bdry (LowerSet.Iic t) α = P.bdry (LowerSet.Iic t) (xor (J (grade ℕ t)) α) := by
  rw [bdry_Iic, bdry_Iic, faces_dual]

theorem isPastingIn_dual {k : ℕ} {V W U : LowerSet P} :
    (dual P J).IsPastingIn k V W U ↔
      P.IsPastingIn k (cond (J (k + 1)) W V) (cond (J (k + 1)) V W) U := by
  have hV := boundary_dual J V k true
  have hW := boundary_dual J W k false
  generalize J (k + 1) = b at hV hW ⊢
  cases b
  · exact ⟨fun ⟨hs, ho, hi⟩ => ⟨hs, ho.trans hV, hi.trans hW⟩,
      fun ⟨hs, ho, hi⟩ => ⟨hs, ho.trans hV.symm, hi.trans hW.symm⟩⟩
  · exact ⟨fun ⟨hs, ho, hi⟩ => ⟨(sup_comm W V).trans hs, (inf_comm W V).trans (hi.trans hW),
        (inf_comm W V).trans (ho.trans hV)⟩,
      fun ⟨hs, ho, hi⟩ => ⟨(sup_comm V W).trans hs, (inf_comm V W).trans (hi.trans hV.symm),
        (inf_comm V W).trans (ho.trans hW.symm)⟩⟩

theorem isPastingIn_cond_dual {k : ℕ} {A B U : LowerSet P} (β : Bool) :
    (dual P J).IsPastingIn k (cond β A B) (cond β B A) U ↔
      P.IsPastingIn k (cond (xor (J (k + 1)) β) A B) (cond (xor (J (k + 1)) β) B A) U := by
  rw [isPastingIn_dual]
  cases J (k + 1) <;> cases β <;> rfl

theorem isMoleculeIn_dual {U : LowerSet P} : IsMoleculeIn (dual P J) U ↔ IsMoleculeIn P U :=
  dual_iff_of_forall P J (Φ := IsMoleculeIn) (fun Q _ h => by
    induction h with
    | point x hx => exact .point (P := dual Q J) x hx
    | atom t hr _ ih =>
      refine .atom (P := dual Q J) t ((isRound_dual J).2 hr) fun α => ?_
      rw [bdry_Iic_dual]
      exact ih _
    | paste k V W U hp _ _ hk ihV ihW =>
      cases hj : J (k + 1)
      · exact .paste (P := dual Q J) k V W U ((isPastingIn_dual J).2 (by rwa [hj])) ihV ihW hk
      · exact .paste (P := dual Q J) k W V U ((isPastingIn_dual J).2 (by rwa [hj])) ihW ihV
          (by rwa [min_comm])) U

theorem isPastingFactorOf_dual {X U : LowerSet P} :
    (dual P J).IsPastingFactorOf X U ↔ P.IsPastingFactorOf X U := by
  refine exists_congr fun k => ?_
  simp only [isPastingIn_dual, isMoleculeIn_dual]
  cases J (k + 1)
  · rfl
  · exact ⟨fun ⟨α, Y, h⟩ => ⟨!α, Y, by simpa only [cond_true, Bool.cond_not] using h⟩,
      fun ⟨α, Y, h⟩ => ⟨!α, Y, by simpa only [cond_true, Bool.cond_not, Bool.not_not] using h⟩⟩

theorem isSubmoleculeOf_dual {X U : LowerSet P} :
    (dual P J).IsSubmoleculeOf X U ↔ P.IsSubmoleculeOf X U :=
  and_congr (isMoleculeIn_dual J)
    ⟨Relation.ReflTransGen.mono (fun _ _ => (isPastingFactorOf_dual (P := P) J).1) X U,
      Relation.ReflTransGen.mono (fun _ _ => (isPastingFactorOf_dual (P := P) J).2) X U⟩

theorem isAtomIn_dual {U : LowerSet P} : (dual P J).IsAtomIn U ↔ P.IsAtomIn U :=
  and_congr (isMoleculeIn_dual J) Iff.rfl

end Atoms.Molecule.OGP
