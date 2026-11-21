import Atoms.Diagrammatic.Equivalence.Division

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem exists_pair_of_hasType {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {h u v w : RoundPastingDiagram X} (d : PasteAtData α n u v)
    (ht : HasBdry false (n + 1) h.toPastingDiagram d.pasting w.toPastingDiagram) (hh : TClosure A h)
    (ihh : Unbiased (TClosure A) h) :
    ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram w.toPastingDiagram d.pasting := by
  intro β
  cases β
  · have hE : h ∈ solutionOperator X (TClosure A) :=
      ⟨by rw [ht.dim_h]; omega, fun α' n' u' eq' => (ihh α' n' u' eq').elim fun s => ⟨s.toLax⟩⟩
    obtain ⟨k', hk', ht'⟩ := exists_inverse_of_mem_solutionOperator
      (A := TClosure A) hh hE ht.dim_h
    exact ⟨k', TClosure.trans hk',
      (ht'.of_equiv_side ht.other).of_equiv_other ht.side⟩
  · exact ⟨h, hh, ht.symm⟩

theorem unbiased_of_tClosure {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A)
    (hA : ∀ e ∈ A, Unbiased (TClosure A) e)
    {e : RoundPastingDiagram X} (he : TClosure A e) :
    Unbiased (TClosure A) e := by
  induction he with
  | base ha => exact hA _ ha
  | @comp h u v w n₀ α₀ d ht hh hu hv ihh ihu ihv =>
    intro α n u' eq
    obtain rfl : n = n₀ := by have h1 := eq.dim_e; have h2 := ht.dim_b; omega
    have pair := exists_pair_of_hasType d ht hh ihh
    obtain rfl | rfl := Bool.eq_or_eq_not α₀ α
    · exact nonempty_unbiasedSolution_compose hDgn eq d pair (ihu _) (ihv _)
    · exact nonempty_unbiasedSolution_compose_mixed hDgn eq d pair (ihv α) (ihu α)
  | @div h u v w n₀ α₀ d ht hh hu hw ihh ihu ihw =>
    intro α n u' eq
    obtain rfl : n = n₀ := by have h1 := eq.dim_e; have h2 := d.dim_u'; omega
    have pair := exists_pair_of_hasType d ht hh ihh
    obtain rfl | rfl := Bool.eq_or_eq_not α₀ α
    · exact nonempty_unbiasedSolution_div_same hDgn d eq pair (ihu _) (ihw _)
    · exact nonempty_unbiasedSolution_div_mixed (α := α) hDgn d eq pair (ihw α)

theorem pos_dim_of_tClosure {A : Set (RoundPastingDiagram X)} (hA : ∀ e ∈ A, 0 < e.dim)
    {e : RoundPastingDiagram X} (he : TClosure A e) : 0 < e.dim := by
  induction he with
  | base ha => exact hA _ ha
  | comp d ht _ _ _ _ _ _ => rw [ht.dim_b]; omega
  | div d _ _ _ _ _ _ _ => rw [d.dim_u']; omega

theorem tClosure_subset_eqvSolutions {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) (hpos : ∀ e ∈ A, 0 < e.dim)
    (hA : ∀ e ∈ A, Unbiased (TClosure A) e) :
    TClosure A ⊆ eqvSolutions X :=
  subset_eqvSolutions fun _ he =>
    ⟨pos_dim_of_tClosure hpos he, fun α n u eq =>
      (unbiased_of_tClosure hDgn hA he α n u eq).elim fun s => ⟨s.toLax⟩⟩

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def eqvOrDgn (X : DiagSet.{u}) : Set (RoundPastingDiagram X) :=
  {a | a ∈ eqvSolutions X ∨ a.IsDegenerate}

theorem pos_dim_of_mem_eqvSolutions {e : RoundPastingDiagram X} (he : e ∈ eqvSolutions X) :
    0 < e.dim := by
  have h : e ∈ solutionOperator X (eqvSolutions X) := by
    rw [solutionOperator_eqvSolutions]; exact he
  exact h.1

theorem pos_dim_of_mem_eqvOrDgn (e : RoundPastingDiagram X) (he : e ∈ eqvOrDgn X) : 0 < e.dim := by
  rcases he with he | he
  · exact pos_dim_of_mem_eqvSolutions he
  · exact dim_pos_of_isDegenerate he

theorem unbiased_of_mem_eqvOrDgn (e : RoundPastingDiagram X) (he : e ∈ eqvOrDgn X) :
    Unbiased (TClosure (eqvOrDgn X)) e := by
  rcases he with he | he
  · intro α n u eq
    obtain ⟨s⟩ := unbiased_tClosure_eqvSolutions he α n u eq
    exact ⟨s.mono (TClosure.mono fun _ hb => Or.inl hb)⟩
  · intro α n u eq
    obtain ⟨s⟩ := nonempty_unbiasedSolution_of_isDegenerate he eq
    exact ⟨s.mono (TClosure.mono fun _ hb => Or.inr hb)⟩

theorem tClosure_eqvOrDgn_subset :
    TClosure (eqvOrDgn X) ⊆ eqvSolutions X :=
  tClosure_subset_eqvSolutions (fun _ hd => Or.inr hd) pos_dim_of_mem_eqvOrDgn
    unbiased_of_mem_eqvOrDgn

theorem isDegenerate_mem_eqvSolutions {e : RoundPastingDiagram X} (he : e.IsDegenerate) :
    e ∈ eqvSolutions X :=
  tClosure_eqvOrDgn_subset (.base (Or.inr he))

theorem mem_eqvSolutions_of_tClosure {e : RoundPastingDiagram X}
    (h : TClosure (eqvSolutions X) e) : e ∈ eqvSolutions X :=
  tClosure_eqvOrDgn_subset (TClosure.mono (fun _ hb => Or.inl hb) h)

theorem tClosure_eqvSolutions_eq :
    TClosure (eqvSolutions X) = eqvSolutions X :=
  Set.Subset.antisymm (fun _ h => mem_eqvSolutions_of_tClosure h) fun _ h => .base h

theorem exists_inverse_mem_eqvSolutions {e : RoundPastingDiagram X} (he : e ∈ eqvSolutions X)
    {n : ℕ} (hn : e.dim = n + 1) :
    ∃ e' ∈ eqvSolutions X,
      HasBdry false n e'.toPastingDiagram (e.boundary n true) (e.boundary n false) := by
  have hE : e ∈ solutionOperator X (eqvSolutions X) := by
    rw [solutionOperator_eqvSolutions]; exact he
  obtain ⟨e', hT, ht⟩ := exists_inverse_of_mem_solutionOperator he hE hn
  exact ⟨e', mem_eqvSolutions_of_tClosure hT, ht⟩

theorem pasteAt_mem_eqvSolutions_iff {α : Bool} {n : ℕ} {e w : RoundPastingDiagram X}
    (d : PasteAtData α n e w) (he : e ∈ eqvSolutions X) :
    d.round ∈ eqvSolutions X ↔ w ∈ eqvSolutions X :=
  ⟨fun h => mem_eqvSolutions_of_tClosure
    (TClosure.div d (h := d.isRound_pasting.unit)
      (hasType_unit d.dim_pasting)
      (.base (isDegenerate_mem_eqvSolutions (isDegenerate_unit _))) (.base he) (.base h)),
    fun h => mem_eqvSolutions_of_tClosure
      (TClosure.pasteAt (fun _ hd => isDegenerate_mem_eqvSolutions hd) d (.base he) (.base h))⟩

theorem biInvWitness_of_mem_eqvSolutions {e : RoundPastingDiagram X} (he : e ∈ eqvSolutions X) :
    BiInvWitness (eqvSolutions X) e := by
  have hpos : 0 < e.dim := pos_dim_of_mem_eqvSolutions he
  have hd : e.dim = e.dim - 1 + 1 := by omega
  obtain ⟨s₀⟩ := unbiased_tClosure_eqvSolutions he (!true) (e.dim - 1) _
    (inverseEquation e hd (!true))
  obtain ⟨s₁⟩ := unbiased_tClosure_eqvSolutions he (!false) (e.dim - 1) _
    (inverseEquation e hd (!false))
  have hL₀ := InverseSolution.equiv_boundary_not_sol hd true s₀
  have hL₁ := InverseSolution.equiv_boundary_sol hd true s₀
  have hR₀ := InverseSolution.equiv_boundary_not_sol hd false s₁
  have hR₁ := InverseSolution.equiv_boundary_sol hd false s₁
  have hdL : s₀.sol.dim = e.dim := s₀.data.dim_u'.trans hd.symm
  have hdR : s₁.sol.dim = e.dim := s₁.data.dim_u'.trans hd.symm
  have hpL : e.toPastingDiagram.Pastable s₀.sol.toPastingDiagram (e.dim - 1) :=
    ⟨hL₁.symm, by rw [hdL]; omega⟩
  have hpR : s₁.sol.toPastingDiagram.Pastable e.toPastingDiagram (e.dim - 1) :=
    ⟨hR₁, by rw [hdR]; omega⟩
  refine BiInvData.witness
    { dim_pos := hpos
      inverse := fun α => cond α s₁.sol s₀.sol
      invertor := fun α => cond α (s₁.side true).witness (s₀.side false).witness
      invertor_mem := fun α => Bool.cond_rec_prop α
        (mem_eqvSolutions_of_tClosure (s₁.side true).mem)
        (mem_eqvSolutions_of_tClosure (s₀.side false).mem)
      dim_inverse := fun α =>
        Bool.cond_rec_prop (p := fun x : RoundPastingDiagram X => x.dim = e.dim) α hdR hdL
      dim_invertor := fun α =>
        Bool.cond_rec_prop (p := fun x : RoundPastingDiagram X => x.dim = e.dim + 1) α
          (by rw [(s₁.side true).hasBdry.dim_h]; omega)
          (by rw [(s₀.side false).hasBdry.dim_h]; omega)
      equiv_boundary_inverse := fun α γ => by
        cases α <;> cases γ
        exacts [hL₁, hL₀, hR₀, hR₁]
      pastable := fun α => by cases α; exacts [hpL, hpR]
      boundary_invertor_composite := fun α => ?_
      boundary_invertor_unit := fun α => ?_ }
  · cases α
    · rw [PastingDiagram.boundary_congr _ hd false]
      exact (s₀.side false).hasBdry.side.trans
        ((equiv_paste_pasteAtBoundary _ _ _ false s₀.data.occ s₀.data.rewritable.isSubmoleculeOf
          (InverseSolution.image_dataOcc hd true s₀) s₀.data.equiv hpL).symm)
    · rw [PastingDiagram.boundary_congr _ hd true]
      exact (s₁.side true).hasBdry.side.trans
        ((equiv_paste_pasteAtBoundary _ _ _ true s₁.data.occ s₁.data.rewritable.isSubmoleculeOf
          (InverseSolution.image_dataOcc hd false s₁) s₁.data.equiv hpR).symm)
  · cases α
    · change ((s₀.side false).witness.toPastingDiagram.boundary e.dim true).Equiv _
      rw [PastingDiagram.boundary_congr _ hd true]
      exact (s₀.side false).hasBdry.other
    · change ((s₁.side true).witness.toPastingDiagram.boundary e.dim false).Equiv _
      rw [PastingDiagram.boundary_congr _ hd false]
      exact (s₁.side true).hasBdry.other

theorem eqvSolutions_subset_equivalences : eqvSolutions X ⊆ equivalences X :=
  subset_equivalences fun _ he => biInvWitness_of_mem_eqvSolutions he

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem BiInvData.tClosure_leftInverse {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) (he : e ∈ equivalences X) {n : ℕ} (hn : e.dim = n + 1) :
    TClosure (equivalences X) (D.inverse false) :=
  TClosure.div (compositeData (α := false) hn (D.hasType_inverse hn false))
    (w := (isRound_boundary_of_isRound e.isRound n false).unit)
    ((D.hasBdry_invertor hn false))
    (.base (D.invertor_mem false)) (.base he)
    (.base (mem_equivalences_of_isDegenerate _ (isDegenerate_unit _)))

noncomputable def BiInvData.invertorData {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) {α : Bool} {n : ℕ}
    {u : RoundPastingDiagram X} (eq : Equation α n e u) :
    InvertorData (TClosure (equivalences X)) eq :=
  let Dz := ((mem_equivalences_iff (D.invertor α)).1 (D.invertor_mem α)).data
  have hz : (D.invertor α).dim = n + 1 + 1 := by rw [D.dim_invertor, eq.dim_e]
  InvertorData.ofSides eq (D.inverse α) (D.hasType_inverse eq.dim_e α) (β := α) (D.invertor α)
    (Dz.inverse false) (.base (.base (D.invertor_mem α)))
    (.base (Dz.tClosure_leftInverse (D.invertor_mem α) hz))
    (D.hasBdry_invertor eq.dim_e α)
    ((D.hasBdry_invertor eq.dim_e α).inverse (Dz.hasType_inverse hz false))

theorem unbiased_tClosure_equivalences {e : RoundPastingDiagram X} (he : e ∈ equivalences X) :
    Unbiased (TClosure (equivalences X)) e := by
  intro α n u eq
  obtain ⟨t⟩ := (((mem_equivalences_iff e).1 he).data.invertorData eq).nonempty_unbiasedSolution
    (fun d hd => TClosure.base (mem_equivalences_of_isDegenerate d hd))
  exact ⟨t.mono TClosure.trans⟩

theorem equivalences_subset_eqvSolutions : equivalences X ⊆ eqvSolutions X := fun _ he =>
  tClosure_subset_eqvSolutions (fun d hd => mem_equivalences_of_isDegenerate d hd)
    (fun e he => ((mem_equivalences_iff e).1 he).data.dim_pos)
    (fun _ he => unbiased_tClosure_equivalences he)
    (.base he)

theorem eqvSolutions_eq_equivalences : eqvSolutions X = equivalences X :=
  Set.Subset.antisymm eqvSolutions_subset_equivalences equivalences_subset_eqvSolutions

theorem mem_equivalences_of_tClosure {e : RoundPastingDiagram X}
    (h : e ∈ TClosure (equivalences X)) : e ∈ equivalences X := by
  rw [← eqvSolutions_eq_equivalences] at h ⊢
  exact mem_eqvSolutions_of_tClosure h

theorem exists_inverse_mem_equivalences {e : RoundPastingDiagram X} (he : e ∈ equivalences X)
    {n : ℕ} (hn : e.dim = n + 1) :
    ∃ e' ∈ equivalences X,
      HasBdry false n e'.toPastingDiagram (e.boundary n true) (e.boundary n false) := by
  rw [← eqvSolutions_eq_equivalences] at he ⊢
  exact exists_inverse_mem_eqvSolutions he hn

theorem pasteAt_mem_equivalences_iff {α : Bool} {n : ℕ} {e w : RoundPastingDiagram X}
    (d : PasteAtData α n e w) (he : e ∈ equivalences X) :
    d.round ∈ equivalences X ↔ w ∈ equivalences X := by
  rw [← eqvSolutions_eq_equivalences] at he ⊢
  exact pasteAt_mem_eqvSolutions_iff d he

theorem BiInvData.leftInverse_mem {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) (he : e ∈ equivalences X) :
    (D.inverse false) ∈ equivalences X :=
  mem_equivalences_of_tClosure
    (D.tClosure_leftInverse he (Nat.succ_pred_eq_of_pos D.dim_pos).symm)

end Atoms.Diagrammatic
