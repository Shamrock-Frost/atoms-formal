import Atoms.Diagrammatic.Equivalence.MixedComposition

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem equiv_pasteAt_swap {γ : Bool} {n : ℕ} {P Q : RoundPastingDiagram X}
    (d₁ : PasteAtData γ n P Q) (d₂ : PasteAtData (!γ) n Q P) (h₁ : d₁.occ.image = ⊤)
    (h₂ : d₂.occ.image = ⊤) : d₂.pasting.Equiv d₁.pasting := by
  have hc := d₁.isPastingAtIn_pasteAtInl
  have hVW : d₁.pasteAtInl.image ⊓ d₁.pasteAtInr.image =
      d₁.pasting.shape.ogp.boundary d₁.pasteAtInr.image n γ :=
    inter_eq_boundary_pasteAt_of_image_univ _ _ n γ d₁.occ d₁.rewritable.isSubmoleculeOf h₁
      d₁.equiv
  have hc' : IsPastingAtIn d₁.pasting.shape.ogp n (!γ) d₁.pasteAtInr.image d₁.pasteAtInl.image
      ⊤ :=
    ⟨hc.isMoleculeIn_right, hc.isMoleculeIn_left, by rw [hc.eq_sup, sup_comm], by
      rw [inf_comm, hVW, Bool.not_not], by
      rw [inf_comm, hc.inf_eq]
      exact IsSubmoleculeOf.refl (hc.isMoleculeIn_left.boundary _ _)⟩
  have hι : (d₂.occ.trans
      ((Within.boundary P.toPastingDiagram n (!γ)).trans d₁.pasteAtInl)).image =
      d₁.pasteAtInr.image ⊓ d₁.pasteAtInl.image := by
    rw [Within.image_trans, h₂, inf_comm, hc.inf_eq,
      ← Within.image_boundary_trans d₁.pasteAtInl n (!γ)]
    rfl
  exact (equiv_pasteAtBoundary_of_within d₁.pasteAtInr d₁.pasteAtInl hc'
    d₂.occ d₂.rewritable.isSubmoleculeOf hι d₂.equiv).trans
    (equiv_restrictTo_univ _)

def inverseEquation (v : RoundPastingDiagram X) {n : ℕ} (hv : v.dim = n + 1) (γ : Bool) :
    Equation γ n v ((isRound_boundary_of_isRound v.isRound n γ).unit) :=
  Equation.ofBoundary hv (by
    change (v.boundary n γ).unit.dim = n + 1
    rw [dim_unit, dim_boundary v.toPastingDiagram (by omega) γ])
    (boundary_unit
      (dim_boundary v.toPastingDiagram (by omega) γ) γ)

namespace InverseSolution

variable {A : Set (RoundPastingDiagram X)}
  (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {v : RoundPastingDiagram X}
  {n : ℕ} (hv : v.dim = n + 1) (δ : Bool)
  (s : UnbiasedSolution (TClosure A) (inverseEquation v hv (!δ)))

theorem equiv_boundary_not_sol : (s.sol.boundary n δ).Equiv (v.boundary n (!δ)) := by
  have h := (s.side false).geometry.equiv_boundary_not_sol
  rw [Bool.not_not] at h
  exact h.trans (boundary_unit
    (dim_boundary v.toPastingDiagram (by omega) (!δ)) δ)

theorem equiv_boundary_sol : (s.sol.boundary n (!δ)).Equiv (v.boundary n δ) := by
  simpa only [Bool.not_not] using
    ((s.side false).geometry.equiv_boundary_sol_of_compat s.compat).trans
      (equiv_substitute_of_image_eq_univ _ _ _ _ (Within.image_refl _))

theorem hasType_inverse :
    HasBdry false n v.toPastingDiagram (s.sol.boundary n true) (s.sol.boundary n false) := by
  have h₁ := equiv_boundary_not_sol hv δ s
  have h₂ := equiv_boundary_sol hv δ s
  have hd : s.sol.dim = n + 1 := s.data.dim_u'
  refine HasBdry.of_inverse hv (by omega) fun γ => ?_
  cases δ <;> cases γ
  exacts [h₂.symm, h₁.symm, h₁.symm, h₂.symm]

theorem image_dataOcc : s.data.occ.image = ⊤ := by
  have h := s.data.equiv.symm
  rw [Bool.not_not] at h
  exact Within.image_eq_univ_of_equiv s.data.occ
    (h.trans ((equiv_boundary_sol hv δ s).symm))

theorem equiv_pasting_composite :
    s.data.pasting.Equiv
      (compositeData (α := δ) s.data.dim_u' (hasType_inverse hv δ s)).pasting :=
  equiv_pasteAt_swap (compositeData (α := δ) s.data.dim_u' (hasType_inverse hv δ s)) s.data
    (Within.image_refl _) (image_dataOcc hv δ s)

def invertorData {u : RoundPastingDiagram X} (eq' : Equation δ n s.sol u) :
    InvertorData (TClosure A) eq' :=
  ⟨v, hasType_inverse hv δ s, fun β => (s.side β).witness, fun β => .base (s.side β).mem,
    fun β => ((s.side β).hasBdry.of_equiv_side (equiv_pasting_composite hv δ s)).of_equiv_other
      ((equiv_boundary_not_sol hv δ s).symm).unit⟩

include hDgn in
theorem unbiasedSide_sol : UnbiasedSide (TClosure A) δ s.sol := by
  intro n' u eq'
  obtain rfl : n' = n := by have h₁ := eq'.dim_e; have h₂ := s.data.dim_u'; omega
  obtain ⟨t⟩ := (invertorData hv δ s eq').nonempty_unbiasedSolution
    (fun d hd => TClosure.base (hDgn d hd))
  exact ⟨t.mono TClosure.trans⟩

end InverseSolution

end Atoms.Diagrammatic
