import Atoms.Molecule.Cylinder.PartialMolecule
import Atoms.Molecule.Pasting.Staged

universe u

open Order

namespace Atoms.Molecule.OGP

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U}

theorem boundary_over_of_boundary_le {V : LowerSet U} (hg : U.IsGlobular V) {n : ℕ} {α : Bool}
    (hK : U.boundary V n α ≤ K) :
    (partialCylinder U K).boundary (over K V) n α = over K (U.boundary V n α) := by
  rcases n with _ | j
  · rw [boundary_over_zero, over_eq_copy_of_le hK α]
  · rw [boundary_over_succ hg, ← over_eq_copy_of_le hK α, ← over_sup,
      sup_eq_left.2 (hg.boundary_le_boundary (Nat.lt_succ_self j) (!α) α)]

end PartialCylinder

open PartialCylinder

namespace IsStagedPasting

variable {U : OGP.{u}} {K : LowerSet U} {m : ℕ} {X : LowerSet U} {L R M : ℕ → LowerSet U}

private theorem isPastingIn_over {i : ℕ} {A B C : LowerSet U} (hA : U.IsGlobular A)
    (hB : U.IsGlobular B) (hp : U.IsPastingIn i A B C)
    (hK : ∀ y ∈ C, grade ℕ y ≤ i → y ∈ K) :
    (partialCylinder U K).IsPastingIn i (over K A) (over K B) (over K C) := by
  have hle (D : LowerSet U) (hD : D ≤ C) (α : Bool) : U.boundary D i α ≤ K := fun y hy =>
    hK y (hD (boundary_le D i α hy)) (grade_le_of_mem_boundary hy)
  refine ⟨by rw [← over_sup, hp.sup_eq], ?_, ?_⟩
  · rw [boundary_over_of_boundary_le hA (hle A (hp.sup_eq ▸ le_sup_left) true), ← over_inf,
      hp.inf_eq_output]
  · rw [boundary_over_of_boundary_le hB (hle B (hp.sup_eq ▸ le_sup_right) false), ← over_inf,
      hp.inf_eq_input]

theorem over (h : U.IsStagedPasting m X L R M)
    (hL : ∀ i < m, L (i + 1) ≤ K) (hR : ∀ i < m, R (i + 1) ≤ K)
    (hK : ∀ i < m, ∀ y ∈ M (i + 1), grade ℕ y ≤ i → y ∈ K) :
    (partialCylinder U K).IsStagedPasting m (over K X) (fun i => over K (L i))
      (fun i => over K (R i)) (fun i => over K (M i)) := by
  refine ⟨by rw [h.stage_zero], fun i hi => isMoleculeIn_over (h.isMoleculeIn_stage i hi),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := h.stage_succ i hi
    have hLm := (h.isMoleculeIn_left i hi).1
    have hRm := (h.isMoleculeIn_right i hi).1
    have hMm := h.isMoleculeIn_stage i hi.le
    have hsub : L (i + 1) ⊔ M i ≤ M (i + 1) := h2.sup_eq ▸ le_sup_left
    exact ⟨isPastingIn_over hLm.isGlobular hMm.isGlobular h1 fun y hy => hK i hi y (hsub hy),
      isPastingIn_over (h1.isMoleculeIn hLm hMm).isGlobular hRm.isGlobular h2 (hK i hi)⟩
  · exact ⟨isMoleculeIn_over (h.isMoleculeIn_left i hi).1, by
      rw [over_eq_copy_of_le (hL i hi) false, krullDim_copy]; exact (h.isMoleculeIn_left i hi).2⟩
  · exact ⟨isMoleculeIn_over (h.isMoleculeIn_right i hi).1, by
      rw [over_eq_copy_of_le (hR i hi) false, krullDim_copy]; exact (h.isMoleculeIn_right i hi).2⟩

end IsStagedPasting

end Atoms.Molecule.OGP
