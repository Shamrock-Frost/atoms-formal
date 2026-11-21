import Atoms.Molecule.Construction.SimplexCubeClass
import Atoms.Molecule.MoleculeShape.Enumeration

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

private theorem exists_grade_of_krullDim {F : ℕ → OGP.{u}} {P : OGP.{u}}
    (h : ∃ n : ℕ, krullDim (⊤ : LowerSet P) = n ∧ Nonempty (P ≅ F n)) :
    ∃ x : P, Nonempty (P ≅ F (grade ℕ x)) := by
  obtain ⟨n, hn, e⟩ := h
  rw [LowerSet.krullDim_top] at hn
  obtain ⟨x, hx⟩ := exists_grade_eq_of_krullDim_eq hn
  exact ⟨x, by rwa [hx]⟩

theorem isOrientedSimplex_iff_exists_grade (P : OGP.{u}) :
    IsOrientedSimplex P ↔ ∃ x : P, Nonempty (P ≅ simplex.{u} (grade ℕ x)) :=
  ⟨fun h => exists_grade_of_krullDim h.nonempty_iso,
    fun ⟨_, h⟩ => isOrientedSimplex_iff.2 ⟨_, h⟩⟩

theorem isOrientedCube_iff_exists_grade (P : OGP.{u}) :
    IsOrientedCube P ↔ ∃ x : P, Nonempty (P ≅ cube.{u} (grade ℕ x)) :=
  ⟨fun h => exists_grade_of_krullDim h.nonempty_iso, fun ⟨_, h⟩ => isOrientedCube_iff.2 ⟨_, h⟩⟩

instance decidableIsOrientedSimplex (P : OGP.{0}) [FinEnum P] [DecidableLE P] :
    Decidable (IsOrientedSimplex P) :=
  decidable_of_iff _ (isOrientedSimplex_iff_exists_grade P).symm

instance decidableIsOrientedCube (P : OGP.{0}) [FinEnum P] [DecidableLE P] :
    Decidable (IsOrientedCube P) :=
  decidable_of_iff _ (isOrientedCube_iff_exists_grade P).symm

end Atoms.Molecule.OGP
