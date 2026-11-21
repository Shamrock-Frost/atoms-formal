import Atoms.Diagrammatic.Horn.SubmoleculeAnodyne
import Atoms.Diagrammatic.Horn.Atomic
import Atoms.Diagrammatic.Horn.MoleculeLocalizer

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def atomicHornWeak : MorphismProperty DiagSet.{u} :=
  grayExactCylinder.{u}.weakEquivalences atomicHornInclusions

instance isALocalizer_atomicHornWeak : Homotopical.IsALocalizer atomicHornWeak.{u} :=
  grayExactCylinder.{u}.isALocalizer_weakEquivalences atomicHornInclusions
    (atomicHornInclusions_le_hornInclusions.trans hornInclusions_le_monomorphisms)

theorem atomicHornInclusions_le_atomicHornWeak : atomicHornInclusions.{u} ≤ atomicHornWeak :=
  fun _ _ f hf ↦ grayExactCylinder.{u}.anodyne_le_weakEquivalences atomicHornInclusions
    (atomicHornInclusions_le_hornInclusions.trans hornInclusions_le_monomorphisms) f
    (grayExactCylinder.{u}.le_anodyne _ f hf)

section Localizer

variable {W : MorphismProperty DiagSet.{u}}

variable [hW : Homotopical.IsALocalizer W] (hA : atomicHornInclusions ≤ W)
include hA

theorem terminal_from_ball_mem (U : Atom) : W (terminal.from (ball U)) := by
  suffices key : ∀ d : ℕ, ∀ U : Atom, U.dimension ≤ d → W (terminal.from (ball U)) from
    key _ U le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro U hUd
  rcases Nat.eq_zero_or_pos U.dimension with h0 | hpos
  · exact terminal_from_ball_mem_of_dimension_eq_zero U h0
  · obtain ⟨h, hU⟩ := exists_atomicHornData U hpos
    subst hU
    have hΛ := terminal_from_horn_mem_of_ball
      (ih (h.atom.dimension - 1) (by omega)) h.toHornData (by omega)
    exact hW.terminal_from_of_mem _
      (hA (hornInclusion h.toHornData) (MorphismProperty.ofHoms.mk h)) hΛ

theorem homOfLe_mem_of_isMoleculeIn (T : Atom) {S R : LowerSet T.ogp} (h : S ≤ R)
    (hS : IsMoleculeIn T.ogp S) (hR : IsMoleculeIn T.ogp R) :
    W (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) :=
  homOfLe_mem_of_isMoleculeIn_of_ball (m := T.dimension)
    (fun U _ ↦ terminal_from_ball_mem hA U) T h hS hR
    ((LowerSet.krullDim_mono le_top).trans_eq
      (LowerSet.krullDim_top.trans T.krullDim_eq_dimension))

theorem homOfLe_complement_mem (T : Atom) {U V : LowerSet T.ogp} (hU : IsMoleculeIn T.ogp U)
    (hr : T.ogp.IsRound U) (hV : T.ogp.IsRewritableSubmolecule V U) :
    W (Subfunctor.homOfLe (closedSubpresheaf_mono T hV.bdryFull_le_complement)) := by
  obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
  exact homOfLe_mem_of_eq_complement_of_ball (fun U _ ↦ terminal_from_ball_mem hA U) T n le_rfl
    hn hU hr hV hV.bdryFull_le_complement rfl rfl

theorem hornInclusions_le_of_atomicHornInclusions_le : hornInclusions ≤ W := by
  rintro _ _ f ⟨h⟩
  exact hW.of_terminal_from _
    (terminal_from_horn_mem_of_ball (m := h.atom.dimension)
      (fun U _ ↦ terminal_from_ball_mem hA U) h (Nat.le_succ _))
    (terminal_from_ball_mem hA h.atom)

end Localizer

theorem hornInclusions_le_generatedALocalizer :
    hornInclusions.{u} ≤ Homotopical.generatedALocalizer atomicHornInclusions :=
  hornInclusions_le_of_atomicHornInclusions_le (Homotopical.le_generatedALocalizer _)

theorem complement_mem_atomicHornWeak (T : Atom) {U V : LowerSet T.ogp}
    (hU : IsMoleculeIn T.ogp U) (hr : T.ogp.IsRound U)
    (hV : T.ogp.IsRewritableSubmolecule V U) :
    atomicHornWeak.{u} (Subfunctor.homOfLe (closedSubpresheaf_mono T hV.bdryFull_le_complement)) :=
  homOfLe_complement_mem atomicHornInclusions_le_atomicHornWeak T hU hr hV

theorem hornInclusions_le_atomicHornAcyclic :
    hornInclusions ≤ MorphismProperty.monomorphisms DiagSet.{u} ⊓ atomicHornWeak :=
  le_inf hornInclusions_le_monomorphisms
    (hornInclusions_le_of_atomicHornInclusions_le atomicHornInclusions_le_atomicHornWeak)

theorem isAtomicHornFibrant_iff_isHornFibrant (X : DiagSet.{u}) :
    IsAtomicHornFibrant X ↔ IsHornFibrant X := by
  refine ⟨fun hX ↦ ?_, fun hX ↦ MorphismProperty.antitone_rlp
    atomicHornInclusions_le_hornInclusions _ hX⟩
  have hT := (grayExactCylinder.{u}.rlp_trivialCofibrations_terminal_from_iff atomicHornInclusions
    (atomicHornInclusions_le_hornInclusions.trans hornInclusions_le_monomorphisms) X).2
    ((isFibrant_atomicHornInclusions_iff X).2 hX)
  exact MorphismProperty.antitone_rlp hornInclusions_le_atomicHornAcyclic _ hT

theorem atomicHornWeak_eq_hornWeak :
    atomicHornWeak.{u} = hornWeak := by
  ext X Y f
  change (∀ Z, grayExactCylinder.{u}.IsFibrant atomicHornInclusions Z → _) ↔
    (∀ Z, grayExactCylinder.{u}.IsFibrant hornInclusions Z → _)
  simp only [isFibrant_atomicHornInclusions_iff, isFibrant_hornInclusions_iff,
    isAtomicHornFibrant_iff_isHornFibrant]

end Atoms.Diagrammatic
