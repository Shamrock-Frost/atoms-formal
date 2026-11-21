import Atoms.Diagrammatic.Horn.AtomicComparison
import Atoms.Diagrammatic.Marked.Lifting

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape HomotopicalAlgebra
open Atoms.Homotopical (MarkedPresheaf)

universe u

namespace Atoms.Diagrammatic

theorem natural_eq_sharp_of_isInftyCategory_zero {X : DiagSet.{u}}
    (hX : IsInftyCategory 0 X) :
    MarkedDiagSet.natural.obj X = (MarkedPresheaf.sharp atomMarking).obj X :=
  MarkedPresheaf.ofMarking_congr X fun U => Set.ext fun x =>
    ⟨fun h => Nat.pos_of_ne_zero fun h0 => not_isEquivalence_of_dimension_eq_zero x h0 h,
      fun h => hX.2 U x (Nat.cast_pos.2 h)⟩

theorem isInftyCategory_zero_of_isAtomicHornFibrant {X : DiagSet.{u}}
    (hX : IsAtomicHornFibrant X) : IsInftyCategory 0 X :=
  isInftyCategory_of_hasMarkedRLP 0 ((MarkedPresheaf.sharp atomMarking).obj X)
    ((hasMarkedRLP_sup _ _ _).2 ⟨(hasMarkedRLP_markedHorns_sharp_iff X).2 hX,
      (hasMarkedRLP_markingGeneratorsAbove_iff 0 _).2 fun U x hn =>
        (MarkedPresheaf.mem_marked_sharp atomMarking X U x).2 (Nat.cast_pos.1 hn)⟩)

theorem isAtomicHornFibrant_of_isInftyCategory_zero {X : DiagSet.{u}}
    (hX : IsInftyCategory 0 X) : IsAtomicHornFibrant X :=
  (hasMarkedRLP_markedHorns_sharp_iff X).1
    (natural_eq_sharp_of_isInftyCategory_zero hX ▸
      hasMarkedRLP_markedHorns_natural_of_hasWeakComposites hX.1)

theorem isAtomicHornFibrant_iff_isInftyCategory_zero (X : DiagSet.{u}) :
    IsAtomicHornFibrant X ↔ IsInftyCategory 0 X :=
  ⟨isInftyCategory_zero_of_isAtomicHornFibrant, isAtomicHornFibrant_of_isInftyCategory_zero⟩

theorem isHornFibrant_iff_isInftyCategory_zero (X : DiagSet.{u}) :
    IsHornFibrant X ↔ IsInftyCategory 0 X :=
  (isAtomicHornFibrant_iff_isHornFibrant X).symm.trans
    (isAtomicHornFibrant_iff_isInftyCategory_zero X)

theorem isFibrant_atomicHornInclusions_iff_isInftyCategory_zero (X : DiagSet.{u}) :
    grayExactCylinder.IsFibrant atomicHornInclusions X ↔ IsInftyCategory 0 X :=
  (isFibrant_atomicHornInclusions_iff X).trans (isAtomicHornFibrant_iff_isInftyCategory_zero X)

theorem isFibrant_hornInclusions_iff_isInftyCategory_zero (X : DiagSet.{u}) :
    grayExactCylinder.IsFibrant hornInclusions X ↔ IsInftyCategory 0 X :=
  (isFibrant_hornInclusions_iff X).trans (isHornFibrant_iff_isInftyCategory_zero X)

end Atoms.Diagrammatic
