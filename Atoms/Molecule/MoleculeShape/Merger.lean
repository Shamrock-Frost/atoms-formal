import Atoms.Molecule.MoleculeShape.ParallelAtom

open CategoryTheory Order

namespace Atoms.Molecule.RoundShape

open OGP

variable (U : RoundShape) {n : ℕ} (hd : U.dimension = n + 1)

def gluing : (U.boundary n false).ogp.restrict ((U.boundary n false).ogp.bdryFull ⊤) ≅
    (U.boundary n true).ogp.restrict ((U.boundary n true).ogp.bdryFull ⊤) :=
  mergerGluing U.isMolecule (U.bdryIso hd false) (U.bdryIso hd true)

theorem isSigned_gluing : (U.gluing hd).IsSigned :=
  isSigned_mergerGluing _ _ _

include hd in
theorem dimension_boundary_eq :
    (U.boundary n false).dimension = (U.boundary n true).dimension :=
  (U.dimension_boundary (by omega) false).trans (U.dimension_boundary (by omega) true).symm

private abbrev mergerShape : MoleculeShape :=
  MoleculeShape.rewriteAtom _ _ (U.gluing hd) (U.isSigned_gluing hd)
    (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
    (U.dimension_boundary_eq hd)

def merger : RoundShape :=
  ⟨U.mergerShape hd, MoleculeShape.isRound_rewriteAtom _ _ (U.gluing hd) (U.isSigned_gluing hd)
    (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
    (U.dimension_boundary_eq hd)⟩

theorem isAtom_merger : (U.merger hd).ogp.IsAtom :=
  MoleculeShape.isAtom_rewriteAtom _ _ (U.gluing hd) (U.isSigned_gluing hd)
    (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
    (U.dimension_boundary_eq hd)

theorem dimension_merger : (U.merger hd).dimension = U.dimension := by
  change (U.mergerShape hd).dimension = _
  rw [MoleculeShape.dimension_rewriteAtom, U.dimension_boundary (by omega) false, hd]

def mergerIncl : (α : Bool) → (U.boundary n α).ogp ⟶ (U.merger hd).ogp
  | false => MoleculeShape.rewriteAtomIncl _ _ (U.gluing hd) (U.isSigned_gluing hd)
      (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
      (U.dimension_boundary_eq hd) false
  | true => MoleculeShape.rewriteAtomIncl _ _ (U.gluing hd) (U.isSigned_gluing hd)
      (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
      (U.dimension_boundary_eq hd) true

instance (α : Bool) : IsInclusion (U.mergerIncl hd α) := by
  cases α
  · exact inferInstanceAs (IsInclusion (MoleculeShape.rewriteAtomIncl _ _ (U.gluing hd)
      (U.isSigned_gluing hd) (U.isRound_boundary U.isRound n false)
      (U.isRound_boundary U.isRound n true) (U.dimension_boundary_eq hd) false))
  · exact inferInstanceAs (IsInclusion (MoleculeShape.rewriteAtomIncl _ _ (U.gluing hd)
      (U.isSigned_gluing hd) (U.isRound_boundary U.isRound n false)
      (U.isRound_boundary U.isRound n true) (U.dimension_boundary_eq hd) true))

theorem map_mergerIncl (α : Bool) : map (U.mergerIncl hd α) ⊤ = (U.merger hd).ogp.bdry ⊤ α := by
  cases α <;> exact MoleculeShape.map_rewriteAtomIncl _ _ (U.gluing hd) (U.isSigned_gluing hd)
    (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
    (U.dimension_boundary_eq hd) _

def toMergerGluing :
    U.ogp.restrict (U.ogp.bdryFull ⊤) ≅ (U.merger hd).ogp.restrict ((U.merger hd).ogp.bdryFull ⊤) :=
  bdryIsoOfCover (U.bdryIso hd false) (U.bdryIso hd true)
    (isoRestrictOfFintype (U.mergerIncl hd false) (U.map_mergerIncl hd false))
    (isoRestrictOfFintype (U.mergerIncl hd true) (U.map_mergerIncl hd true)) fun x y => by
      rw [isoRestrictOfFintype_hom_apply, isoRestrictOfFintype_hom_apply]
      exact (apply_eq_apply_iff_mergerGluing U.isMolecule (U.bdryIso hd false) (U.bdryIso hd true)
        U.isRound (by rw [U.krullDim_top_eq hd]; exact_mod_cast n.succ_pos) x y).trans
        (MoleculeShape.rewriteAtomIncl_false_eq_true_iff _ _ (U.gluing hd) (U.isSigned_gluing hd)
          (U.isRound_boundary U.isRound n false) (U.isRound_boundary U.isRound n true)
          (U.dimension_boundary_eq hd) x y).symm

theorem isSigned_toMergerGluing : (U.toMergerGluing hd).IsSigned :=
  isSigned_bdryIsoOfCover _ _ _ _ _

private abbrev toMergerShape : MoleculeShape :=
  MoleculeShape.rewriteAtom U.toMoleculeShape (U.merger hd).toMoleculeShape (U.toMergerGluing hd)
    (U.isSigned_toMergerGluing hd) U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm

def toMerger : RoundShape :=
  ⟨U.toMergerShape hd, MoleculeShape.isRound_rewriteAtom _ _ (U.toMergerGluing hd)
    (U.isSigned_toMergerGluing hd) U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm⟩

theorem isAtom_toMerger : (U.toMerger hd).ogp.IsAtom :=
  MoleculeShape.isAtom_rewriteAtom _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm

theorem dimension_toMerger : (U.toMerger hd).dimension = U.dimension + 1 :=
  MoleculeShape.dimension_rewriteAtom _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm

def inputIncl : U.ogp ⟶ (U.toMerger hd).ogp :=
  MoleculeShape.rewriteAtomIncl _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm false

def outputIncl : (U.merger hd).ogp ⟶ (U.toMerger hd).ogp :=
  MoleculeShape.rewriteAtomIncl _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm true

instance : IsInclusion (U.inputIncl hd) :=
  inferInstanceAs (IsInclusion (MoleculeShape.rewriteAtomIncl _ _ (U.toMergerGluing hd)
    (U.isSigned_toMergerGluing hd) U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm
    false))

instance : IsInclusion (U.outputIncl hd) :=
  inferInstanceAs (IsInclusion (MoleculeShape.rewriteAtomIncl _ _ (U.toMergerGluing hd)
    (U.isSigned_toMergerGluing hd) U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm
    true))

theorem map_inputIncl : map (U.inputIncl hd) ⊤ = (U.toMerger hd).ogp.bdry ⊤ false :=
  MoleculeShape.map_rewriteAtomIncl _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm false

theorem map_outputIncl : map (U.outputIncl hd) ⊤ = (U.toMerger hd).ogp.bdry ⊤ true :=
  MoleculeShape.map_rewriteAtomIncl _ _ (U.toMergerGluing hd) (U.isSigned_toMergerGluing hd)
    U.isRound (U.merger hd).isRound (U.dimension_merger hd).symm true

end Atoms.Molecule.RoundShape
