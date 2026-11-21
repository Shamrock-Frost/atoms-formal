import Atoms.Diagrammatic.Marked.Basic
import Atoms.Diagrammatic.Horn.Basic
import Atoms.Shape.MarkedHorn

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def markedClosedSubset (U : Atom) (S : LowerSet U.ogp) (A : Set U.ogp)
    (hA : ∀ a ∈ A, a ∈ S ∧ 0 < grade ℕ a) : MarkedDiagSet.{u} :=
  Homotopical.MarkedPresheaf.ofMarking (closedSubpresheaf U S).toFunctor
  ⟨fun V => {x | IsDegenerate _ x ∨
      ∃ a ∈ A, Atom.map (x.1.down : V ⟶ U) ⊤ = LowerSet.Iic a ∧ V.dimension = grade ℕ a},
    fun _ _ hx => by
      rcases hx with hx | ⟨a, ha, -, hd⟩
      · exact dimension_pos_of_isDegenerate hx
      · exact (congrArg (0 < ·) hd).mpr (hA a ha).2,
    fun _ b p hp y => Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩,
    fun V W e x => by
      have hmap : Atom.map (e.hom ≫ (x.1.down : W ⟶ U)) ⊤ = Atom.map (x.1.down : W ⟶ U) ⊤ :=
        SetLike.coe_injective (Set.image_univ.trans
          ((range_iso_hom_comp e (x.1.down : W ⟶ U)).trans Set.image_univ.symm))
      refine or_congr (isDegenerate_map_iso_iff e x).symm ?_
      refine exists_congr fun a => and_congr_right fun _ => ?_
      refine and_congr ?_ ?_
      · exact Iff.of_eq (congrArg (· = LowerSet.Iic a) hmap.symm)
      · exact Iff.of_eq (congrArg (· = grade ℕ a) (Atom.dimension_eq_of_iso e).symm)⟩

end Atoms.Diagrammatic

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

def source (h : MarkedHornData) : MarkedDiagSet.{u} :=
  markedClosedSubset h.atom h.hornSet h.marking h.marking_mem

def target (h : MarkedHornData) : MarkedDiagSet.{u} :=
  markedClosedSubset h.atom ⊤ h.targetMarking h.targetMarking_mem

end Atoms.Shape.MarkedHornData

namespace Atoms.Diagrammatic

noncomputable def markedHornInclusion (h : MarkedHornData) :
    (h.source : MarkedDiagSet.{u}) ⟶ h.target :=
  Homotopical.MarkedPresheaf.homMk
    (Subfunctor.homOfLe (closedSubpresheaf_mono h.atom (le_top : h.hornSet ≤ ⊤))) fun _ _ hx => by
      rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hx with
        hx | ⟨a, ha, him, hd⟩
      · exact (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inl (isDegenerate_app _ hx))
      · exact (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr ⟨a, h.mem_targetMarking_iff.2 (Or.inr (Or.inr ha)), him, hd⟩)

def markedHorns : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms markedHornInclusion

def closedSubpresheafUnivIso (U : Atom) :
    (closedSubpresheaf.{u} U ⊤).toFunctor ≅ ball U :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun f => f.1
      invFun := fun f => ⟨f, fun _ => LowerSet.mem_top⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

end Atoms.Diagrammatic

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

noncomputable def forgetArrowIso (h : MarkedHornData) :
    Arrow.mk (Homotopical.MarkedPresheaf.forget.map (markedHornInclusion.{u} h)) ≅
      Arrow.mk (hornInclusion h.toHornData) :=
  Arrow.isoMk (Iso.refl _) (closedSubpresheafUnivIso h.atom) rfl

end Atoms.Shape.MarkedHornData
