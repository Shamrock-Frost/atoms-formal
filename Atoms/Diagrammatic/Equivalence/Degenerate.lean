import Atoms.Diagrammatic.Equivalence.Basic
import Atoms.Diagrammatic.Pasting.Invertors

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

noncomputable def BiInvData.ofIsDegenerate (e : RoundPastingDiagram X) (he : e.IsDegenerate) :
    BiInvData {d : RoundPastingDiagram X | d.IsDegenerate} e :=
  let r : RoundPastingDiagram X := ⟨e.reverse he, PastingDiagram.isRound_reverse he e.isRound⟩
  { dim_pos := PastingDiagram.dim_pos_of_isDegenerate he
    inverse := fun _ => r
    invertor := fun α => ⟨e.invertor he α, PastingDiagram.isRound_invertor he e.isRound α⟩
    invertor_mem := fun α => e.isDegenerate_invertor he α
    dim_inverse := fun _ => e.dim_reverse he
    dim_invertor := fun α => e.dim_invertor he α
    equiv_boundary_inverse := fun _ γ => by
      cases γ
      exacts [e.boundary_reverse he false, e.boundary_reverse he true]
    pastable := fun α => (e.boundary_invertor_composite he α).choose
    boundary_invertor_composite := fun α => (e.boundary_invertor_composite he α).choose_spec
    boundary_invertor_unit := fun α => e.boundary_invertor_unit he e.isRound α }

theorem mem_equivalences_of_isDegenerate (e : RoundPastingDiagram X) (he : e.IsDegenerate) :
    e ∈ equivalences X :=
  subset_equivalences (A := {d : RoundPastingDiagram X | d.IsDegenerate})
    (fun d hd => (BiInvData.ofIsDegenerate d hd).witness) he

theorem degenerate_isEquivalence (X : DiagSet.{u}) {U : Atom} (x : diagram X U)
    (hx : IsDegenerate X x) : IsEquivalence X x :=
  mem_equivalences_of_isDegenerate (cellRound x) ((PastingDiagram.isDegenerate_ofCell_iff x).2 hx)

theorem unit_mem_equivalences (u : RoundPastingDiagram X) :
    (u.isRound.unit : RoundPastingDiagram X) ∈ equivalences X :=
  mem_equivalences_of_isDegenerate _ (u.isDegenerate_unit)

def BiInvData.mapTo {X Y : DiagSet.{u}} {S : Set (RoundPastingDiagram X)}
    {e : RoundPastingDiagram X} (d : BiInvData S e) (f : X ⟶ Y) :
    BiInvData ((fun d : RoundPastingDiagram X =>
        (⟨d.toPastingDiagram.mapTo f, d.isRound⟩ : RoundPastingDiagram Y)) '' S)
      ⟨e.toPastingDiagram.mapTo f, e.isRound⟩ where
  dim_pos := d.dim_pos
  inverse α := ⟨(d.inverse α).toPastingDiagram.mapTo f, (d.inverse α).isRound⟩
  invertor α := ⟨(d.invertor α).toPastingDiagram.mapTo f, (d.invertor α).isRound⟩
  invertor_mem α := ⟨d.invertor α, d.invertor_mem α, rfl⟩
  dim_inverse := d.dim_inverse
  dim_invertor := d.dim_invertor
  equiv_boundary_inverse α γ := (d.equiv_boundary_inverse α γ).boundary_mapTo f
  pastable α := by
    simpa only [Bool.apply_cond (PastingDiagram.mapTo · f), PastingDiagram.dim_def,
      PastingDiagram.mapTo_shape] using (d.pastable α).mapTo f
  boundary_invertor_composite α := by
    change (((d.invertor α).toPastingDiagram.mapTo f).boundary e.dim α).Equiv _
    rw [PastingDiagram.boundary_mapTo]
    simpa only [Bool.apply_cond (PastingDiagram.mapTo · f), PastingDiagram.dim_def,
      PastingDiagram.mapTo_shape] using ((d.boundary_invertor_composite α).mapTo f).trans
        (PastingDiagram.paste_mapTo _ _ _ (d.pastable α) f ((d.pastable α).mapTo f))
  boundary_invertor_unit α := by
    change (((d.invertor α).toPastingDiagram.mapTo f).boundary e.dim (!α)).Equiv
      ((e.toPastingDiagram.mapTo f).boundary (e.dim - 1) α).unit
    rw [PastingDiagram.boundary_mapTo, PastingDiagram.boundary_mapTo, PastingDiagram.unit_mapTo]
    exact (d.boundary_invertor_unit α).mapTo f

theorem BiInvWitness.mapTo {S : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X}
    (h : BiInvWitness S e) (f : X ⟶ Y) :
    BiInvWitness ((fun d : RoundPastingDiagram X =>
        (⟨d.mapTo f, d.isRound⟩ : RoundPastingDiagram Y)) '' S)
      ⟨e.mapTo f, e.isRound⟩ :=
  (h.data.mapTo f).witness

theorem mapTo_mem_equivalences (f : X ⟶ Y) {e : RoundPastingDiagram X}
    (he : e ∈ equivalences X) : (⟨e.mapTo f, e.isRound⟩ : RoundPastingDiagram Y) ∈ equivalences Y :=
  subset_equivalences (A := (fun d : RoundPastingDiagram X =>
      (⟨d.mapTo f, d.isRound⟩ : RoundPastingDiagram Y)) '' equivalences X)
    (by rintro _ ⟨d, hd, rfl⟩; exact ((mem_equivalences_iff d).1 hd).mapTo f) ⟨e, he, rfl⟩

theorem IsEquivalence.map (f : X ⟶ Y) {U : Atom} {x : diagram X U} (hx : IsEquivalence X x) :
    IsEquivalence Y (f.app (Opposite.op U) x) := by
  have hc : cellRound (f.app (op U) x) = ⟨(cellRound x).mapTo f, (cellRound x).isRound⟩ :=
    RoundPastingDiagram.ext (PastingDiagram.ofCell_app f x)
  change cellRound (f.app (op U) x) ∈ equivalences Y
  rw [hc]
  exact mapTo_mem_equivalences f hx

theorem isEquivalence_map_iso_iff {U V : Atom} (e : U ≅ V) (x : diagram X V) :
    IsEquivalence X (X.map e.hom.op x) ↔ IsEquivalence X x :=
  ⟨mem_equivalences_of_equiv (PastingDiagram.equiv_ofCell_map_iso e x),
    mem_equivalences_of_equiv
      ((PastingDiagram.equiv_ofCell_map_iso e x).symm)⟩

theorem Equivalent.map (f : X ⟶ Y) {u v : RoundPastingDiagram X} (h : Equivalent u v) :
    Equivalent (⟨u.mapTo f, u.isRound⟩ : RoundPastingDiagram Y) ⟨v.mapTo f, v.isRound⟩ := by
  let d := h.data
  refine EquivalenceData.equivalent
    { dim_eq := d.dim_eq
      equivalence := ⟨d.equivalence.mapTo f, d.equivalence.isRound⟩
      mem := mapTo_mem_equivalences f d.mem
      dim_equivalence := d.dim_equivalence
      source := ?_
      target := ?_ }
  · change ((d.equivalence.mapTo f).boundary u.dim false).Equiv (u.mapTo f)
    rw [PastingDiagram.boundary_mapTo]
    exact d.source.mapTo f
  · change ((d.equivalence.mapTo f).boundary u.dim true).Equiv (v.mapTo f)
    rw [PastingDiagram.boundary_mapTo]
    exact d.target.mapTo f

theorem equivalent_refl {X : DiagSet.{u}} (u : RoundPastingDiagram X) : Equivalent u u :=
  EquivalenceData.equivalent
    { dim_eq := rfl
      equivalence := u.isRound.unit
      mem := unit_mem_equivalences u
      dim_equivalence := u.dim_unit
      source := PastingDiagram.boundary_unit rfl false
      target := PastingDiagram.boundary_unit rfl true }

end Atoms.Diagrammatic
