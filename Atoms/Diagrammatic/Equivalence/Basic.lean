import Atoms.Diagrammatic.Pasting.Reverse

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def BiInvWitness {X : DiagSet.{u}} (A : Set (RoundPastingDiagram X)) (e : RoundPastingDiagram X) :
    Prop :=
  0 < e.dim ∧ ∃ eL eR z h : RoundPastingDiagram X, z ∈ A ∧ h ∈ A ∧
    eL.dim = e.dim ∧ eR.dim = e.dim ∧
    (eL.boundary (e.dim - 1) false).Equiv (e.boundary (e.dim - 1) true) ∧
    (eL.boundary (e.dim - 1) true).Equiv (e.boundary (e.dim - 1) false) ∧
    (eR.boundary (e.dim - 1) false).Equiv (e.boundary (e.dim - 1) true) ∧
    (eR.boundary (e.dim - 1) true).Equiv (e.boundary (e.dim - 1) false) ∧
    z.dim = e.dim + 1 ∧ h.dim = e.dim + 1 ∧
    (∃ hp : e.Pastable eL.toPastingDiagram (e.dim - 1),
      (z.boundary e.dim false).Equiv (e.paste eL.toPastingDiagram (e.dim - 1) hp)) ∧
    (z.boundary e.dim true).Equiv (e.boundary (e.dim - 1) false).unit ∧
    (h.boundary e.dim false).Equiv (e.boundary (e.dim - 1) true).unit ∧
    (∃ hq : eR.Pastable e.toPastingDiagram (e.dim - 1),
      (h.boundary e.dim true).Equiv (eR.paste e.toPastingDiagram (e.dim - 1) hq))

structure BiInvData {X : DiagSet.{u}} (A : Set (RoundPastingDiagram X)) (e : RoundPastingDiagram X)
    where
  dim_pos : 0 < e.dim
  inverse : Bool → RoundPastingDiagram X
  invertor : Bool → RoundPastingDiagram X
  invertor_mem : ∀ α, invertor α ∈ A
  dim_inverse : ∀ α, (inverse α).dim = e.dim
  dim_invertor : ∀ α, (invertor α).dim = e.dim + 1
  equiv_boundary_inverse : ∀ α γ,
    ((inverse α).boundary (e.dim - 1) γ).Equiv (e.boundary (e.dim - 1) (!γ))
  pastable : ∀ α, (cond α (inverse α).toPastingDiagram e.toPastingDiagram).Pastable
    (cond α e.toPastingDiagram (inverse α).toPastingDiagram) (e.dim - 1)
  boundary_invertor_composite : ∀ α, ((invertor α).boundary e.dim α).Equiv
    ((cond α (inverse α).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (inverse α).toPastingDiagram) (e.dim - 1) (pastable α))
  boundary_invertor_unit : ∀ α,
    ((invertor α).boundary e.dim (!α)).Equiv (e.boundary (e.dim - 1) α).unit

theorem BiInvData.witness {A : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X}
    (d : BiInvData A e) : BiInvWitness A e :=
  ⟨d.dim_pos, d.inverse false, d.inverse true, d.invertor false, d.invertor true,
    d.invertor_mem false, d.invertor_mem true, d.dim_inverse false, d.dim_inverse true,
    d.equiv_boundary_inverse false false, d.equiv_boundary_inverse false true,
    d.equiv_boundary_inverse true false, d.equiv_boundary_inverse true true,
    d.dim_invertor false, d.dim_invertor true,
    ⟨d.pastable false, d.boundary_invertor_composite false⟩, d.boundary_invertor_unit false,
    d.boundary_invertor_unit true, ⟨d.pastable true, d.boundary_invertor_composite true⟩⟩

noncomputable def BiInvWitness.data {A : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X}
    (h : BiInvWitness A e) : BiInvData A e :=
  have H := h.2.choose_spec.choose_spec.choose_spec.choose_spec
  { dim_pos := h.1
    inverse := fun α => cond α h.2.choose_spec.choose h.2.choose
    invertor := fun α =>
      cond α h.2.choose_spec.choose_spec.choose_spec.choose h.2.choose_spec.choose_spec.choose
    invertor_mem := fun α => by cases α; exacts [H.1, H.2.1]
    dim_inverse := fun α => by cases α; exacts [H.2.2.1, H.2.2.2.1]
    dim_invertor := fun α => by
      cases α; exacts [H.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.1]
    equiv_boundary_inverse := fun α γ => by
      cases α <;> cases γ
      exacts [H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.1]
    pastable := fun α => by
      cases α; exacts [H.2.2.2.2.2.2.2.2.2.2.1.fst, H.2.2.2.2.2.2.2.2.2.2.2.2.2.fst]
    boundary_invertor_composite := fun α => by
      cases α; exacts [H.2.2.2.2.2.2.2.2.2.2.1.snd, H.2.2.2.2.2.2.2.2.2.2.2.2.2.snd]
    boundary_invertor_unit := fun α => by
      cases α; exacts [H.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.1] }

theorem biInvWitness_iff_nonempty {A : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X} :
    BiInvWitness A e ↔ Nonempty (BiInvData A e) :=
  ⟨fun h => ⟨h.data⟩, fun ⟨d⟩ => d.witness⟩

attribute [irreducible] BiInvWitness

def BiInvData.mono {A B : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X} (hAB : A ⊆ B)
    (d : BiInvData A e) : BiInvData B e :=
  { d with invertor_mem := fun α => hAB (d.invertor_mem α) }

def biInvOperator (X : DiagSet.{u}) :
    Set (RoundPastingDiagram X) →o Set (RoundPastingDiagram X) where
  toFun A := {e | BiInvWitness A e}
  monotone' _ _ hAB _ he := ((BiInvWitness.data he).mono hAB).witness

def equivalences (X : DiagSet.{u}) : Set (RoundPastingDiagram X) := (biInvOperator X).gfp

def cellRound {X : DiagSet.{u}} {U : Atom} (x : diagram X U) : RoundPastingDiagram X :=
  ⟨PastingDiagram.ofCell x, U.isAtom.isRound⟩

def IsEquivalence (X : DiagSet.{u}) {U : Atom} (x : diagram X U) : Prop :=
  cellRound x ∈ equivalences X

def Equivalent {X : DiagSet.{u}} (u v : RoundPastingDiagram X) : Prop :=
  u.dim = v.dim ∧ ∃ e ∈ equivalences X, e.dim = u.dim + 1 ∧
    (e.boundary u.dim false).Equiv u.toPastingDiagram ∧
      (e.boundary u.dim true).Equiv v.toPastingDiagram

structure EquivalenceData {X : DiagSet.{u}} (u v : RoundPastingDiagram X) where
  dim_eq : u.dim = v.dim
  equivalence : RoundPastingDiagram X
  mem : equivalence ∈ equivalences X
  dim_equivalence : equivalence.dim = u.dim + 1
  source : (equivalence.boundary u.dim false).Equiv u.toPastingDiagram
  target : (equivalence.boundary u.dim true).Equiv v.toPastingDiagram

theorem EquivalenceData.equivalent {u v : RoundPastingDiagram X} (d : EquivalenceData u v) :
    Equivalent u v :=
  ⟨d.dim_eq, d.equivalence, d.mem, d.dim_equivalence, d.source, d.target⟩

noncomputable def Equivalent.data {u v : RoundPastingDiagram X} (h : Equivalent u v) :
    EquivalenceData u v :=
  ⟨h.1, h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.1, h.2.choose_spec.2.2.1,
    h.2.choose_spec.2.2.2⟩

theorem equivalent_iff_nonempty {u v : RoundPastingDiagram X} :
    Equivalent u v ↔ Nonempty (EquivalenceData u v) :=
  ⟨fun h => ⟨h.data⟩, fun ⟨d⟩ => d.equivalent⟩

attribute [irreducible] Equivalent

theorem biInvOperator_equivalences : biInvOperator X (equivalences X) = equivalences X :=
  (biInvOperator X).map_gfp

theorem subset_equivalences {A : Set (RoundPastingDiagram X)} (h : A ⊆ biInvOperator X A) :
    A ⊆ equivalences X :=
  (biInvOperator X).le_gfp h

theorem mem_equivalences_iff (e : RoundPastingDiagram X) :
    e ∈ equivalences X ↔ BiInvWitness (equivalences X) e := by
  conv_lhs => rw [← biInvOperator_equivalences]
  rfl

theorem BiInvWitness.of_equiv {A : Set (RoundPastingDiagram X)} {e e' : RoundPastingDiagram X}
    (h : e.Equiv e'.toPastingDiagram) (he : BiInvWitness A e) : BiInvWitness A e' := by
  let d := he.data
  have hdim : e.dim = e'.dim := PastingDiagram.dim_eq_of_equiv h
  have hb : ∀ α, (e.boundary (e.dim - 1) α).Equiv (e'.boundary (e.dim - 1) α) :=
    fun α => h.boundary (e.dim - 1) α
  have hp' : e'.Pastable (d.inverse false).toPastingDiagram (e.dim - 1) :=
    ⟨(hb true).symm.trans (d.pastable false).1,
      lt_of_lt_of_eq (d.pastable false).2 (congrArg (min · (d.inverse false).dim) hdim)⟩
  have hq' : (d.inverse true).Pastable e'.toPastingDiagram (e.dim - 1) :=
    ⟨(d.pastable true).1.trans (hb false),
      lt_of_lt_of_eq (d.pastable true).2 (congrArg (min (d.inverse true).dim ·) hdim)⟩
  rw [BiInvWitness, ← hdim]
  exact ⟨d.dim_pos, d.inverse false, d.inverse true, d.invertor false, d.invertor true,
    d.invertor_mem false, d.invertor_mem true, d.dim_inverse false, d.dim_inverse true,
    (d.equiv_boundary_inverse false false).trans (hb true),
    (d.equiv_boundary_inverse false true).trans (hb false),
    (d.equiv_boundary_inverse true false).trans (hb true),
    (d.equiv_boundary_inverse true true).trans (hb false),
    d.dim_invertor false, d.dim_invertor true,
    ⟨hp', (d.boundary_invertor_composite false).trans
      (PastingDiagram.Equiv.paste h (.refl _) _ hp')⟩,
    (d.boundary_invertor_unit false).trans (hb false).unit,
    (d.boundary_invertor_unit true).trans (hb true).unit,
    ⟨hq', (d.boundary_invertor_composite true).trans
      (PastingDiagram.Equiv.paste (.refl _) h _ hq')⟩⟩

theorem mem_equivalences_of_equiv {e e' : RoundPastingDiagram X} (h : e.Equiv e'.toPastingDiagram)
    (he : e ∈ equivalences X) : e' ∈ equivalences X :=
  (mem_equivalences_iff e').2 (((mem_equivalences_iff e).1 he).of_equiv h)

theorem pos_dim_of_mem_equivalences {e : RoundPastingDiagram X} (he : e ∈ equivalences X) :
    0 < e.dim :=
  ((mem_equivalences_iff e).1 he).data.dim_pos

theorem not_isEquivalence_of_dimension_eq_zero {U : Atom} (x : diagram X U)
    (hU : U.dimension = 0) : ¬ IsEquivalence X x := fun hx =>
  (pos_dim_of_mem_equivalences hx).ne' hU

end Atoms.Diagrammatic
