import Atoms.Diagrammatic.Equivalence.Congruence
import Atoms.Diagrammatic.Localization.CellularExtension

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def toMergerInclusion (U : RoundShape) (hU : 0 < U.dimension) :
    realize.{u}.obj U.rdc ⟶ ball (toMergerAtom U hU) :=
  realize.map (RDCpx.ofInclusion (P := U.rdc) (Q := atomToRDCpx.obj (toMergerAtom U hU))
      (toMergerInputIncl U hU)) ≫ (realizeAtomIso _).hom

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def HasWeakComposites (X : DiagSet.{u}) : Prop :=
  ∀ u : RoundPastingDiagram X,
    ∃ c : diagram X (mergerAtomAll u.roundShape), Equivalent u (cellRound c)

def IsInftyCategory (n : ℕ∞) (X : DiagSet.{u}) : Prop :=
  HasWeakComposites X ∧
    ∀ (U : Atom) (x : diagram X U), n < U.dimension → IsEquivalence X x

section Point

variable (u : RoundPastingDiagram X) (h : u.dim = 0)

def pointAtom : Atom :=
  Atom.ofIsAtom u.shape.toFiniteOGP (u.shape.isAtom_of_dimension_eq_zero h)

def pointCell : diagram X (pointAtom u h) :=
  uliftYonedaEquiv ((realizeAtomIso (pointAtom u h)).inv ≫ u.map)

theorem ofCell_pointCell_map :
    (PastingDiagram.ofCell (pointCell u h)).map = u.map := by
  simp only [PastingDiagram.ofCell, pointCell, Equiv.symm_apply_apply]
  exact (realizeAtomIso (pointAtom u h)).hom_inv_id_assoc u.map

theorem ofCell_pointCell : PastingDiagram.ofCell (pointCell u h) = u.toPastingDiagram := by
  change (⟨(pointAtom u h).toMoleculeShape, (PastingDiagram.ofCell (pointCell u h)).map⟩ :
    PastingDiagram X) = ⟨u.shape, u.map⟩
  congr 1
  exact ofCell_pointCell_map u h

include h in
theorem exists_weakComposite_of_dim_eq_zero :
    ∃ c : diagram X (mergerAtomAll u.roundShape), Equivalent u (cellRound c) := by
  rw [mergerAtomAll_of_eq_zero u.roundShape h]
  refine ⟨pointCell u h, equivalent_of_equiv ?_⟩
  change u.toPastingDiagram.Equiv (PastingDiagram.ofCell (pointCell u h))
  rw [ofCell_pointCell u h]

end Point

theorem hasWeakComposites_iff_positive (X : DiagSet.{u}) :
    HasWeakComposites X ↔
      ∀ (u : RoundPastingDiagram X) (hu : 0 < u.dim),
        ∃ c : diagram X (mergerAtom u.roundShape hu), Equivalent u (cellRound c) := by
  constructor
  · exact fun hX u hu => mergerAtomAll_of_pos u.roundShape hu ▸ hX u
  · intro hX u
    rcases Nat.eq_zero_or_pos u.dim with h0 | hu
    · exact exists_weakComposite_of_dim_eq_zero u h0
    · rw [mergerAtomAll_of_pos u.roundShape hu]
      exact hX u hu

theorem mem_equivalences_of_cells {n : ℕ}
    (h : ∀ (U : Atom) (x : diagram X U), n < U.dimension → IsEquivalence X x)
    (u : RoundPastingDiagram X) (hd : n < u.dim) : u ∈ equivalences X :=
  mem_equivalences_of_forall_cellAt u (by omega) fun t ht => h _ (u.cellAt t)
    (lt_of_lt_of_eq hd ((dimension_principalAtomRDC u.shape.rdc t).trans ht).symm)

theorem exists_equivalence_cell_side (hX : HasWeakComposites X) (s : Bool)
    (u v : RoundPastingDiagram X) (h : Equivalent u v) :
    ∃ (U : Atom) (c : diagram X U), IsEquivalence X c ∧
      U.dimension = u.dim + 1 ∧
      ((PastingDiagram.ofCell c).boundary u.dim s).Equiv u.toPastingDiagram ∧
      ((PastingDiagram.ofCell c).boundary u.dim (!s)).Equiv v.toPastingDiagram := by
  have key : ∀ u v : RoundPastingDiagram X, Equivalent u v →
      ∃ (U : Atom) (c : diagram X U), IsEquivalence X c ∧
        U.dimension = u.dim + 1 ∧
        ((PastingDiagram.ofCell c).boundary u.dim false).Equiv u.toPastingDiagram ∧
        ((PastingDiagram.ofCell c).boundary u.dim true).Equiv v.toPastingDiagram := by
    intro u v h
    obtain ⟨-, e, he, hde, hs, ht⟩ := h.data
    obtain ⟨c, hc⟩ := hX e
    have hk : u.dim < e.dim := by omega
    refine ⟨_, c, (mem_equivalences_iff_of_equivalent hc).1 he, ?_, ?_, ?_⟩
    · change (cellRound c).dim = u.dim + 1
      rw [← hc.data.dim_eq, hde]
    · exact (hc.equiv_boundary hk false).symm.trans hs
    · exact (hc.equiv_boundary hk true).symm.trans ht
  cases s
  · exact key u v h
  · obtain ⟨U, c, hc, hd, hf, ht⟩ := key v u (equivalent_symm h)
    rw [← h.data.dim_eq] at hd hf ht
    exact ⟨U, c, hc, hd, ht, hf⟩

theorem biInvWitness_of_forall_parallel {A : Set (RoundPastingDiagram X)}
    {e e' : RoundPastingDiagram X} {n : ℕ} (hd : e.dim = n + 1)
    (he' : HasRoundType e'.toPastingDiagram
      ⟨e.boundary n true, isRound_boundary_of_isRound e.isRound n true⟩
      ⟨e.boundary n false, isRound_boundary_of_isRound e.isRound n false⟩)
    (hA : ∀ s t : RoundPastingDiagram X, Parallel s t → s.dim = n + 1 →
      ∃ z ∈ A, HasRoundType z.toPastingDiagram s t) :
    BiInvWitness A e := by
  have hb (α : Bool) : (e.boundary n α).dim = n := dim_boundary _ (by omega) α
  let a : RoundPastingDiagram X :=
    ⟨e.boundary n false, isRound_boundary_of_isRound e.isRound n false⟩
  let b : RoundPastingDiagram X := ⟨e.boundary n true, isRound_boundary_of_isRound e.isRound n true⟩
  have he₁ : HasBdry false n e.toPastingDiagram a.toPastingDiagram b.toPastingDiagram :=
    ⟨hd, hb false, hb true, .refl _, .refl _⟩
  have he₂ : HasBdry false n e'.toPastingDiagram b.toPastingDiagram a.toPastingDiagram :=
    .of_dim_eq (hb true) he'.dim_eq (hb true) (hb false) he'.source he'.target
  have hm : e.dim - 1 = n := by rw [hd]; rfl
  have hp : e.Pastable e'.toPastingDiagram n := he₁.pastable he₂ (.refl _)
  have hq : e'.Pastable e.toPastingDiagram n := he₂.pastable he₁ (.refl _)
  have hte : HasRoundType e.toPastingDiagram a b :=
    .of_equiv_boundary (hb false) (hb true) hd fun β => by cases β <;> exact .refl _
  let p : RoundPastingDiagram X :=
    ⟨e.paste e'.toPastingDiagram n hp, isRound_paste_of_dim e e' he₁.dim_h he₂.dim_h _⟩
  let q : RoundPastingDiagram X :=
    ⟨e'.paste e.toPastingDiagram n hq, isRound_paste_of_dim e' e he₂.dim_h he₁.dim_h _⟩
  have htp : HasRoundType p.toPastingDiagram a a := hte.paste he' (.refl _) (hb false) hp
  have htq : HasRoundType q.toPastingDiagram b b := he'.paste hte (.refl _) (hb true) hq
  have hd₁ : p.dim = e.dim :=
    (dim_paste e.toPastingDiagram e'.toPastingDiagram n hp).trans
      ((congrArg₂ max he₁.dim_h he₂.dim_h).trans ((max_self _).trans hd.symm))
  have hd₂ : q.dim = e.dim :=
    (dim_paste e'.toPastingDiagram e.toPastingDiagram n hq).trans
      ((congrArg₂ max he₂.dim_h he₁.dim_h).trans ((max_self _).trans hd.symm))
  have hd₃ : (isRound_boundary_of_isRound e.isRound n true).unit.dim = e.dim :=
    ((dim_unit _).trans (congrArg (· + 1) (hb true))).trans hd.symm
  obtain ⟨z, hzA, hz⟩ := hA p (isRound_boundary_of_isRound e.isRound n false).unit
    (htp.parallel (hasRoundType_unit a)) (hd₁.trans hd)
  obtain ⟨w, hwA, hw⟩ := hA (isRound_boundary_of_isRound e.isRound n true).unit q
    ((hasRoundType_unit b).parallel htq) (hd₃.trans hd)
  refine BiInvData.witness
    { dim_pos := by rw [hd]; exact Nat.succ_pos n
      inverse := fun _ => e'
      invertor := fun α => cond α w z
      invertor_mem := fun α => by cases α; exacts [hzA, hwA]
      dim_inverse := fun _ => he₂.dim_h.trans hd.symm
      dim_invertor := fun α => by
        cases α
        exacts [hz.dim_eq.trans (congrArg (· + 1) hd₁), hw.dim_eq.trans (congrArg (· + 1) hd₃)]
      equiv_boundary_inverse := fun _ γ => by
        rw [hm]
        cases γ
        exacts [he₂.side.trans he₁.other.symm, he₂.other.trans he₁.side.symm]
      pastable := fun α => by
        rw [hm]
        cases α
        exacts [hp, hq]
      boundary_invertor_composite := fun α => by
        cases α
        · have h := hz.source
          rw [PastingDiagram.boundary_congr _ hd₁] at h
          have key : ∀ p, (cond false e'.toPastingDiagram e.toPastingDiagram).paste
              (cond false e.toPastingDiagram e'.toPastingDiagram) (e.dim - 1) p =
                e.paste e'.toPastingDiagram n hp := fun p =>
            (PastingDiagram.paste_eq_pasteOr p hm rfl rfl).trans (PastingDiagram.pasteOr_of hp)
          rw [key]
          exact h
        · have h := hw.target
          rw [PastingDiagram.boundary_congr _ hd₃] at h
          have key : ∀ p, (cond true e'.toPastingDiagram e.toPastingDiagram).paste
              (cond true e.toPastingDiagram e'.toPastingDiagram) (e.dim - 1) p =
                e'.paste e.toPastingDiagram n hq := fun p =>
            (PastingDiagram.paste_eq_pasteOr p hm rfl rfl).trans (PastingDiagram.pasteOr_of hq)
          rw [key]
          exact h
      boundary_invertor_unit := fun α => by
        rw [hm]
        cases α
        · have h := hz.target
          rw [PastingDiagram.boundary_congr _ hd₁] at h
          exact h
        · have h := hw.source
          rw [PastingDiagram.boundary_congr _ hd₃] at h
          exact h }

theorem mem_equivalences_of_forall_parallel {k : ℕ}
    (hX : ∀ s t : RoundPastingDiagram X, Parallel s t → k ≤ s.dim →
      ∃ (U : Atom) (x : diagram X U), HasRoundType (PastingDiagram.ofCell x) s t)
    (e : RoundPastingDiagram X) (he : k < e.dim) : e ∈ equivalences X := by
  refine subset_equivalences (A := {e | k < e.dim}) (fun e he => ?_) he
  obtain ⟨n, hn⟩ : ∃ n, e.dim = n + 1 := ⟨e.dim - 1, by have : k < e.dim := he; omega⟩
  have he' : k < n + 1 := hn ▸ he
  obtain ⟨U, x, hx⟩ := hX _ _ (parallel_boundary e.isRound hn true false)
    ((dim_boundary _ (by omega) true).trans_ge (by omega))
  refine biInvWitness_of_forall_parallel hn (e' := cellRound x) hx fun s t hst hs => ?_
  obtain ⟨V, z, hz⟩ := hX s t hst (by omega)
  exact ⟨cellRound z, show k < (PastingDiagram.ofCell z).dim by rw [hz.dim_eq]; omega, hz⟩

theorem nonempty_iso_mergerAtom (u : RoundPastingDiagram X) (hu : 0 < u.dim)
    (h : Parallel ⟨u.boundary (u.dim - 1) false, isRound_boundary_of_isRound u.isRound _ false⟩
      ⟨u.boundary (u.dim - 1) true, isRound_boundary_of_isRound u.isRound _ true⟩) :
    Nonempty (h.cellShape ≅ mergerAtom u.roundShape hu) := by
  have hd : u.dim = (u.dim - 1) + 1 := (Nat.sub_add_cancel hu).symm
  have hdV : h.cellShape.toMoleculeShape.dimension = (u.dim - 1) + 1 :=
    h.dimension_cellShape.trans (congrArg (· + 1) (dim_boundary _ (Nat.sub_le _ _) false))
  have hdW : (mergerAtom u.roundShape hu).toMoleculeShape.dimension = (u.dim - 1) + 1 :=
    (dimension_mergerAtom u.roundShape hu).trans hd
  have φ (α : Bool) : Nonempty ((h.cellShape.toMoleculeShape.boundary (u.dim - 1) α).ogp ≅
      ((mergerAtom u.roundShape hu).toMoleculeShape.boundary (u.dim - 1) α).ogp) := by
    have hI : map (h.cellShapeEmb α) ⊤ = h.cellShape.ogp.bdry ⊤ α :=
      (h.map_cellShapeEmb α).trans (h.bdry_cellShape α).symm
    refine ⟨h.cellShape.toMoleculeShape.bdryIso hdV α ≪≫
      (isoRestrictOfFintype (h.cellShapeEmb α) hI).symm ≪≫ ?_ ≪≫
        (mergerAtomBoundaryIso u.roundShape hu α).symm⟩
    cases α <;> exact Iso.refl _
  obtain ⟨Θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso _ _ (fun α => (φ α).some)
    h.cellShape.isAtom (mergerAtom u.roundShape hu).isAtom hdV hdW
  exact ⟨Atom.isoOfOGPIso Θ⟩

theorem exists_weakComposite_of_cell (u : RoundPastingDiagram X) (hu : 0 < u.dim)
    (h : Parallel ⟨u.boundary (u.dim - 1) false, isRound_boundary_of_isRound u.isRound _ false⟩
      ⟨u.boundary (u.dim - 1) true, isRound_boundary_of_isRound u.isRound _ true⟩)
    {c' : diagram X h.cellShape}
    (hc' : HasRoundType (PastingDiagram.ofCell c')
      ⟨u.boundary (u.dim - 1) false, isRound_boundary_of_isRound u.isRound _ false⟩
      ⟨u.boundary (u.dim - 1) true, isRound_boundary_of_isRound u.isRound _ true⟩)
    (he : ∀ {V : Atom} (c : diagram X V),
      (PastingDiagram.ofCell c).Equiv (PastingDiagram.ofCell c') → Parallel u (cellRound c) →
        Equivalent u (cellRound c)) :
    ∃ c : diagram X (mergerAtom u.roundShape hu), Equivalent u (cellRound c) := by
  obtain ⟨θ⟩ := nonempty_iso_mergerAtom u hu h
  have hcc := PastingDiagram.equiv_ofCell_map_iso θ.symm c'
  have htu : HasRoundType u.toPastingDiagram
      ⟨u.boundary (u.dim - 1) false, isRound_boundary_of_isRound u.isRound _ false⟩
      ⟨u.boundary (u.dim - 1) true, isRound_boundary_of_isRound u.isRound _ true⟩ :=
    .of_equiv_boundary (dim_boundary _ (Nat.sub_le _ _) false)
      (dim_boundary _ (Nat.sub_le _ _) true) (Nat.sub_add_cancel hu).symm fun β => by
        cases β <;> exact .refl _
  exact ⟨_, he _ hcc ((HasRoundType.parallel (d := cellRound c') htu hc').of_equiv_right hcc)⟩

end Atoms.Diagrammatic
