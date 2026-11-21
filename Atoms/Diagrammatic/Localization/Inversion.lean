import Atoms.Diagrammatic.Localization.CellularExtension
import Atoms.Diagrammatic.Equivalence
import Atoms.Diagrammatic.InftyCategory
import Atoms.Diagrammatic.Marked.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Mathlib.CategoryTheory.Functor.OfSequence

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

namespace Parallel

variable {v w : RoundPastingDiagram X} (h : Parallel v w)

noncomputable def reindexCell (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) : diagram Y h.cellShape :=
  Y.map (h.exists_iso_hasRoundType f x hx).choose.hom.op x

theorem hasRoundType_reindexCell (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) :
    HasRoundType (PastingDiagram.ofCell (h.reindexCell f x hx))
      ⟨v.toPastingDiagram.mapTo f, v.isRound⟩ ⟨w.toPastingDiagram.mapTo f, w.isRound⟩ :=
  (h.exists_iso_hasRoundType f x hx).choose_spec

theorem reindexCell_eq (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) (e : h.cellShape ≅ H) :
    h.reindexCell f x hx = Y.map e.hom.op x := by
  rw [reindexCell, Atom.iso_eq (h.exists_iso_hasRoundType f x hx).choose e]

theorem equiv_ofCell_reindexCell (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) :
    (PastingDiagram.ofCell (h.reindexCell f x hx)).Equiv (PastingDiagram.ofCell x) :=
  equiv_ofCell_map_iso _ x

theorem nonempty_iso_of_hasRoundType (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) : Nonempty (h.cellShape ≅ H) :=
  ⟨(h.exists_iso_hasRoundType f x hx).choose⟩

end Parallel

structure InversionData (X : DiagSet.{u}) where
  ι : Type u
  shape : ι → Atom
  cell : ∀ i, diagram X (shape i)
  dim_pos : ∀ i, 0 < (shape i).dimension

private theorem hasRoundType_cond (α : Bool) {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    {k : ℕ} (hv : v.dim = k) (hw : w.dim = k) (ha : a.dim = k + 1)
    (h₁ : (a.boundary k α).Equiv v.toPastingDiagram)
    (h₂ : (a.boundary k (!α)).Equiv w.toPastingDiagram) :
    HasRoundType a (cond α w v) (cond α v w) := by
  subst hv
  cases α
  · exact { dim_eq := ha, dim_eq_dim := hw.symm, source := h₁, target := h₂ }
  · exact
      { dim_eq := (by rw [hw]; exact ha : a.dim = w.dim + 1)
        dim_eq_dim := hw
        source := (by rw [hw]; exact h₂ : (a.boundary w.dim false).Equiv w.toPastingDiagram)
        target := (by rw [hw]; exact h₁ : (a.boundary w.dim true).Equiv v.toPastingDiagram) }

private theorem parallel_of_equiv_boundary {u v : RoundPastingDiagram X} {k : ℕ}
    (hu : u.dim = k + 1) (hv : v.dim = k + 1)
    (h : ∀ γ, (u.boundary k γ).Equiv (v.boundary k γ)) : Parallel u v :=
  ⟨hu.trans hv.symm, Or.inr fun γ => by
    rw [boundary_congr u.toPastingDiagram (show u.dim - 1 = k by omega),
      boundary_congr v.toPastingDiagram (show v.dim - 1 = k by omega)]
    exact h γ⟩

theorem PastingDiagram.equiv_of_eq {u v : PastingDiagram X} (h : u = v) : u.Equiv v :=
  h ▸ .refl u

private theorem paste_congr_dim {u v : PastingDiagram X} {k k' : ℕ} (hk : k = k')
    (h : u.Pastable v k) (h' : u.Pastable v k') : u.paste v k h = u.paste v k' h' := by
  subst hk
  rfl

private theorem dim_cellRound {U : Atom} (x : diagram X U) :
    (cellRound x).dim = U.dimension :=
  rfl

private def bdryRound (e : RoundPastingDiagram X) (α : Bool) : RoundPastingDiagram X :=
  ⟨e.boundary (e.dim - 1) α, isRound_boundary_of_isRound e.isRound _ α⟩

structure InverseData (X : DiagSet.{u}) where
  cell : RoundPastingDiagram X
  inverse : Bool → RoundPastingDiagram X
  dim_pos : 0 < cell.dim
  dim_inverse : ∀ α, (inverse α).dim = cell.dim
  equiv_boundary_inverse : ∀ α γ,
    ((inverse α).boundary (cell.dim - 1) γ).Equiv (cell.boundary (cell.dim - 1) (!γ))

namespace InverseData

variable (D : InverseData X)

theorem pastable (α : Bool) :
    (cond α (D.inverse α).toPastingDiagram D.cell.toPastingDiagram).Pastable
      (cond α D.cell.toPastingDiagram (D.inverse α).toPastingDiagram) (D.cell.dim - 1) :=
  Pastable.of_side α (D.equiv_boundary_inverse α α)
    (by rw [D.dim_inverse]; have := D.dim_pos; omega) (by have := D.dim_pos; omega)

@[implicit_reducible]
noncomputable def composite (α : Bool) : RoundPastingDiagram X :=
  ⟨(cond α (D.inverse α).toPastingDiagram D.cell.toPastingDiagram).paste
      (cond α D.cell.toPastingDiagram (D.inverse α).toPastingDiagram) (D.cell.dim - 1)
      (D.pastable α),
    isRound_paste_of_round α (D.pastable α) D.cell.isRound (by have := D.dim_pos; omega)
      (by rw [D.dim_inverse]; omega)⟩

@[implicit_reducible]
def unitBdry (α : Bool) : RoundPastingDiagram X :=
  (isRound_boundary_of_isRound D.cell.isRound (D.cell.dim - 1) α).unit

theorem dim_composite (α : Bool) : (D.composite α).dim = D.cell.dim := by
  dsimp only [composite]
  simp only [dim_paste, Bool.apply_cond PastingDiagram.dim, D.dim_inverse, Bool.cond_self,
    max_self]

private theorem dim_unitBdry (α : Bool) : (D.unitBdry α).dim = D.cell.dim := by
  have := D.dim_pos
  dsimp only [unitBdry]
  rw [PastingDiagram.dim_unit, dim_boundary _ (Nat.sub_le _ _)]
  omega

private theorem parallel_composite_unitBdry (α : Bool) :
    Parallel (D.composite α) (D.unitBdry α) := by
  have hd := D.dim_pos
  refine parallel_of_equiv_boundary (k := D.cell.dim - 1)
    (by rw [D.dim_composite]; omega) (by rw [D.dim_unitBdry]; omega) fun γ => ?_
  have hf : ((cond γ (cond α D.cell.toPastingDiagram (D.inverse α).toPastingDiagram)
      (cond α (D.inverse α).toPastingDiagram D.cell.toPastingDiagram)).boundary
        (D.cell.dim - 1) γ).Equiv (D.cell.boundary (D.cell.dim - 1) α) := by
    cases α <;> cases γ
    exacts [.refl _, D.equiv_boundary_inverse false true, D.equiv_boundary_inverse true false,
      .refl _]
  exact ((equiv_boundary_paste (D.pastable α) γ).trans hf).trans
    (boundary_unit (dim_boundary _ (Nat.sub_le _ _) α) γ).symm

@[implicit_reducible]
noncomputable def source (α : Bool) : RoundPastingDiagram X :=
  cond α (D.unitBdry α) (D.composite α)

@[implicit_reducible]
noncomputable def target (α : Bool) : RoundPastingDiagram X :=
  cond α (D.composite α) (D.unitBdry α)

private theorem parallel_source_target (α : Bool) : Parallel (D.source α) (D.target α) := by
  cases α
  exacts [D.parallel_composite_unitBdry false, (D.parallel_composite_unitBdry true).symm]

theorem dim_source (α : Bool) : (D.source α).dim = D.cell.dim :=
  Bool.cond_rec_prop (p := fun u : RoundPastingDiagram X => u.dim = D.cell.dim) α
    (D.dim_unitBdry α) (D.dim_composite α)

private def mapTo (f : X ⟶ Y) : InverseData Y where
  cell := D.cell.mapTo f
  inverse α := (D.inverse α).mapTo f
  dim_pos := D.dim_pos
  dim_inverse := D.dim_inverse
  equiv_boundary_inverse α γ := (D.equiv_boundary_inverse α γ).boundary_mapTo f

private theorem composite_mapTo (f : X ⟶ Y) (α : Bool) :
    ((D.composite α).toPastingDiagram.mapTo f).Equiv
      ((D.mapTo f).composite α).toPastingDiagram := by
  cases α
  exacts [paste_mapTo _ _ _ (D.pastable false) f ((D.mapTo f).pastable false),
    paste_mapTo _ _ _ (D.pastable true) f ((D.mapTo f).pastable true)]

private theorem unitBdry_mapTo (f : X ⟶ Y) (α : Bool) :
    (D.unitBdry α).toPastingDiagram.mapTo f = ((D.mapTo f).unitBdry α).toPastingDiagram :=
  (unit_mapTo _ f).symm.trans
    (congrArg PastingDiagram.unit (boundary_mapTo D.cell.toPastingDiagram f _ α).symm)

private def biInvDataMapTo (f : X ⟶ Y) {S : Set (RoundPastingDiagram Y)}
    (z : Bool → RoundPastingDiagram Y) (hzS : ∀ α, z α ∈ S)
    (hz : ∀ α, HasRoundType (z α).toPastingDiagram ((D.source α).mapTo f)
      ((D.target α).mapTo f)) :
    BiInvData S (D.cell.mapTo f) :=
    { dim_pos := D.dim_pos
      inverse := (D.mapTo f).inverse
      invertor := z
      invertor_mem := hzS
      dim_inverse := (D.mapTo f).dim_inverse
      dim_invertor := fun α => (hz α).dim_eq.trans (congrArg (· + 1) (D.dim_source α))
      equiv_boundary_inverse := (D.mapTo f).equiv_boundary_inverse
      pastable := (D.mapTo f).pastable
      boundary_invertor_composite := fun α => by
        have h := (hz α).equiv_boundary_cond (D.dim_source α) α
        cases α
        exacts [h.trans (D.composite_mapTo f false), h.trans (D.composite_mapTo f true)]
      boundary_invertor_unit := fun α => by
        have h := (hz α).equiv_boundary_cond (D.dim_source α) (!α)
        cases α
        exacts [h.trans (equiv_of_eq (D.unitBdry_mapTo f false)),
          h.trans (equiv_of_eq (D.unitBdry_mapTo f true))] }

private theorem hasRoundType_mapTo_of_equiv_boundary (f : X ⟶ Y) (α : Bool)
    {a : PastingDiagram Y} (ha : a.dim = D.cell.dim + 1)
    (h₁ : (a.boundary D.cell.dim α).Equiv ((D.composite α).mapTo f).toPastingDiagram)
    (h₂ : (a.boundary D.cell.dim (!α)).Equiv ((D.unitBdry α).mapTo f).toPastingDiagram) :
    HasRoundType a ((D.source α).mapTo f) ((D.target α).mapTo f) := by
  have h := hasRoundType_cond α (v := (D.composite α).mapTo f) (w := (D.unitBdry α).mapTo f)
    (D.dim_composite α) (D.dim_unitBdry α) ha h₁ h₂
  cases α <;> exact h

private theorem hasRoundType_of_biInvData (f : X ⟶ Y) {e : RoundPastingDiagram Y}
    {S : Set (RoundPastingDiagram Y)} (d : BiInvData S e)
    (he : e.toPastingDiagram.Equiv (D.cell.mapTo f).toPastingDiagram)
    (hinv : ∀ α, ((D.inverse α).mapTo f).toPastingDiagram.Equiv (d.inverse α).toPastingDiagram)
    (α : Bool) {z : PastingDiagram Y} (hz : z.Equiv (d.invertor α).toPastingDiagram) :
    HasRoundType z ((D.source α).mapTo f) ((D.target α).mapTo f) := by
  have hde : e.dim = D.cell.dim := dim_eq_of_equiv he
  have hzd : z.dim = D.cell.dim + 1 :=
    (dim_eq_of_equiv hz).trans ((d.dim_invertor α).trans (congrArg (· + 1) hde))
  refine D.hasRoundType_mapTo_of_equiv_boundary f α hzd ?_ ?_
  · have hk : e.dim - 1 = (D.mapTo f).cell.dim - 1 := by rw [hde]; rfl
    have hp : (cond α ((D.mapTo f).inverse α).toPastingDiagram
        (D.mapTo f).cell.toPastingDiagram).Pastable (cond α (D.mapTo f).cell.toPastingDiagram
          ((D.mapTo f).inverse α).toPastingDiagram) (e.dim - 1) := hk ▸ (D.mapTo f).pastable α
    have hX : ((cond α (d.inverse α).toPastingDiagram e.toPastingDiagram).paste
        (cond α e.toPastingDiagram (d.inverse α).toPastingDiagram) (e.dim - 1)
          (d.pastable α)).Equiv ((D.mapTo f).composite α).toPastingDiagram := by
      refine PastingDiagram.Equiv.trans ?_
        (equiv_of_eq (paste_congr_dim hk hp ((D.mapTo f).pastable α)))
      cases α
      · exact Equiv.paste he (hinv false).symm _ hp
      · exact Equiv.paste (hinv true).symm he _ hp
    exact (hz.boundary D.cell.dim α).trans ((equiv_of_eq (boundary_congr _ hde.symm α)).trans
      ((d.boundary_invertor_composite α).trans (hX.trans (D.composite_mapTo f α).symm)))
  · have hu : ((D.cell.mapTo f).toPastingDiagram.boundary (D.cell.dim - 1) α).unit =
        ((D.unitBdry α).mapTo f).toPastingDiagram := (D.unitBdry_mapTo f α).symm
    have hU : ((d.invertor α).boundary e.dim (!α)).Equiv (e.boundary (e.dim - 1) α).unit :=
      d.boundary_invertor_unit α
    have hV : (e.boundary (e.dim - 1) α).unit.Equiv
        ((D.cell.mapTo f).toPastingDiagram.boundary (e.dim - 1) α).unit :=
      (he.boundary (e.dim - 1) α).unit
    rw [hde] at hU hV
    exact ((hz.boundary D.cell.dim (!α)).trans hU).trans (hV.trans (equiv_of_eq hu))

private theorem equivalent_composite_unitBdry {e : RoundPastingDiagram X}
    (he : e.Equiv D.cell.toPastingDiagram) (d : BiInvData (equivalences X) e)
    (hinv : ∀ α, Equivalent (d.inverse α) (D.inverse α)) (α : Bool) :
    Equivalent (D.composite α) (D.unitBdry α) := by
  have hde : e.dim = D.cell.dim := dim_eq_of_equiv he
  have hpos := D.dim_pos
  have hk : e.dim - 1 = D.cell.dim - 1 := by rw [hde]
  have hce : Equivalent D.cell e := equivalent_of_equiv he.symm
  let P : RoundPastingDiagram X :=
    ⟨(cond α (d.inverse α).toPastingDiagram e.toPastingDiagram).paste
        (cond α e.toPastingDiagram (d.inverse α).toPastingDiagram) (e.dim - 1) (d.pastable α),
      isRound_paste_of_round α (d.pastable α) e.isRound (by omega)
        (by rw [d.dim_inverse]; omega)⟩
  have h₁ : Equivalent (D.composite α) P := by
    have hDi := D.dim_inverse α
    have hp := (D.pastable α).of_equiv (.cond (.refl _) α he.symm) (.cond he.symm α (.refl _))
    have hr := isRound_paste_of_round α hp e.isRound (by omega) (by omega)
    refine equivalent_trans (equivalent_paste_cond α hce rfl hDi (D.pastable α) hp
      (D.composite α).isRound hr) ?_
    simpa only [Bool.cond_not] using equivalent_paste_cond (!α) (equivalent_symm (hinv α))
      hk.symm (by omega) (by simpa only [Bool.cond_not] using hp)
      (by simpa only [Bool.cond_not] using d.pastable α) (by simpa only [Bool.cond_not] using hr)
      (by simpa only [Bool.cond_not] using P.isRound)
  have h₂ := d.equivalent_invertor α P.isRound
  have hb := he.boundary (e.dim - 1) α
  rw [boundary_congr D.cell.toPastingDiagram hk] at hb
  exact equivalent_trans h₁ (equivalent_trans h₂ (equivalent_of_equiv hb.unit))

end InverseData

private theorem hasRoundType_of_equivalent_inverse {e : RoundPastingDiagram X} (f : X ⟶ Y)
    {b : RoundPastingDiagram Y} (hb : b.toPastingDiagram.Equiv (e.toPastingDiagram.mapTo f))
    {S : Set (RoundPastingDiagram Y)} (d : BiInvData S b) (α : Bool) {U : Atom}
    (c : diagram Y U) (hc : Equivalent (d.inverse α) (cellRound c)) :
    HasRoundType (PastingDiagram.ofCell c) ((bdryRound e true).mapTo f)
      ((bdryRound e false).mapTo f) := by
  have hbd : b.dim = e.dim := dim_eq_of_equiv hb
  have hpos := d.dim_pos
  have hcd : (cellRound c).dim = e.dim := hc.data.dim_eq.symm.trans ((d.dim_inverse α).trans hbd)
  have hk : b.dim - 1 = e.dim - 1 := by rw [hbd]
  have key : ∀ γ, ((PastingDiagram.ofCell c).boundary (e.dim - 1) γ).Equiv
      ((e.boundary (e.dim - 1) (!γ)).mapTo f) := by
    intro γ
    have h₁ := (hc.equiv_boundary (k := e.dim - 1) (by rw [d.dim_inverse]; omega) γ).symm
    have h₂ := d.equiv_boundary_inverse α γ
    rw [hk] at h₂
    exact h₁.trans (h₂.trans ((hb.boundary (e.dim - 1) (!γ)).trans
      (equiv_of_eq (boundary_mapTo e.toPastingDiagram f _ _))))
  have hv : ((bdryRound e true).mapTo f).dim = e.dim - 1 := dim_boundary _ (Nat.sub_le _ _) true
  have hw : ((bdryRound e false).mapTo f).dim = e.dim - 1 := dim_boundary _ (Nat.sub_le _ _) false
  exact hasRoundType_cond false hv hw (by change (cellRound c).dim = _; omega) (key false)
    (key true)

namespace InversionData

variable (A : InversionData X)

@[implicit_reducible]
def inverseExtension : CellularExtensionData X where
  ι := A.ι × Bool
  source j := bdryRound (cellRound (A.cell j.1)) true
  target j := bdryRound (cellRound (A.cell j.1)) false
  parallel j := parallel_boundary (cellRound (A.cell j.1)).isRound
    (by rw [dim_cellRound]; have := A.dim_pos j.1; omega) true false

@[implicit_reducible]
noncomputable def inverseData (i : A.ι) : InverseData A.inverseExtension.extension where
  cell := ⟨(ofCell (A.cell i)).mapTo A.inverseExtension.incl, (A.shape i).isAtom.isRound⟩
  inverse α := ⟨ofCell (A.inverseExtension.cell (i, α)),
    (A.inverseExtension.shape (i, α)).isAtom.isRound⟩
  dim_pos := A.dim_pos i
  dim_inverse α := by
    have h₃ : (A.inverseExtension.source (i, α)).dim = (A.shape i).dimension - 1 :=
      dim_boundary _ (Nat.sub_le _ _) true
    have := A.dim_pos i
    exact (A.inverseExtension.dimension_shape (i, α)).trans
      (by omega : (A.inverseExtension.source (i, α)).dim + 1 = (A.shape i).dimension)
  equiv_boundary_inverse α γ := by
    have h := (A.inverseExtension.hasRoundType_cell (i, α)).equiv_boundary_cond
      (k := (A.shape i).dimension - 1) (dim_boundary _ (Nat.sub_le _ _) true) γ
    cases γ
    exacts [h.trans (equiv_of_eq (boundary_mapTo (cellRound (A.cell i)).toPastingDiagram
        A.inverseExtension.incl _ true).symm),
      h.trans (equiv_of_eq (boundary_mapTo (cellRound (A.cell i)).toPastingDiagram
        A.inverseExtension.incl _ false).symm)]

@[implicit_reducible]
noncomputable def invertorExtension : CellularExtensionData A.inverseExtension.extension where
  ι := A.ι × Bool
  source j := (A.inverseData j.1).source j.2
  target j := (A.inverseData j.1).target j.2
  parallel j := (A.inverseData j.1).parallel_source_target j.2

noncomputable def step : DiagSet.{u} := A.invertorExtension.extension

noncomputable def stepIncl : X ⟶ A.step := A.inverseExtension.incl ≫ A.invertorExtension.incl

instance mono_stepIncl : Mono A.stepIncl :=
  inferInstanceAs (Mono (A.inverseExtension.incl ≫ A.invertorExtension.incl))

@[implicit_reducible]
noncomputable def next : InversionData A.step where
  ι := A.ι × Bool
  shape := A.invertorExtension.shape
  cell := A.invertorExtension.cell
  dim_pos j := lt_of_lt_of_eq (Nat.succ_pos _) (A.invertorExtension.dimension_shape j).symm

theorem biInvWitness_step (i : A.ι) :
    BiInvWitness {z | ∃ j, z = cellRound (A.next.cell j)}
      (cellRound (A.stepIncl.app (op (A.shape i)) (A.cell i))) := by
  have hw := ((A.inverseData i).biInvDataMapTo A.invertorExtension.incl
    (S := {z | ∃ j, z = cellRound (A.next.cell j)})
    (fun α => cellRound (A.invertorExtension.cell (i, α))) (fun α => ⟨(i, α), rfl⟩)
    (fun α => A.invertorExtension.hasRoundType_cell (i, α))).witness
  refine BiInvWitness.of_equiv (equiv_of_eq ?_) hw
  exact (mapTo_comp (ofCell (A.cell i)) A.inverseExtension.incl A.invertorExtension.incl).symm.trans
    (ofCell_app A.stepIncl (A.cell i)).symm

theorem exists_stepIncl_comp_eq (hY : HasWeakComposites Y) (g : X ⟶ Y)
    (hg : ∀ i, IsEquivalence Y (g.app (op (A.shape i)) (A.cell i))) :
    ∃ g' : A.step ⟶ Y, A.stepIncl ≫ g' = g ∧
      ∀ j, IsEquivalence Y (g'.app (op (A.next.shape j)) (A.next.cell j)) := by
  let d : ∀ i, BiInvData (equivalences Y) (cellRound (g.app (op (A.shape i)) (A.cell i))) :=
    fun i => ((mem_equivalences_iff _).1 (hg i)).data
  have hL : ∀ j : A.ι × Bool, ∃ x : diagram Y (A.inverseExtension.shape j),
      HasRoundType (PastingDiagram.ofCell x) ((A.inverseExtension.source j).mapTo g)
        ((A.inverseExtension.target j).mapTo g) ∧
      Equivalent ((d j.1).inverse j.2) (cellRound x) := by
    rintro ⟨i, α⟩
    obtain ⟨c, hc⟩ := hY ((d i).inverse α)
    obtain ⟨e, he⟩ := (A.inverseExtension.parallel (i, α)).exists_iso_hasRoundType g c
      (hasRoundType_of_equivalent_inverse g (equiv_of_eq (ofCell_app g (A.cell i))) (d i) α
        c hc)
    exact ⟨_, he, equivalent_trans hc (equivalent_of_equiv (equiv_ofCell_map_iso e c).symm)⟩
  choose L hL hLe using hL
  let g₁ := A.inverseExtension.desc g L hL
  have hcell : ∀ i, (cellRound (g.app (op (A.shape i)) (A.cell i))).Equiv
      ((A.inverseData i).mapTo g₁).cell.toPastingDiagram := fun i =>
    equiv_of_eq ((ofCell_app g (A.cell i)).trans ((congrArg (ofCell (A.cell i)).mapTo
      (A.inverseExtension.incl_desc g L hL).symm).trans (mapTo_comp _ _ _)))
  have hinv : ∀ i α, Equivalent ((d i).inverse α) (((A.inverseData i).mapTo g₁).inverse α) :=
    fun i α => equivalent_trans (hLe (i, α)) (equivalent_of_equiv (equiv_of_eq
      ((congrArg PastingDiagram.ofCell (A.inverseExtension.desc_app_cell g L hL (i, α))).symm.trans
        (ofCell_app g₁ (A.inverseExtension.cell (i, α))))))
  have hZ : ∀ j : A.ι × Bool, ∃ z : diagram Y (A.invertorExtension.shape j),
      HasRoundType (PastingDiagram.ofCell z) ((A.invertorExtension.source j).mapTo g₁)
        ((A.invertorExtension.target j).mapTo g₁) ∧ IsEquivalence Y z := by
    rintro ⟨i, α⟩
    let D := A.inverseData i
    have h : Equivalent ((D.composite α).mapTo g₁) ((D.unitBdry α).mapTo g₁) :=
      equivalent_trans (equivalent_of_equiv (D.composite_mapTo g₁ α))
        (equivalent_trans ((D.mapTo g₁).equivalent_composite_unitBdry (hcell i) (d i) (hinv i) α)
          (equivalent_of_equiv (equiv_of_eq (D.unitBdry_mapTo g₁ α).symm)))
    obtain ⟨U, c, hc, hdc, h₁, h₂⟩ := exists_equivalence_cell_side hY α _ _ h
    have hk : ((D.composite α).mapTo g₁).dim = D.cell.dim := D.dim_composite α
    rw [hk] at hdc h₁ h₂
    obtain ⟨e, he⟩ := (A.invertorExtension.parallel (i, α)).exists_iso_hasRoundType g₁ c
      (D.hasRoundType_mapTo_of_equiv_boundary g₁ α hdc h₁ h₂)
    exact ⟨_, he, (isEquivalence_map_iso_iff e c).2 hc⟩
  choose Z hZ hZe using hZ
  refine ⟨A.invertorExtension.desc g₁ Z hZ, ?_, fun j => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (A.inverseExtension.incl ≫ ·)
      (A.invertorExtension.incl_desc g₁ Z hZ)).trans (A.inverseExtension.incl_desc g L hL))
  · have h := hZe j
    rw [← A.invertorExtension.desc_app_cell g₁ Z hZ j] at h
    exact h

theorem exists_withins_next_cell (i : A.ι) (α : Bool) :
    ∃ (wu : Within (ofCell (A.stepIncl.app _ (A.cell i))) (ofCell (A.next.cell (i, α))))
      (wl : Within (ofCell (A.invertorExtension.incl.app _ (A.inverseExtension.cell (i, α))))
        (ofCell (A.next.cell (i, α))))
      (w₁ : Within ⟨unitShape ((A.shape i).toMoleculeShape.boundary
          ((A.shape i).dimension - 1) α),
          realize.map (cylProj ((A.shape i).toMoleculeShape.boundary
              ((A.shape i).dimension - 1) α)
            (((A.shape i).toMoleculeShape.boundary ((A.shape i).dimension - 1) α).ogp.bdryFull
              ⊤)) ≫
            realize.map ((A.shape i).toMoleculeShape.boundaryInclRDC
              ((A.shape i).dimension - 1) α) ≫ (ofCell (A.stepIncl.app _ (A.cell i))).map⟩
        (ofCell (A.next.cell (i, α)))),
      w₁.image = (A.next.shape (i, α)).ogp.boundary ⊤ (A.shape i).dimension (!α) ∧
      (A.next.shape (i, α)).ogp.IsPastingIn ((A.shape i).dimension - 1)
        (cond α wl.image wu.image) (cond α wu.image wl.image)
        ((A.next.shape (i, α)).ogp.boundary ⊤ (A.shape i).dimension α) := by
  let c := A.invertorExtension
  let D := A.inverseData i
  have h₃ : (ofCell (A.stepIncl.app _ (A.cell i))).map =
      (ofCell (A.cell i)).map ≫ A.inverseExtension.incl ≫ c.incl :=
    ofCell_app_map A.stepIncl (A.cell i)
  have h₄ := ofCell_app_map c.incl (A.inverseExtension.cell (i, α))
  have hk (β : Bool) : OGP.map ((c.parallel (i, α)).cellShapeEmb β) ⊤ =
      (A.next.shape (i, α)).ogp.boundary ⊤ (A.shape i).dimension β :=
    ((c.parallel (i, α)).map_cellShapeEmb β).trans
      (congrArg (fun m => (A.next.shape (i, α)).ogp.boundary ⊤ m β) (D.dim_source α))
  obtain ⟨wP, wU, hwP, hwU⟩ : ∃ (wP : Within ((D.composite α).toPastingDiagram.mapTo c.incl)
      (ofCell (c.cell (i, α)))) (wU : Within ((D.unitBdry α).toPastingDiagram.mapTo c.incl)
      (ofCell (c.cell (i, α)))),
      wP.image = (A.next.shape (i, α)).ogp.boundary ⊤ (A.shape i).dimension α ∧
        wU.image = (A.next.shape (i, α)).ogp.boundary ⊤ (A.shape i).dimension (!α) := by
    cases α
    · exact ⟨⟨_, c.ofInclusion_cellShapeEmb_false_comp_ofCell_cell (i, false)⟩,
        ⟨_, c.ofInclusion_cellShapeEmb_true_comp_ofCell_cell (i, false)⟩, hk false, hk true⟩
    · exact ⟨⟨_, c.ofInclusion_cellShapeEmb_true_comp_ofCell_cell (i, true)⟩,
        ⟨_, c.ofInclusion_cellShapeEmb_false_comp_ofCell_cell (i, true)⟩, hk true, hk false⟩
  have hunit : ((D.unitBdry α).toPastingDiagram.mapTo c.incl).map =
      realize.map (cylProj ((A.shape i).toMoleculeShape.boundary ((A.shape i).dimension - 1) α)
        (((A.shape i).toMoleculeShape.boundary ((A.shape i).dimension - 1) α).ogp.bdryFull ⊤)) ≫
        realize.map ((A.shape i).toMoleculeShape.boundaryInclRDC
          ((A.shape i).dimension - 1) α) ≫ (ofCell (A.stepIncl.app _ (A.cell i))).map :=
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans h₃.symm))))
  let wh := (Within.pasteIn α (D.pastable α)).mapTo c.incl
  obtain ⟨wc, hp⟩ := Within.exists_isPastingIn_pasteIn α (D.pastable α)
  refine ⟨@Within.mk _ _ _ (wh.trans wP).emb (wh.trans wP).isInclusion
      ((wh.trans wP).comm.trans ((Category.assoc _ _ _).trans h₃.symm)),
    @Within.mk _ _ _ ((wc.mapTo c.incl).trans wP).emb ((wc.mapTo c.incl).trans wP).isInclusion
      (((wc.mapTo c.incl).trans wP).comm.trans h₄.symm),
    @Within.mk _ _ _ wU.emb wU.isInclusion (wU.comm.trans hunit), hwU, ?_⟩
  have hu : map (wh.trans wP).emb ⊤ = map wP.emb (Within.pasteIn α (D.pastable α)).image :=
    (Within.image_trans _ wP).trans (congrArg (map wP.emb) (Within.image_mapTo _ c.incl))
  have hl : map ((wc.mapTo c.incl).trans wP).emb ⊤ = map wP.emb wc.image :=
    (Within.image_trans _ wP).trans (congrArg (map wP.emb) (Within.image_mapTo wc c.incl))
  have hp' := (isPastingIn_map_iff wP.emb _ _ _ ⊤).2 hp
  rw [Bool.apply_cond (map wP.emb), Bool.apply_cond (map wP.emb), ← hu, ← hl] at hp'
  rw [← hwP]
  exact hp'

theorem exists_biInvData_step (i : A.ι) :
    ∃ (e : RoundPastingDiagram A.step) (d : BiInvData Set.univ e),
      e.toPastingDiagram.Equiv (ofCell (A.stepIncl.app (op (A.shape i)) (A.cell i))) ∧
      ∀ α, (ofCell (A.invertorExtension.incl.app _ (A.inverseExtension.cell (i, α)))).Equiv
          (d.inverse α).toPastingDiagram ∧
        (ofCell (A.next.cell (i, α))).Equiv (d.invertor α).toPastingDiagram := by
  refine ⟨_, (A.inverseData i).biInvDataMapTo A.invertorExtension.incl (S := Set.univ)
    (fun α => cellRound (A.invertorExtension.cell (i, α))) (fun _ => Set.mem_univ _)
    (fun α => A.invertorExtension.hasRoundType_cell (i, α)), equiv_of_eq ?_, fun α =>
    ⟨equiv_of_eq (ofCell_app _ _), .refl _⟩⟩
  exact (mapTo_comp (ofCell (A.cell i)) A.inverseExtension.incl A.invertorExtension.incl).symm.trans
    (ofCell_app A.stepIncl (A.cell i)).symm

theorem dimension_inverseExtension_shape (j : A.ι × Bool) :
    (A.inverseExtension.shape j).dimension = (A.shape j.1).dimension := by
  have h₁ := A.inverseExtension.dimension_shape j
  have h₂ : (A.inverseExtension.source j).dim = (A.shape j.1).dimension - 1 :=
    dim_boundary _ (Nat.sub_le _ _) true
  have := A.dim_pos j.1
  omega

theorem dimension_next_shape (j : A.ι × Bool) :
    (A.next.shape j).dimension = (A.shape j.1).dimension + 1 :=
  (A.invertorExtension.dimension_shape j).trans
    (congrArg (· + 1) ((A.inverseData j.1).dim_source j.2))

def Inverts (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) : Prop :=
  ∀ i, ∃ (e : RoundPastingDiagram Y) (d : BiInvData Set.univ e),
    e.toPastingDiagram.Equiv (ofCell (f.app (op (A.shape i)) (A.cell i))) ∧
    ∀ α, (ofCell (L (i, α)).2).Equiv (d.inverse α).toPastingDiagram ∧
      (ofCell (Z (i, α)).2).Equiv (d.invertor α).toPastingDiagram

section StepDesc

private theorem hasRoundType_inverse_stepDesc {A : InversionData X} (f : X ⟶ Y)
    (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) (hLZ : A.Inverts f L Z) (j : A.ι × Bool) :
    HasRoundType (ofCell (L j).2) ((A.inverseExtension.source j).mapTo f)
      ((A.inverseExtension.target j).mapTo f) := by
  obtain ⟨e, d, he, hd⟩ := hLZ j.1
  exact hasRoundType_of_equivalent_inverse f (he.trans (equiv_of_eq (ofCell_app f (A.cell j.1))))
    d j.2 (L j).2 (equivalent_of_equiv (hd j.2).1.symm)

private noncomputable def stepDescInverse {A : InversionData X} (f : X ⟶ Y)
    (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) (hLZ : A.Inverts f L Z) :
    A.inverseExtension.extension ⟶ Y :=
  A.inverseExtension.desc f
    (fun j => (A.inverseExtension.parallel j).reindexCell f (L j).2
      (hasRoundType_inverse_stepDesc f L Z hLZ j))
    (fun j => (A.inverseExtension.parallel j).hasRoundType_reindexCell f (L j).2
      (hasRoundType_inverse_stepDesc f L Z hLZ j))

private theorem hasRoundType_invertor_stepDesc {A : InversionData X} (f : X ⟶ Y)
    (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) (hLZ : A.Inverts f L Z) (j : A.ι × Bool) :
    HasRoundType (ofCell (Z j).2)
      ((A.invertorExtension.source j).mapTo (stepDescInverse f L Z hLZ))
      ((A.invertorExtension.target j).mapTo (stepDescInverse f L Z hLZ)) := by
  obtain ⟨e, d, he, hd⟩ := hLZ j.1
  refine (A.inverseData j.1).hasRoundType_of_biInvData (stepDescInverse f L Z hLZ) d
    (he.trans (equiv_of_eq ?_)) (fun α => ?_) j.2 (hd j.2).2
  · exact (ofCell_app f (A.cell j.1)).trans ((congrArg (ofCell (A.cell j.1)).mapTo
      (A.inverseExtension.incl_desc f _ _).symm).trans (mapTo_comp _ _ _))
  · refine (equiv_of_eq ((ofCell_app _ _).symm.trans (congrArg ofCell
      (A.inverseExtension.desc_app_cell _ _ _ (j.1, α))))).trans
      (((A.inverseExtension.parallel _).equiv_ofCell_reindexCell _ _ _).trans (hd α).1)

noncomputable def stepDesc (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) : A.step ⟶ Y :=
  A.invertorExtension.desc (stepDescInverse f L Z hLZ)
    (fun j => (A.invertorExtension.parallel j).reindexCell _ (Z j).2
      (hasRoundType_invertor_stepDesc f L Z hLZ j))
    (fun j => (A.invertorExtension.parallel j).hasRoundType_reindexCell _ (Z j).2
      (hasRoundType_invertor_stepDesc f L Z hLZ j))

private theorem incl_stepDescInverse {A : InversionData X} (f : X ⟶ Y)
    (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) (hLZ : A.Inverts f L Z) :
    A.inverseExtension.incl ≫ stepDescInverse f L Z hLZ = f :=
  CellularExtensionData.incl_desc _ _ _ _

private theorem stepDescInverse_app_cell {A : InversionData X} (f : X ⟶ Y)
    (L Z : A.ι × Bool → Σ H : Atom, diagram Y H) (hLZ : A.Inverts f L Z)
    (j : A.inverseExtension.ι) :
    (stepDescInverse f L Z hLZ).app _ (A.inverseExtension.cell j) =
      (A.inverseExtension.parallel j).reindexCell f (L j).2
        (hasRoundType_inverse_stepDesc f L Z hLZ j) := by
  rw [stepDescInverse, CellularExtensionData.desc_app_cell]

private theorem incl_stepDesc (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) :
    A.invertorExtension.incl ≫ A.stepDesc f L Z hLZ = stepDescInverse f L Z hLZ :=
  CellularExtensionData.incl_desc _ _ _ _

@[reassoc (attr := simp)]
theorem stepIncl_stepDesc (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) :
    A.stepIncl ≫ A.stepDesc f L Z hLZ = f :=
  (Category.assoc _ _ _).trans ((congrArg (A.inverseExtension.incl ≫ ·)
    (A.incl_stepDesc f L Z hLZ)).trans (incl_stepDescInverse f L Z hLZ))

theorem stepDesc_app_inverse (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) (j : A.inverseExtension.ι)
    (e : A.inverseExtension.shape j ≅ (L j).1) :
    (A.stepDesc f L Z hLZ).app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) =
      Y.map e.hom.op (L j).2 := by
  have h₁ := congrArg (fun φ => φ.app _ (A.inverseExtension.cell j)) (A.incl_stepDesc f L Z hLZ)
  exact h₁.trans ((stepDescInverse_app_cell f L Z hLZ j).trans
    ((A.inverseExtension.parallel j).reindexCell_eq f (L j).2
      (hasRoundType_inverse_stepDesc f L Z hLZ j) e))

private theorem stepDesc_app_cell (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) (j : A.invertorExtension.ι) :
    (A.stepDesc f L Z hLZ).app _ (A.invertorExtension.cell j) =
      (A.invertorExtension.parallel j).reindexCell _ (Z j).2
        (hasRoundType_invertor_stepDesc f L Z hLZ j) := by
  rw [stepDesc]
  exact CellularExtensionData.desc_app_cell A.invertorExtension _ _ _ j

theorem stepDesc_app_next (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) (j : A.next.ι) (e : A.next.shape j ≅ (Z j).1) :
    (A.stepDesc f L Z hLZ).app _ (A.next.cell j) = Y.map e.hom.op (Z j).2 :=
  (A.stepDesc_app_cell f L Z hLZ j).trans ((A.invertorExtension.parallel j).reindexCell_eq _
    (Z j).2 (hasRoundType_invertor_stepDesc f L Z hLZ j) e)

theorem nonempty_iso_inverse_stepDesc (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) (j : A.ι × Bool) :
    Nonempty (A.inverseExtension.shape j ≅ (L j).1) :=
  (A.inverseExtension.parallel j).nonempty_iso_of_hasRoundType _ _
    (hasRoundType_inverse_stepDesc f L Z hLZ j)

theorem nonempty_iso_next_stepDesc (f : X ⟶ Y) (L Z : A.ι × Bool → Σ H : Atom, diagram Y H)
    (hLZ : A.Inverts f L Z) (j : A.ι × Bool) : Nonempty (A.next.shape j ≅ (Z j).1) :=
  (A.invertorExtension.parallel j).nonempty_iso_of_hasRoundType _ _
    (hasRoundType_invertor_stepDesc f L Z hLZ j)

end StepDesc

theorem step_hom_ext {φ φ' : A.step ⟶ Y} (h₀ : A.stepIncl ≫ φ = A.stepIncl ≫ φ')
    (h₁ : ∀ j, φ.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) =
      φ'.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)))
    (h₂ : ∀ j, φ.app _ (A.next.cell j) = φ'.app _ (A.next.cell j)) : φ = φ' :=
  A.invertorExtension.hom_ext
    (A.inverseExtension.hom_ext ((Category.assoc _ _ _).symm.trans (h₀.trans
      (Category.assoc _ _ _))) h₁) h₂

end InversionData

namespace InversionData

variable (A : InversionData X)

@[implicit_reducible]
noncomputable def stage : ℕ → Σ Z : DiagSet.{u}, InversionData Z
  | 0 => ⟨X, A⟩
  | n + 1 => ⟨(stage n).2.step, (stage n).2.next⟩

private noncomputable def sequence : ℕ ⥤ DiagSet.{u} :=
  Functor.ofSequence fun n => (A.stage n).2.stepIncl

noncomputable def localization : DiagSet.{u} := colimit A.sequence

noncomputable def toLocalization : X ⟶ A.localization := colimit.ι A.sequence 0

instance mono_toLocalization : Mono A.toLocalization := by
  let c : (MorphismProperty.monomorphisms DiagSet.{u}).TransfiniteCompositionOfShape ℕ
      A.toLocalization :=
    { F := A.sequence
      isoBot := Iso.refl _
      incl := (colimit.cocone A.sequence).ι
      isColimit := colimit.isColimit A.sequence
      fac := Category.id_comp _
      map_mem := fun n _ => by
        have h : A.sequence.map (homOfLE (Order.le_succ n)) = (A.stage n).2.stepIncl :=
          Functor.ofSequence_map_homOfLE_succ _ n
        rw [h]
        exact (A.stage n).2.mono_stepIncl }
  exact MorphismProperty.transfiniteCompositionsOfShape_le _ ℕ _ (c.mem _)

noncomputable def stageι (n : ℕ) : (A.stage n).1 ⟶ A.localization := colimit.ι A.sequence n

@[reassoc (attr := simp)]
theorem stepIncl_stageι (n : ℕ) : (A.stage n).2.stepIncl ≫ A.stageι (n + 1) = A.stageι n :=
  (congrArg (· ≫ colimit.ι A.sequence (n + 1))
    (Functor.ofSequence_map_homOfLE_succ _ n).symm).trans (colimit.w A.sequence _)

noncomputable def desc (g : ∀ n, (A.stage n).1 ⟶ Y)
    (hg : ∀ n, (A.stage n).2.stepIncl ≫ g (n + 1) = g n) : A.localization ⟶ Y :=
  colimit.desc A.sequence ⟨Y, NatTrans.ofSequence g fun n => by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (congrArg (· ≫ g (n + 1)) (Functor.ofSequence_map_homOfLE_succ _ n)).trans (hg n)⟩

@[reassoc (attr := simp)]
theorem stageι_desc (g : ∀ n, (A.stage n).1 ⟶ Y)
    (hg : ∀ n, (A.stage n).2.stepIncl ≫ g (n + 1) = g n) (n : ℕ) :
    A.stageι n ≫ A.desc g hg = g n :=
  colimit.ι_desc _ _

theorem hom_ext {φ φ' : A.localization ⟶ Y} (h : ∀ n, A.stageι n ≫ φ = A.stageι n ≫ φ') :
    φ = φ' :=
  colimit.hom_ext h

theorem isEquivalence_toLocalization (i : A.ι) :
    IsEquivalence A.localization (A.toLocalization.app (op (A.shape i)) (A.cell i)) := by
  let S : Set (RoundPastingDiagram A.localization) := {z | ∃ (n : ℕ) (j : (A.stage n).2.ι),
    z = cellRound ((colimit.ι A.sequence n).app (op ((A.stage n).2.shape j))
      ((A.stage n).2.cell j))}
  refine subset_equivalences (A := S) ?_ ⟨0, i, rfl⟩
  rintro _ ⟨n, j, rfl⟩
  have hw := ((A.stage n).2.biInvWitness_step j).mapTo (colimit.ι A.sequence (n + 1))
  have hsub : (fun d : RoundPastingDiagram (A.stage n).2.step =>
      d.mapTo (colimit.ι A.sequence (n + 1))) ''
        {z | ∃ k, z = cellRound ((A.stage n).2.next.cell k)} ⊆ S := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨n + 1, k, RoundPastingDiagram.ext (ofCell_app _ _).symm⟩
  refine BiInvWitness.of_equiv (equiv_of_eq ?_) ((hw.data.mono hsub).witness)
  exact (congrArg (·.mapTo (colimit.ι A.sequence (n + 1)))
    (ofCell_app (A.stage n).2.stepIncl ((A.stage n).2.cell j))).trans
    ((mapTo_comp _ _ _).symm.trans ((congrArg (ofCell ((A.stage n).2.cell j)).mapTo
      (A.stepIncl_stageι n)).trans (ofCell_app _ _).symm))

theorem isEquivalence_of_toLocalization_comp_eq (g : A.localization ⟶ Y)
    (i : A.ι) : IsEquivalence Y ((A.toLocalization ≫ g).app (op (A.shape i)) (A.cell i)) := by
  exact (A.isEquivalence_toLocalization i).map g

private noncomputable def extendStage (hY : HasWeakComposites Y) (g : X ⟶ Y)
    (hg : ∀ i, IsEquivalence Y (g.app (op (A.shape i)) (A.cell i))) :
    ∀ n, {g' : (A.stage n).1 ⟶ Y //
      ∀ i, IsEquivalence Y (g'.app (op ((A.stage n).2.shape i)) ((A.stage n).2.cell i))}
  | 0 => ⟨g, hg⟩
  | n + 1 =>
    ⟨((A.stage n).2.exists_stepIncl_comp_eq hY (extendStage hY g hg n).1
        (extendStage hY g hg n).2).choose,
      ((A.stage n).2.exists_stepIncl_comp_eq hY (extendStage hY g hg n).1
        (extendStage hY g hg n).2).choose_spec.2⟩

private theorem stepIncl_comp_extendStage (hY : HasWeakComposites Y) (g : X ⟶ Y)
    (hg : ∀ i, IsEquivalence Y (g.app (op (A.shape i)) (A.cell i))) (n : ℕ) :
    (A.stage n).2.stepIncl ≫ (A.extendStage hY g hg (n + 1)).1 = (A.extendStage hY g hg n).1 :=
  ((A.stage n).2.exists_stepIncl_comp_eq hY (A.extendStage hY g hg n).1
    (A.extendStage hY g hg n).2).choose_spec.1

theorem exists_toLocalization_comp_eq (hY : HasWeakComposites Y) (f : X ⟶ Y)
    (hf : ∀ i, IsEquivalence Y (f.app (op (A.shape i)) (A.cell i))) :
    ∃ g : A.localization ⟶ Y, A.toLocalization ≫ g = f :=
  ⟨A.desc (fun n => (A.extendStage hY f hf n).1) (A.stepIncl_comp_extendStage hY f hf),
    A.stageι_desc _ _ 0⟩

private theorem map_map_iso {W : DiagSet.{u}} {U V T : Atom} (e₁ : U ≅ V) (e₂ : V ≅ T) (e : U ≅ T)
    (z : W.obj (op T)) : W.map e₁.hom.op (W.map e₂.hom.op z) = W.map e.hom.op z := by
  rw [Atom.iso_eq e (e₁ ≪≫ e₂)]
  exact (Functor.map_comp_apply W _ _ _).symm

structure Hom {Y : DiagSet.{u}} (A : InversionData X) (B : InversionData Y) where
  map : X ⟶ Y
  index : A.ι → B.ι
  iso : ∀ i, A.shape i ≅ B.shape (index i)
  map_app_cell : ∀ i,
    map.app (op (A.shape i)) (A.cell i) = Y.map (iso i).hom.op (B.cell (index i))

namespace Hom

variable {A} {Z : DiagSet.{u}} {B : InversionData Y} {C : InversionData Z}

@[ext]
theorem ext {φ ψ : A.Hom B} (h₁ : φ.map = ψ.map) (h₂ : φ.index = ψ.index) : φ = ψ := by
  obtain ⟨f, σ, e, he⟩ := φ
  obtain ⟨f', σ', e', he'⟩ := ψ
  obtain rfl : f = f' := h₁
  obtain rfl : σ = σ' := h₂
  obtain rfl : e = e' := funext fun i => Atom.iso_eq _ _
  rfl

def id (A : InversionData X) : A.Hom A where
  map := 𝟙 X
  index i := i
  iso _ := Iso.refl _
  map_app_cell _ := (Functor.map_id_apply X _ _).symm

def comp (φ : A.Hom B) (ψ : B.Hom C) : A.Hom C where
  map := φ.map ≫ ψ.map
  index i := ψ.index (φ.index i)
  iso i := φ.iso i ≪≫ ψ.iso (φ.index i)
  map_app_cell i := (NatTrans.comp_app_apply _ _ _ _).trans
    ((congrArg (ψ.map.app _) (φ.map_app_cell i)).trans ((NatTrans.naturality_apply _ _ _).trans
      ((congrArg (Z.map _) (ψ.map_app_cell _)).trans (map_map_iso _ _ _ _))))

theorem inverts_step (φ : A.Hom B) :
    A.Inverts (φ.map ≫ B.stepIncl)
      (fun j => ⟨B.inverseExtension.shape (φ.index j.1, j.2),
        B.invertorExtension.incl.app _ (B.inverseExtension.cell (φ.index j.1, j.2))⟩)
      (fun j => ⟨B.next.shape (φ.index j.1, j.2), B.next.cell (φ.index j.1, j.2)⟩) := by
  intro i
  obtain ⟨e, d, he, hd⟩ := B.exists_biInvData_step (φ.index i)
  have hx : (φ.map ≫ B.stepIncl).app _ (A.cell i) =
      B.step.map (φ.iso i).hom.op (B.stepIncl.app _ (B.cell (φ.index i))) :=
    (congrArg (B.stepIncl.app _) (φ.map_app_cell i)).trans (NatTrans.naturality_apply _ _ _)
  exact ⟨e, d, he.trans ((equiv_ofCell_map_iso (φ.iso i) _).symm.trans
    (equiv_of_eq (congrArg ofCell hx.symm))), hd⟩

noncomputable def step (φ : A.Hom B) : A.step ⟶ B.step :=
  A.stepDesc _ _ _ φ.inverts_step

@[reassoc (attr := simp)]
theorem stepIncl_step (φ : A.Hom B) : A.stepIncl ≫ φ.step = φ.map ≫ B.stepIncl :=
  A.stepIncl_stepDesc _ _ _ φ.inverts_step

theorem step_app_inverse (φ : A.Hom B) (j : A.inverseExtension.ι)
    (e : A.inverseExtension.shape j ≅ B.inverseExtension.shape (φ.index j.1, j.2)) :
    φ.step.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) =
      B.step.map e.hom.op
        (B.invertorExtension.incl.app _ (B.inverseExtension.cell (φ.index j.1, j.2))) :=
  A.stepDesc_app_inverse _ _ _ φ.inverts_step j e

theorem nonempty_iso_inverse (φ : A.Hom B) (j : A.inverseExtension.ι) :
    Nonempty (A.inverseExtension.shape j ≅ B.inverseExtension.shape (φ.index j.1, j.2)) :=
  A.nonempty_iso_inverse_stepDesc _ _ _ φ.inverts_step j

noncomputable def next (φ : A.Hom B) : A.next.Hom B.next where
  map := φ.step
  index j := (φ.index j.1, j.2)
  iso j := Classical.choice (A.nonempty_iso_next_stepDesc _ _ _ φ.inverts_step j)
  map_app_cell j := A.stepDesc_app_next _ _ _ φ.inverts_step j _

@[simp]
theorem next_map (φ : A.Hom B) : φ.next.map = φ.step := rfl

theorem step_comp (φ : A.Hom B) (ψ : B.Hom C) : (φ.comp ψ).step = φ.step ≫ ψ.step := by
  refine A.step_hom_ext ?_ (fun j => ?_) (fun j => ?_)
  · rw [stepIncl_step, stepIncl_step_assoc, stepIncl_step]
    exact Category.assoc _ _ _
  · let e₁ := Classical.choice (φ.nonempty_iso_inverse j)
    let e₂ := Classical.choice (ψ.nonempty_iso_inverse (φ.index j.1, j.2))
    exact ((φ.comp ψ).step_app_inverse j (e₁ ≪≫ e₂)).trans ((map_map_iso e₁ e₂ _ _).symm.trans
      ((congrArg (C.step.map e₁.hom.op) (ψ.step_app_inverse _ e₂)).symm.trans
        ((NatTrans.naturality_apply _ _ _).symm.trans ((congrArg (ψ.step.app _)
          (φ.step_app_inverse j e₁)).symm.trans (NatTrans.comp_app_apply _ _ _ _).symm))))
  · let i₁ := φ.next.iso j
    let i₂ := ψ.next.iso (φ.index j.1, j.2)
    calc (φ.comp ψ).step.app _ (A.next.cell j)
        = C.step.map ((φ.comp ψ).next.iso j).hom.op
            (C.next.cell (ψ.index (φ.index j.1), j.2)) := (φ.comp ψ).next.map_app_cell j
      _ = C.step.map i₁.hom.op (C.step.map i₂.hom.op
            (C.next.cell (ψ.index (φ.index j.1), j.2))) := (map_map_iso i₁ i₂ _ _).symm
      _ = C.step.map i₁.hom.op (ψ.step.app _ (B.next.cell (φ.index j.1, j.2))) :=
          congrArg (C.step.map i₁.hom.op) (ψ.next.map_app_cell _).symm
      _ = ψ.step.app _ (B.step.map i₁.hom.op (B.next.cell (φ.index j.1, j.2))) :=
          (NatTrans.naturality_apply _ _ _).symm
      _ = ψ.step.app _ (φ.step.app _ (A.next.cell j)) :=
          congrArg (ψ.step.app _) (φ.next.map_app_cell j).symm
      _ = (φ.step ≫ ψ.step).app _ (A.next.cell j) := (NatTrans.comp_app_apply _ _ _ _).symm

theorem step_id (A : InversionData X) : (Hom.id A).step = 𝟙 A.step := by
  refine A.step_hom_ext ?_ (fun j => ?_) (fun j => ?_)
  · rw [stepIncl_step]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact ((Hom.id A).step_app_inverse j (Iso.refl _)).trans (Functor.map_id_apply _ _ _)
  · exact ((Hom.id A).next.map_app_cell j).trans ((congrArg (fun e : A.next.shape j ≅ _ =>
      A.step.map e.hom.op _) (Atom.iso_eq _ (Iso.refl _))).trans (Functor.map_id_apply _ _ _))

noncomputable def stage (φ : A.Hom B) : ∀ n, (A.stage n).2.Hom (B.stage n).2
  | 0 => φ
  | n + 1 => (stage φ n).next

theorem stage_comp (φ : A.Hom B) (ψ : B.Hom C) (n : ℕ) :
    (φ.comp ψ).stage n = (φ.stage n).comp (ψ.stage n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((φ.comp ψ).stage n).next = ((φ.stage n).next).comp ((ψ.stage n).next)
    rw [ih]
    exact Hom.ext (step_comp _ _) rfl

theorem stage_id (A : InversionData X) (n : ℕ) : (Hom.id A).stage n = Hom.id _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((Hom.id A).stage n).next = _
    rw [ih]
    exact Hom.ext (step_id _) rfl

noncomputable def localizationMap (φ : A.Hom B) : A.localization ⟶ B.localization :=
  A.desc (fun n => (φ.stage n).map ≫ B.stageι n) fun n =>
    ((φ.stage n).stepIncl_step_assoc (B.stageι (n + 1))).trans
      (congrArg ((φ.stage n).map ≫ ·) (B.stepIncl_stageι n))

@[reassoc (attr := simp)]
theorem stageι_localizationMap (φ : A.Hom B) (n : ℕ) :
    A.stageι n ≫ φ.localizationMap = (φ.stage n).map ≫ B.stageι n :=
  A.stageι_desc _ _ n

@[reassoc (attr := simp)]
theorem toLocalization_localizationMap (φ : A.Hom B) :
    A.toLocalization ≫ φ.localizationMap = φ.map ≫ B.toLocalization :=
  φ.stageι_localizationMap 0

theorem localizationMap_comp (φ : A.Hom B) (ψ : B.Hom C) :
    (φ.comp ψ).localizationMap = φ.localizationMap ≫ ψ.localizationMap :=
  A.hom_ext fun n => by
    rw [stageι_localizationMap, stageι_localizationMap_assoc, stageι_localizationMap,
      stage_comp]
    exact Category.assoc _ _ _

theorem localizationMap_id (A : InversionData X) : (Hom.id A).localizationMap = 𝟙 _ :=
  A.hom_ext fun n => by
    rw [stageι_localizationMap, stage_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

noncomputable def stageFrom {n : ℕ} (φ : A.Hom (C.stage n).2) :
    ∀ k, (A.stage k).2.Hom (C.stage (n + k)).2
  | 0 => φ
  | k + 1 => (stageFrom φ k).next

noncomputable def localizationMapFrom {n : ℕ} (φ : A.Hom (C.stage n).2) :
    A.localization ⟶ C.localization :=
  A.desc (fun k => (φ.stageFrom k).map ≫ C.stageι (n + k)) fun k =>
    ((φ.stageFrom k).stepIncl_step_assoc (C.stageι (n + k + 1))).trans
      (congrArg ((φ.stageFrom k).map ≫ ·) (C.stepIncl_stageι (n + k)))

@[reassoc (attr := simp)]
theorem toLocalization_localizationMapFrom {n : ℕ} (φ : A.Hom (C.stage n).2) :
    A.toLocalization ≫ φ.localizationMapFrom = φ.map ≫ C.stageι n :=
  A.stageι_desc _ _ 0

end Hom

end InversionData

private theorem exists_mem_bdryFull_apply_eq_apply_top {S W : Atom}
    (hW : W.dimension < S.dimension) (x : S ⟶ W) :
    ∃ b ∈ S.ogp.bdryFull ⊤, x b = x S.top := by
  have hS : krullDim (⊤ : LowerSet S.ogp) = (S.dimension - 1 : ℕ) + 1 := by
    rw [LowerSet.krullDim_top, S.krullDim_eq_dimension]
    exact_mod_cast (by omega : S.dimension = S.dimension - 1 + 1)
  have hle : krullDim (LowerSet.Iic (x S.top)) ≤ (S.dimension - 1 : ℕ) := by
    calc krullDim (LowerSet.Iic (x S.top)) ≤ krullDim (⊤ : LowerSet W.ogp) :=
          LowerSet.krullDim_mono le_top
      _ = W.dimension := by rw [LowerSet.krullDim_top, W.krullDim_eq_dimension]
      _ ≤ (S.dimension - 1 : ℕ) := by exact_mod_cast (by omega : W.dimension ≤ S.dimension - 1)
  have himg := (Atom.isMap x).image_boundary S.top (S.dimension - 1) false
  rw [S.Iic_top, boundary_eq_self hle] at himg
  obtain ⟨b, hb, hbx⟩ := himg.ge (LowerSet.mem_Iic_iff.2 le_rfl)
  refine ⟨b, LowerSet.mem_sup_iff.2 (Or.inl ?_), hbx⟩
  rw [bdry_eq_boundary hS]
  exact hb

private theorem eq_of_eqOn_bdryFull {S W : Atom} (hW : W.dimension < S.dimension)
    {x y : S ⟶ W} (h : ∀ b ∈ S.ogp.bdryFull ⊤, x b = y b) : x = y := by
  have htop : x S.top = y S.top := by
    obtain ⟨b, hb, hbx⟩ := exists_mem_bdryFull_apply_eq_apply_top hW x
    obtain ⟨c, hc, hcy⟩ := exists_mem_bdryFull_apply_eq_apply_top hW y
    refine le_antisymm ?_ ?_
    · rw [← hbx, h b hb]
      exact (Atom.isMap y).monotone (S.le_top b)
    · rw [← hcy, ← h c hc]
      exact (Atom.isMap x).monotone (S.le_top c)
  refine Atom.hom_ext fun z => ?_
  by_cases hz : z ∈ S.ogp.bdryFull ⊤
  · exact h z hz
  · obtain rfl : z = S.top := not_not.1 ((S.mem_bdryFull_top_iff z).not.1 hz)
    exact htop

theorem eq_of_equiv_boundary_ball {S W : Atom} (hW : W.dimension < S.dimension)
    {k : ℕ} (hk : k + 1 = S.dimension) {x y : diagram (ball.{u} W) S}
    (h : ∀ α, ((ofCell x).boundary k α).Equiv ((ofCell y).boundary k α)) : x = y := by
  refine ULift.ext _ _ (eq_of_eqOn_bdryFull hW fun b hb => ?_)
  have hS : krullDim (⊤ : LowerSet S.ogp) = k + 1 := by
    rw [LowerSet.krullDim_top, S.krullDim_eq_dimension, ← hk]
    push_cast
    rfl
  obtain ⟨α, hbα⟩ : ∃ α, b ∈ S.ogp.boundary ⊤ k α := by
    rcases LowerSet.mem_sup_iff.1 hb with h' | h'
    · rw [bdry_eq_boundary hS] at h'
      exact ⟨false, h'⟩
    · rw [bdry_eq_boundary hS] at h'
      exact ⟨true, h'⟩
  rw [← MoleculeShape.map_boundaryIncl_top] at hbα
  obtain ⟨q, -, rfl⟩ := hbα
  obtain ⟨ψ, hψ⟩ := h α
  let B := S.toMoleculeShape.boundary k α
  have : Subsingleton (((ofCell x).boundary k α).shape.ogp ≅ ((ofCell y).boundary k α).shape.ogp) :=
    B.isMolecule.subsingleton_iso
  obtain rfl : ψ = Iso.refl _ := Subsingleton.elim _ _
  have he : realize.map (RDCpx.isoOfIso (P := B.rdc) (Q := B.rdc) (Iso.refl B.ogp)).hom = 𝟙 _ :=
    (congrArg realize.map (by ext; rfl :
      (RDCpx.isoOfIso (P := B.rdc) (Q := B.rdc) (Iso.refl B.ogp)).hom = 𝟙 B.rdc)).trans
      (realize.map_id _)
  have hψ' := (Category.id_comp _).symm.trans ((congrArg (· ≫ _) he.symm).trans hψ)
  let T := principalAtomRDC B.rdc q
  let c := principalInclusionRDC B.rdc q
  have hval : ∀ z : diagram (ball W) S,
      ConcreteCategory.hom (((realize.map (S.toMoleculeShape.boundaryInclRDC k α) ≫
        (ofCell z).map).app (op T) ⟨c⟩).down : T ⟶ W) T.top =
        ConcreteCategory.hom (z.down : S ⟶ W) (S.toMoleculeShape.boundaryIncl k α q) := fun z =>
    congrArg (fun t => ConcreteCategory.hom (z.down : S ⟶ W)
      (S.toMoleculeShape.boundaryIncl k α t)) (principalInclusionRDC_top B.rdc q)
  exact (hval x).symm.trans ((congrArg (fun m : realize.obj B.rdc ⟶ ball W =>
    ConcreteCategory.hom ((m.app (op T) ⟨c⟩).down : T ⟶ W) T.top) hψ').symm.trans (hval y))

theorem isDegenerate_ball_of_dimension_lt {S W : Atom} (hW : W.dimension < S.dimension)
    (x : diagram (ball.{u} W) S) : IsDegenerate (ball W) x := by
  let f : S ⟶ W := x.down
  refine ⟨Atom.ofClosure W (f S.top), principalLift W (f S.top) f
    (apply_mem_closure_apply_top f), ⟨Atom.closureIncl W (f S.top)⟩,
    isCollapseHom_of_apply_eq_top _ (principalLift_apply_top f), fun hiso => ?_,
    congrArg ULift.up (principalLift_comp_closureIncl _ _ _ _)⟩
  have h₁ := Atom.dimension_eq_of_iso (asIso (principalLift W (f S.top) f
    (apply_mem_closure_apply_top f)))
  rw [Atom.dimension_ofClosure] at h₁
  exact absurd (h₁.trans_le ((grade_mono (W.le_top _)).trans_eq W.dimension_eq.symm))
    (not_le.2 hW)

theorem isIso_or_isDegenerate_map_of_apply_top_eq {Y : DiagSet.{u}} {V W : Atom} (g : V ⟶ W)
    (hg : g V.top = W.top) (w : diagram Y W) : IsIso g ∨ IsDegenerate Y (Y.map g.op w) := by
  by_cases h : IsIso g
  · exact Or.inl h
  · exact Or.inr ⟨W, g, w, isCollapseHom_of_apply_eq_top g hg, h, rfl⟩

theorem isIso_or_isDegenerate_ball {U V : Atom} (hUV : U.dimension ≤ V.dimension)
    (y : diagram (ball.{u} U) V) : IsIso (y.down : V ⟶ U) ∨ IsDegenerate (ball U) y := by
  let f : V ⟶ U := y.down
  by_cases ht : f V.top = U.top
  · rcases isIso_or_isDegenerate_map_of_apply_top_eq (Y := ball U) f ht ⟨𝟙 U⟩ with h | h
    · exact Or.inl h
    · exact Or.inr ((congrArg (IsDegenerate (ball U))
        (congrArg ULift.up (Category.comp_id f))).mp h)
  · refine Or.inr ?_
    let a := f V.top
    have hlt : grade ℕ a < U.dimension := by
      rw [U.dimension_eq]
      exact grade_strictMono ((U.le_top a).lt_of_ne ht)
    let p := principalLift U a f (apply_mem_closure_apply_top f)
    have hp : IsDegenerate (ball (Atom.ofClosure U a)) ⟨p⟩ :=
      isDegenerate_ball_of_dimension_lt (by rw [Atom.dimension_ofClosure]; omega) ⟨p⟩
    have h := isDegenerate_app (uliftYoneda.{u}.map (Atom.closureIncl U a)) hp
    exact (congrArg (IsDegenerate (ball U)) (congrArg ULift.up
      (principalLift_comp_closureIncl U a f (apply_mem_closure_apply_top f)))).mp h

private theorem CellularExtensionData.hom_ext_ball (c : CellularExtensionData X) {W : Atom}
    (hW : ∀ e, W.dimension < (c.shape e).dimension) {φ φ' : c.extension ⟶ ball W}
    (h : c.incl ≫ φ = c.incl ≫ φ') : φ = φ' := by
  refine c.hom_ext h fun e => eq_of_equiv_boundary_ball (hW e) (c.dimension_shape e).symm
    fun α => ?_
  have t := (c.hasRoundType_cell e).mapTo φ
  have t' := (c.hasRoundType_cell e).mapTo φ'
  have hm : ∀ u : PastingDiagram X, (u.mapTo c.incl).mapTo φ = (u.mapTo c.incl).mapTo φ' :=
    fun u => (mapTo_comp _ _ _).symm.trans ((congrArg u.mapTo h).trans (mapTo_comp _ _ _))
  have hx := equiv_of_eq (congrArg (·.boundary (c.source e).dim α) (ofCell_app φ (c.cell e)))
  have hy := equiv_of_eq (congrArg (·.boundary (c.source e).dim α) (ofCell_app φ' (c.cell e)))
  cases α
  · exact hx.trans (t.source.trans ((equiv_of_eq (hm _)).trans (t'.source.symm.trans hy.symm)))
  · exact hx.trans (t.target.trans ((equiv_of_eq (hm _)).trans (t'.target.symm.trans hy.symm)))

namespace InversionData

variable (A : InversionData X)

private theorem step_hom_ext_ball {W : Atom}
    (hW : ∀ i, W.dimension < (A.shape i).dimension) {φ φ' : A.step ⟶ ball W}
    (h : A.stepIncl ≫ φ = A.stepIncl ≫ φ') : φ = φ' := by
  refine A.invertorExtension.hom_ext_ball (fun j => ?_)
    (A.inverseExtension.hom_ext_ball (fun j => ?_) ((Category.assoc _ _ _).symm.trans
      (h.trans (Category.assoc _ _ _))))
  · exact (hW j.1).trans_le ((Nat.le_succ _).trans (A.dimension_next_shape j).ge)
  · exact (hW j.1).trans_eq (A.dimension_inverseExtension_shape j).symm

private theorem lt_dimension_stage_shape {m : ℕ} (hm : ∀ i, m < (A.shape i).dimension) :
    ∀ n i, m < ((A.stage n).2.shape i).dimension
  | 0, i => hm i
  | n + 1, j => (lt_dimension_stage_shape hm n j.1).trans_le
      ((Nat.le_succ _).trans ((A.stage n).2.dimension_next_shape j).ge)

theorem hom_ext_ball {W : Atom} (hW : ∀ i, W.dimension < (A.shape i).dimension)
    {φ φ' : A.localization ⟶ ball W} (h : A.toLocalization ≫ φ = A.toLocalization ≫ φ') :
    φ = φ' := by
  refine A.hom_ext fun n => ?_
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (A.stage n).2.step_hom_ext_ball (A.lt_dimension_stage_shape hW n)
      (((A.stepIncl_stageι_assoc n φ).trans ih).trans (A.stepIncl_stageι_assoc n φ').symm)

end InversionData

end Atoms.Diagrammatic
