import Atoms.Diagrammatic.Rewriting.Layered
import Atoms.Molecule.Path

open CategoryTheory Order Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP
open Atoms.Diagrammatic.PastingDiagram

universe u v w

namespace Atoms.Diagrammatic.Layered.Signature

def track (S : Signature.{v}) : List (Cell S.Pt S.Ed S.Ce × ℕ) → ℕ → Option ℕ
  | [], y => some y
  | (c, o) :: ls, y =>
    if y ≤ 2 * o then track S ls y
    else if 2 * (o + (S.cellType c).1.length) ≤ y then
      track S ls (y + 2 * (S.cellType c).2.length - 2 * (S.cellType c).1.length)
    else none

def FullRound (S : Signature.{v}) (d : Diagram S.Pt S.Ed S.Ce) : Prop :=
  d.layers = [] ∨ ∀ y < 2 * d.source.length, 0 < y → S.track d.layers y = none

instance (S : Signature.{v}) : DecidablePred S.FullRound := fun d =>
  inferInstanceAs (Decidable (d.layers = [] ∨ _))

variable {S : Signature.{v}} [DecidableEq S.Pt]

section NumEdges

variable {P Q : OGP.{w}} [Fintype P] [DecidableLE P] {U V W : LowerSet P}

private noncomputable def numEdges (U : LowerSet P) : ℕ := by
  classical exact (edgeList U).length

private theorem numEdges_eq [DecidablePred (· ∈ U)] : numEdges U = (edgeList U).length := by
  unfold numEdges
  congr

private theorem le_numEdges {y : ℕ} {x : P} (h : IsPathPos U y x) : y ≤ 2 * numEdges U := by
  classical
  rw [numEdges_eq]
  exact h.le

private theorem isPathPos_cond_iff_numEdges (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (α : Bool) {x : P} :
    IsPathPos U (cond α (2 * numEdges U) 0) x ↔ P.boundary U 0 α = LowerSet.Iic x := by
  classical
  rw [numEdges_eq]
  exact isPathPos_cond_iff hU hd α

private theorem isPathPos_right_numEdges (hp : P.IsPastingIn 0 V W U) (hV : IsMoleculeIn P V)
    (hW : IsMoleculeIn P W) (hd : krullDim U ≤ 1) {y : ℕ} {x : P} (h : IsPathPos W y x) :
    IsPathPos U (2 * numEdges V + y) x := by
  classical
  rw [numEdges_eq]
  exact hp.isPathPos_right hV hW hd h

private theorem numEdges_eq_add (hp : P.IsPastingIn 0 V W U) (hV : IsMoleculeIn P V)
    (hW : IsMoleculeIn P W) (hd : krullDim U ≤ 1) : numEdges U = numEdges V + numEdges W := by
  classical
  simp only [numEdges_eq]
  exact hp.length_edgeList_eq_add hV hW hd

private theorem numEdges_map [Fintype Q] [DecidableLE Q] (f : P ⟶ Q) [IsInclusion f]
    (hU : IsMoleculeIn P U) (hd : krullDim U = 1) : numEdges (OGP.map f U) = numEdges U := by
  classical
  rw [numEdges_eq, numEdges_eq, edgeList_map f hU hd, List.length_map]

private theorem numEdges_of_isAtomIn (h : P.IsAtomIn U) (hd : krullDim U = 1) :
    numEdges U = 1 := by
  classical
  rw [numEdges_eq]
  exact length_edgeList_of_isAtomIn h hd

end NumEdges

variable {X : DiagSet.{u}} {m : PastingDiagram X}

local notation "∂₁[" w ", " α "]" => OGP.boundary _ (Within.image w) 1 α

private def Tracks (a m : PastingDiagram X) (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (w : Within a m) (x : m.shape.ogp) (y z : ℕ), IsPathPos ∂₁[w, false] y x →
    IsPathPos ∂₁[w, true] z x → R y z

private theorem Tracks.mono {a : PastingDiagram X} {R R' : ℕ → ℕ → Prop} (h : Tracks a m R)
    (hR : ∀ y z, R y z → R' y z) : Tracks a m R' :=
  fun w x y z hy hz => hR y z (h w x y z hy hz)

private theorem isMoleculeIn_bdry {a : PastingDiagram X} (w : Within a m) (α : Bool) :
    IsMoleculeIn m.shape.ogp ∂₁[w, α] :=
  w.isMoleculeIn_image.boundary 1 α

private theorem krullDim_bdry {a : PastingDiagram X} (w : Within a m) (α : Bool) :
    krullDim ∂₁[w, α] ≤ 1 :=
  krullDim_boundary_le _ 1 α

private theorem isPastingIn_trans {a b : PastingDiagram X} (k : ℕ) (h : a.Pastable b k)
    (w : Within (a.paste b k h) m) :
    m.shape.ogp.IsPastingIn k ((Within.pasteInl a b k h).trans w).image
      ((Within.pasteInr a b k h).trans w).image w.image := by
  rw [Within.image_trans, Within.image_trans]
  exact (isPastingIn_map_iff w.emb k _ _ _).2 (Within.isPastingIn_paste a b k h)

private theorem bdry_eq_image {a : PastingDiagram X} (w : Within a m) (ha : a.dim ≤ 1)
    (α : Bool) : ∂₁[w, α] = w.image :=
  boundary_eq_self (by rw [w.krullDim_image]; exact_mod_cast ha) α

private theorem paste_zero_cases {a b : PastingDiagram X} (h : a.Pastable b 0)
    (w : Within (a.paste b 0 h) m) {x : m.shape.ogp} {Y Z : ℕ}
    (hY : IsPathPos ∂₁[w, false] Y x) (hZ : IsPathPos ∂₁[w, true] Z x) :
    (IsPathPos ∂₁[(Within.pasteInl a b 0 h).trans w, false] Y x ∧
      IsPathPos ∂₁[(Within.pasteInl a b 0 h).trans w, true] Z x) ∨
    ∃ y z, IsPathPos ∂₁[(Within.pasteInr a b 0 h).trans w, false] y x ∧
      IsPathPos ∂₁[(Within.pasteInr a b 0 h).trans w, true] z x ∧
      Y = 2 * numEdges ∂₁[(Within.pasteInl a b 0 h).trans w, false] + y ∧
      Z = 2 * numEdges ∂₁[(Within.pasteInl a b 0 h).trans w, true] + z := by
  set wl := (Within.pasteInl a b 0 h).trans w
  set wr := (Within.pasteInr a b 0 h).trans w
  have hp := isPastingIn_trans 0 h w
  have hgl := wl.isMoleculeIn_image.isGlobular
  have hgr := wr.isMoleculeIn_image.isGlobular
  have hb (β : Bool) := hp.boundary_of_lt hgl hgr Nat.zero_lt_one β
  have hinr (β : Bool) : wl.image ⊓ wr.image ≤ ∂₁[wr, β] :=
    hp.inf_eq_input ▸ hgr.boundary_le_boundary Nat.zero_lt_one false β
  have hmem (β : Bool) {P : ℕ} (hP : IsPathPos ∂₁[w, β] P x) : x ∈ ∂₁[wl, β] ⊔ ∂₁[wr, β] := by
    rw [(hb β).sup_eq]
    exact hP.mem (isMoleculeIn_bdry w β) (krullDim_bdry w β)
  by_cases hr : x ∈ wr.image
  · have hx (β : Bool) {P : ℕ} (hP : IsPathPos ∂₁[w, β] P x) : x ∈ ∂₁[wr, β] := by
      rcases LowerSet.mem_sup_iff.1 (hmem β hP) with h' | h'
      · exact hinr β (LowerSet.mem_inf_iff.2 ⟨boundary_le _ _ _ h', hr⟩)
      · exact h'
    obtain ⟨y, hy⟩ := exists_isPathPos (isMoleculeIn_bdry wr false) (krullDim_bdry wr false)
      (hx false hY)
    obtain ⟨z, hz⟩ := exists_isPathPos (isMoleculeIn_bdry wr true) (krullDim_bdry wr true)
      (hx true hZ)
    refine Or.inr ⟨y, z, hy, hz, ?_, ?_⟩
    · exact hY.unique (isMoleculeIn_bdry w false) (krullDim_bdry w false)
        (isPathPos_right_numEdges (hb false) (isMoleculeIn_bdry wl false)
          (isMoleculeIn_bdry wr false) (krullDim_bdry w false) hy)
    · exact hZ.unique (isMoleculeIn_bdry w true) (krullDim_bdry w true)
        (isPathPos_right_numEdges (hb true) (isMoleculeIn_bdry wl true)
          (isMoleculeIn_bdry wr true) (krullDim_bdry w true) hz)
  · have hx (β : Bool) {P : ℕ} (hP : IsPathPos ∂₁[w, β] P x) : x ∈ ∂₁[wl, β] :=
      (LowerSet.mem_sup_iff.1 (hmem β hP)).resolve_right fun h' => hr (boundary_le _ _ _ h')
    obtain ⟨y, hy⟩ := exists_isPathPos (isMoleculeIn_bdry wl false) (krullDim_bdry wl false)
      (hx false hY)
    obtain ⟨z, hz⟩ := exists_isPathPos (isMoleculeIn_bdry wl true) (krullDim_bdry wl true)
      (hx true hZ)
    have e₁ := hY.unique (isMoleculeIn_bdry w false) (krullDim_bdry w false)
      ((hb false).isPathPos_left (isMoleculeIn_bdry wl false) (isMoleculeIn_bdry wr false)
        (krullDim_bdry w false) hy)
    have e₂ := hZ.unique (isMoleculeIn_bdry w true) (krullDim_bdry w true)
      ((hb true).isPathPos_left (isMoleculeIn_bdry wl true) (isMoleculeIn_bdry wr true)
        (krullDim_bdry w true) hz)
    subst e₁ e₂
    exact Or.inl ⟨hy, hz⟩

namespace PathInterp

variable (I : S.PathInterp X)

omit [DecidableEq S.Pt] in
private theorem isAtom_ofEdge : (e : Edge S.Pt S.Ed) → IsAtom (I.ofEdge e).shape.ogp
  | .gen e => (I.edge e).1.isAtom
  | .unit _ => isAtom_unitShape_of_dimension_eq_zero _ dimension_atomPoint

omit [DecidableEq S.Pt] in
private theorem numEdges_image_ofEdge (e : Edge S.Pt S.Ed) (w : Within (I.ofEdge e) m) :
    numEdges w.image = 1 := by
  have hd : krullDim (⊤ : LowerSet (I.ofEdge e).shape.ogp) = 1 := by
    rw [LowerSet.krullDim_top, (I.ofEdge e).shape.krullDim_eq_dimension, ← dim_def,
      I.dim_ofEdge e]
    rfl
  rw [Within.image, numEdges_map w.emb (I.ofEdge e).shape.isMolecule hd]
  exact numEdges_of_isAtomIn (I.isAtom_ofEdge e) hd

private theorem numEdges_image_pathCons :
    ∀ {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} {y : S.Pt},
      S.walk (S.tgt e) p = some y → ∀ {a : PastingDiagram X} (w : Within a m),
      a = I.pathCons e p → numEdges w.image = p.length + 1
  | e, [], _, _, a, w, ha => by
    subst ha
    exact I.numEdges_image_ofEdge e w
  | e, f :: p, y, h, a, w, ha => by
    obtain ⟨hf, h'⟩ := S.walk_cons_eq_some.1 h
    have hx := I.spans_of_hasRoundType (I.hasRoundType_ofEdge e)
    have hy := I.spans_pathCons h'
    rw [hf] at hy
    have hc := hx.pastable hy
    have heq : I.pathCons e (f :: p) = (I.ofEdge e).paste (I.pathCons f p) 0 hc := pasteOr_of hc
    rw [heq] at ha
    subst ha
    have hp := isPastingIn_trans 0 hc w
    have hd : krullDim w.image ≤ 1 := by
      rw [w.krullDim_image, dim_paste, I.dim_ofEdge, I.dim_pathCons h']
      rfl
    rw [numEdges_eq_add hp (Within.isMoleculeIn_image _) (Within.isMoleculeIn_image _) hd,
      I.numEdges_image_ofEdge, numEdges_image_pathCons h' _ rfl, List.length_cons]
    omega

private theorem numEdges_image_path {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p)
    (w : Within (I.path p hp.ne_nil) m) : numEdges w.image = p.length := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp.ne_nil
  obtain ⟨x, y, h⟩ := S.exists_pathEnds_of_isPath hp
  obtain ⟨-, h'⟩ := S.pathEnds_cons_eq_some.1 h
  exact I.numEdges_image_pathCons h' w rfl

private theorem exists_within_bdry {a : PastingDiagram X} {s t : List (Edge S.Pt S.Ed)}
    (hs : S.IsPath s) (ht : S.IsPath t) (h : HasRoundType a (I.pathRound s hs) (I.pathRound t ht))
    (w : Within a m) (α : Bool) : ∃ (hst : S.IsPath (cond α t s))
      (wp : Within (I.path (cond α t s) hst.ne_nil) m), wp.image = ∂₁[w, α] := by
  have e := h.equiv_boundary_cond (k := 1) (I.dim_path hs) α
  have hst : S.IsPath (cond α t s) := by cases α <;> assumption
  have e' : (a.boundary 1 α).Equiv (I.path (cond α t s) hst.ne_nil) := by
    cases α <;> exact e
  refine ⟨hst, (Within.ofEquiv e'.symm).trans ((Within.boundary a 1 α).trans w), ?_⟩
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary_trans w 1 α

private theorem numEdges_bdry {a : PastingDiagram X} {s t : List (Edge S.Pt S.Ed)}
    (hs : S.IsPath s) (ht : S.IsPath t) (h : HasRoundType a (I.pathRound s hs) (I.pathRound t ht))
    (w : Within a m) (α : Bool) : numEdges ∂₁[w, α] = (cond α t s).length := by
  obtain ⟨hst, wp, hwp⟩ := I.exists_within_bdry hs ht h w α
  rw [← hwp]
  exact I.numEdges_image_path hst wp

end PathInterp

namespace Interp

variable (I : S.Interp X)

private theorem tracks_of_isRound {a : PastingDiagram X} {s t : List (Edge S.Pt S.Ed)}
    (hs : S.IsPath s) (ht : S.IsPath t) (h : HasRoundType a (I.pathRound s hs) (I.pathRound t ht))
    (hr : a.IsRound) :
    Tracks a m fun y z => (y = 0 ∧ z = 0) ∨ (y = 2 * s.length ∧ z = 2 * t.length) := by
  intro w x y z hy hz
  have hR := w.round_image_iff.2 hr
  have hda : a.dim = 2 := h.dim_eq.trans (congrArg (· + 1) (I.dim_path hs))
  have hU := w.isMoleculeIn_image
  have hinf : OGP.boundary _ w.image 1 false ⊓ OGP.boundary _ w.image 1 true =
      boundaryFull _ w.image 0 :=
    hR.inf_boundary_succ 0 (by rw [w.krullDim_image, hda]; exact_mod_cast (by omega : 1 < 2))
  have hx : x ∈ boundaryFull _ w.image 0 := hinf ▸ LowerSet.mem_inf_iff.2
    ⟨hy.mem (isMoleculeIn_bdry w false) (krullDim_bdry w false),
      hz.mem (isMoleculeIn_bdry w true) (krullDim_bdry w true)⟩
  have hpos (β : Bool) (hβ : x ∈ OGP.boundary _ w.image 0 β) (α : Bool) :
      IsPathPos ∂₁[w, α] (cond β (2 * numEdges ∂₁[w, α]) 0) x := by
    obtain ⟨v, hv, hbv⟩ := exists_boundary_zero_eq_Iic hU β
    rw [hbv] at hβ
    obtain rfl : x = v := le_antisymm hβ (hv hβ)
    refine (isPathPos_cond_iff_numEdges (isMoleculeIn_bdry w α) (krullDim_bdry w α) β).2 ?_
    rw [hU.isGlobular 0 1 Nat.zero_lt_one β α, hbv]
  have hNs := I.numEdges_bdry hs ht h w false
  have hNt := I.numEdges_bdry hs ht h w true
  rcases LowerSet.mem_sup_iff.1 hx with hβ | hβ
  · left
    exact ⟨hy.unique (isMoleculeIn_bdry w false) (krullDim_bdry w false) (hpos false hβ false),
      hz.unique (isMoleculeIn_bdry w true) (krullDim_bdry w true) (hpos false hβ true)⟩
  · right
    have e₁ := hy.unique (isMoleculeIn_bdry w false) (krullDim_bdry w false) (hpos true hβ false)
    have e₂ := hz.unique (isMoleculeIn_bdry w true) (krullDim_bdry w true) (hpos true hβ true)
    simp only [cond_true] at e₁ e₂ hNs hNt
    rw [e₁, e₂, hNs, hNt]
    exact ⟨rfl, rfl⟩

private theorem tracks_whisker_true {x : PastingDiagram X} {a b c : S.Pt} (hx : I.Spans x a b)
    {B : List (Edge S.Pt S.Ed)} (hB : S.walk b B = some c) {k k' : ℕ}
    (hN : ∀ w : Within x m, numEdges ∂₁[w, false] = k ∧ numEdges ∂₁[w, true] = k')
    {R : ℕ → ℕ → Prop} (hT : Tracks x m R) :
    Tracks (I.whisker true B x) m fun y z => R y z ∨ (2 * k ≤ y ∧ z + 2 * k = y + 2 * k') := by
  obtain _ | ⟨f, B⟩ := B
  · exact hT.mono fun y z h => Or.inl h
  have hp := hx.pastable_whisker true (c := c) hB
  obtain ⟨-, hB'⟩ := S.walk_cons_eq_some.1 hB
  have hdim : (I.pathCons f B).dim ≤ 1 := (I.dim_pathCons hB').le
  rw [I.whisker_cons_of hp]
  intro w ξ Y Z hY hZ
  rcases paste_zero_cases hp w hY hZ with ⟨h₁, h₂⟩ | ⟨y, z, h₁, h₂, rfl, rfl⟩
  · exact Or.inl (hT _ ξ Y Z h₁ h₂)
  · right
    obtain ⟨hk, hk'⟩ := hN ((Within.pasteInl _ _ 0 hp).trans w)
    rw [bdry_eq_image _ hdim] at h₁ h₂
    have e := h₁.unique (Within.isMoleculeIn_image _)
      (by rw [Within.krullDim_image]; exact_mod_cast hdim) h₂
    omega

private theorem tracks_whisker_false {x : PastingDiagram X} {a b c : S.Pt} (hx : I.Spans x a b)
    {A : List (Edge S.Pt S.Ed)} (hA : S.walk c A = some a) {R : ℕ → ℕ → Prop}
    (hT : Tracks x m R) :
    Tracks (I.whisker false A x) m fun y z => (y ≤ 2 * A.length ∧ z = y) ∨
      ∃ y' z', R y' z' ∧ y = 2 * A.length + y' ∧ z = 2 * A.length + z' := by
  obtain _ | ⟨f, A⟩ := A
  · exact hT.mono fun y z h => Or.inr ⟨y, z, h, by simp, by simp⟩
  have hp := hx.pastable_whisker false (c := c) hA
  obtain ⟨-, hA'⟩ := S.walk_cons_eq_some.1 hA
  have hdim : (I.pathCons f A).dim ≤ 1 := (I.dim_pathCons hA').le
  rw [I.whisker_cons_of hp]
  intro w ξ Y Z hY hZ
  have hN := I.numEdges_image_pathCons hA' ((Within.pasteInl _ _ 0 hp).trans w) rfl
  have hdA : krullDim ((Within.pasteInl _ _ 0 hp).trans w).image ≤ 1 := by
    rw [Within.krullDim_image]
    exact_mod_cast hdim
  rcases paste_zero_cases hp w hY hZ with ⟨h₁, h₂⟩ | ⟨y, z, h₁, h₂, rfl, rfl⟩
  · left
    rw [bdry_eq_image _ hdim] at h₁ h₂
    have e := h₁.unique (Within.isMoleculeIn_image _) hdA h₂
    have hle := le_numEdges h₁
    rw [hN] at hle
    simp only [List.length_cons]
    omega
  · right
    refine ⟨y, z, hT _ ξ y z h₁ h₂, ?_, ?_⟩ <;>
      rw [bdry_eq_image _ hdim, hN, List.length_cons]

variable [DecidableEq S.Ed]

private theorem tracks_layer (hS : S.WellFormed) {e : Edge S.Pt S.Ed}
    {q p' : List (Edge S.Pt S.Ed)} {l : Cell S.Pt S.Ed S.Ce × ℕ} {x z : S.Pt}
    (hp : S.pathEnds (e :: q) = some (x, z)) (h : S.applyLayer (e :: q) l.1 l.2 = some p') :
    Tracks (I.layer e q l) m fun y y' => (y ≤ 2 * l.2 ∧ y' = y) ∨
      (2 * l.2 < y ∧ 2 * (l.2 + (S.cellType l.1).1.length) ≤ y ∧
        y' + 2 * (S.cellType l.1).1.length = y + 2 * (S.cellType l.1).2.length) := by
  obtain ⟨hne, hseg, -⟩ := S.eq_of_applyLayer_eq_some h
  have hp' := hp
  rw [← hseg] at hp'
  obtain ⟨-, hw⟩ := S.pathEnds_eq_some_iff.1 hp'
  rw [S.walk_append, S.walk_append] at hw
  obtain ⟨b, hb, hBz⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨a, hA, hsab⟩ := Option.bind_eq_some_iff.1 hb
  have hs : S.pathEnds (S.cellType l.1).1 = some (a, b) := S.pathEnds_eq_some_iff.2 ⟨hne, hsab⟩
  have ht : S.pathEnds (S.cellType l.1).2 = some (a, b) :=
    (S.pathEnds_cellType_snd hS l.1).trans hs
  have hc := I.hasRoundType_cellDiagram hS (I.pathCons e q).unit (S.isPath_of_pathEnds hs)
  have hcr := I.isRound_cellDiagram (I.pathCons e q).unit (S.isPath_of_pathEnds hs)
  have hxs : I.Spans (I.cellDiagram (I.pathCons e q).unit l.1) a b :=
    (I.spans_of_hasRoundType (I.hasRoundType_path hne hs)).of_hasRoundType hc
  have T := I.tracks_whisker_false (m := m) (hxs.whisker true hBz) hA
    (I.tracks_whisker_true hxs hBz (k := (S.cellType l.1).1.length)
      (k' := (S.cellType l.1).2.length)
      (fun w => ⟨I.numEdges_bdry _ _ hc w false, I.numEdges_bdry _ _ hc w true⟩)
      (I.tracks_of_isRound _ _ hc hcr))
  have hlen := congrArg List.length hseg
  simp only [List.length_append, List.length_take, List.length_drop, List.length_cons] at hlen
  have hk := List.length_pos_of_ne_nil hne
  have ho : ((e :: q).take l.2).length = l.2 := by
    rw [List.length_take, List.length_cons]
    omega
  refine T.mono fun y y' hr => ?_
  rw [ho] at hr
  rcases hr with hr | ⟨y₀, z₀, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨h₁, h₂⟩, rfl, rfl⟩
  · exact Or.inl hr
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega, by omega⟩

omit [DecidableEq S.Pt] [DecidableEq S.Ed] in
private theorem track_cons_of {l : Cell S.Pt S.Ed S.Ce × ℕ} {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    {y y' : ℕ} (h : (y ≤ 2 * l.2 ∧ y' = y) ∨ (2 * l.2 < y ∧
      2 * (l.2 + (S.cellType l.1).1.length) ≤ y ∧
        y' + 2 * (S.cellType l.1).1.length = y + 2 * (S.cellType l.1).2.length)) :
    S.track (l :: ls) y = S.track ls y' := by
  obtain ⟨c, o⟩ := l
  dsimp only at h
  rcases h with ⟨h₁, rfl⟩ | ⟨h₁, h₂, h₃⟩
  · rw [track, if_pos h₁]
  · rw [track, if_neg (by omega), if_pos h₂]
    congr 1
    omega

private theorem tracks_layers (hS : S.WellFormed) {e : Edge S.Pt S.Ed}
    {q r : List (Edge S.Pt S.Ed)} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z)) :
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} → S.targetFrom (e :: q) ls = some r →
      Tracks (I.layers e q ls) m fun y y' => S.track ls y = some y'
  | [], _ => by
    have hpath := S.isPath_of_pathEnds hp
    refine (I.tracks_of_isRound hpath hpath (hasRoundType_unit (I.pathRound _ hpath))
      (isRound_unit (I.isRound_path hpath))).mono ?_
    rintro y y' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  | [l], h => by
    obtain ⟨p', h₁, -⟩ := Option.bind_eq_some_iff.1 h
    exact (I.tracks_layer hS hp h₁).mono fun y y' hr => (track_cons_of hr).trans rfl
  | l :: l' :: ls, h => by
    obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hp' := S.pathEnds_applyLayer hS h₁ hp
    obtain _ | ⟨e', q'⟩ := p'
    · simp only [pathEnds, reduceCtorEq] at hp'
    have ih := tracks_layers hS hp' h₂
    obtain ⟨hc, he⟩ := I.layers_cons_cons hS hp h₁ h₂ (I.hasRoundType_layers hS hp' h₂)
    rw [he]
    intro w ξ Y Z hY hZ
    have hp1 := isPastingIn_trans 1 hc w
    have hξ := hp1.inf_boundary_le (LowerSet.mem_inf_iff.2
      ⟨hY.mem (isMoleculeIn_bdry w false) (krullDim_bdry w false),
        hZ.mem (isMoleculeIn_bdry w true) (krullDim_bdry w true)⟩)
    obtain ⟨⟨-, hl⟩, -⟩ := LowerSet.mem_inf_iff.1 hξ
    obtain ⟨Z', hZ'⟩ := exists_isPathPos (isMoleculeIn_bdry _ true) (krullDim_bdry _ true) hl
    rw [hp1.boundary_input] at hY
    rw [hp1.boundary_output] at hZ
    have hmid := hp1.inf_eq_output.symm.trans hp1.inf_eq_input
    have h₃ := I.tracks_layer hS hp h₁ _ ξ Y Z' hY hZ'
    rw [hmid] at hZ'
    rw [track_cons_of h₃]
    exact ih _ ξ Z' Z hZ' hZ

theorem isRound_diagram_of_fullRound (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ [])
    (h : S.FullRound d) : (I.diagram d hsrc).IsRound := by
  rcases h with hl | h
  · exact I.isRound_diagram_of_layers_eq_nil (S.isPath_source_of_target hd) hl
  obtain ⟨_ | ⟨e, p⟩, ls⟩ := d
  · exact absurd rfl hsrc
  have hpath := S.isPath_source_of_target hd
  have hqpath := S.isPath_target hS hd
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath hpath
  have hd' := hd
  rw [target, if_pos hpath] at hd'
  have hty := I.hasRoundType_layers hS hp hd'
  have hT := I.tracks_layers hS hp hd' (m := I.layers e p ls)
  rw [diagram_mk, ← (Within.refl (I.layers e p ls)).round_image_iff]
  set w := Within.refl (I.layers e p ls)
  have hU := w.isMoleculeIn_image
  have hda : (I.layers e p ls).dim = 2 := hty.dim_eq.trans (congrArg (· + 1) (I.dim_path hpath))
  have hdU : krullDim w.image = 2 := by rw [w.krullDim_image, hda]; rfl
  have hN := I.numEdges_bdry hpath hqpath hty w false
  simp only [cond_false] at hN
  obtain ⟨hst, wp, hwp⟩ := I.exists_within_bdry hpath hqpath hty w false
  have hRp : OGP.IsRound _ ∂₁[w, false] := hwp ▸ wp.round_image_iff.2 (I.isRound_path hst)
  refine ⟨hU.isGlobular, fun _ => ?_, fun n hn => ?_⟩
  · rw [← hU.isGlobular 0 1 Nat.zero_lt_one false false,
      ← hU.isGlobular 0 1 Nat.zero_lt_one true false]
    refine hRp.inf_boundary_zero ?_
    rw [← hwp, wp.krullDim_image, I.dim_path hst]
    exact_mod_cast Nat.one_pos
  obtain rfl : n = 0 := by
    rw [hdU] at hn
    have : n + 1 < 2 := by exact_mod_cast hn
    omega
  refine le_antisymm ?_ (sup_le
    (le_inf (hU.isGlobular.boundary_le_boundary Nat.zero_lt_one _ _)
      (hU.isGlobular.boundary_le_boundary Nat.zero_lt_one _ _))
    (le_inf (hU.isGlobular.boundary_le_boundary Nat.zero_lt_one _ _)
      (hU.isGlobular.boundary_le_boundary Nat.zero_lt_one _ _)))
  intro ξ hξ
  obtain ⟨h₁, h₂⟩ := LowerSet.mem_inf_iff.1 hξ
  obtain ⟨Y, hY⟩ := exists_isPathPos (isMoleculeIn_bdry w false) (krullDim_bdry w false) h₁
  obtain ⟨Z, hZ⟩ := exists_isPathPos (isMoleculeIn_bdry w true) (krullDim_bdry w true) h₂
  have htr := hT w ξ Y Z hY hZ
  dsimp only at htr h
  have hle := le_numEdges hY
  have hend (β : Bool) (hβ : Y = cond β (2 * numEdges ∂₁[w, false]) 0) :
      ξ ∈ boundaryFull _ w.image 0 := by
    rw [hβ] at hY
    have hb :=
      (isPathPos_cond_iff_numEdges (isMoleculeIn_bdry w false) (krullDim_bdry w false) β).1 hY
    rw [hU.isGlobular 0 1 Nat.zero_lt_one β false] at hb
    have hmem : ξ ∈ OGP.boundary _ w.image 0 β := hb ▸ LowerSet.mem_Iic_iff.2 le_rfl
    cases β
    exacts [LowerSet.mem_sup_iff.2 (Or.inl hmem), LowerSet.mem_sup_iff.2 (Or.inr hmem)]
  rcases Nat.eq_zero_or_pos Y with hY0 | hY0
  · exact hend false hY0
  rcases hle.lt_or_eq with hlt | heq
  · rw [hN] at hlt
    rw [h Y hlt hY0] at htr
    exact absurd htr (by simp)
  · exact hend true heq

end Interp

end Atoms.Diagrammatic.Layered.Signature
