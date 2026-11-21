import Atoms.Diagrammatic.Rewriting.Path
import Atoms.Diagrammatic.Context.Pushforward

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered.Signature

variable {S : Signature.{v}} {X Y : DiagSet.{u}}

namespace PathInterp

variable (I : S.PathInterp X)

noncomputable def whisker (α : Bool) : List (Edge S.Pt S.Ed) → PastingDiagram X →
    PastingDiagram X
  | [], x => x
  | f :: w, x => (cond α x (I.pathCons f w)).pasteOr (cond α (I.pathCons f w) x) 0

@[simp] theorem whisker_nil (α : Bool) (x : PastingDiagram X) : I.whisker α [] x = x := rfl

theorem whisker_cons_of {α : Bool} {f : Edge S.Pt S.Ed} {w : List (Edge S.Pt S.Ed)}
    {x : PastingDiagram X}
    (h : (cond α x (I.pathCons f w)).Pastable (cond α (I.pathCons f w) x) 0) :
    I.whisker α (f :: w) x = (cond α x (I.pathCons f w)).paste (cond α (I.pathCons f w) x) 0 h :=
  pasteOr_of h

def Spans (x : PastingDiagram X) (a b : S.Pt) : Prop :=
  0 < x.dim ∧ ∀ β, (x.boundary 0 β).Equiv (PastingDiagram.ofCell (I.point (cond β b a)))

theorem Spans.of_equiv {I : S.PathInterp X} {x x' : PastingDiagram X} {a b : S.Pt}
    (hx : I.Spans x a b) (h : x.Equiv x') : I.Spans x' a b :=
  ⟨dim_eq_of_equiv h ▸ hx.1, fun β => (h.boundary 0 β).symm.trans (hx.2 β)⟩

theorem spans_of_hasRoundType {x : PastingDiagram X} {a b : S.Pt}
    (h : HasRoundType x (cellRound (I.point a)) (cellRound (I.point b))) : I.Spans x a b :=
  ⟨by rw [h.dim_eq]; exact Nat.succ_pos _, fun β => by
    have e := h.equiv_boundary_cond dimension_atomPoint β
    cases β <;> exact e⟩

theorem Spans.of_hasRoundType {I : S.PathInterp X} {x : PastingDiagram X}
    {v w : RoundPastingDiagram X} {a b : S.Pt} (hv : I.Spans v.toPastingDiagram a b)
    (h : HasRoundType x v w) : I.Spans x a b :=
  ⟨by rw [h.dim_eq]; exact Nat.succ_pos _, fun β =>
    (equiv_boundary_boundary x hv.1 false β).symm.trans ((h.source.boundary 0 β).trans (hv.2 β))⟩

theorem Spans.pastable {I : S.PathInterp X} {x y : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) (hy : I.Spans y b c) : x.Pastable y 0 :=
  ⟨(hx.2 true).trans (hy.2 false).symm, lt_min hx.1 hy.1⟩

theorem Spans.paste {I : S.PathInterp X} {x y : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) (hy : I.Spans y b c) (h : x.Pastable y 0) :
    I.Spans (x.paste y 0 h) a c :=
  ⟨by rw [dim_paste]; exact lt_max_of_lt_left hx.1, fun β => (equiv_boundary_paste h β).trans
    (by cases β; exacts [hx.2 false, hy.2 true])⟩

variable [DecidableEq S.Pt]

theorem spans_pathCons {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} {b : S.Pt}
    (h : S.walk (S.tgt e) p = some b) : I.Spans (I.pathCons e p) (S.src e) b :=
  I.spans_of_hasRoundType (I.hasRoundType_path (List.cons_ne_nil e p)
    (S.pathEnds_cons_eq_some.2 ⟨rfl, h⟩))

theorem Spans.pastable_whisker {I : S.PathInterp X} (α : Bool) {x : PastingDiagram X}
    {a b c : S.Pt} (hx : I.Spans x a b) {f : Edge S.Pt S.Ed} {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) (f :: w) = some (cond α c a)) :
    (cond α x (I.pathCons f w)).Pastable (cond α (I.pathCons f w) x) 0 := by
  obtain ⟨hf, hw⟩ := S.walk_cons_eq_some.1 hw
  have hp := I.spans_pathCons hw
  rw [hf] at hp
  cases α
  exacts [hp.pastable hx, hx.pastable hp]

theorem Spans.whisker {I : S.PathInterp X} (α : Bool) {x : PastingDiagram X}
    {a b c : S.Pt} (hx : I.Spans x a b) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) :
    I.Spans (I.whisker α w x) (cond α a c) (cond α c b) := by
  obtain _ | ⟨f, w⟩ := w
  · have h : cond α b c = cond α c a := Option.some.inj hw
    cases α
    · obtain rfl : c = a := h
      exact hx
    · obtain rfl : b = c := h
      exact hx
  rw [I.whisker_cons_of (hx.pastable_whisker α hw)]
  obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
  have hp := I.spans_pathCons hw'
  rw [hf] at hp
  cases α
  exacts [hp.paste hx _, hx.paste hp _]

theorem whisker_equiv (α : Bool) {x x' : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) (h : x.Equiv x') {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) :
    (I.whisker α w x).Equiv (I.whisker α w x') := by
  obtain _ | ⟨f, w⟩ := w
  · exact h
  have hp := hx.pastable_whisker α hw
  have hp' := (hx.of_equiv h).pastable_whisker α hw
  rw [whisker_cons_of _ hp, whisker_cons_of _ hp']
  exact Equiv.paste (.cond h α (.refl _)) (.cond (.refl _) α h) hp hp'

theorem whisker_append (α : Bool) {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) {w₁ w₂ : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) (cond α (w₁ ++ w₂) (w₂ ++ w₁)) = some (cond α c a)) :
    (I.whisker α (cond α (w₁ ++ w₂) (w₂ ++ w₁)) x).Equiv (I.whisker α w₂ (I.whisker α w₁ x)) := by
  obtain _ | ⟨f, w₁⟩ := w₁
  · cases α <;> simp only [List.nil_append, List.append_nil, cond_true, cond_false, whisker_nil]
      <;> exact .refl _
  obtain _ | ⟨g, w₂⟩ := w₂
  · cases α <;> simp only [List.nil_append, List.append_nil, cond_true, cond_false, whisker_nil]
      <;> exact .refl _
  cases α
  · simp only [cond_false] at hw ⊢
    rw [List.cons_append] at hw ⊢
    obtain ⟨-, hw'⟩ := S.walk_cons_eq_some.1 hw
    obtain ⟨m, hm, hma⟩ := S.walk_append_eq_some hw'
    obtain ⟨hfm, hma'⟩ := S.walk_cons_eq_some.1 hma
    have hP₂ := I.spans_pathCons hm
    have hP₁ := I.spans_pathCons hma'
    rw [hfm] at hP₁
    have h₀ := hP₂.pastable hP₁
    have h₁ := hP₁.pastable hx
    have h₂ := hP₂.pastable (hP₁.paste hx h₁)
    obtain ⟨h₀', e⟩ := I.equiv_pathCons_append hw'
    have h₅ : (I.pathCons g (w₂ ++ f :: w₁)).Pastable x 0 :=
      (Pastable.paste_left h₀ h₁).of_equiv e.symm (.refl _)
    rw [I.whisker_cons_of (α := false) (x := x) h₅, I.whisker_cons_of (α := false) (x := x) h₁]
    simp only [cond_false]
    rw [I.whisker_cons_of (α := false) (x := (I.pathCons f w₁).paste x 0 h₁) h₂]
    simp only [cond_false]
    obtain ⟨h₃, h₄, e'⟩ := equiv_paste_assoc h₀ (Pastable.paste_left h₀ h₁)
    exact (Equiv.paste e (.refl _) h₅ _).trans e'
  · simp only [cond_true] at hw ⊢
    rw [List.cons_append] at hw ⊢
    obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
    obtain ⟨m, hm, hmc⟩ := S.walk_append_eq_some hw'
    obtain ⟨hgm, hmc'⟩ := S.walk_cons_eq_some.1 hmc
    have hP₁ := I.spans_pathCons hm
    rw [hf] at hP₁
    have hP₂ := I.spans_pathCons hmc'
    rw [hgm] at hP₂
    have h₁ := hx.pastable hP₁
    have h₂ := (hx.paste hP₁ h₁).pastable hP₂
    obtain ⟨h₀', e⟩ := I.equiv_pathCons_append hw'
    obtain ⟨h₃, h₄, e'⟩ := equiv_paste_assoc h₁ h₂
    have h₅ : x.Pastable (I.pathCons f (w₁ ++ g :: w₂)) 0 := h₄.of_equiv (.refl _) e.symm
    rw [I.whisker_cons_of (α := true) (x := x) h₅, I.whisker_cons_of (α := true) (x := x) h₁]
    simp only [cond_true]
    rw [I.whisker_cons_of (α := true) (x := x.paste (I.pathCons f w₁) 0 h₁) h₂]
    simp only [cond_true]
    exact (Equiv.paste (.refl _) e h₅ h₄).trans e'.symm

theorem whisker_comm {x : PastingDiagram X} {a b c d : S.Pt} (hx : I.Spans x a b)
    {l r : List (Edge S.Pt S.Ed)} (hl : S.walk c l = some a) (hr : S.walk b r = some d) :
    (I.whisker false l (I.whisker true r x)).Equiv (I.whisker true r (I.whisker false l x)) := by
  obtain _ | ⟨f, l⟩ := l
  · exact .refl _
  obtain _ | ⟨g, r⟩ := r
  · exact .refl _
  obtain ⟨-, hl'⟩ := S.walk_cons_eq_some.1 hl
  obtain ⟨hg, hr'⟩ := S.walk_cons_eq_some.1 hr
  have hL := I.spans_pathCons hl'
  have hR := I.spans_pathCons hr'
  rw [hg] at hR
  have h₁ := hx.pastable hR
  have h₂ := hL.pastable (hx.paste hR h₁)
  have h₃ := hL.pastable hx
  have h₄ := (hL.paste hx h₃).pastable hR
  rw [I.whisker_cons_of (α := true) (x := x) h₁, I.whisker_cons_of (α := false) (x := x) h₃]
  simp only [cond_true, cond_false]
  rw [I.whisker_cons_of (α := false) (x := x.paste (I.pathCons g r) 0 h₁) h₂,
    I.whisker_cons_of (α := true) (x := (I.pathCons f l).paste x 0 h₃) h₄]
  simp only [cond_true, cond_false]
  obtain ⟨h₅, h₆, e⟩ := equiv_paste_assoc h₃ h₄
  exact (Equiv.paste (.refl _) (.refl _) h₂ h₆).trans e.symm

theorem exists_whisker_paste (α : Bool) {y z : PastingDiagram X} {a b c : S.Pt}
    (hy : I.Spans y a b) (h : y.Pastable z 1) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) :
    ∃ h', (I.whisker α w (y.paste z 1 h)).Equiv
      ((I.whisker α w y).paste (I.whisker α w z) 1 h') := by
  obtain _ | ⟨f, w⟩ := w
  · exact ⟨h, .refl _⟩
  have hyz : I.Spans (y.paste z 1 h) a b :=
    ⟨by rw [dim_paste]; exact lt_max_of_lt_left hy.1, fun β =>
      (equiv_boundary_paste_of_lt h false Nat.one_pos β).symm.trans (hy.2 β)⟩
  have hp := hyz.pastable_whisker α hw
  obtain ⟨hy', hz', h', e⟩ := exists_paste_cond_paste α h hp
    (I.dim_pathCons (S.walk_cons_eq_some.1 hw).2) Nat.one_pos
  rw [whisker_cons_of _ hp, whisker_cons_of _ hy', whisker_cons_of _ hz']
  exact ⟨h', e⟩

theorem whisker_boundary (α : Bool) {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) {n : ℕ} (hn : 0 < n) (hd : n ≤ x.dim) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) (β : Bool) :
    ((I.whisker α w x).boundary n β).Equiv (I.whisker α w (x.boundary n β)) := by
  obtain _ | ⟨f, w⟩ := w
  · exact .refl _
  have hp := hx.pastable_whisker α hw
  obtain ⟨hp', e⟩ := exists_equiv_boundary_paste_cond α hp
    (I.dim_pathCons (S.walk_cons_eq_some.1 hw).2) hn hd β
  rw [whisker_cons_of _ hp, whisker_cons_of _ hp']
  exact e

theorem whisker_path (α : Bool) {q : List (Edge S.Pt S.Ed)} {a b c : S.Pt} (hq : q ≠ [])
    (hqe : S.pathEnds q = some (a, b)) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) (hqw : cond α (q ++ w) (w ++ q) ≠ []) :
    (I.whisker α w (I.path q hq)).Equiv (I.path (cond α (q ++ w) (w ++ q)) hqw) := by
  obtain _ | ⟨f, w⟩ := w
  · cases α <;> exact PastingDiagram.equiv_of_eq (by simp)
  have hx := I.spans_of_hasRoundType (I.hasRoundType_path hq hqe)
  have hp := hx.pastable_whisker α hw
  rw [whisker_cons_of _ hp]
  obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
  have hfw := S.pathEnds_cons_eq_some.2 ⟨hf, hw'⟩
  cases α
  · obtain ⟨h, e⟩ := I.equiv_path_append (List.cons_ne_nil f w) hq
      (S.isPath_of_pathEnds (S.pathEnds_append hfw hqe))
    exact e.symm
  · obtain ⟨h, e⟩ := I.equiv_path_append hq (List.cons_ne_nil f w)
      (S.isPath_of_pathEnds (S.pathEnds_append hqe hfw))
    exact e.symm

theorem dim_whisker (α : Bool) {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) (hd : 1 ≤ x.dim) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) : (I.whisker α w x).dim = x.dim := by
  obtain _ | ⟨f, w⟩ := w
  · rfl
  rw [whisker_cons_of _ (hx.pastable_whisker α hw), dim_paste_cond,
    I.dim_pathCons (S.walk_cons_eq_some.1 hw).2]
  exact max_eq_left hd

private theorem whisker_mapTo (α : Bool) {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c a)) (f : X ⟶ Y)
    {y : PastingDiagram Y} (h : y.Equiv (x.mapTo f)) :
    ((I.mapTo f).whisker α w y).Equiv ((I.whisker α w x).mapTo f) := by
  obtain _ | ⟨g, w⟩ := w
  · exact h
  have hp := hx.pastable_whisker α hw
  have eP := I.pathCons_mapTo f (S.walk_cons_eq_some.1 hw).2
  have hp' : (cond α y ((I.mapTo f).pathCons g w)).Pastable
      (cond α ((I.mapTo f).pathCons g w) y) 0 := by
    cases α
    · exact (hp.mapTo f).of_equiv eP.symm h.symm
    · exact (hp.mapTo f).of_equiv h.symm eP.symm
  rw [whisker_cons_of _ hp, whisker_cons_of _ hp']
  cases α
  · exact (Equiv.paste eP h hp' (hp.mapTo f)).trans (paste_mapTo _ _ 0 hp f _).symm
  · exact (Equiv.paste h eP hp' (hp.mapTo f)).trans (paste_mapTo _ _ 0 hp f _).symm

theorem hasRoundType_whisker (α : Bool) {s t w : List (Edge S.Pt S.Ed)} {a b c : S.Pt}
    (hs : S.pathEnds s = some (a, b)) (ht : S.pathEnds t = some (a, b)) {x : PastingDiagram X}
    (hx : HasRoundType x (I.pathRound s (S.isPath_of_pathEnds hs))
      (I.pathRound t (S.isPath_of_pathEnds ht)))
    (hw : S.walk (cond α b c) w = some (cond α c a)) :
    HasRoundType (I.whisker α w x)
      (I.pathRound _ (S.isPath_of_pathEnds (S.pathEnds_whisker α hs hw)))
      (I.pathRound _ (S.isPath_of_pathEnds (S.pathEnds_whisker α ht hw))) := by
  have hsp := I.spans_of_hasRoundType (I.hasRoundType_path (S.isPath_of_pathEnds hs).ne_nil hs)
  have hxs := hsp.of_hasRoundType hx
  have hd1 : (I.pathRound s (S.isPath_of_pathEnds hs)).dim = 1 :=
    I.dim_path (S.isPath_of_pathEnds hs)
  have hdx : x.dim = 1 + 1 := hx.dim_eq.trans (congrArg (· + 1) hd1)
  refine .of_equiv_boundary (I.dim_path (S.isPath_of_pathEnds (S.pathEnds_whisker α hs hw)))
    (I.dim_path (S.isPath_of_pathEnds (S.pathEnds_whisker α ht hw)))
    ((I.dim_whisker α hxs (by omega) hw).trans hdx) fun β => ?_
  have hb := hx.equiv_boundary_cond hd1 β
  have key : ∀ {q : List (Edge S.Pt S.Ed)} (hq : S.pathEnds q = some (a, b)),
      (x.boundary 1 β).Equiv (I.path q (S.isPath_of_pathEnds hq).ne_nil) →
      ((I.whisker α w x).boundary 1 β).Equiv
        (I.path (cond α (q ++ w) (w ++ q))
          (S.isPath_of_pathEnds (S.pathEnds_whisker α hq hw)).ne_nil) := fun hq e =>
    (I.whisker_boundary α hxs Nat.one_pos (by omega) hw β).trans ((I.whisker_equiv α
      ((I.spans_of_hasRoundType (I.hasRoundType_path _ hq)).of_equiv e.symm) e hw).trans
      (I.whisker_path α _ hq hw _))
  cases β
  · exact key hs hb
  · exact key ht hb

omit [DecidableEq S.Pt] in
theorem whisker_equiv_paste (α : Bool) {x v : PastingDiagram X} {w : List (Edge S.Pt S.Ed)}
    (hw : w ≠ []) (e : (I.path w hw).Equiv v) (hp : (cond α x v).Pastable (cond α v x) 0) :
    (I.whisker α w x).Equiv ((cond α x v).paste (cond α v x) 0 hp) := by
  obtain _ | ⟨f, w⟩ := w
  · exact absurd rfl hw
  have hp' : (cond α x (I.pathCons f w)).Pastable (cond α (I.pathCons f w) x) 0 :=
    hp.of_equiv (.cond (.refl _) α e.symm) (.cond e.symm α (.refl _))
  rw [I.whisker_cons_of hp']
  exact Equiv.paste (.cond (.refl _) α e) (.cond e α (.refl _)) hp' hp

theorem exists_whisker_interchange {U V Sz Tz : List (Edge S.Pt S.Ed)} {a m b : S.Pt}
    (hU : S.pathEnds U = some (a, m)) (hV : S.pathEnds V = some (a, m))
    (hS : S.pathEnds Sz = some (m, b)) (hT : S.pathEnds Tz = some (m, b)) {y z : PastingDiagram X}
    (hy : HasRoundType y (I.pathRound U (S.isPath_of_pathEnds hU))
      (I.pathRound V (S.isPath_of_pathEnds hV)))
    (hz : HasRoundType z (I.pathRound Sz (S.isPath_of_pathEnds hS))
      (I.pathRound Tz (S.isPath_of_pathEnds hT))) :
    ∃ h₁ h₂, ((I.whisker false U z).paste (I.whisker true Tz y) 1 h₁).Equiv
      ((I.whisker true Sz y).paste (I.whisker false V z) 1 h₂) := by
  have hys := (I.spans_of_hasRoundType (I.hasRoundType_path _ hU)).of_hasRoundType hy
  have hzs := (I.spans_of_hasRoundType (I.hasRoundType_path _ hS)).of_hasRoundType hz
  have hp := hys.pastable hzs
  have hdy : y.dim = 2 :=
    hy.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hU)))
  have hdz : z.dim = 2 :=
    hz.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hS)))
  obtain ⟨i₁, i₂, i₃, e₁⟩ := equiv_paste_interchange false (c := z) (h := y) hp (by omega)
    (by omega)
  obtain ⟨j₁, j₂, j₃, e₂⟩ := equiv_paste_interchange true (c := y) (h := z) hp (by omega)
    (by omega)
  have by₁ := hy.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hU))
  have bz₁ := hz.equiv_boundary_cond (I.dim_path (S.isPath_of_pathEnds hS))
  have eU := I.whisker_equiv_paste false (x := z) (S.isPath_of_pathEnds hU).ne_nil
    (by₁ false).symm i₁
  have eT := I.whisker_equiv_paste true (x := y) (S.isPath_of_pathEnds hT).ne_nil
    (bz₁ true).symm i₂
  have eS := I.whisker_equiv_paste true (x := y) (S.isPath_of_pathEnds hS).ne_nil
    (bz₁ false).symm j₁
  have eV := I.whisker_equiv_paste false (x := z) (S.isPath_of_pathEnds hV).ne_nil
    (by₁ true).symm j₂
  exact ⟨i₃.of_equiv eU.symm eT.symm, j₃.of_equiv eS.symm eV.symm,
    (Equiv.paste eU eT _ i₃).trans (e₁.trans (e₂.symm.trans (Equiv.paste eS eV _ j₃).symm))⟩

end PathInterp

variable (S) in
structure Interp [DecidableEq S.Pt] (X : DiagSet.{u}) extends S.PathInterp X where
  cell : S.Ce → Σ U : Atom, diagram X U
  hasRoundType_cell : ∀ c (hs : S.IsPath (S.cellSource c)) (ht : S.IsPath (S.cellTarget c)),
    HasRoundType (PastingDiagram.ofCell (cell c).2) (toPathInterp.pathRound _ hs)
      (toPathInterp.pathRound _ ht)

namespace Interp

variable [DecidableEq S.Pt] (I : S.Interp X)

noncomputable def mapTo (f : X ⟶ Y) : S.Interp Y where
  toPathInterp := I.toPathInterp.mapTo f
  cell c := ⟨(I.cell c).1, f.app _ (I.cell c).2⟩
  hasRoundType_cell c hs ht := by
    have h := (I.hasRoundType_cell c hs ht).mapTo f
    rw [← PastingDiagram.ofCell_app] at h
    exact h.of_equiv (I.path_mapTo f hs).symm (I.path_mapTo f ht).symm

@[simp] theorem toPathInterp_mapTo (f : X ⟶ Y) :
    (I.mapTo f).toPathInterp = I.toPathInterp.mapTo f :=
  rfl

noncomputable def cellDiagram (x : PastingDiagram X) : Cell S.Pt S.Ed S.Ce → PastingDiagram X
  | .gen c => PastingDiagram.ofCell (I.cell c).2
  | .unitor k e => I.unitorDiagram k e
  | .unit [] => x
  | .unit (e :: p) => (I.pathCons e p).unit

theorem hasRoundType_cellDiagram (hS : S.WellFormed) (x : PastingDiagram X)
    {c : Cell S.Pt S.Ed S.Ce} (hs : S.IsPath (S.cellType c).1) :
    HasRoundType (I.cellDiagram x c) (I.pathRound _ hs)
      (I.pathRound _ (S.isPath_cellType_snd hS hs)) := by
  cases c with
  | gen c => exact I.hasRoundType_cell c hs _
  | unitor k e => exact I.hasRoundType_unitorDiagram k e
  | unit p =>
    obtain _ | ⟨e, p⟩ := p
    · exact absurd rfl hs.ne_nil
    · exact hasRoundType_unit (I.pathRound _ hs)

theorem isRound_cellDiagram (x : PastingDiagram X) {c : Cell S.Pt S.Ed S.Ce}
    (hs : S.IsPath (S.cellType c).1) : (I.cellDiagram x c).IsRound := by
  cases c with
  | gen c => exact (cellRound (I.cell c).2).isRound
  | unitor k e => exact I.isRound_unitorDiagram k e
  | unit p =>
    obtain _ | ⟨e, p⟩ := p
    · exact absurd rfl hs.ne_nil
    · exact isRound_unit (I.isRound_path hs)

noncomputable def layer (e : Edge S.Pt S.Ed) (q : List (Edge S.Pt S.Ed))
    (l : Cell S.Pt S.Ed S.Ce × ℕ) : PastingDiagram X :=
  I.whisker false ((e :: q).take l.2)
    (I.whisker true ((e :: q).drop (l.2 + (S.cellType l.1).1.length))
      (I.cellDiagram (I.pathCons e q).unit l.1))

variable [DecidableEq S.Ed]

theorem hasRoundType_layer (hS : S.WellFormed) {e : Edge S.Pt S.Ed} {q p' : List (Edge S.Pt S.Ed)}
    {l : Cell S.Pt S.Ed S.Ce × ℕ} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z))
    (h : S.applyLayer (e :: q) l.1 l.2 = some p') :
    HasRoundType (I.layer e q l) (I.pathRound _ (S.isPath_of_pathEnds hp))
      (I.pathRound p' (S.isPath_of_pathEnds (S.pathEnds_applyLayer hS h hp))) := by
  obtain ⟨hne, hseg, rfl⟩ := S.eq_of_applyLayer_eq_some h
  have hp' := hp
  rw [← hseg] at hp'
  obtain ⟨-, hw⟩ := S.pathEnds_eq_some_iff.1 hp'
  rw [S.walk_append, S.walk_append] at hw
  obtain ⟨b, hb, hBz⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨a, hA, hsab⟩ := Option.bind_eq_some_iff.1 hb
  have hs : S.pathEnds (S.cellType l.1).1 = some (a, b) := S.pathEnds_eq_some_iff.2 ⟨hne, hsab⟩
  have ht : S.pathEnds (S.cellType l.1).2 = some (a, b) :=
    (S.pathEnds_cellType_snd hS l.1).trans hs
  have h₁ := I.hasRoundType_whisker true hs ht
    (I.hasRoundType_cellDiagram hS (I.pathCons e q).unit (S.isPath_of_pathEnds hs))
    (c := z) hBz
  have h₂ := I.hasRoundType_whisker false (S.pathEnds_whisker true hs (c := z) hBz)
    (S.pathEnds_whisker true ht (c := z) hBz) h₁ (c := x) hA
  refine h₂.of_equiv (PastingDiagram.equiv_of_eq ?_) (PastingDiagram.equiv_of_eq ?_) <;>
    simp only [PathInterp.toPastingDiagram_pathRound] <;> refine I.path_congr ?_ _ _
  · simp only [cond_true, cond_false, ← List.append_assoc]
    exact hseg
  · simp only [cond_true, cond_false, List.append_assoc]

noncomputable def layers (e : Edge S.Pt S.Ed) (q : List (Edge S.Pt S.Ed)) :
    List (Cell S.Pt S.Ed S.Ce × ℕ) → PastingDiagram X
  | [] => (I.pathCons e q).unit
  | [l] => I.layer e q l
  | l :: l' :: ls => match S.applyLayer (e :: q) l.1 l.2 with
    | some (e' :: q') => (I.layer e q l).pasteOr (layers e' q' (l' :: ls)) 1
    | _ => I.layer e q l

noncomputable def diagram : (d : Diagram S.Pt S.Ed S.Ce) → d.source ≠ [] → PastingDiagram X
  | ⟨[], _⟩, h => absurd rfl h
  | ⟨e :: q, ls⟩, _ => I.layers e q ls

@[simp] theorem diagram_mk (e : Edge S.Pt S.Ed) (q : List (Edge S.Pt S.Ed))
    (ls : List (Cell S.Pt S.Ed S.Ce × ℕ)) (h : e :: q ≠ []) :
    I.diagram ⟨e :: q, ls⟩ h = I.layers e q ls :=
  rfl

theorem layers_cons_cons (hS : S.WellFormed) {e e' : Edge S.Pt S.Ed}
    {q q' r : List (Edge S.Pt S.Ed)} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z))
    {l l' : Cell S.Pt S.Ed S.Ce × ℕ} {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (h₁ : S.applyLayer (e :: q) l.1 l.2 = some (e' :: q'))
    (h₂ : S.targetFrom (e' :: q') (l' :: ls) = some r)
    (hr : HasRoundType (I.layers e' q' (l' :: ls))
      (I.pathRound _ (S.isPath_of_pathEnds (S.pathEnds_applyLayer hS h₁ hp)))
      (I.pathRound r (S.isPath_of_pathEnds
        (S.pathEnds_targetFrom hS h₂ (S.pathEnds_applyLayer hS h₁ hp))))) :
    ∃ hc, I.layers e q (l :: l' :: ls) = (I.layer e q l).paste (I.layers e' q' (l' :: ls)) 1 hc :=
  have hc := (I.hasRoundType_layer hS hp h₁).pastable hr (.refl _)
    (I.dim_path (S.isPath_of_pathEnds hp))
  ⟨hc, by simp only [layers, h₁]; exact pasteOr_of hc⟩

theorem hasRoundType_layers (hS : S.WellFormed) {e : Edge S.Pt S.Ed}
    {q r : List (Edge S.Pt S.Ed)} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z)) :
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} → (h : S.targetFrom (e :: q) ls = some r) →
    HasRoundType (I.layers e q ls) (I.pathRound _ (S.isPath_of_pathEnds hp))
      (I.pathRound r (S.isPath_of_pathEnds (S.pathEnds_targetFrom hS h hp)))
  | [], h => by
    obtain rfl := Option.some.inj h
    exact hasRoundType_unit (I.pathRound _ (S.isPath_of_pathEnds hp))
  | [l], h => by
    obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h₂
    exact I.hasRoundType_layer hS hp h₁
  | l :: l' :: ls, h => by
    obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hp' := S.pathEnds_applyLayer hS h₁ hp
    obtain _ | ⟨e', q'⟩ := p'
    · simp only [pathEnds_nil, reduceCtorEq] at hp'
    have hr := hasRoundType_layers hS hp' h₂
    obtain ⟨hc, he⟩ := I.layers_cons_cons hS hp h₁ h₂ hr
    rw [he]
    exact (I.hasRoundType_layer hS hp h₁).paste hr (.refl _)
      (I.dim_path (S.isPath_of_pathEnds hp)) hc

theorem hasRoundType_diagram (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ []) :
    HasRoundType (I.diagram d hsrc) (I.pathRound _ (S.isPath_source_of_target hd))
      (I.pathRound q (S.isPath_target hS hd)) := by
  obtain ⟨_ | ⟨e, p⟩, ls⟩ := d
  · exact absurd rfl hsrc
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hd)
  have hd' := hd
  rw [target, if_pos (S.isPath_source_of_target hd)] at hd'
  exact I.hasRoundType_layers hS hp hd'

theorem dim_diagram (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hd : S.target d = some q) (hsrc : d.source ≠ []) : (I.diagram d hsrc).dim = 2 :=
  (I.hasRoundType_diagram hS hd hsrc).dim_eq.trans
    (congrArg (· + 1) (I.dim_path (S.isPath_source_of_target hd)))

theorem equiv_boundary_diagram (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ []) (α : Bool)
    (hq : cond α q d.source ≠ []) :
    ((I.diagram d hsrc).boundary 1 α).Equiv (I.path (cond α q d.source) hq) := by
  have h := (I.hasRoundType_diagram hS hd hsrc).equiv_boundary_cond
    (I.dim_path (S.isPath_source_of_target hd)) α
  cases α <;> exact h

omit [DecidableEq S.Ed] in
private theorem layer_eq_cellDiagram {e : Edge S.Pt S.Ed} {q : List (Edge S.Pt S.Ed)}
    {l : Cell S.Pt S.Ed S.Ce × ℕ}
    (h : (e :: q).take l.2 ++ (S.cellType l.1).1 ++
      (e :: q).drop (l.2 + (S.cellType l.1).1.length) = (S.cellType l.1).1 ∨
      (e :: q).take l.2 ++ (S.cellType l.1).2 ++
        (e :: q).drop (l.2 + (S.cellType l.1).1.length) = (S.cellType l.1).2) :
    I.layer e q l = I.cellDiagram (I.pathCons e q).unit l.1 := by
  have hn : ∀ {A B C : List (Edge S.Pt S.Ed)}, A ++ B ++ C = B → A = [] ∧ C = [] := fun h => by
    have := congrArg List.length h
    simp only [List.length_append] at this
    exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
  obtain ⟨hA, hC⟩ : _ ∧ _ := h.elim hn hn
  rw [layer, hA, hC, PathInterp.whisker_nil, PathInterp.whisker_nil]

theorem isRound_diagram_of_layers_eq_nil {d : Diagram S.Pt S.Ed S.Ce} (hd : S.IsPath d.source)
    (hl : d.layers = []) : (I.diagram d hd.ne_nil).IsRound := by
  obtain ⟨_ | ⟨e, p⟩, ls⟩ := d
  · exact absurd rfl hd.ne_nil
  subst hl
  exact isRound_unit (I.isRound_path hd)

theorem isRound_diagram_of_first (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ [])
    {l : Cell S.Pt S.Ed S.Ce × ℕ} {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (hl : d.layers = l :: ls) (hc : (S.cellType l.1).1 = d.source) :
    (I.diagram d hsrc).IsRound := by
  obtain ⟨_ | ⟨e, p⟩, ls'⟩ := d
  · exact absurd rfl hsrc
  obtain rfl : ls' = l :: ls := hl
  have hpath := S.isPath_source_of_target hd
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath hpath
  rw [target, if_pos hpath] at hd
  obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 hd
  have hs : S.IsPath (S.cellType l.1).1 := hc ▸ hpath
  have hlay := I.layer_eq_cellDiagram (Or.inl ((S.eq_of_applyLayer_eq_some h₁).2.1.trans hc.symm))
  obtain _ | ⟨l', ls⟩ := ls
  · rw [diagram_mk, layers, hlay]
    exact I.isRound_cellDiagram _ hs
  have hp' := S.pathEnds_applyLayer hS h₁ hp
  obtain _ | ⟨e', q'⟩ := p'
  · simp only [pathEnds_nil, reduceCtorEq] at hp'
  have hr := I.hasRoundType_layers hS hp' h₂
  obtain ⟨hc', he⟩ := I.layers_cons_cons hS hp h₁ h₂ hr
  rw [diagram_mk, he]
  refine isRound_paste_of_round false (u := I.layer e p l) (x := I.layers e' q' (l' :: ls)) hc'
    (hlay ▸ I.isRound_cellDiagram _ hs) ?_ ?_
  · exact (I.hasRoundType_layer hS hp h₁).dim_eq.trans
      (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hp)))
  · exact (hr.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hp')))).le

private theorem equiv_layers_append (hS : S.WellFormed) {e e' : Edge S.Pt S.Ed}
    {q q' r : List (Edge S.Pt S.Ed)} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z))
    {l l' : Cell S.Pt S.Ed S.Ce × ℕ} {ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (h₁ : S.targetFrom (e :: q) (l :: ls) = some (e' :: q'))
    (h₂ : S.targetFrom (e' :: q') (l' :: ls') = some r) :
    ∃ hc, (I.layers e q (l :: ls ++ l' :: ls')).Equiv
      ((I.layers e q (l :: ls)).paste (I.layers e' q' (l' :: ls')) 1 hc) := by
  have hp' := S.pathEnds_targetFrom hS h₁ hp
  have hR := I.hasRoundType_layers hS hp' h₂
  induction ls generalizing e q l with
  | nil =>
    obtain ⟨p₁, h₃, h₄⟩ := Option.bind_eq_some_iff.1 h₁
    obtain rfl := Option.some.inj h₄
    obtain ⟨hc, he⟩ := I.layers_cons_cons hS hp h₃ h₂ hR
    exact ⟨hc, PastingDiagram.equiv_of_eq he⟩
  | cons l₂ ls ih =>
    obtain ⟨p₁, h₃, h₄⟩ := Option.bind_eq_some_iff.1 h₁
    have hp₁ := S.pathEnds_applyLayer hS h₃ hp
    obtain _ | ⟨e₁, q₁⟩ := p₁
    · simp only [pathEnds_nil, reduceCtorEq] at hp₁
    obtain ⟨hc, e₂⟩ := ih hp₁ h₄
    have h₅ : S.targetFrom (e₁ :: q₁) (l₂ :: (ls ++ l' :: ls')) = some r := by
      rw [← List.cons_append, S.targetFrom_append, h₄, Option.bind_some]
      exact h₂
    obtain ⟨hc₁, he₁⟩ := I.layers_cons_cons hS hp h₃ h₄ (I.hasRoundType_layers hS hp₁ h₄)
    obtain ⟨hc₂, he₂⟩ := I.layers_cons_cons hS hp h₃ h₅ (I.hasRoundType_layers hS hp₁ h₅)
    have h₆ := Pastable.paste_left hc₁ hc
    obtain ⟨h₈, h₇, e₃⟩ := equiv_paste_assoc hc₁ h₆
    rw [List.cons_append, List.cons_append, he₂, he₁]
    exact ⟨h₆, (Equiv.paste (.refl _) e₂ hc₂ h₇).trans e₃.symm⟩

theorem equiv_diagram_append (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hd' : d'.source = q)
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) (hl : d.layers ≠ []) (hl' : d'.layers ≠ [])
    (he : (S.target d').isSome) :
    ∃ h, (I.diagram (d ++ d') hsrc).Equiv ((I.diagram d hsrc).paste (I.diagram d' hsrc') 1 h) := by
  obtain ⟨_ | ⟨e, p⟩, ls₀⟩ := d
  · exact absurd rfl hsrc
  obtain _ | ⟨l, ls⟩ := ls₀
  · exact absurd rfl hl
  obtain ⟨_ | ⟨e', p'⟩, ls₁⟩ := d'
  · exact absurd rfl hsrc'
  obtain _ | ⟨l', ls'⟩ := ls₁
  · exact absurd rfl hl'
  dsimp only at hd'
  subst hd'
  have hpath := S.isPath_source_of_target hd
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath hpath
  rw [target, if_pos hpath] at hd
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 he
  rw [target, if_pos (S.isPath_source_of_target hr)] at hr
  dsimp only at hd hr hp
  have key : I.diagram (⟨e :: p, l :: ls⟩ ++ ⟨e' :: p', l' :: ls'⟩) hsrc =
      I.layers e p (l :: ls ++ l' :: ls') := rfl
  rw [key, diagram_mk, diagram_mk]
  exact I.equiv_layers_append hS hp hd hr

theorem isRound_diagram_of_last (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ [])
    {l : Cell S.Pt S.Ed S.Ce × ℕ} {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (hl : d.layers = ls ++ [l]) (hc : (S.cellType l.1).2 = q) :
    (I.diagram d hsrc).IsRound := by
  obtain ⟨_ | ⟨e, p⟩, ls'⟩ := d
  · exact absurd rfl hsrc
  obtain rfl : ls' = ls ++ [l] := hl
  have hpath := S.isPath_source_of_target hd
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath hpath
  rw [target, if_pos hpath] at hd
  dsimp only at hd hp ⊢
  rw [S.targetFrom_append] at hd
  obtain ⟨p₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 hd
  obtain ⟨p₂, h₃, h₄⟩ := Option.bind_eq_some_iff.1 h₂
  obtain rfl := Option.some.inj h₄
  have hp₁ := S.pathEnds_targetFrom hS h₁ hp
  obtain _ | ⟨e₁, q₁⟩ := p₁
  · simp only [pathEnds_nil, reduceCtorEq] at hp₁
  have hlay := I.layer_eq_cellDiagram (e := e₁) (q := q₁)
    (Or.inr ((S.eq_of_applyLayer_eq_some h₃).2.2.symm.trans hc.symm))
  have hround : (I.layers e₁ q₁ [l]).IsRound := by
    rw [layers, hlay]
    exact I.isRound_cellDiagram _ (S.isPath_cellType_of_applyLayer h₃ hp₁)
  rw [diagram_mk]
  obtain _ | ⟨l₀, ls⟩ := ls
  · simp only [targetFrom, Option.some.injEq, List.cons.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact hround
  obtain ⟨hc', hD⟩ := I.equiv_layers_append hS hp h₁ (l' := l) (ls' := []) h₂
  refine hD.isRound_iff.2 (isRound_paste_of_round true (u := I.layers e₁ q₁ [l])
    (x := I.layers e p (l₀ :: ls)) hc' hround ?_ ?_)
  · exact (I.hasRoundType_layers hS hp₁ h₂).dim_eq.trans
      (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hp₁)))
  · exact ((I.hasRoundType_layers hS hp h₁).dim_eq.trans
      (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hp)))).le

omit [DecidableEq S.Ed] in
private theorem cellDiagram_mapTo (f : X ⟶ Y) (x : PastingDiagram X) (y : PastingDiagram Y)
    {c : Cell S.Pt S.Ed S.Ce} (hs : S.IsPath (S.cellType c).1) :
    ((I.mapTo f).cellDiagram y c).Equiv ((I.cellDiagram x c).mapTo f) := by
  cases c with
  | gen c => exact PastingDiagram.equiv_of_eq (PastingDiagram.ofCell_app _ _)
  | unitor k e => exact I.unitorDiagram_mapTo f k e
  | unit p =>
    obtain _ | ⟨e, p⟩ := p
    · exact absurd rfl hs.ne_nil
    obtain ⟨_, _, h⟩ := S.exists_pathEnds_of_isPath hs
    exact (I.pathCons_mapTo f (S.pathEnds_cons_eq_some.1 h).2).unit.trans
      (PastingDiagram.equiv_of_eq (unit_mapTo _ _))

private theorem layer_mapTo (hS : S.WellFormed) (f : X ⟶ Y) {e : Edge S.Pt S.Ed}
    {q p' : List (Edge S.Pt S.Ed)} {l : Cell S.Pt S.Ed S.Ce × ℕ} {x z : S.Pt}
    (hp : S.pathEnds (e :: q) = some (x, z)) (h : S.applyLayer (e :: q) l.1 l.2 = some p') :
    ((I.mapTo f).layer e q l).Equiv ((I.layer e q l).mapTo f) := by
  obtain ⟨hne, hseg, -⟩ := S.eq_of_applyLayer_eq_some h
  have hp' := hp
  rw [← hseg] at hp'
  obtain ⟨-, hw⟩ := S.pathEnds_eq_some_iff.1 hp'
  rw [S.walk_append, S.walk_append] at hw
  obtain ⟨b, hb, hBz⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨a, hA, hsab⟩ := Option.bind_eq_some_iff.1 hb
  have hs : S.pathEnds (S.cellType l.1).1 = some (a, b) := S.pathEnds_eq_some_iff.2 ⟨hne, hsab⟩
  have hc := (I.spans_of_hasRoundType (I.hasRoundType_path _ hs)).of_hasRoundType
    (I.hasRoundType_cellDiagram hS (I.pathCons e q).unit (S.isPath_of_pathEnds hs))
  have e₁ := I.whisker_mapTo true hc (c := z) hBz f
    (I.cellDiagram_mapTo f _ ((I.mapTo f).pathCons e q).unit (S.isPath_of_pathEnds hs))
  exact I.whisker_mapTo false (hc.whisker true (c := z) hBz) (c := x) hA f e₁

private theorem layers_mapTo (hS : S.WellFormed) (f : X ⟶ Y) {e : Edge S.Pt S.Ed}
    {q r : List (Edge S.Pt S.Ed)} {x z : S.Pt} (hp : S.pathEnds (e :: q) = some (x, z)) :
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} → (h : S.targetFrom (e :: q) ls = some r) →
    ((I.mapTo f).layers e q ls).Equiv ((I.layers e q ls).mapTo f)
  | [], _ => ((I.pathCons_mapTo f (S.pathEnds_cons_eq_some.1 hp).2).unit).trans
      (PastingDiagram.equiv_of_eq (unit_mapTo _ _))
  | [l], h => by
    obtain ⟨p', h₁, -⟩ := Option.bind_eq_some_iff.1 h
    exact I.layer_mapTo hS f hp h₁
  | l :: l' :: ls, h => by
    obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hp' := S.pathEnds_applyLayer hS h₁ hp
    obtain _ | ⟨e', q'⟩ := p'
    · simp only [pathEnds_nil, reduceCtorEq] at hp'
    obtain ⟨hc, he⟩ := I.layers_cons_cons hS hp h₁ h₂ (I.hasRoundType_layers hS hp' h₂)
    obtain ⟨hc', he'⟩ := (I.mapTo f).layers_cons_cons hS hp h₁ h₂
      ((I.mapTo f).hasRoundType_layers hS hp' h₂)
    rw [he, he']
    exact (Equiv.paste (I.layer_mapTo hS f hp h₁) (layers_mapTo hS f hp' h₂) hc'
      (hc.mapTo f)).trans (paste_mapTo _ _ 1 hc f _).symm

theorem diagram_mapTo (hS : S.WellFormed) (f : X ⟶ Y) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ []) :
    ((I.mapTo f).diagram d hsrc).Equiv ((I.diagram d hsrc).mapTo f) := by
  obtain ⟨_ | ⟨e, p⟩, ls⟩ := d
  · exact absurd rfl hsrc
  have hpath := S.isPath_source_of_target hd
  obtain ⟨x, z, hp⟩ := S.exists_pathEnds_of_isPath hpath
  rw [target, if_pos hpath] at hd
  exact I.layers_mapTo hS f hp hd

omit [DecidableEq S.Ed] in
private theorem pasteOr_equiv {x x' y y' : PastingDiagram X} {n : ℕ} (hx : x.Equiv x')
    (hy : y.Equiv y') : (x.pasteOr y n).Equiv (x'.pasteOr y' n) := by
  by_cases h : x.Pastable y n
  · have h' := h.of_equiv hx hy
    rw [pasteOr_of h, pasteOr_of h']
    exact Equiv.paste hx hy h h'
  · have h' : ¬ x'.Pastable y' n := fun h' => h (h'.of_equiv hx.symm hy.symm)
    rw [PastingDiagram.pasteOr, dif_neg h, PastingDiagram.pasteOr, dif_neg h']
    exact hx

theorem diagram_congr {d d' : Diagram S.Pt S.Ed S.Ce} (h : d = d') (hd : d.source ≠ [])
    (hd' : d'.source ≠ []) : I.diagram d hd = I.diagram d' hd' := by
  subst h
  rfl

noncomputable def attach (α : Bool) : List (Edge S.Pt S.Ed) → List (Cell S.Pt S.Ed S.Ce × ℕ) →
    PastingDiagram X → PastingDiagram X
  | e :: q, l :: ls, x =>
    (cond α x (I.layers e q (l :: ls))).pasteOr (cond α (I.layers e q (l :: ls)) x) 1
  | [], _, x => x
  | _ :: _, [], x => x

@[simp] theorem attach_nil (α : Bool) (p : List (Edge S.Pt S.Ed)) (x : PastingDiagram X) :
    I.attach α p [] x = x := by
  cases p <;> rfl

theorem attach_of {α : Bool} {p : List (Edge S.Pt S.Ed)} (hp : p ≠ [])
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hl : ls ≠ []) {x : PastingDiagram X}
    (h : (cond α x (I.diagram ⟨p, ls⟩ hp)).Pastable (cond α (I.diagram ⟨p, ls⟩ hp) x) 1) :
    I.attach α p ls x =
      (cond α x (I.diagram ⟨p, ls⟩ hp)).paste (cond α (I.diagram ⟨p, ls⟩ hp) x) 1 h := by
  obtain _ | ⟨e, q⟩ := p
  · exact absurd rfl hp
  obtain _ | ⟨l, ls⟩ := ls
  · exact absurd rfl hl
  exact pasteOr_of h

theorem attach_equiv (α : Bool) (p : List (Edge S.Pt S.Ed)) (ls : List (Cell S.Pt S.Ed S.Ce × ℕ))
    {x x' : PastingDiagram X} (h : x.Equiv x') :
    (I.attach α p ls x).Equiv (I.attach α p ls x') := by
  obtain _ | ⟨e, q⟩ := p
  · exact h
  obtain _ | ⟨l, ls⟩ := ls
  · exact h
  exact pasteOr_equiv (.cond h α (.refl _)) (.cond (.refl _) α h)

theorem equiv_diagram_attach (hS : S.WellFormed) {p p₁ p₂ : List (Edge S.Pt S.Ed)}
    (hp : S.IsPath p) {A m C : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (hA : S.targetFrom p A = some p₁) (hm : S.targetFrom p₁ m = some p₂)
    (hC : (S.targetFrom p₂ C).isSome) (hm₀ : m ≠ []) :
    (I.diagram ⟨p, A ++ m ++ C⟩ hp.ne_nil).Equiv (I.attach true p₂ C
      (I.attach false p A (I.diagram ⟨p₁, m⟩
        (S.isPath_target hS (d := ⟨p, A⟩) (by rw [target, if_pos hp]; exact hA)).ne_nil))) := by
  have hp₁ : S.IsPath p₁ := S.isPath_target hS (S.target_mk_of_targetFrom hp hA)
  have hp₂ : S.IsPath p₂ := S.isPath_target hS (S.target_mk_of_targetFrom hp₁ hm)
  have hAm : S.targetFrom p (A ++ m) = some p₂ := by
    rw [S.targetFrom_append, hA, Option.bind_some, hm]
  have e₁ : (I.diagram ⟨p, A ++ m⟩ hp.ne_nil).Equiv
      (I.attach false p A (I.diagram ⟨p₁, m⟩ hp₁.ne_nil)) := by
    obtain _ | ⟨l, ls⟩ := A
    · obtain rfl : p = p₁ := Option.some.inj hA
      simp only [List.nil_append, attach_nil]
      exact .refl _
    obtain ⟨h, e⟩ := I.equiv_diagram_append hS (d := ⟨p, l :: ls⟩) (d' := ⟨p₁, m⟩)
      (S.target_mk_of_targetFrom hp hA) rfl hp.ne_nil hp₁.ne_nil (List.cons_ne_nil _ _) hm₀
      (by rw [S.target_mk_of_targetFrom hp₁ hm]; rfl)
    rw [I.attach_of (α := false) (x := I.diagram ⟨p₁, m⟩ hp₁.ne_nil) hp.ne_nil
      (List.cons_ne_nil _ _) h]
    exact (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans e
  obtain _ | ⟨l, ls⟩ := C
  · rw [List.append_nil, attach_nil]
    exact e₁
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hC
  obtain ⟨h, e⟩ := I.equiv_diagram_append hS (d := ⟨p, A ++ m⟩) (d' := ⟨p₂, l :: ls⟩)
    (S.target_mk_of_targetFrom hp hAm) rfl hp.ne_nil hp₂.ne_nil
    (fun h => hm₀ (List.append_eq_nil_iff.1 h).2) (List.cons_ne_nil _ _)
    (by rw [S.target_mk_of_targetFrom hp₂ hq]; rfl)
  have h' := h.of_equiv e₁ (.refl _)
  rw [I.attach_of (α := true) (x := I.attach false p A (I.diagram ⟨p₁, m⟩ hp₁.ne_nil))
    hp₂.ne_nil (List.cons_ne_nil _ _) h']
  exact (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans
    (e.trans (Equiv.paste e₁ (.refl _) h h'))

theorem equiv_boundary_attach (hS : S.WellFormed) (α : Bool) {p : List (Edge S.Pt S.Ed)}
    (hp : S.IsPath p) {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hls : (S.targetFrom p ls).isSome)
    {x : PastingDiagram X} {n : ℕ} (hn : 1 < n) (hx : n ≤ x.dim) (β : Bool)
    (h : ls ≠ [] → (cond α (x.boundary n β) (I.diagram ⟨p, ls⟩ hp.ne_nil)).Pastable
      (cond α (I.diagram ⟨p, ls⟩ hp.ne_nil) (x.boundary n β)) 1) :
    ((I.attach α p ls x).boundary n β).Equiv (I.attach α p ls (x.boundary n β)) := by
  obtain _ | ⟨l, ls'⟩ := ls
  · rw [attach_nil, attach_nil]
  have hb := h (List.cons_ne_nil _ _)
  have hp' := PastingDiagram.pastable_of_boundary α hn hx hb
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hls
  have hdim := I.dim_diagram hS (d := ⟨p, l :: ls'⟩) (S.target_mk_of_targetFrom hp hq)
    hp.ne_nil
  obtain ⟨hp'', e⟩ := exists_equiv_boundary_paste_cond α hp' hdim (by omega) hx β
  rw [I.attach_of hp.ne_nil (List.cons_ne_nil _ _) hp',
    I.attach_of hp.ne_nil (List.cons_ne_nil _ _) hp'']
  exact e

theorem dim_attach (hS : S.WellFormed) (α : Bool) {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p)
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hls : (S.targetFrom p ls).isSome)
    {x : PastingDiagram X} (hx : 2 ≤ x.dim)
    (h : ls ≠ [] → (cond α x (I.diagram ⟨p, ls⟩ hp.ne_nil)).Pastable
      (cond α (I.diagram ⟨p, ls⟩ hp.ne_nil) x) 1) : (I.attach α p ls x).dim = x.dim := by
  obtain _ | ⟨l, ls'⟩ := ls
  · rw [attach_nil]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hls
  have hdim := I.dim_diagram hS (d := ⟨p, l :: ls'⟩) (S.target_mk_of_targetFrom hp hr)
    hp.ne_nil
  rw [I.attach_of hp.ne_nil (List.cons_ne_nil _ _) (h (List.cons_ne_nil _ _)), dim_paste_cond,
    hdim]
  omega

omit [DecidableEq S.Ed] in
private theorem cellDiagram_congr (x y : PastingDiagram X) {c : Cell S.Pt S.Ed S.Ce}
    (hc : (S.cellType c).1 ≠ []) : I.cellDiagram x c = I.cellDiagram y c := by
  cases c with
  | gen c => rfl
  | unitor k e => rfl
  | unit p =>
    obtain _ | ⟨e, p⟩ := p
    · exact absurd rfl hc
    · rfl

theorem diagram_singleton {p L R : List (Edge S.Pt S.Ed)} {l : Cell S.Pt S.Ed S.Ce × ℕ}
    (hp : p ≠ []) (h : p = L ++ (S.cellType l.1).1 ++ R) (hL : L.length = l.2)
    (hc : (S.cellType l.1).1 ≠ []) (x : PastingDiagram X) :
    I.diagram ⟨p, [l]⟩ hp = I.whisker false L (I.whisker true R (I.cellDiagram x l.1)) := by
  obtain _ | ⟨e, q⟩ := p
  · exact absurd rfl hp
  rw [diagram_mk, layers, layer, I.cellDiagram_congr _ x hc, h, ← hL]
  simp [List.drop_append, List.drop_eq_nil_of_le]

theorem diagram_nil {p : List (Edge S.Pt S.Ed)} (hp : p ≠ []) :
    I.diagram ⟨p, []⟩ hp = (I.path p hp).unit := by
  obtain _ | ⟨e, q⟩ := p
  · exact absurd rfl hp
  · rfl

theorem diagram_unit_singleton {p : List (Edge S.Pt S.Ed)} (hp : p ≠ []) :
    I.diagram ⟨p, [(.unit p, 0)]⟩ hp = (I.path p hp).unit := by
  rw [I.diagram_singleton (l := (.unit p, 0)) (L := []) (R := []) hp (by simp [cellType]) rfl hp
    (I.path p hp).unit, PathInterp.whisker_nil, PathInterp.whisker_nil]
  obtain _ | ⟨e, q⟩ := p
  · exact absurd rfl hp
  · rfl

private theorem equiv_diagram_whisker_singleton (hS : S.WellFormed) (α : Bool)
    {w p p₁ : List (Edge S.Pt S.Ed)} {l : Cell S.Pt S.Ed S.Ce × ℕ} {a b c : S.Pt}
    (hp : S.pathEnds p = some (a, b)) (h : S.applyLayer p l.1 l.2 = some p₁)
    (hw : S.walk (cond α b c) w = some (cond α c a))
    (hne : (Diagram.whisker α w ⟨p, [l]⟩).source ≠ []) (hp' : p ≠ []) :
    (I.diagram (Diagram.whisker α w ⟨p, [l]⟩) hne).Equiv
      (I.whisker α w (I.diagram ⟨p, [l]⟩ hp')) := by
  obtain ⟨hc, L, R, rfl, hL, -⟩ := S.applyLayer_eq_some_iff.1 h
  obtain ⟨x₀, y₀, hLw, hs, hRw⟩ := S.exists_walk_of_split hp hc
  have ht := (S.pathEnds_cellType_snd hS l.1).trans hs
  let j := (I.pathCons (.unit a) []).unit
  let x := I.cellDiagram j l.1
  have hx : I.Spans x x₀ y₀ := (I.spans_of_hasRoundType
    (I.hasRoundType_path (S.isPath_of_pathEnds hs).ne_nil hs)).of_hasRoundType
    (I.hasRoundType_cellDiagram hS _ (S.isPath_of_pathEnds hs))
  have hxR := hx.whisker true (c := b) hRw
  rw [I.diagram_singleton hp' rfl hL hc j]
  cases α
  · have e := I.diagram_singleton (l := (l.1, l.2 + w.length)) hne
      (L := w ++ L) (R := R) (by simp [Diagram.whisker]) (by simp [hL, Nat.add_comm]) hc j
    simp only [Diagram.whisker, cond_false, List.map_cons, List.map_nil] at e ⊢
    rw [e]
    have hwL : S.walk c (w ++ L) = some x₀ := by
      simp only [cond_false] at hw
      rw [S.walk_append, hw, Option.bind_some, hLw]
    exact I.whisker_append false hxR (w₁ := L) (w₂ := w) hwL
  · have e := I.diagram_singleton (l := l) hne (L := L) (R := R ++ w) (by simp [Diagram.whisker])
      hL hc j
    simp only [Diagram.whisker, cond_true] at e ⊢
    rw [e]
    have hRw' : S.walk y₀ (R ++ w) = some c := by
      simp only [cond_true] at hw
      rw [S.walk_append, hRw, Option.bind_some, hw]
    have e₁ := I.whisker_append true hx (w₁ := R) (w₂ := w) hRw'
    exact (I.whisker_equiv false (hx.whisker true (c := c) hRw') e₁ (c := a) hLw).trans
      (I.whisker_comm hxR hLw hw)

theorem equiv_diagram_whisker (hS : S.WellFormed) (α : Bool) {w p q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} {a b c : S.Pt} (hp : S.pathEnds p = some (a, b))
    (hls : ls ≠ []) (h : S.targetFrom p ls = some q)
    (hw : S.walk (cond α b c) w = some (cond α c a))
    (hne : (Diagram.whisker α w ⟨p, ls⟩).source ≠ []) :
    (I.diagram (Diagram.whisker α w ⟨p, ls⟩) hne).Equiv
      (I.whisker α w (I.diagram ⟨p, ls⟩ (S.isPath_of_pathEnds hp).ne_nil)) := by
  obtain _ | ⟨l, ls⟩ := ls
  · exact absurd rfl hls
  induction ls generalizing p l with
  | nil =>
    obtain ⟨p₁, h₁, -⟩ := Option.bind_eq_some_iff.1 h
    exact I.equiv_diagram_whisker_singleton hS α hp h₁ hw hne _
  | cons l' ls ih =>
    obtain ⟨p₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hp₁ := S.pathEnds_applyLayer hS h₁ hp
    have hpath := S.isPath_of_pathEnds hp
    have hpath₁ := S.isPath_of_pathEnds hp₁
    have h₁' : S.targetFrom p [l] = some p₁ := by
      rw [targetFrom, h₁, Option.bind_some]; rfl
    obtain ⟨hc, e⟩ := I.equiv_diagram_append hS (d := ⟨p, [l]⟩) (d' := ⟨p₁, l' :: ls⟩)
      (S.target_mk_of_targetFrom hpath h₁') rfl hpath.ne_nil hpath₁.ne_nil (List.cons_ne_nil _ _)
      (List.cons_ne_nil _ _) (by rw [S.target_mk_of_targetFrom hpath₁ h₂]; rfl)
    have hW : ∀ {p' : List (Edge S.Pt S.Ed)}, p' ≠ [] → ∀ ls' : List (Cell S.Pt S.Ed S.Ce × ℕ),
        (Diagram.whisker α w ⟨p', ls'⟩).source ≠ [] := fun hp' ls' => by
      rw [Diagram.source_whisker]
      cases α
      · exact List.append_ne_nil_of_right_ne_nil _ hp'
      · exact List.append_ne_nil_of_left_ne_nil hp' _
    have hsplit : Diagram.whisker α w ⟨p, l :: l' :: ls⟩ =
        Diagram.whisker α w ⟨p, [l]⟩ ++ Diagram.whisker α w ⟨p₁, l' :: ls⟩ := by
      cases α <;> rfl
    have hwt := S.targetFrom_whisker α w h₁'
    have hwt₂ := S.targetFrom_whisker α w h₂
    have hwpath : S.IsPath (Diagram.whisker α w ⟨p, [l]⟩).source := by
      rw [Diagram.source_whisker]
      exact S.isPath_of_pathEnds (S.pathEnds_whisker α hp hw)
    have hwpath₁ : S.IsPath (Diagram.whisker α w ⟨p₁, l' :: ls⟩).source := by
      rw [Diagram.source_whisker]
      exact S.isPath_of_pathEnds (S.pathEnds_whisker α hp₁ hw)
    obtain ⟨hc', e'⟩ := I.equiv_diagram_append hS (d := Diagram.whisker α w ⟨p, [l]⟩)
      (d' := Diagram.whisker α w ⟨p₁, l' :: ls⟩) (S.target_mk_of_targetFrom hwpath hwt)
      (by rw [Diagram.source_whisker]) (hW hpath.ne_nil _) (hW hpath₁.ne_nil _)
      (by cases α <;> exact List.cons_ne_nil _ _) (by cases α <;> exact List.cons_ne_nil _ _)
      (by rw [target, if_pos hwpath₁, hwt₂]; rfl)
    have hsp := (I.spans_of_hasRoundType (I.hasRoundType_path hpath.ne_nil hp)).of_hasRoundType
      (I.hasRoundType_diagram hS (S.target_mk_of_targetFrom hpath h₁') hpath.ne_nil)
    obtain ⟨hc'', e''⟩ := I.exists_whisker_paste α hsp hc hw
    have e₁ := I.equiv_diagram_whisker_singleton hS α hp h₁ hw (hW hpath.ne_nil _) hpath.ne_nil
    have e₂ := ih (l := l') hp₁ (List.cons_ne_nil _ _) h₂ (hW hpath₁.ne_nil _)
    refine (PastingDiagram.equiv_of_eq (I.diagram_congr hsplit _ _)).trans (e'.trans ?_)
    refine (Equiv.paste e₁ e₂ hc' hc'').trans (e''.symm.trans ?_)
    have hsp₂ : I.Spans (I.diagram ⟨p, [l]⟩ hpath.ne_nil |>.paste
        (I.diagram ⟨p₁, l' :: ls⟩ hpath₁.ne_nil) 1 hc) a b :=
      ⟨by rw [dim_paste]; exact lt_max_of_lt_left hsp.1, fun β =>
        (equiv_boundary_paste_of_lt hc false Nat.one_pos β).symm.trans (hsp.2 β)⟩
    exact I.whisker_equiv α hsp₂
      (e.symm.trans (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _))) hw

end Interp

section Presented

variable (S : Signature.{u}) [DecidableEq S.Pt]

private noncomputable def edgeStage : CellularExtensionData (DiagSet.discrete S.Pt) where
  ι := S.Ed
  source e := DiagSet.discretePoint (S.edgeSource e)
  target e := DiagSet.discretePoint (S.edgeTarget e)
  parallel _ := DiagSet.parallel_discretePoint _ _

private noncomputable def edgeInterp : S.PathInterp (edgeStage S).extension where
  point x := (edgeStage S).incl.app _ x
  edge e := ⟨(edgeStage S).shape e, (edgeStage S).cell e⟩
  hasRoundType_edge e := by
    have h := (edgeStage S).hasRoundType_cell e
    have hp (x : S.Pt) : (DiagSet.discretePoint x).mapTo (edgeStage S).incl =
        cellRound ((edgeStage S).incl.app _ x) :=
      RoundPastingDiagram.ext (PastingDiagram.ofCell_app _ _).symm
    exact (hp (S.edgeSource e)) ▸ (hp (S.edgeTarget e)) ▸ h

private noncomputable def cellStage (hS : S.WellFormed) :
    CellularExtensionData (edgeStage S).extension where
  ι := S.Ce
  source c := (edgeInterp S).pathRound (S.cellSource c) (hS c).1
  target c := (edgeInterp S).pathRound (S.cellTarget c) (by rw [IsPath, ← (hS c).2]; exact (hS c).1)
  parallel c := by
    obtain ⟨x, y, h⟩ := S.exists_pathEnds_of_isPath (hS c).1
    exact HasRoundType.parallel ((edgeInterp S).hasRoundType_path _ h)
      ((edgeInterp S).hasRoundType_path _ ((hS c).2 ▸ h))

noncomputable def presented (hS : S.WellFormed) : DiagSet.{u} := (cellStage S hS).extension

noncomputable def presentation (hS : S.WellFormed) : Presentation (S.presented hS) :=
  ((Presentation.discrete S.Pt).extend (edgeStage S)).extend (cellStage S hS)

noncomputable def tautInterp (hS : S.WellFormed) : S.Interp (S.presented hS) where
  toPathInterp := (edgeInterp S).mapTo (cellStage S hS).incl
  cell c := ⟨(cellStage S hS).shape c, (cellStage S hS).cell c⟩
  hasRoundType_cell c hs ht := ((cellStage S hS).hasRoundType_cell c).of_equiv
    ((edgeInterp S).path_mapTo _ hs).symm ((edgeInterp S).path_mapTo _ ht).symm

theorem tautInterp_point (hS : S.WellFormed) (x : S.Pt) :
    (S.tautInterp hS).point x = (S.presentation hS).point x :=
  rfl

theorem tautInterp_cell (hS : S.WellFormed) (c : S.Ce) :
    ((S.tautInterp hS).cell c).2 = (S.presentation hS).cell (Sum.inr c) :=
  rfl

end Presented

end Atoms.Diagrammatic.Layered.Signature
