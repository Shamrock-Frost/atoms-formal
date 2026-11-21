import Atoms.Diagrammatic.Rewriting.Relation

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered

namespace UnitorKind

def toLeft : UnitorKind → UnitorKind
  | right => left
  | rightInverse => leftInverse
  | k => k

end UnitorKind

def Cell.isUnit {Pt Ed Ce : Type v} : Cell Pt Ed Ce → Bool
  | .unit _ => true
  | _ => false

def Diagram.eraseUnits {Pt Ed Ce : Type v} (d : Diagram Pt Ed Ce) : Diagram Pt Ed Ce :=
  ⟨d.source, d.layers.filter fun l => !l.1.isUnit⟩

inductive UnitMove
  | cancel
  | trade
  | slide

namespace Signature

variable (S : Signature.{v}) [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

def cancel (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ) : Option (Diagram S.Pt S.Ed S.Ce) :=
  match d.layers.drop h with
  | (.unitor _ _, _) :: (.unitor _ _, _) :: _ =>
    if S.IsPath d.source ∧ (S.targetFrom d.source (d.layers.take h)).isSome ∧
        S.targetFrom d.source (d.layers.take (h + 2)) = S.targetFrom d.source (d.layers.take h)
    then some ⟨d.source, d.layers.take h ++ d.layers.drop (h + 2)⟩ else none
  | _ => none

def trade (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ) : Option (Diagram S.Pt S.Ed S.Ce) :=
  match d.layers.drop h with
  | (.unitor k _, o) :: rest =>
    if S.IsPath d.source ∧ k.side = true then
      match S.targetFrom d.source (d.layers.take h),
        S.targetFrom d.source (d.layers.take (h + 1)) with
      | some before, some after =>
        match (cond k.removes before after)[o + 2]? with
        | some f =>
          let d' : Diagram S.Pt S.Ed S.Ce :=
            ⟨d.source, d.layers.take h ++ (.unitor k.toLeft f, o + 1) :: rest⟩
          if (S.target d').isSome then some d' else none
        | none => none
      | _, _ => none
    else none
  | _ => none

def slideData (k : UnitorKind) (e : Edge S.Pt S.Ed) (q p : ℕ) (s t : List (Edge S.Pt S.Ed)) :
    Option (Edge S.Pt S.Ed × ℕ × ℕ) :=
  match k with
  | .leftInverse => if q = p ∧ some e = t.head? then s.head?.map (·, p, p + 1) else none
  | .rightInverse => if q + 1 = p + t.length ∧ some e = t.getLast? then
      s.getLast?.map (·, p + s.length - 1, p) else none
  | .left => if q + 1 = p ∧ some e = t.head? then s.head?.map (·, p - 1, p - 1) else none
  | .right => if q + 1 = p + t.length ∧ some e = t.getLast? then
      s.getLast?.map (·, p + s.length - 1, p) else none

def slide (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ) : Option (Diagram S.Pt S.Ed S.Ce) :=
  match d.layers.drop h with
  | (g, p) :: (.unitor k e, q) :: rest =>
    match S.slideData k e q p (S.cellType g).1 (S.cellType g).2 with
    | some (f, uo, go) =>
      let d' : Diagram S.Pt S.Ed S.Ce :=
        ⟨d.source, d.layers.take h ++ (.unitor k f, uo) :: (g, go) :: rest⟩
      if (S.target d').isSome ∧ S.target d' = S.target d then some d' else none
    | none => none
  | _ => none

def unitApply : UnitMove → Diagram S.Pt S.Ed S.Ce → ℕ → Option (Diagram S.Pt S.Ed S.Ce)
  | .cancel => S.cancel
  | .trade => S.trade
  | .slide => S.slide

end Signature

namespace RelSignature

variable (S : RelSignature.{v})

def completeSide (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (α : Bool) (h o : ℕ) :
    Diagram S.Pt S.Ed S.Ce :=
  if (S.side r α).layers = [] then
    ⟨d.source, d.layers.take h ++ (.unit (S.side r α).source, o) :: d.layers.drop h⟩
  else d

theorem eraseUnits_completeSide {d : Diagram S.Pt S.Ed S.Ce}
    (hd : ∀ l ∈ d.layers, l.1.isUnit = false) (r : S.Rel) (α : Bool) (h o : ℕ) :
    (S.completeSide d r α h o).eraseUnits = d := by
  have hf : ∀ ls : List (Cell S.Pt S.Ed S.Ce × ℕ), (∀ l ∈ ls, l.1.isUnit = false) →
      ls.filter (fun l => !l.1.isUnit) = ls := fun ls h =>
    List.filter_eq_self.2 fun l hl => by simp [h l hl]
  have hu : (Cell.unit (S.side r α).source : Cell S.Pt S.Ed S.Ce).isUnit = true := rfl
  rw [completeSide]
  split_ifs
  · simp only [Diagram.eraseUnits, List.filter_append, List.filter_cons, hu, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    rw [hf _ fun l hl => hd l (List.mem_of_mem_take hl),
      hf _ fun l hl => hd l (List.mem_of_mem_drop hl), List.take_append_drop]
  · exact congrArg (Diagram.mk d.source) (hf _ hd)

variable [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

inductive Link : Diagram S.Pt S.Ed S.Ce → Diagram S.Pt S.Ed S.Ce → Type v
  | relation (r : S.Rel) (h o : ℕ) {d d' : Diagram S.Pt S.Ed S.Ce}
      (hd : S.relationApply d r h o = some d') : Link d d'
  | relationBackward (r : S.Rel) (h o : ℕ) {d d' : Diagram S.Pt S.Ed S.Ce}
      (hinv : S.invertible r = true) (hd : S.relationApply d' r h o = some d) : Link d d'
  | identification (h : ℕ) {d d' : Diagram S.Pt S.Ed S.Ce} (hd : S.swap d h = some d') :
      Link d d'
  | unit (m : UnitMove) (forward : Bool) (h : ℕ) {d d' : Diagram S.Pt S.Ed S.Ce}
      (hd : cond forward (S.unitApply m d h) (S.unitApply m d' h) = some (cond forward d' d)) :
      Link d d'

inductive RewriteChain : Diagram S.Pt S.Ed S.Ce → Diagram S.Pt S.Ed S.Ce → Type v
  | refl (d : Diagram S.Pt S.Ed S.Ce) : RewriteChain d d
  | cons {d d' d'' : Diagram S.Pt S.Ed S.Ce} : S.Link d d' → RewriteChain d' d'' →
      RewriteChain d d''

variable {S}

theorem isSome_target_and_source_of_relationApply {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ}
    (hd : S.relationApply d r h o = some d') :
    (S.target d).isSome ∧ (S.target d').isSome ∧ d'.source = d.source := by
  unfold relationApply at hd
  split at hd
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
  · split_ifs at hd with h₁
    · simp only at hd
      split_ifs at hd with h₂
      obtain rfl := Option.some.inj hd
      exact ⟨h₁.1, h₂, rfl⟩

omit [DecidableEq S.Ce] in
theorem isSome_target_and_source_of_swap {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.swap d h = some d') : (S.target d').isSome ∧ d'.source = d.source := by
  rw [Signature.swap] at hd
  split at hd
  · obtain ⟨n, -, hd⟩ := Option.bind_eq_some_iff.1 hd
    split_ifs at hd with hc
    obtain rfl := Option.some.inj hd
    exact ⟨hc, rfl⟩
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

end RelSignature

namespace Signature

variable {S : Signature.{v}} {X : DiagSet.{u}}

namespace Interp

variable [DecidableEq S.Pt] (I : S.Interp X) [DecidableEq S.Ed]

omit [DecidableEq S.Ed] in
private theorem hasRoundType_cellDiagram_of_eq (hS : S.WellFormed) (x : PastingDiagram X)
    {c : Cell S.Pt S.Ed S.Ce} {s t : List (Edge S.Pt S.Ed)} (hc : S.cellType c = (s, t))
    {a b : S.Pt} (hs : S.pathEnds s = some (a, b)) :
    ∃ ht : S.pathEnds t = some (a, b), HasRoundType (I.cellDiagram x c)
      (I.pathRound s (S.isPath_of_pathEnds hs)) (I.pathRound t (S.isPath_of_pathEnds ht)) := by
  have hs' : S.IsPath (S.cellType c).1 := by rw [hc]; exact S.isPath_of_pathEnds hs
  have ht : S.pathEnds t = some (a, b) := by
    have := S.pathEnds_cellType_snd hS c
    rw [hc] at this
    exact this.trans hs
  refine ⟨ht, (I.hasRoundType_cellDiagram hS x hs').of_equiv ?_ ?_⟩ <;>
    exact PastingDiagram.equiv_of_eq (I.path_congr (by rw [hc]) _ _)

private theorem equiv_two_layers (hS : S.WellFormed) {cl cr : Cell S.Pt S.Ed S.Ce}
    {Sl Tl Sr Tr M : List (Edge S.Pt S.Ed)} (hcl : S.cellType cl = (Sl, Tl))
    (hcr : S.cellType cr = (Sr, Tr)) {a m₁ m₂ b : S.Pt} (hl : S.pathEnds Sl = some (a, m₁))
    (hM : S.walk m₁ M = some m₂) (hr : S.pathEnds Sr = some (m₂, b))
    (hne : Sl ++ M ++ Sr ≠ []) :
    (I.diagram ⟨Sl ++ M ++ Sr, [(cr, Sl.length + M.length), (cl, 0)]⟩ hne).Equiv
      (I.diagram ⟨Sl ++ M ++ Sr, [(cl, 0), (cr, Tl.length + M.length)]⟩ hne) := by
  let j := (I.pathCons (.unit a) []).unit
  obtain ⟨htl, hxl⟩ := I.hasRoundType_cellDiagram_of_eq hS j hcl hl
  obtain ⟨htr, hxr⟩ := I.hasRoundType_cellDiagram_of_eq hS j hcr hr
  have hSl := S.isPath_of_pathEnds hl
  have hSr := S.isPath_of_pathEnds hr
  have hTl := S.isPath_of_pathEnds htl
  have hTr := S.isPath_of_pathEnds htr
  have hcl₁ : (S.cellType cl).1 ≠ [] := by rw [hcl]; exact hSl.ne_nil
  have hcr₁ : (S.cellType cr).1 ≠ [] := by rw [hcr]; exact hSr.ne_nil
  have hxs := (I.spans_of_hasRoundType (I.hasRoundType_path _ hl)).of_hasRoundType hxl
  have ap₁ : S.applyLayer (Sl ++ M ++ Sr) cr (Sl.length + M.length) = some (Sl ++ M ++ Tr) :=
    S.applyLayer_eq_some_iff.2 ⟨hcr₁, Sl ++ M, [], by simp [hcr], by simp, by simp [hcr]⟩
  have ap₂ : S.applyLayer (Sl ++ M ++ Tr) cl 0 = some (Tl ++ M ++ Tr) :=
    S.applyLayer_eq_some_iff.2 ⟨hcl₁, [], M ++ Tr, by simp [hcl], rfl, by simp [hcl]⟩
  have ap₃ : S.applyLayer (Sl ++ M ++ Sr) cl 0 = some (Tl ++ M ++ Sr) :=
    S.applyLayer_eq_some_iff.2 ⟨hcl₁, [], M ++ Sr, by simp [hcl], rfl, by simp [hcl]⟩
  have ap₄ : S.applyLayer (Tl ++ M ++ Sr) cr (Tl.length + M.length) = some (Tl ++ M ++ Tr) :=
    S.applyLayer_eq_some_iff.2 ⟨hcr₁, Tl ++ M, [], by simp [hcr], by simp, by simp [hcr]⟩
  have hp₀ : S.pathEnds (Sl ++ M ++ Sr) = some (a, b) := by
    refine S.pathEnds_eq_some_iff.2 ⟨hne, ?_⟩
    rw [S.walk_append, S.walk_append, (S.pathEnds_eq_some_iff.1 hl).2, Option.bind_some, hM,
      Option.bind_some, (S.pathEnds_eq_some_iff.1 hr).2]
  have hpath := S.isPath_of_pathEnds hp₀
  have hpath₁ := S.isPath_of_pathEnds (S.pathEnds_applyLayer hS ap₁ hp₀)
  have hpath₃ := S.isPath_of_pathEnds (S.pathEnds_applyLayer hS ap₃ hp₀)
  have eq₁ := I.diagram_singleton (l := (cr, Sl.length + M.length)) hpath.ne_nil
    (L := Sl ++ M) (R := []) (by simp [hcr]) (by simp) hcr₁ j
  have eq₂ := I.diagram_singleton (l := (cl, 0)) hpath₁.ne_nil (L := []) (R := M ++ Tr)
    (by simp [hcl]) rfl hcl₁ j
  have eq₃ := I.diagram_singleton (l := (cl, 0)) hpath.ne_nil (L := []) (R := M ++ Sr)
    (by simp [hcl]) rfl hcl₁ j
  have eq₄ := I.diagram_singleton (l := (cr, Tl.length + M.length)) hpath₃.ne_nil
    (L := Tl ++ M) (R := []) (by simp [hcr]) (by simp) hcr₁ j
  simp only [PathInterp.whisker_nil] at eq₁ eq₂ eq₃ eq₄
  obtain ⟨hc, e⟩ := I.equiv_diagram_append hS (d := ⟨Sl ++ M ++ Sr, [(cr, Sl.length + M.length)]⟩)
    (d' := ⟨Sl ++ M ++ Tr, [(cl, 0)]⟩) (S.target_singleton hpath ap₁) rfl hpath.ne_nil
    hpath₁.ne_nil (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (by rw [S.target_singleton hpath₁ ap₂]; rfl)
  obtain ⟨hc', e'⟩ := I.equiv_diagram_append hS (d := ⟨Sl ++ M ++ Sr, [(cl, 0)]⟩)
    (d' := ⟨Tl ++ M ++ Sr, [(cr, Tl.length + M.length)]⟩) (S.target_singleton hpath ap₃) rfl
    hpath.ne_nil hpath₃.ne_nil (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (by rw [S.target_singleton hpath₃ ap₄]; rfl)
  have hy := I.hasRoundType_whisker true hl htl hxl (c := m₂) hM
  have hy' : HasRoundType (I.whisker true M (I.cellDiagram j cl))
      (I.pathRound (Sl ++ M) (S.isPath_of_pathEnds (S.pathEnds_whisker true hl hM)))
      (I.pathRound (Tl ++ M) (S.isPath_of_pathEnds (S.pathEnds_whisker true htl hM))) := hy
  obtain ⟨h₁, h₂, ei⟩ := I.exists_whisker_interchange (S.pathEnds_whisker true hl hM)
    (S.pathEnds_whisker true htl hM) hr htr hy' hxr
  have wT := I.whisker_append true hxs (c := b) (w₁ := M) (w₂ := Tr) (by
    simp only [cond_true]
    rw [S.walk_append, hM, Option.bind_some]; exact (S.pathEnds_eq_some_iff.1 htr).2)
  have wS := I.whisker_append true hxs (c := b) (w₁ := M) (w₂ := Sr) (by
    simp only [cond_true]
    rw [S.walk_append, hM, Option.bind_some]; exact (S.pathEnds_eq_some_iff.1 hr).2)
  have ed₁ := PastingDiagram.equiv_of_eq eq₁
  have ed₂ := (PastingDiagram.equiv_of_eq eq₂).trans wT
  have ed₃ := (PastingDiagram.equiv_of_eq eq₃).trans wS
  have ed₄ := PastingDiagram.equiv_of_eq eq₄
  exact (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans (e.trans
    ((Equiv.paste ed₁ ed₂ hc h₁).trans (ei.trans ((Equiv.paste ed₃ ed₄ hc' h₂).symm.trans
      (e'.symm.trans (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)))))))

private theorem exists_middle {α : Type v} {A B C D : List α} (h : A ++ B = C ++ D)
    (hl : A.length ≤ C.length) : ∃ M, C = A ++ M ∧ B = M ++ D := by
  rcases List.append_eq_append_iff.1 h with ⟨M, hC, hB⟩ | ⟨M, hA, hD⟩
  · exact ⟨M, hC, hB⟩
  · have hM : M = [] := by
      have := congrArg List.length hA
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hM
    simp only [List.append_nil, List.nil_append] at hA hD
    exact ⟨[], by simp [hA], hD.symm⟩

theorem equiv_diagram_whisker_whisker (hS : S.WellFormed) {L R s q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} {a x y b : S.Pt} (hs : S.pathEnds s = some (x, y))
    (hL : S.walk a L = some x) (hR : S.walk y R = some b) (hl : ls ≠ [])
    (ht : S.targetFrom s ls = some q)
    (hne : (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls⟩)).source ≠ []) :
    (I.diagram (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls⟩)) hne).Equiv
      (I.whisker false L (I.whisker true R
        (I.diagram ⟨s, ls⟩ (S.isPath_of_pathEnds hs).ne_nil))) := by
  have hsR : S.pathEnds (s ++ R) = some (x, b) := S.pathEnds_whisker true hs hR
  have ht₁ : S.targetFrom (s ++ R) ls = some (q ++ R) := S.targetFrom_whisker true R ht
  have ht₂ : S.target ⟨s ++ R, ls⟩ = some (q ++ R) :=
    S.target_mk_of_targetFrom (S.isPath_of_pathEnds hsR) ht₁
  have e₁ := I.equiv_diagram_whisker hS false (p := s ++ R) (ls := ls) hsR hl ht₁ (c := a) hL hne
  have hsp := (I.spans_of_hasRoundType (I.hasRoundType_path _ hsR)).of_hasRoundType
    (I.hasRoundType_diagram hS ht₂ (S.isPath_of_pathEnds hsR).ne_nil)
  exact (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans (e₁.trans
    (I.whisker_equiv false hsp (I.equiv_diagram_whisker hS true (p := s) hs hl ht hR _) hL))

private theorem equiv_whisker_whisker (hS : S.WellFormed) {L R s q : List (Edge S.Pt S.Ed)}
    {ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)} {a x y b : S.Pt} (hs : S.pathEnds s = some (x, y))
    (hL : S.walk a L = some x) (hR : S.walk y R = some b) (hl : ls ≠ []) (hl' : ls' ≠ [])
    (ht : S.targetFrom s ls = some q) (ht' : S.targetFrom s ls' = some q)
    (e : (I.diagram ⟨s, ls⟩ (S.isPath_of_pathEnds hs).ne_nil).Equiv
      (I.diagram ⟨s, ls'⟩ (S.isPath_of_pathEnds hs).ne_nil))
    (hne : (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls⟩)).source ≠ []) :
    (I.diagram (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls⟩)) hne).Equiv
      (I.diagram (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls'⟩)) hne) := by
  have hpath := S.isPath_of_pathEnds hs
  have key : ∀ {ls₀ : List (Cell S.Pt S.Ed S.Ce × ℕ)}, ls₀ ≠ [] → S.targetFrom s ls₀ = some q →
      (I.diagram (Diagram.whisker false L (Diagram.whisker true R ⟨s, ls₀⟩)) hne).Equiv
        (I.whisker false L (I.whisker true R (I.diagram ⟨s, ls₀⟩ hpath.ne_nil))) :=
    fun hl₀ ht₀ => I.equiv_diagram_whisker_whisker hS hs hL hR hl₀ ht₀ hne
  have hsp := (I.spans_of_hasRoundType (I.hasRoundType_path _ hs)).of_hasRoundType
    (I.hasRoundType_diagram hS (d := ⟨s, ls⟩) (S.target_mk_of_targetFrom hpath ht)
      hpath.ne_nil)
  refine (key hl ht).trans ((I.whisker_equiv false (hsp.whisker true hR)
    (I.whisker_equiv true hsp e hR) hL).trans (key hl' ht').symm)

theorem equiv_diagram_swapLayers (hS : S.WellFormed) {p q : List (Edge S.Pt S.Ed)} {a b : S.Pt}
    (hp : S.pathEnds p = some (a, b)) {l₁ l₂ : Cell S.Pt S.Ed S.Ce × ℕ}
    {n : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p [l₁, l₂] = some q)
    (hn : S.swapLayers l₁ l₂ = some n) :
    S.targetFrom p n = some q ∧ (I.diagram ⟨p, [l₁, l₂]⟩ (S.isPath_of_pathEnds hp).ne_nil).Equiv
      (I.diagram ⟨p, n⟩ (S.isPath_of_pathEnds hp).ne_nil) := by
  obtain ⟨c₁, o₁⟩ := l₁
  obtain ⟨c₂, o₂⟩ := l₂
  obtain ⟨p₁, ap₁, h₂⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p₂, ap₂, h₃⟩ := Option.bind_eq_some_iff.1 h₂
  obtain rfl : p₂ = q := Option.some.inj h₃
  rw [swapLayers] at hn
  dsimp only at ap₁ ap₂ hn
  have hpath := S.isPath_of_pathEnds hp
  have hp₁' := S.pathEnds_applyLayer hS ap₁ hp
  obtain ⟨hne₁, L₁, R₁, rfl, hL₁, rfl⟩ := S.applyLayer_eq_some_iff.1 ap₁
  obtain ⟨hne₂, L₂, R₂, hp₁, hL₂, rfl⟩ := S.applyLayer_eq_some_iff.1 ap₂
  generalize hc₁ : S.cellType c₁ = st₁ at hne₁ hL₁ hp₁ hn hp hpath hp₁' ⊢
  generalize hc₂ : S.cellType c₂ = st₂ at hne₂ hL₂ hp₁ hn ⊢
  obtain ⟨S₁, T₁⟩ := st₁
  obtain ⟨S₂, T₂⟩ := st₂
  dsimp only at hne₁ hne₂ hL₁ hL₂ hp₁ hn hp hpath hp₁' ⊢
  split_ifs at hn with hcase₁ hcase₂
  · obtain rfl := (Option.some.inj hn).symm
    obtain ⟨M, rfl, rfl⟩ := exists_middle (A := L₂ ++ S₂) (B := R₂) (C := L₁)
      (D := T₁ ++ R₁) (by simpa only [List.append_assoc] using hp₁.symm)
      (by simp only [List.length_append]; omega)
    have hs : S.pathEnds (L₂ ++ (S₂ ++ M ++ S₁) ++ R₁) = some (a, b) := by
      simpa only [List.append_assoc] using hp
    obtain ⟨x, y, hLw, hsw, hRw⟩ := S.exists_walk_of_split hs (by simp [hne₂])
    obtain ⟨x', m₁, hx', hS₂, hMS⟩ := S.exists_walk_of_split (L := []) (s := S₂) (R := M ++ S₁)
      (by simpa only [List.nil_append, List.append_assoc] using hsw) hne₂
    obtain rfl : x = x' := Option.some.inj hx'
    obtain ⟨m₂, hMw, hS₁w⟩ := S.walk_append_eq_some hMS
    have hS₁ : S.pathEnds S₁ = some (m₂, y) := S.pathEnds_eq_some_iff.2 ⟨hne₁, hS₁w⟩
    have hne₀ : S₂ ++ M ++ S₁ ≠ [] := by simp [hne₂]
    have e := I.equiv_two_layers hS hc₂ hc₁ hS₂ hMw hS₁ hne₀
    have ap₁' : S.applyLayer (S₂ ++ M ++ S₁) c₁ (S₂.length + M.length) = some (S₂ ++ M ++ T₁) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₁, hne₁], S₂ ++ M, [], by simp [hc₁], by simp,
        by simp [hc₁]⟩
    have ap₂' : S.applyLayer (S₂ ++ M ++ T₁) c₂ 0 = some (T₂ ++ M ++ T₁) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₂, hne₂], [], M ++ T₁, by simp [hc₂], rfl,
        by simp [hc₂]⟩
    have ap₃' : S.applyLayer (S₂ ++ M ++ S₁) c₂ 0 = some (T₂ ++ M ++ S₁) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₂, hne₂], [], M ++ S₁, by simp [hc₂], rfl,
        by simp [hc₂]⟩
    have ap₄' : S.applyLayer (T₂ ++ M ++ S₁) c₁ (T₂.length + M.length) = some (T₂ ++ M ++ T₁) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₁, hne₁], T₂ ++ M, [], by simp [hc₁], by simp,
        by simp [hc₁]⟩
    have ht : S.targetFrom (S₂ ++ M ++ S₁) [(c₁, S₂.length + M.length), (c₂, 0)] =
        some (T₂ ++ M ++ T₁) := by
      simp only [targetFrom, ap₁', ap₂', Option.bind_some]
    have ht' : S.targetFrom (S₂ ++ M ++ S₁) [(c₂, 0), (c₁, T₂.length + M.length)] =
        some (T₂ ++ M ++ T₁) := by
      simp only [targetFrom, ap₃', ap₄', Option.bind_some]
    have hd₁ : Diagram.whisker false L₂ (Diagram.whisker true R₁
        ⟨S₂ ++ M ++ S₁, [(c₁, S₂.length + M.length), (c₂, 0)]⟩) =
        ⟨L₂ ++ S₂ ++ M ++ S₁ ++ R₁, [(c₁, o₁), (c₂, o₂)]⟩ := by
      simp only [Diagram.whisker, cond_true, cond_false, List.map_cons, List.map_nil,
        List.append_assoc, Diagram.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      simp only [List.length_append] at hL₁
      omega
    have hd₂ : Diagram.whisker false L₂ (Diagram.whisker true R₁
        ⟨S₂ ++ M ++ S₁, [(c₂, 0), (c₁, T₂.length + M.length)]⟩) =
        ⟨L₂ ++ S₂ ++ M ++ S₁ ++ R₁, [(c₂, o₂), (c₁, o₁ + T₂.length - S₂.length)]⟩ := by
      simp only [Diagram.whisker, cond_true, cond_false, List.map_cons, List.map_nil,
        List.append_assoc, Diagram.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      simp only [List.length_append] at hL₁
      omega
    have hne' : (Diagram.whisker false L₂ (Diagram.whisker true R₁
        ⟨S₂ ++ M ++ S₁, [(c₁, S₂.length + M.length), (c₂, 0)]⟩)).source ≠ [] := by
      rw [hd₁]; exact hpath.ne_nil
    refine ⟨?_, (PastingDiagram.equiv_of_eq (I.diagram_congr hd₁.symm _ hne')).trans
      ((I.equiv_whisker_whisker hS hsw hLw hRw (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) ht
        ht' e hne').trans (PastingDiagram.equiv_of_eq (I.diagram_congr hd₂ _ _)))⟩
    have := S.targetFrom_whisker false L₂ (S.targetFrom_whisker true R₁ ht')
    rw [hd₂] at this
    simpa only [List.append_assoc, cond_true, cond_false] using this
  · obtain rfl := (Option.some.inj hn).symm
    obtain ⟨M, rfl, rfl⟩ := exists_middle (A := L₁ ++ T₁) (B := R₁) (C := L₂)
      (D := S₂ ++ R₂) (by simpa only [List.append_assoc] using hp₁)
      (by simp only [List.length_append]; omega)
    have hs : S.pathEnds (L₁ ++ (S₁ ++ M ++ S₂) ++ R₂) = some (a, b) := by
      simpa only [List.append_assoc] using hp
    obtain ⟨x, y, hLw, hsw, hRw⟩ := S.exists_walk_of_split hs (by simp [hne₁])
    obtain ⟨x', m₁, hx', hS₁, hMS⟩ := S.exists_walk_of_split (L := []) (s := S₁) (R := M ++ S₂)
      (by simpa only [List.nil_append, List.append_assoc] using hsw) hne₁
    obtain rfl : x = x' := Option.some.inj hx'
    obtain ⟨m₂, hMw, hS₂w⟩ := S.walk_append_eq_some hMS
    have hS₂ : S.pathEnds S₂ = some (m₂, y) := S.pathEnds_eq_some_iff.2 ⟨hne₂, hS₂w⟩
    have hne₀ : S₁ ++ M ++ S₂ ≠ [] := by simp [hne₁]
    have e := (I.equiv_two_layers hS hc₁ hc₂ hS₁ hMw hS₂ hne₀).symm
    have ap₁' : S.applyLayer (S₁ ++ M ++ S₂) c₁ 0 = some (T₁ ++ M ++ S₂) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₁, hne₁], [], M ++ S₂, by simp [hc₁], rfl,
        by simp [hc₁]⟩
    have ap₂' : S.applyLayer (T₁ ++ M ++ S₂) c₂ (T₁.length + M.length) = some (T₁ ++ M ++ T₂) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₂, hne₂], T₁ ++ M, [], by simp [hc₂], by simp,
        by simp [hc₂]⟩
    have ap₃' : S.applyLayer (S₁ ++ M ++ S₂) c₂ (S₁.length + M.length) = some (S₁ ++ M ++ T₂) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₂, hne₂], S₁ ++ M, [], by simp [hc₂], by simp,
        by simp [hc₂]⟩
    have ap₄' : S.applyLayer (S₁ ++ M ++ T₂) c₁ 0 = some (T₁ ++ M ++ T₂) :=
      S.applyLayer_eq_some_iff.2 ⟨by simp [hc₁, hne₁], [], M ++ T₂, by simp [hc₁], rfl,
        by simp [hc₁]⟩
    have ht : S.targetFrom (S₁ ++ M ++ S₂) [(c₁, 0), (c₂, T₁.length + M.length)] =
        some (T₁ ++ M ++ T₂) := by
      simp only [targetFrom, ap₁', ap₂', Option.bind_some]
    have ht' : S.targetFrom (S₁ ++ M ++ S₂) [(c₂, S₁.length + M.length), (c₁, 0)] =
        some (T₁ ++ M ++ T₂) := by
      simp only [targetFrom, ap₃', ap₄', Option.bind_some]
    have hd₁ : Diagram.whisker false L₁ (Diagram.whisker true R₂
        ⟨S₁ ++ M ++ S₂, [(c₁, 0), (c₂, T₁.length + M.length)]⟩) =
        ⟨L₁ ++ S₁ ++ (M ++ (S₂ ++ R₂)), [(c₁, o₁), (c₂, o₂)]⟩ := by
      simp only [Diagram.whisker, cond_true, cond_false, List.map_cons, List.map_nil,
        List.append_assoc, Diagram.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      simp only [List.length_append] at hL₂
      omega
    have hd₂ : Diagram.whisker false L₁ (Diagram.whisker true R₂
        ⟨S₁ ++ M ++ S₂, [(c₂, S₁.length + M.length), (c₁, 0)]⟩) =
        ⟨L₁ ++ S₁ ++ (M ++ (S₂ ++ R₂)), [(c₂, o₂ - T₁.length + S₁.length), (c₁, o₁)]⟩ := by
      simp only [Diagram.whisker, cond_true, cond_false, List.map_cons, List.map_nil,
        List.append_assoc, Diagram.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      simp only [List.length_append] at hL₂
      omega
    have hne' : (Diagram.whisker false L₁ (Diagram.whisker true R₂
        ⟨S₁ ++ M ++ S₂, [(c₁, 0), (c₂, T₁.length + M.length)]⟩)).source ≠ [] := by
      rw [hd₁]; exact hpath.ne_nil
    refine ⟨?_, (PastingDiagram.equiv_of_eq (I.diagram_congr hd₁.symm _ hne')).trans
      ((I.equiv_whisker_whisker hS hsw hLw hRw (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) ht
        ht' e hne').trans (PastingDiagram.equiv_of_eq (I.diagram_congr hd₂ _ _)))⟩
    have := S.targetFrom_whisker false L₁ (S.targetFrom_whisker true R₂ ht')
    rw [hd₂] at this
    simpa only [List.append_assoc, cond_true, cond_false] using this

omit [DecidableEq S.Pt] [DecidableEq S.Ed] in
private theorem ne_nil_of_swapLayers {l₁ l₂ : Cell S.Pt S.Ed S.Ce × ℕ}
    {n : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hn : S.swapLayers l₁ l₂ = some n) : n ≠ [] := by
  rw [swapLayers] at hn
  split_ifs at hn <;> (obtain rfl := (Option.some.inj hn).symm; exact List.cons_ne_nil _ _)

theorem equiv_diagram_swap (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.swap d h = some d') {q : List (Edge S.Pt S.Ed)} (ht : S.target d = some q)
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) :
    (I.diagram d hsrc).Equiv (I.diagram d' hsrc') := by
  obtain ⟨l₁, l₂, rest, n, hdrop, hn, rfl⟩ := S.eq_of_swap_eq_some hd
  obtain ⟨s, ls⟩ := d
  dsimp only at hdrop hsrc hsrc' ⊢
  have hls : ls = ls.take h ++ [l₁, l₂] ++ rest := by
    rw [List.append_assoc]
    exact (List.take_append_drop h ls).symm.trans (congrArg _ hdrop)
  have hpath := S.isPath_source_of_target ht
  rw [target, if_pos hpath] at ht
  dsimp only at ht hpath
  rw [hls, S.targetFrom_append, S.targetFrom_append] at ht
  obtain ⟨p₂, h₁, h₃⟩ := Option.bind_eq_some_iff.1 ht
  obtain ⟨p, hA, h₂⟩ := Option.bind_eq_some_iff.1 h₁
  obtain ⟨x, z, hs⟩ := S.exists_pathEnds_of_isPath hpath
  have hp := S.pathEnds_targetFrom hS hA hs
  obtain ⟨ht', e⟩ := I.equiv_diagram_swapLayers hS hp h₂ hn
  refine (PastingDiagram.equiv_of_eq (I.diagram_congr (congrArg (Diagram.mk s) hls) _ _)).trans
    ((I.equiv_diagram_attach hS hpath hA h₂ (by rw [h₃]; rfl) (List.cons_ne_nil _ _)).trans ?_)
  exact (I.attach_equiv true _ _ (I.attach_equiv false _ _ e)).trans
    (I.equiv_diagram_attach hS hpath hA ht' (by rw [h₃]; rfl) (ne_nil_of_swapLayers hn)).symm

end Interp

end Signature

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] {hS : S.WellFormed}
  {X : DiagSet.{u}}

namespace Interp

variable (I : S.Interp hS X)

noncomputable def relationStep (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (h o : ℕ) :
    PastingDiagram X :=
  match S.targetFrom d.source (d.layers.take h),
    S.targetFrom d.source (d.layers.take (h + (S.relSource r).layers.length)) with
  | some p, some p₂ =>
    I.toInterp.attach true p₂ (d.layers.drop (h + (S.relSource r).layers.length))
      (I.toInterp.attach false d.source (d.layers.take h)
        (I.whisker false (p.take o) (I.whisker true (p.drop (o + (S.relSource r).source.length))
          (PastingDiagram.ofCell (I.rel r).2))))
  | _, _ => PastingDiagram.ofCell (I.rel r).2

variable [DecidableEq S.Ce]

private theorem relationStep_spec {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') :
    (I.relationStep d r h o).dim = 3 ∧
      ∀ β (hc : (S.completeSide (cond β d' d) r β h o).source ≠ []),
        ((I.relationStep d r h o).boundary 2 β).Equiv
          (I.diagram (S.completeSide (cond β d' d) r β h o) hc) := by
  let J := I.toInterp
  obtain ⟨htd, hlen⟩ : (S.target d).isSome ∧
      h + (S.relSource r).layers.length ≤ d.layers.length := by
    rw [relationApply] at hd
    split at hd
    · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
    split_ifs at hd with hc
    exact ⟨hc.1, hc.2.1⟩
  obtain ⟨L, R, hp, hL, hdd⟩ := S.exists_eq_of_relationApply_eq_some hS hd
  obtain rfl : d' = _ := hdd true
  have hdl : d.layers = d.layers.take h ++ (S.relSource r).layers.map (fun l => (l.1, l.2 + o)) ++
      d.layers.drop (h + (S.relSource r).layers.length) := congrArg Diagram.layers (hdd false)
  have hAl : (d.layers.take h).length = h := by
    simp only [List.length_take]
    omega
  have hseg : (d.layers.drop h).take (S.relSource r).layers.length =
      (S.relSource r).layers.map (fun l => (l.1, l.2 + o)) := by
    conv_lhs => rw [hdl]
    simp [hAl]
  have hpsrc := isPath_source_side hS r
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  have hpd : S.IsPath d.source := by
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 htd
    exact S.isPath_source_of_target hq'
  obtain ⟨a, b, hab⟩ := S.exists_pathEnds_of_isPath hpd
  have hpe := S.pathEnds_targetFrom hS.1 hp hab
  obtain ⟨x, y, hLw, hsxy, hRw⟩ := S.exists_walk_of_split hpe hpsrc.ne_nil
  have hLt : (L ++ (S.relSource r).source ++ R).take o = L := by
    subst hL
    simp
  have hRt : (L ++ (S.relSource r).source ++ R).drop (o + (S.relSource r).source.length) = R := by
    subst hL
    simp [List.drop_append, List.drop_eq_nil_of_le]
  have hside : ∀ β, S.targetFrom (S.relSource r).source (S.side r β).layers = some q := fun β => by
    have := (target_side hS r β).trans hq
    rw [Signature.target, if_pos (by rw [source_side hS]; exact hpsrc), source_side hS] at this
    exact this
  have hmid : ∀ β, ∃ M : List (Cell S.Pt S.Ed S.Ce × ℕ), M ≠ [] ∧
      S.targetFrom (L ++ (S.relSource r).source ++ R) M = some (L ++ q ++ R) ∧
      (∀ hM, (J.diagram ⟨L ++ (S.relSource r).source ++ R, M⟩ hM).Equiv
        (J.whisker false L (J.whisker true R (sideRound J hS r β).toPastingDiagram))) ∧
      S.completeSide (cond β ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ d) r β h o =
        ⟨d.source, d.layers.take h ++ M ++ d.layers.drop (h + (S.relSource r).layers.length)⟩ := by
    intro β
    have hsrcβ := source_side hS r β
    have heta : S.side r β = ⟨(S.relSource r).source, (S.side r β).layers⟩ := by
      have : S.side r β = ⟨(S.side r β).source, (S.side r β).layers⟩ := rfl
      rw [hsrcβ] at this
      exact this
    have hap' : S.applyLayer (L ++ (S.relSource r).source ++ R) (.unit (S.relSource r).source) o =
        some (L ++ (S.relSource r).source ++ R) :=
      S.applyLayer_eq_some_iff.2 ⟨hpsrc.ne_nil, L, R, rfl, hL, rfl⟩
    by_cases hl : (S.side r β).layers = []
    · have hqs : q = (S.relSource r).source := by
        have := hside β
        rw [hl] at this
        exact (Option.some.inj this).symm
      subst hqs
      refine ⟨[(.unit (S.relSource r).source, o)], List.cons_ne_nil _ _, ?_, fun hM => ?_, ?_⟩
      · simp only [Signature.targetFrom, hap', Option.bind_some]
      · rw [J.diagram_singleton hM rfl hL (by exact hpsrc.ne_nil) (J.pathCons (.unit a) []).unit]
        obtain ⟨e, q', he⟩ := List.exists_cons_of_ne_nil hpsrc.ne_nil
        have h₁ : J.cellDiagram (J.pathCons (.unit a) []).unit (.unit (S.relSource r).source) =
            (J.pathCons e q').unit := by
          rw [he]
          rfl
        have h₂ : (sideRound J hS r β).toPastingDiagram = (J.pathCons e q').unit := by
          exact (J.diagram_congr (d' := ⟨e :: q', []⟩) (heta.trans (by rw [hl, he])) _
            (List.cons_ne_nil e q')).trans rfl
        rw [h₁, h₂]
      · cases β
        · rw [completeSide, if_pos hl]
          simp only [side, cond_false] at hl ⊢
          simp only [hl, List.length_nil, Nat.add_zero, List.append_assoc,
            List.singleton_append]
        · rw [completeSide, if_pos hl]
          simp only [side, cond_true] at hl ⊢
          simp only [hl, List.map_nil, List.append_nil, List.take_left' hAl,
            List.drop_left' hAl, (hS.2 r).source_eq, List.append_assoc, List.singleton_append]
    · have hw : (⟨L ++ (S.relSource r).source ++ R, (S.side r β).layers.map
          (fun l => (l.1, l.2 + o))⟩ : Diagram S.Pt S.Ed S.Ce) = Diagram.whisker false L
            (Diagram.whisker true R ⟨(S.relSource r).source, (S.side r β).layers⟩) := by
        subst hL
        simp [Diagram.whisker]
      refine ⟨(S.side r β).layers.map (fun l => (l.1, l.2 + o)), by simpa using hl, ?_,
        fun hM => ?_, ?_⟩
      · have := S.targetFrom_whisker false L (S.targetFrom_whisker true R (hside β))
        rw [← hw] at this
        simpa only [List.append_assoc, cond_true, cond_false] using this
      · have hne : (Diagram.whisker false L (Diagram.whisker true R
            ⟨(S.relSource r).source, (S.side r β).layers⟩)).source ≠ [] := by
          rw [← hw]; exact hM
        refine (PastingDiagram.equiv_of_eq (J.diagram_congr hw _ hne)).trans
          ((J.equiv_diagram_whisker_whisker hS.1 hsxy hLw hRw hl (hside β) hne).trans ?_)
        exact PastingDiagram.equiv_of_eq (congrArg (fun z => J.whisker false L (J.whisker true R z))
          (J.diagram_congr heta.symm _ _))
      · cases β
        · rw [completeSide, if_neg hl]
          simp only [side, cond_false] at hl ⊢
          rw [← hdl]
        · rw [completeSide, if_neg hl]
          rfl
  have hshift : S.targetFrom (L ++ (S.relSource r).source ++ R)
      ((S.relSource r).layers.map (fun l => (l.1, l.2 + o))) = some (L ++ q ++ R) := by
    have := S.targetFrom_whisker false L (S.targetFrom_whisker true R (hside false))
    subst hL
    simpa [Diagram.whisker, side] using this
  have hp₂ : S.targetFrom d.source (d.layers.take (h + (S.relSource r).layers.length)) =
      some (L ++ q ++ R) := by
    rw [List.take_add, S.targetFrom_append, hp, Option.bind_some, hseg]
    exact hshift
  have hCt : (S.targetFrom (L ++ q ++ R) (d.layers.drop (h + (S.relSource r).layers.length))).isSome
      := by
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 htd
    rw [Signature.target, if_pos hpd, ← List.take_append_drop (h + (S.relSource r).layers.length)
      d.layers, S.targetFrom_append, hp₂, Option.bind_some] at hq'
    rw [hq']
    rfl
  have hstep : I.relationStep d r h o = J.attach true (L ++ q ++ R)
      (d.layers.drop (h + (S.relSource r).layers.length)) (J.attach false d.source
        (d.layers.take h)
          (J.whisker false L (J.whisker true R (PastingDiagram.ofCell (I.rel r).2)))) := by
    simp only [relationStep, hp, hp₂, hLt, hRt]
    rfl
  rw [hstep]
  have hρ := I.hasRoundType_rel r
  have hsideT := fun β => hasRoundType_side J hS r hq β
  have hd2 : (sideRound J hS r false).dim = 2 :=
    (hsideT false).dim_eq.trans (congrArg (· + 1) (J.dim_path hpsrc))
  have hdρ : (PastingDiagram.ofCell (I.rel r).2).dim = 3 := hρ.dim_eq.trans (congrArg (· + 1) hd2)
  have hspsrc := J.spans_of_hasRoundType (J.hasRoundType_path hpsrc.ne_nil hsxy)
  have hspside := fun β => hspsrc.of_hasRoundType (hsideT β)
  have hspρ := (hspside false).of_hasRoundType hρ
  have eρ : ∀ β, ((PastingDiagram.ofCell (I.rel r).2).boundary 2 β).Equiv
      (sideRound J hS r β).toPastingDiagram := fun β => by
    have := hρ.equiv_boundary_cond hd2 β
    cases β <;> exact this
  obtain ⟨core, hcore⟩ : ∃ c, c = J.whisker false L (J.whisker true R
      (PastingDiagram.ofCell (I.rel r).2)) := ⟨_, rfl⟩
  rw [← hcore]
  have hdR : (J.whisker true R (PastingDiagram.ofCell (I.rel r).2)).dim = 3 :=
    (J.dim_whisker true hspρ (by omega) hRw).trans hdρ
  have hdcore : core.dim = 3 := by
    rw [hcore, J.dim_whisker false (hspρ.whisker true (c := b) hRw) (by omega) hLw]
    exact hdR
  have hcoreb : ∀ β, (core.boundary 2 β).Equiv
      (J.whisker false L (J.whisker true R (sideRound J hS r β).toPastingDiagram)) := fun β => by
    rw [hcore]
    have hspb := (hspside β).of_equiv (eρ β).symm
    have e₁ := J.whisker_boundary true hspρ (n := 2) two_pos (by omega) hRw β
    have e₂ := J.whisker_boundary false (hspρ.whisker true (c := b) hRw) (n := 2) two_pos
      (by omega) hLw β
    exact e₂.trans ((J.whisker_equiv false (hspb.whisker true hRw) e₁.symm hLw).symm.trans
      (J.whisker_equiv false (hspb.whisker true hRw) (J.whisker_equiv true hspb (eρ β) hRw) hLw))
  have hpp : S.IsPath (L ++ (S.relSource r).source ++ R) := S.isPath_of_pathEnds hpe
  have hpp₂ : S.IsPath (L ++ q ++ R) := S.isPath_of_pathEnds (S.pathEnds_targetFrom hS.1 hp₂ hab)
  have key : ∀ β, ∃ M : List (Cell S.Pt S.Ed S.Ce × ℕ), M ≠ [] ∧
      S.targetFrom (L ++ (S.relSource r).source ++ R) M = some (L ++ q ++ R) ∧
      (d.layers.take h ≠ [] → (J.diagram ⟨d.source, d.layers.take h⟩ hpd.ne_nil).Pastable
        (core.boundary 2 β) 1) ∧
      ((J.attach false d.source (d.layers.take h) core).boundary 2 β).Equiv
        (J.attach false d.source (d.layers.take h) (J.diagram ⟨_, M⟩ hpp.ne_nil)) ∧
      (J.diagram ⟨d.source, d.layers.take h ++ M⟩ hpd.ne_nil).Equiv
        (J.attach false d.source (d.layers.take h) (J.diagram ⟨_, M⟩ hpp.ne_nil)) ∧
      S.completeSide (cond β ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ d) r β h o =
        ⟨d.source, d.layers.take h ++ M ++ d.layers.drop (h + (S.relSource r).layers.length)⟩ :=
      fun β => by
    obtain ⟨M, hMne, hMt, hMe, hMc⟩ := hmid β
    have EM := (hcoreb β).trans (hMe hpp.ne_nil).symm
    have hAp : d.layers.take h ≠ [] → (J.diagram ⟨d.source, d.layers.take h⟩ hpd.ne_nil).Pastable
        (core.boundary 2 β) 1 := fun hA => by
      obtain ⟨hc, -⟩ := J.equiv_diagram_append hS.1 (d := ⟨d.source, d.layers.take h⟩)
        (d' := ⟨_, M⟩) (S.target_mk_of_targetFrom hpd hp) rfl hpd.ne_nil hpp.ne_nil hA hMne
        (by rw [S.target_mk_of_targetFrom hpp hMt]; rfl)
      exact hc.of_equiv (.refl _) EM.symm
    have X1b := J.equiv_boundary_attach hS.1 false hpd (by rw [hp]; rfl) (n := 2) one_lt_two
      (by omega) β hAp
    have F := J.equiv_diagram_attach hS.1 hpd hp hMt (C := []) rfl hMne
    rw [J.attach_nil] at F
    exact ⟨M, hMne, hMt, hAp, X1b.trans (J.attach_equiv false _ _ EM),
      (PastingDiagram.equiv_of_eq (J.diagram_congr (by simp) _ _)).trans F, hMc⟩
  have hdX : (J.attach false d.source (d.layers.take h) core).dim = 3 := by
    obtain ⟨M, -, -, hAp, -, -, -⟩ := key false
    rw [J.dim_attach hS.1 false hpd (by rw [hp]; rfl) (by omega)
      (fun hA => PastingDiagram.pastable_of_boundary false one_lt_two (by omega) (hAp hA))]
    exact hdcore
  have hCp : ∀ β, d.layers.drop (h + (S.relSource r).layers.length) ≠ [] →
      ((J.attach false d.source (d.layers.take h) core).boundary 2 β).Pastable
        (J.diagram ⟨L ++ q ++ R, d.layers.drop (h + (S.relSource r).layers.length)⟩
          hpp₂.ne_nil) 1 := fun β hC => by
    obtain ⟨M, hMne, hMt, -, XA, FA, -⟩ := key β
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 hCt
    obtain ⟨hc, -⟩ := J.equiv_diagram_append hS.1 (d := ⟨d.source, d.layers.take h ++ M⟩)
      (d' := ⟨L ++ q ++ R, d.layers.drop (h + (S.relSource r).layers.length)⟩)
      (S.target_mk_of_targetFrom hpd (by rw [S.targetFrom_append, hp, Option.bind_some, hMt]))
      rfl hpd.ne_nil hpp₂.ne_nil (fun h' => hMne (List.append_eq_nil_iff.1 h').2) hC
      (by rw [S.target_mk_of_targetFrom hpp₂ hq']; rfl)
    exact hc.of_equiv (XA.trans FA.symm).symm (.refl _)
  refine ⟨?_, fun β hc => ?_⟩
  · rw [J.dim_attach hS.1 true hpp₂ hCt (by omega)
      (fun hC => PastingDiagram.pastable_of_boundary true one_lt_two (by omega) (hCp false hC))]
    exact hdX
  · obtain ⟨M, hMne, hMt, -, XA, -, hMc⟩ := key β
    refine (J.equiv_boundary_attach hS.1 true hpp₂ hCt (n := 2) one_lt_two (by omega) β
      (hCp β)).trans ((J.attach_equiv true _ _ XA).trans ?_)
    exact (J.equiv_diagram_attach hS.1 hpd hp hMt hCt hMne).symm.trans
      (PastingDiagram.equiv_of_eq (J.diagram_congr hMc.symm _ _))

theorem dim_relationStep {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') : (I.relationStep d r h o).dim = 3 :=
  (I.relationStep_spec hd).1

theorem equiv_boundary_relationStep {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') (α : Bool)
    (hc : (S.completeSide (cond α d' d) r α h o).source ≠ []) :
    ((I.relationStep d r h o).boundary 2 α).Equiv
      (I.diagram (S.completeSide (cond α d' d) r α h o) hc) :=
  (I.relationStep_spec hd).2 α hc

end Interp

end RelSignature

end Atoms.Diagrammatic.Layered
