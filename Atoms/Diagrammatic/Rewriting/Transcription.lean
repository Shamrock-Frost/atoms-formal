import Atoms.Diagrammatic.Rewriting.Chain

namespace Atoms.Diagrammatic.Layered.Transcription

abbrev TEdge := ℕ × ℕ

abbrev TCell := ℕ × ℕ

abbrev TDiagram := List TEdge × List (TCell × ℕ)

abbrev TLink := ℕ × Bool × ℕ × ℕ × ℕ × ℕ

abbrev TGenerator := String × ℕ × ℕ × Bool × TDiagram × TDiagram × Option ℕ × Option Bool ×
  Option ℕ × Option (List TEdge × List TEdge) × String

abbrev TProof := String × ℕ × String × List (String × List ℕ) × List TDiagram × List TLink

variable (gs : List TGenerator)

def boundary (g : TGenerator) (α : Bool) : TDiagram :=
  cond α g.2.2.2.2.2.1 g.2.2.2.2.1

def hasDim (n i : ℕ) : Bool :=
  gs[i]?.any fun g => g.2.1 == n

def index? (p : ℕ → Bool) (i : ℕ) : Option {j : Fin gs.length // p j = true} :=
  if h : i < gs.length then if hp : p i = true then some ⟨⟨i, h⟩, hp⟩ else none else none

abbrev Points := {i : Fin gs.length // hasDim gs 0 i = true}

def unitPoint? : TDiagram → Option (Points gs)
  | ([(1, x)], []) => index? gs (hasDim gs 0) x
  | _ => none

def isEdge (i : ℕ) : Bool :=
  hasDim gs 1 i && (gs[i]?.bind fun g => unitPoint? gs (boundary g false)).isSome &&
    (gs[i]?.bind fun g => unitPoint? gs (boundary g true)).isSome

abbrev Edges := {i : Fin gs.length // isEdge gs i = true}

def edgeEnd (α : Bool) (e : Edges gs) : Points gs :=
  (gs[e.1.1]?.bind fun g => unitPoint? gs (boundary g α)).get (by
    have h := e.2
    simp only [isEdge, Bool.and_eq_true] at h
    cases α
    exacts [h.1.2, h.2])

def edge? : TEdge → Option (Edge (Points gs) (Edges gs))
  | (0, i) => (index? gs (isEdge gs) i).map .gen
  | (1, x) => (index? gs (hasDim gs 0) x).map .unit
  | _ => none

def path? (p : List TEdge) : Option (List (Edge (Points gs) (Edges gs))) :=
  p.mapM (edge? gs)

def layerlessPath? (d : TDiagram) : Option (List (Edge (Points gs) (Edges gs))) :=
  if d.2 = [] then path? gs d.1 else none

def isCell (i : ℕ) : Bool :=
  hasDim gs 2 i && (gs[i]?.bind fun g => layerlessPath? gs (boundary g false)).isSome &&
    (gs[i]?.bind fun g => layerlessPath? gs (boundary g true)).isSome

abbrev Cells := {i : Fin gs.length // isCell gs i = true}

def cellBoundary (α : Bool) (c : Cells gs) : List (Edge (Points gs) (Edges gs)) :=
  (gs[c.1.1]?.bind fun g => layerlessPath? gs (boundary g α)).get (by
    have h := c.2
    simp only [isCell, Bool.and_eq_true] at h
    cases α
    exacts [h.1.2, h.2])

def unitorKind? : ℕ → Option UnitorKind
  | 1 => some .left
  | 2 => some .leftInverse
  | 3 => some .right
  | 4 => some .rightInverse
  | _ => none

def edgeOfCode? (e : ℕ) : Option (Edge (Points gs) (Edges gs)) :=
  edge? gs (e % 2, e / 2)

def cell? : TCell → Option (Cell (Points gs) (Edges gs) (Cells gs))
  | (0, i) => (index? gs (isCell gs) i).map .gen
  | (k, e) => (unitorKind? k).bind fun k => (edgeOfCode? gs e).map (.unitor k)

def rawDiagram? (d : TDiagram) : Option (Diagram (Points gs) (Edges gs) (Cells gs)) :=
  (path? gs d.1).bind fun s =>
    (d.2.mapM fun l => (cell? gs l.1).map (·, l.2)).map (Diagram.mk s)

def isRel (i : ℕ) : Bool :=
  hasDim gs 3 i && (gs[i]?.any fun g => g.2.2.1 != 5) &&
    (gs[i]?.bind fun g => rawDiagram? gs (boundary g false)).isSome &&
    (gs[i]?.bind fun g => rawDiagram? gs (boundary g true)).isSome

abbrev Rels := {i : Fin gs.length // isRel gs i = true}

def relSide (α : Bool) (r : Rels gs) : Diagram (Points gs) (Edges gs) (Cells gs) :=
  (gs[r.1.1]?.bind fun g => rawDiagram? gs (boundary g α)).get (by
    have h := r.2
    simp only [isRel, Bool.and_eq_true] at h
    cases α
    exacts [h.1.2, h.2])

def signature : RelSignature.{0} where
  Pt := Points gs
  Ed := Edges gs
  Ce := Cells gs
  edgeSource := edgeEnd gs false
  edgeTarget := edgeEnd gs true
  cellSource := cellBoundary gs false
  cellTarget := cellBoundary gs true
  Rel := Rels gs
  relSource := relSide gs false
  relTarget := relSide gs true
  invertible r := gs[r.1].2.2.2.1

instance : DecidableEq (signature gs).Pt := inferInstanceAs (DecidableEq (Points gs))

instance : DecidableEq (signature gs).Ed := inferInstanceAs (DecidableEq (Edges gs))

instance : DecidableEq (signature gs).Ce := inferInstanceAs (DecidableEq (Cells gs))

instance : DecidableEq (signature gs).Rel := inferInstanceAs (DecidableEq (Rels gs))

instance : Fintype (signature gs).Ce := inferInstanceAs (Fintype (Cells gs))

instance : Fintype (signature gs).Rel := inferInstanceAs (Fintype (Rels gs))

abbrev SDiagram := Diagram (signature gs).Pt (signature gs).Ed (signature gs).Ce

def diagram? (d : TDiagram) : Option (SDiagram gs) :=
  rawDiagram? gs d

def generatorsDecode : Bool :=
  (List.range gs.length).all fun i =>
    hasDim gs 0 i || isEdge gs i || isCell gs i || isRel gs i ||
      (hasDim gs 3 i && gs[i]?.any fun g => g.2.2.1 == 5)

def unitMove? : ℕ → Option UnitMove
  | 2 => some .cancel
  | 3 => some .trade
  | 4 => some .slide
  | _ => none

def link? (d d' : SDiagram gs) : TLink → Option ((signature gs).Link d d')
  | (0, fwd, h, o, r, _) => (index? gs (isRel gs) r).bind fun r =>
    if fwd then
      if hd : (signature gs).relationApply d r h o = some d' then some (.relation r h o hd)
      else none
    else
      if hinv : (signature gs).invertible r = true then
        if hd : (signature gs).relationApply d' r h o = some d then
          some (.relationBackward r h o hinv hd)
        else none
      else none
  | (1, fwd, h, _, _, _) =>
    if fwd then
      if hd : (signature gs).swap d h = some d' then some (.identification h hd) else none
    else none
  | (k, fwd, h, _, _, _) => (unitMove? k).bind fun m =>
    if hd : cond fwd ((signature gs).unitApply m d h) ((signature gs).unitApply m d' h) =
        some (cond fwd d' d) then some (.unit m fwd h hd)
    else none

def chainFrom? : (d : SDiagram gs) → (ds : List (SDiagram gs)) → List TLink →
    Option ((signature gs).RewriteChain d ((d :: ds).getLast (List.cons_ne_nil d ds)))
  | d, [], [] => some (.refl d)
  | d, d' :: ds, l :: ls =>
    (link? gs d d' l).bind fun k => (chainFrom? d' ds ls).map (.cons k)
  | _, [], _ :: _ => none
  | _, _ :: _, [] => none

def theoremSides? (pf : TProof) : Option (SDiagram gs × SDiagram gs) :=
  if hasDim gs 3 pf.2.1 && gs[pf.2.1]?.any (fun g => g.2.2.1 == 5) then
    (gs[pf.2.1]?.bind fun g => diagram? gs (boundary g false)).bind fun s =>
      (gs[pf.2.1]?.bind fun g => diagram? gs (boundary g true)).map (s, ·)
  else none

def chainBetween? (s t : SDiagram gs) (pf : TProof) : Option ((signature gs).RewriteChain s t) :=
  match pf.2.2.2.2.1.mapM (diagram? gs) with
  | some (d :: ds) =>
    if hs : d = s then
      if ht : (d :: ds).getLast (List.cons_ne_nil d ds) = t then
        (chainFrom? gs d ds pf.2.2.2.2.2).map fun c => cast (by subst hs; rw [ht]) c
      else none
    else none
  | _ => none

def check (pf : TProof) : Bool :=
  decide (signature gs).WellFormed && generatorsDecode gs &&
    match theoremSides? gs pf with
    | some (s, t) => (chainBetween? gs s t pf).isSome
    | none => false

variable {gs}

theorem wellFormed_of_check {pf : TProof} (h : check gs pf = true) : (signature gs).WellFormed := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem isSome_theoremSides_of_check {pf : TProof} (h : check gs pf = true) :
    (theoremSides? gs pf).isSome := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i heq
    rw [heq]
    rfl
  · exact absurd h Bool.false_ne_true

def theoremSource {pf : TProof} (h : check gs pf = true) : SDiagram gs :=
  ((theoremSides? gs pf).get (isSome_theoremSides_of_check h)).1

def theoremTarget {pf : TProof} (h : check gs pf = true) : SDiagram gs :=
  ((theoremSides? gs pf).get (isSome_theoremSides_of_check h)).2

theorem isSome_chainBetween_of_check {pf : TProof} (h : check gs pf = true) :
    (chainBetween? gs (theoremSource h) (theoremTarget h) pf).isSome := by
  obtain ⟨⟨s, t⟩, he⟩ := Option.isSome_iff_exists.1 (isSome_theoremSides_of_check h)
  have h₁ : theoremSource h = s := by simp only [theoremSource, he, Option.get_some]
  have h₂ : theoremTarget h = t := by simp only [theoremTarget, he, Option.get_some]
  have hc := h
  simp only [check, Bool.and_eq_true, he] at hc
  rw [h₁, h₂]
  exact hc.2

def chainOfCheck {pf : TProof} (h : check gs pf = true) :
    (signature gs).RewriteChain (theoremSource h) (theoremTarget h) :=
  (chainBetween? gs (theoremSource h) (theoremTarget h) pf).get (isSome_chainBetween_of_check h)

end Atoms.Diagrammatic.Layered.Transcription
