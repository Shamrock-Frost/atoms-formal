import Atoms.Diagrammatic.Presentation

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem PastingDiagram.pastable_of_boundary (α : Bool) {x y : PastingDiagram X} {n : ℕ}
    (hn : 1 < n) (hx : n ≤ x.dim) {β : Bool}
    (h : (cond α (x.boundary n β) y).Pastable (cond α y (x.boundary n β)) 1) :
    (cond α x y).Pastable (cond α y x) 1 := by
  have hs := (equiv_boundary_boundary x hn β α).symm.trans h.side
  refine Pastable.of_side α hs (by omega) ?_
  cases α
  exacts [(lt_min_iff.1 h.2).1, (lt_min_iff.1 h.2).2]

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.Layered

inductive UnitorKind
  | left
  | leftInverse
  | right
  | rightInverse
  deriving DecidableEq

namespace UnitorKind

def side : UnitorKind → Bool
  | left => false
  | leftInverse => false
  | right => true
  | rightInverse => true

def removes : UnitorKind → Bool
  | left => true
  | leftInverse => false
  | right => true
  | rightInverse => false

end UnitorKind

inductive Edge (Pt Ed : Type v)
  | gen (e : Ed)
  | unit (x : Pt)
  deriving DecidableEq

inductive Cell (Pt Ed Ce : Type v)
  | gen (c : Ce)
  | unitor (k : UnitorKind) (e : Edge Pt Ed)
  | unit (p : List (Edge Pt Ed))
  deriving DecidableEq

structure Diagram (Pt Ed Ce : Type v) where
  source : List (Edge Pt Ed)
  layers : List (Cell Pt Ed Ce × ℕ)
  deriving DecidableEq

namespace Diagram

variable {Pt Ed Ce : Type v}

def append (d e : Diagram Pt Ed Ce) : Diagram Pt Ed Ce := ⟨d.source, d.layers ++ e.layers⟩

instance : Append (Diagram Pt Ed Ce) := ⟨append⟩

@[simp] theorem source_append (d e : Diagram Pt Ed Ce) : (d ++ e).source = d.source := rfl

@[simp] theorem layers_append (d e : Diagram Pt Ed Ce) :
    (d ++ e).layers = d.layers ++ e.layers := rfl

def whisker (α : Bool) (w : List (Edge Pt Ed)) (d : Diagram Pt Ed Ce) : Diagram Pt Ed Ce :=
  cond α ⟨d.source ++ w, d.layers⟩ ⟨w ++ d.source, d.layers.map fun l => (l.1, l.2 + w.length)⟩

end Diagram

structure Signature where
  Pt : Type v
  Ed : Type v
  Ce : Type v
  edgeSource : Ed → Pt
  edgeTarget : Ed → Pt
  cellSource : Ce → List (Edge Pt Ed)
  cellTarget : Ce → List (Edge Pt Ed)

namespace Signature

variable (S : Signature.{v})

def src : Edge S.Pt S.Ed → S.Pt
  | .gen e => S.edgeSource e
  | .unit x => x

def tgt : Edge S.Pt S.Ed → S.Pt
  | .gen e => S.edgeTarget e
  | .unit x => x

def unitPath (σ : Bool) (e : Edge S.Pt S.Ed) : List (Edge S.Pt S.Ed) :=
  cond σ [e, .unit (S.tgt e)] [.unit (S.src e), e]

def cellType : Cell S.Pt S.Ed S.Ce → List (Edge S.Pt S.Ed) × List (Edge S.Pt S.Ed)
  | .gen c => (S.cellSource c, S.cellTarget c)
  | .unitor k e => cond k.removes (S.unitPath k.side e, [e]) ([e], S.unitPath k.side e)
  | .unit p => (p, p)

variable [DecidableEq S.Pt]

def walk (x : S.Pt) : List (Edge S.Pt S.Ed) → Option S.Pt
  | [] => some x
  | e :: p => if S.src e = x then walk (S.tgt e) p else none

def pathEnds : List (Edge S.Pt S.Ed) → Option (S.Pt × S.Pt)
  | [] => none
  | e :: p => (S.walk (S.tgt e) p).map (S.src e, ·)

@[simp] theorem pathEnds_nil : S.pathEnds [] = none := rfl

def IsPath (p : List (Edge S.Pt S.Ed)) : Prop := (S.pathEnds p).isSome

instance : DecidablePred S.IsPath :=
  fun p => inferInstanceAs (Decidable ((S.pathEnds p).isSome = true))

theorem IsPath.ne_nil {S : Signature.{v}} [DecidableEq S.Pt] {p : List (Edge S.Pt S.Ed)}
    (hp : S.IsPath p) : p ≠ [] := by
  rintro rfl
  exact Bool.false_ne_true hp

theorem walk_append (x : S.Pt) (p q : List (Edge S.Pt S.Ed)) :
    S.walk x (p ++ q) = (S.walk x p).bind fun y => S.walk y q := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [List.cons_append, walk]
    split_ifs
    · exact ih _
    · rfl

theorem walk_append_eq_some {x z : S.Pt} {p q : List (Edge S.Pt S.Ed)}
    (h : S.walk x (p ++ q) = some z) : ∃ y, S.walk x p = some y ∧ S.walk y q = some z := by
  rw [S.walk_append] at h
  exact Option.bind_eq_some_iff.1 h

theorem walk_cons_eq_some {x y : S.Pt} {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} :
    S.walk x (e :: p) = some y ↔ S.src e = x ∧ S.walk (S.tgt e) p = some y := by
  by_cases h : S.src e = x
  · simp only [walk, h, ↓reduceIte, true_and]
  · simp only [walk, h, ↓reduceIte, false_and, reduceCtorEq]

theorem pathEnds_cons_eq_some {x y : S.Pt} {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} :
    S.pathEnds (e :: p) = some (x, y) ↔ S.src e = x ∧ S.walk (S.tgt e) p = some y := by
  simp only [pathEnds, Option.map_eq_some_iff, Prod.mk.injEq]
  exact ⟨fun ⟨z, hz, h1, h2⟩ => ⟨h1, h2 ▸ hz⟩, fun ⟨h1, h2⟩ => ⟨y, h2, h1, rfl⟩⟩

theorem exists_pathEnds_of_isPath {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p) :
    ∃ x y, S.pathEnds p = some (x, y) := by
  obtain ⟨⟨x, y⟩, h⟩ := Option.isSome_iff_exists.1 hp
  exact ⟨x, y, h⟩

theorem isPath_of_pathEnds {p : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (h : S.pathEnds p = some (x, y)) : S.IsPath p :=
  Option.isSome_iff_exists.2 ⟨_, h⟩

theorem pathEnds_append {p q : List (Edge S.Pt S.Ed)} {x y z : S.Pt}
    (hp : S.pathEnds p = some (x, y)) (hq : S.pathEnds q = some (y, z)) :
    S.pathEnds (p ++ q) = some (x, z) := by
  obtain _ | ⟨e, p⟩ := p
  · simp only [pathEnds_nil, reduceCtorEq] at hp
  obtain _ | ⟨f, q⟩ := q
  · simp only [pathEnds_nil, reduceCtorEq] at hq
  obtain ⟨rfl, hp'⟩ := S.pathEnds_cons_eq_some.1 hp
  obtain ⟨rfl, hq'⟩ := S.pathEnds_cons_eq_some.1 hq
  rw [List.cons_append]
  refine S.pathEnds_cons_eq_some.2 ⟨rfl, ?_⟩
  rw [walk_append, hp']
  exact S.walk_cons_eq_some.2 ⟨rfl, hq'⟩

theorem pathEnds_singleton (e : Edge S.Pt S.Ed) : S.pathEnds [e] = some (S.src e, S.tgt e) :=
  rfl

theorem isPath_singleton (e : Edge S.Pt S.Ed) : S.IsPath [e] :=
  S.isPath_of_pathEnds (S.pathEnds_singleton e)

theorem pathEnds_unitPath (σ : Bool) (e : Edge S.Pt S.Ed) :
    S.pathEnds (S.unitPath σ e) = some (S.src e, S.tgt e) := by
  cases σ <;> simp only [unitPath, cond_true, cond_false, pathEnds, walk, src, tgt, if_pos,
    Option.map_some]

theorem isPath_unitPath (σ : Bool) (e : Edge S.Pt S.Ed) : S.IsPath (S.unitPath σ e) :=
  S.isPath_of_pathEnds (S.pathEnds_unitPath σ e)

def WellFormed : Prop :=
  ∀ c, (S.pathEnds (S.cellSource c)).isSome ∧ S.pathEnds (S.cellSource c) =
    S.pathEnds (S.cellTarget c)

instance [Fintype S.Ce] : Decidable S.WellFormed :=
  inferInstanceAs (Decidable (∀ c : S.Ce, (S.pathEnds (S.cellSource c)).isSome ∧
    S.pathEnds (S.cellSource c) = S.pathEnds (S.cellTarget c)))

theorem pathEnds_eq_some_iff {p : List (Edge S.Pt S.Ed)} {x z : S.Pt} :
    S.pathEnds p = some (x, z) ↔ p ≠ [] ∧ S.walk x p = some z := by
  obtain _ | ⟨e, p⟩ := p
  · simp only [pathEnds_nil, reduceCtorEq, ne_eq, not_true_eq_false, false_and]
  · exact S.pathEnds_cons_eq_some.trans
      ⟨fun h => ⟨List.cons_ne_nil e p, S.walk_cons_eq_some.2 h⟩,
        fun h => S.walk_cons_eq_some.1 h.2⟩

theorem exists_walk_of_split {L s R : List (Edge S.Pt S.Ed)} {a b : S.Pt}
    (hp : S.pathEnds (L ++ s ++ R) = some (a, b)) (hs : s ≠ []) :
    ∃ x y, S.walk a L = some x ∧ S.pathEnds s = some (x, y) ∧ S.walk y R = some b := by
  obtain ⟨-, hw⟩ := S.pathEnds_eq_some_iff.1 hp
  rw [S.walk_append, S.walk_append] at hw
  obtain ⟨y, hy, hR⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨x, hx, hs'⟩ := Option.bind_eq_some_iff.1 hy
  exact ⟨x, y, hx, S.pathEnds_eq_some_iff.2 ⟨hs, hs'⟩, hR⟩

theorem pathEnds_whisker (α : Bool) {s w : List (Edge S.Pt S.Ed)} {a b c : S.Pt}
    (hs : S.pathEnds s = some (a, b)) (hw : S.walk (cond α b c) w = some (cond α c a)) :
    S.pathEnds (cond α (s ++ w) (w ++ s)) = some (cond α a c, cond α c b) := by
  obtain ⟨hne, hs⟩ := S.pathEnds_eq_some_iff.1 hs
  cases α <;> simp only [cond_false, cond_true] at hw ⊢ <;>
    refine S.pathEnds_eq_some_iff.2 ⟨?_, ?_⟩
  · exact List.append_ne_nil_of_right_ne_nil w hne
  · rw [walk_append, hw]
    exact hs
  · exact List.append_ne_nil_of_left_ne_nil hne w
  · rw [walk_append, hs]
    exact hw

theorem pathEnds_cellType_snd (hS : S.WellFormed) (c : Cell S.Pt S.Ed S.Ce) :
    S.pathEnds (S.cellType c).2 = S.pathEnds (S.cellType c).1 := by
  cases c with
  | gen c => exact (hS c).2.symm
  | unitor k e =>
    cases k <;> simp only [cellType, UnitorKind.removes, cond_true, cond_false,
      pathEnds_unitPath, pathEnds_singleton]
  | unit p => rfl

theorem isPath_cellType_snd (hS : S.WellFormed) {c : Cell S.Pt S.Ed S.Ce}
    (hs : S.IsPath (S.cellType c).1) : S.IsPath (S.cellType c).2 := by
  rw [IsPath, S.pathEnds_cellType_snd hS c]
  exact hs

theorem isPath_cellType_unitor_fst (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    S.IsPath (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 := by
  cases k
  exacts [S.isPath_unitPath false e, S.isPath_singleton e, S.isPath_unitPath true e,
    S.isPath_singleton e]

theorem isPath_cellType_unitor_snd (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    S.IsPath (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 := by
  cases k
  exacts [S.isPath_singleton e, S.isPath_unitPath false e, S.isPath_singleton e,
    S.isPath_unitPath true e]

variable [DecidableEq S.Ed]

def applyLayer (p : List (Edge S.Pt S.Ed)) (c : Cell S.Pt S.Ed S.Ce) (o : ℕ) :
    Option (List (Edge S.Pt S.Ed)) :=
  if (S.cellType c).1 ≠ [] ∧ ((p.drop o).take (S.cellType c).1.length = (S.cellType c).1) then
    some (p.take o ++ (S.cellType c).2 ++ p.drop (o + (S.cellType c).1.length))
  else none

theorem eq_of_applyLayer_eq_some {p p' : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o : ℕ}
    (h : S.applyLayer p c o = some p') : (S.cellType c).1 ≠ [] ∧
      p.take o ++ (S.cellType c).1 ++ p.drop (o + (S.cellType c).1.length) = p ∧
        p' = p.take o ++ (S.cellType c).2 ++ p.drop (o + (S.cellType c).1.length) := by
  rw [applyLayer] at h
  split_ifs at h with hc
  obtain ⟨hne, hseg⟩ := hc
  refine ⟨hne, ?_, (Option.some.inj h).symm⟩
  conv_rhs => rw [← List.take_append_drop o p,
    ← List.take_append_drop (S.cellType c).1.length (p.drop o), hseg]
  rw [List.drop_drop, List.append_assoc]

theorem applyLayer_eq_some_iff {p p' : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce} {o : ℕ} :
    S.applyLayer p c o = some p' ↔ (S.cellType c).1 ≠ [] ∧ ∃ L R, p = L ++ (S.cellType c).1 ++ R ∧
      L.length = o ∧ p' = L ++ (S.cellType c).2 ++ R := by
  constructor
  · intro h
    obtain ⟨hne, hseg, rfl⟩ := S.eq_of_applyLayer_eq_some h
    refine ⟨hne, _, _, hseg.symm, ?_, rfl⟩
    have hl := congrArg List.length hseg
    have hc : 0 < (S.cellType c).1.length := List.length_pos_iff.2 hne
    simp only [List.length_append, List.length_take, List.length_drop] at hl
    simp only [List.length_take]
    omega
  · rintro ⟨hne, L, R, rfl, rfl, rfl⟩
    rw [applyLayer, if_pos ⟨hne, by simp⟩]
    simp

end Signature

namespace Diagram

variable {Pt Ed Ce : Type v}

theorem source_whisker (α : Bool) (w : List (Edge Pt Ed)) (d : Diagram Pt Ed Ce) :
    (d.whisker α w).source = cond α (d.source ++ w) (w ++ d.source) := by
  cases α <;> rfl

def unitFirst (d : Diagram Pt Ed Ce) : Diagram Pt Ed Ce :=
  ⟨d.source, (.unit d.source, 0) :: d.layers⟩

@[simp] theorem source_unitFirst (d : Diagram Pt Ed Ce) : d.unitFirst.source = d.source :=
  rfl

@[simp] theorem layers_unitFirst (d : Diagram Pt Ed Ce) :
    d.unitFirst.layers = (.unit d.source, 0) :: d.layers :=
  rfl

end Diagram

namespace Signature

variable (S : Signature.{v}) [DecidableEq S.Pt] [DecidableEq S.Ed]

theorem applyLayer_whisker (α : Bool) (w : List (Edge S.Pt S.Ed)) {p p' : List (Edge S.Pt S.Ed)}
    {c : Cell S.Pt S.Ed S.Ce} {o : ℕ} (h : S.applyLayer p c o = some p') :
    S.applyLayer (cond α (p ++ w) (w ++ p)) c (cond α o (o + w.length)) =
      some (cond α (p' ++ w) (w ++ p')) := by
  obtain ⟨hne, L, R, rfl, rfl, rfl⟩ := S.applyLayer_eq_some_iff.1 h
  refine S.applyLayer_eq_some_iff.2 ⟨hne, ?_⟩
  cases α
  · exact ⟨w ++ L, R, by simp, by simp [Nat.add_comm], by simp⟩
  · exact ⟨L, R ++ w, by simp, rfl, by simp⟩

theorem isPath_cellType_of_applyLayer {p p' : List (Edge S.Pt S.Ed)} {c : Cell S.Pt S.Ed S.Ce}
    {o : ℕ} (h : S.applyLayer p c o = some p') {x z : S.Pt} (hp : S.pathEnds p = some (x, z)) :
    S.IsPath (S.cellType c).1 := by
  obtain ⟨hne, hseg, -⟩ := S.eq_of_applyLayer_eq_some h
  rw [← hseg] at hp
  obtain ⟨-, hp⟩ := S.pathEnds_eq_some_iff.1 hp
  rw [walk_append, walk_append] at hp
  obtain ⟨b, hb, -⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨a, -, hsab⟩ := Option.bind_eq_some_iff.1 hb
  exact S.isPath_of_pathEnds (S.pathEnds_eq_some_iff.2 ⟨hne, hsab⟩)

theorem pathEnds_applyLayer (hS : S.WellFormed) {p p' : List (Edge S.Pt S.Ed)}
    {c : Cell S.Pt S.Ed S.Ce} {o : ℕ} (h : S.applyLayer p c o = some p') {x z : S.Pt}
    (hp : S.pathEnds p = some (x, z)) : S.pathEnds p' = some (x, z) := by
  obtain ⟨hne, hseg, rfl⟩ := S.eq_of_applyLayer_eq_some h
  rw [← hseg] at hp
  obtain ⟨-, hp⟩ := S.pathEnds_eq_some_iff.1 hp
  rw [walk_append, walk_append] at hp
  obtain ⟨b, hb, hz⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨a, ha, hab⟩ := Option.bind_eq_some_iff.1 hb
  have ht := S.pathEnds_eq_some_iff.1 ((S.pathEnds_cellType_snd hS c).trans
    (S.pathEnds_eq_some_iff.2 ⟨hne, hab⟩))
  refine S.pathEnds_eq_some_iff.2 ⟨List.append_ne_nil_of_left_ne_nil
    (List.append_ne_nil_of_right_ne_nil _ ht.1) _, ?_⟩
  rw [walk_append, walk_append, ha, Option.bind_some, ht.2, Option.bind_some, hz]

def targetFrom (p : List (Edge S.Pt S.Ed)) : List (Cell S.Pt S.Ed S.Ce × ℕ) →
    Option (List (Edge S.Pt S.Ed))
  | [] => some p
  | l :: ls => (S.applyLayer p l.1 l.2).bind fun q => targetFrom q ls

def target (d : Diagram S.Pt S.Ed S.Ce) : Option (List (Edge S.Pt S.Ed)) :=
  if S.IsPath d.source then S.targetFrom d.source d.layers else none

theorem targetFrom_append (p : List (Edge S.Pt S.Ed)) (ls ls' : List (Cell S.Pt S.Ed S.Ce × ℕ)) :
    S.targetFrom p (ls ++ ls') = (S.targetFrom p ls).bind fun q => S.targetFrom q ls' := by
  induction ls generalizing p with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.cons_append, targetFrom, Option.bind_assoc]
    congr 1
    funext q
    exact ih q

theorem target_mk_of_targetFrom {p q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hp : S.IsPath p) (h : S.targetFrom p ls = some q) :
    S.target ⟨p, ls⟩ = some q := by
  rw [target, if_pos hp]; exact h

theorem pathEnds_targetFrom (hS : S.WellFormed) {p r : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p ls = some r) {x z : S.Pt}
    (hp : S.pathEnds p = some (x, z)) : S.pathEnds r = some (x, z) := by
  induction ls generalizing p with
  | nil => exact Option.some.inj h ▸ hp
  | cons l ls ih =>
    obtain ⟨p', h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    exact ih h₂ (S.pathEnds_applyLayer hS h₁ hp)

theorem targetFrom_whisker (α : Bool) (w : List (Edge S.Pt S.Ed)) {p q : List (Edge S.Pt S.Ed)}
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (h : S.targetFrom p ls = some q) :
    S.targetFrom (Diagram.whisker α w ⟨p, ls⟩).source (Diagram.whisker α w ⟨p, ls⟩).layers =
      some (cond α (q ++ w) (w ++ q)) := by
  induction ls generalizing p with
  | nil =>
    obtain rfl : p = q := Option.some.inj h
    cases α <;> rfl
  | cons l ls ih =>
    obtain ⟨p₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have e := S.applyLayer_whisker α w h₁
    have ih' := ih h₂
    cases α
    · simp only [Diagram.whisker, cond_false, List.map_cons, targetFrom] at e ih' ⊢
      rw [e, Option.bind_some]
      exact ih'
    · simp only [Diagram.whisker, cond_true, targetFrom] at e ih' ⊢
      rw [e, Option.bind_some]
      exact ih'

theorem target_singleton {p q : List (Edge S.Pt S.Ed)} (hp : S.IsPath p)
    {l : Cell S.Pt S.Ed S.Ce × ℕ} (h : S.applyLayer p l.1 l.2 = some q) :
    S.target ⟨p, [l]⟩ = some q :=
  S.target_mk_of_targetFrom hp ((congrArg (·.bind fun q => S.targetFrom q []) h).trans rfl)

theorem isPath_source_of_target {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hd : S.target d = some q) : S.IsPath d.source := by
  by_contra h
  rw [target, if_neg h] at hd
  exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

theorem targetFrom_of_target {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) : S.targetFrom d.source d.layers = some q := by
  rw [target, if_pos (S.isPath_source_of_target hq)] at hq
  exact hq

theorem pathEnds_target (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) {x z : S.Pt}
    (hp : S.pathEnds d.source = some (x, z)) : S.pathEnds q = some (x, z) := by
  rw [target, if_pos (S.isPath_source_of_target hd)] at hd
  exact S.pathEnds_targetFrom hS hd hp

theorem isPath_target (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) : S.IsPath q :=
  have ⟨_, _, h⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hd)
  S.isPath_of_pathEnds (S.pathEnds_target hS hd h)

def swapLayers (l₁ l₂ : Cell S.Pt S.Ed S.Ce × ℕ) : Option (List (Cell S.Pt S.Ed S.Ce × ℕ)) :=
  if l₂.2 + (S.cellType l₂.1).1.length ≤ l₁.2 then
    some [l₂, (l₁.1, l₁.2 + (S.cellType l₂.1).2.length - (S.cellType l₂.1).1.length)]
  else if l₁.2 + (S.cellType l₁.1).2.length ≤ l₂.2 then
    some [(l₂.1, l₂.2 - (S.cellType l₁.1).2.length + (S.cellType l₁.1).1.length), l₁]
  else none

def swap (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ) : Option (Diagram S.Pt S.Ed S.Ce) :=
  match d.layers.drop h with
  | l₁ :: l₂ :: rest => (S.swapLayers l₁ l₂).bind fun n =>
      if (S.target ⟨d.source, d.layers.take h ++ n ++ rest⟩).isSome then
        some ⟨d.source, d.layers.take h ++ n ++ rest⟩
      else none
  | _ => none

theorem eq_of_swap_eq_some {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ} (hd : S.swap d h = some d') :
    ∃ l₁ l₂ rest n, d.layers.drop h = l₁ :: l₂ :: rest ∧ S.swapLayers l₁ l₂ = some n ∧
      d' = ⟨d.source, d.layers.take h ++ n ++ rest⟩ := by
  rw [swap] at hd
  split at hd
  · rename_i l₁ l₂ rest hdrop
    obtain ⟨n, hn, hd⟩ := Option.bind_eq_some_iff.1 hd
    split_ifs at hd
    exact ⟨l₁, l₂, rest, n, hdrop, hn, (Option.some.inj hd).symm⟩
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])

theorem applyLayer_unit_self {p : List (Edge S.Pt S.Ed)} (hp : p ≠ []) :
    S.applyLayer p (.unit p) 0 = some p :=
  S.applyLayer_eq_some_iff.2 ⟨hp, [], [], by simp [cellType], rfl, by simp [cellType]⟩

theorem target_unitFirst (d : Diagram S.Pt S.Ed S.Ce) : S.target d.unitFirst = S.target d := by
  rw [target, target, Diagram.source_unitFirst, Diagram.layers_unitFirst]
  by_cases hp : S.IsPath d.source
  · rw [if_pos hp, if_pos hp, targetFrom, S.applyLayer_unit_self hp.ne_nil, Option.bind_some]
  · rw [if_neg hp, if_neg hp]

theorem swap_unitFirst {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ} (hsw : S.swap d h = some d') :
    S.swap d.unitFirst (h + 1) = some d'.unitFirst := by
  obtain ⟨l₁, l₂, rest, n, hdrop, hn, rfl⟩ := S.eq_of_swap_eq_some hsw
  have hsome : (S.target ⟨d.source, d.layers.take h ++ n ++ rest⟩).isSome := by
    rw [swap] at hsw
    split at hsw
    · rename_i l₁' l₂' rest' hdrop'
      rw [hdrop] at hdrop'
      obtain ⟨rfl, rfl, rfl⟩ : l₁ = l₁' ∧ l₂ = l₂' ∧ rest = rest' := by simpa using hdrop'
      rw [hn, Option.bind_some] at hsw
      split_ifs at hsw with hc
      exact hc
    · exact absurd hsw (by simp only [reduceCtorEq, not_false_eq_true])
  have hu : (S.target ⟨d.source, (Cell.unit d.source, 0) :: (d.layers.take h ++ n ++ rest)⟩).isSome
      := by
    rw [← S.target_unitFirst ⟨d.source, d.layers.take h ++ n ++ rest⟩] at hsome
    exact hsome
  simp only [swap, Diagram.layers_unitFirst, List.drop_succ_cons, hdrop, hn, Option.bind_some,
    Diagram.source_unitFirst, List.take_succ_cons, List.cons_append, hu, ↓reduceIte]
  rfl

end Signature

namespace Signature

variable {S : Signature.{v}} {X Y : DiagSet.{u}}

variable (S) in
structure PathInterp (X : DiagSet.{u}) where
  point : S.Pt → diagram X atomPoint
  edge : S.Ed → Σ U : Atom, diagram X U
  hasRoundType_edge : ∀ e, HasRoundType (PastingDiagram.ofCell (edge e).2)
    (cellRound (point (S.edgeSource e))) (cellRound (point (S.edgeTarget e)))

namespace PathInterp

variable (I : S.PathInterp X)

noncomputable def mapTo (f : X ⟶ Y) : S.PathInterp Y where
  point x := f.app _ (I.point x)
  edge e := ⟨(I.edge e).1, f.app _ (I.edge e).2⟩
  hasRoundType_edge e := by
    have h := (I.hasRoundType_edge e).mapTo f
    rw [← PastingDiagram.ofCell_app] at h
    have hp (x : S.Pt) : (cellRound (I.point x)).mapTo f = cellRound (f.app _ (I.point x)) :=
      RoundPastingDiagram.ext (PastingDiagram.ofCell_app _ _).symm
    rw [hp, hp] at h
    exact h

noncomputable def ofEdge : Edge S.Pt S.Ed → PastingDiagram X
  | .gen e => PastingDiagram.ofCell (I.edge e).2
  | .unit x => (PastingDiagram.ofCell (I.point x)).unit

theorem hasRoundType_ofEdge : (e : Edge S.Pt S.Ed) →
    HasRoundType (I.ofEdge e) (cellRound (I.point (S.src e))) (cellRound (I.point (S.tgt e)))
  | .gen e => I.hasRoundType_edge e
  | .unit x => hasRoundType_unit (cellRound (I.point x))

theorem isRound_ofEdge : (e : Edge S.Pt S.Ed) → (I.ofEdge e).IsRound
  | .gen e => (cellRound (I.edge e).2).isRound
  | .unit x => isRound_unit (cellRound (I.point x)).isRound

theorem dim_ofEdge (e : Edge S.Pt S.Ed) : (I.ofEdge e).dim = 1 :=
  (I.hasRoundType_ofEdge e).dim_eq.trans (congrArg (· + 1) dimension_atomPoint)

theorem ofEdge_mapTo (f : X ⟶ Y) : (e : Edge S.Pt S.Ed) →
    (I.mapTo f).ofEdge e = (I.ofEdge e).mapTo f
  | .gen _ => PastingDiagram.ofCell_app _ _
  | .unit _ => (congrArg PastingDiagram.unit (PastingDiagram.ofCell_app _ _)).trans
      (unit_mapTo _ _)

noncomputable def pathCons (e : Edge S.Pt S.Ed) : List (Edge S.Pt S.Ed) → PastingDiagram X
  | [] => I.ofEdge e
  | f :: p => (I.ofEdge e).pasteOr (pathCons f p) 0

noncomputable def path : (p : List (Edge S.Pt S.Ed)) → p ≠ [] → PastingDiagram X
  | [], h => absurd rfl h
  | e :: p, _ => I.pathCons e p

@[simp] theorem path_cons (e : Edge S.Pt S.Ed) (p : List (Edge S.Pt S.Ed)) (h : e :: p ≠ []) :
    I.path (e :: p) h = I.pathCons e p :=
  rfl

theorem path_congr {p q : List (Edge S.Pt S.Ed)} (h : p = q) (hp : p ≠ []) (hq : q ≠ []) :
    I.path p hp = I.path q hq := by
  subst h
  rfl

private theorem pathCons_spec [DecidableEq S.Pt] {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)}
    {y : S.Pt} (h : S.walk (S.tgt e) p = some y) :
    HasRoundType (I.pathCons e p) (cellRound (I.point (S.src e))) (cellRound (I.point y)) ∧
      (I.pathCons e p).IsRound := by
  induction p generalizing e with
  | nil =>
    obtain rfl : S.tgt e = y := Option.some.inj h
    exact ⟨I.hasRoundType_ofEdge e, I.isRound_ofEdge e⟩
  | cons f p ih =>
    obtain ⟨hf, h⟩ := S.walk_cons_eq_some.1 h
    obtain ⟨ht, hr⟩ := ih h
    have he := I.hasRoundType_ofEdge e
    rw [← hf] at he
    have hp := he.pastable ht (.refl _) dimension_atomPoint
    refine ⟨?_, ?_⟩ <;> rw [pathCons, pasteOr_of hp]
    · exact he.paste ht (.refl _) dimension_atomPoint hp
    · exact isRound_paste_of_dim ⟨_, I.isRound_ofEdge e⟩ ⟨_, hr⟩ (I.dim_ofEdge e)
        (ht.dim_eq.trans (congrArg (· + 1) dimension_atomPoint)) hp

section Paths

variable [DecidableEq S.Pt]

theorem dim_pathCons {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} {y : S.Pt}
    (h : S.walk (S.tgt e) p = some y) : (I.pathCons e p).dim = 1 :=
  (I.pathCons_spec h).1.dim_eq.trans (congrArg (· + 1) dimension_atomPoint)

theorem hasRoundType_path {p : List (Edge S.Pt S.Ed)} (hp : p ≠ []) {x y : S.Pt}
    (h : S.pathEnds p = some (x, y)) :
    HasRoundType (I.path p hp) (cellRound (I.point x)) (cellRound (I.point y)) := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp
  obtain ⟨rfl, h'⟩ := S.pathEnds_cons_eq_some.1 h
  exact (I.pathCons_spec h').1

theorem isRound_path {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p) :
    (I.path p hp.ne_nil).IsRound := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp.ne_nil
  obtain ⟨x, y, h⟩ := S.exists_pathEnds_of_isPath hp
  exact (I.pathCons_spec (S.pathEnds_cons_eq_some.1 h).2).2

theorem dim_path {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p) : (I.path p hp.ne_nil).dim = 1 :=
  have ⟨_, _, h⟩ := S.exists_pathEnds_of_isPath hp
  (I.hasRoundType_path hp.ne_nil h).dim_eq.trans (congrArg (· + 1) dimension_atomPoint)

noncomputable def pathRound (p : List (Edge S.Pt S.Ed)) (hp : S.IsPath p) : RoundPastingDiagram X :=
  ⟨I.path p hp.ne_nil, I.isRound_path hp⟩

@[simp] theorem toPastingDiagram_pathRound (p : List (Edge S.Pt S.Ed)) (hp : S.IsPath p) :
    (I.pathRound p hp).toPastingDiagram = I.path p hp.ne_nil :=
  rfl

theorem equiv_pathCons_append {e f : Edge S.Pt S.Ed} {p q : List (Edge S.Pt S.Ed)} {z : S.Pt}
    (h : S.walk (S.tgt e) (p ++ f :: q) = some z) :
    ∃ hp, (I.pathCons e (p ++ f :: q)).Equiv ((I.pathCons e p).paste (I.pathCons f q) 0 hp) := by
  induction p generalizing e with
  | nil =>
    obtain ⟨hf, hq⟩ := S.walk_cons_eq_some.1 h
    have he := I.hasRoundType_ofEdge e
    rw [← hf] at he
    have hp := he.pastable (I.pathCons_spec hq).1 (.refl _) dimension_atomPoint
    exact ⟨hp, PastingDiagram.equiv_of_eq (pasteOr_of hp)⟩
  | cons g p ih =>
    rw [List.cons_append] at h
    obtain ⟨hg, hpq⟩ := S.walk_cons_eq_some.1 h
    obtain ⟨h₁, e₁⟩ := ih hpq
    rw [walk_append] at hpq
    obtain ⟨y, hy, hz⟩ := Option.bind_eq_some_iff.1 hpq
    obtain ⟨hf, hz⟩ := S.walk_cons_eq_some.1 hz
    have he := I.hasRoundType_ofEdge e
    rw [← hg] at he
    have hy' := (I.pathCons_spec hy).1
    have hz' := (I.pathCons_spec hz).1
    rw [hf] at hz'
    have h₀ := he.pastable hy' (.refl _) dimension_atomPoint
    have hc : I.pathCons e (g :: p) = (I.ofEdge e).paste (I.pathCons g p) 0 h₀ := pasteOr_of h₀
    have hpq' := he.pastable (hy'.paste hz' (.refl _) dimension_atomPoint h₁) (.refl _)
      dimension_atomPoint
    obtain ⟨h₃, h₄, e₂⟩ := equiv_paste_assoc h₀ (Pastable.paste_left h₀ h₁)
    rw [hc]
    refine ⟨Pastable.paste_left h₀ h₁, ?_⟩
    refine PastingDiagram.Equiv.trans (PastingDiagram.equiv_of_eq (pasteOr_of
      (hpq'.of_equiv (.refl _) e₁.symm))) ?_
    exact (Equiv.paste (.refl _) e₁ _ h₄).trans e₂.symm

theorem equiv_path_append {p q : List (Edge S.Pt S.Ed)} (hp : p ≠ []) (hq : q ≠ [])
    (hpq : S.IsPath (p ++ q)) :
    ∃ h, (I.path (p ++ q) hpq.ne_nil).Equiv ((I.path p hp).paste (I.path q hq) 0 h) := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp
  obtain _ | ⟨f, q⟩ := q
  · exact absurd rfl hq
  obtain ⟨x, z, hxz⟩ := S.exists_pathEnds_of_isPath hpq
  rw [List.cons_append] at hxz
  exact I.equiv_pathCons_append (S.pathEnds_cons_eq_some.1 hxz).2

theorem pathCons_mapTo (f : X ⟶ Y) {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} {y : S.Pt}
    (h : S.walk (S.tgt e) p = some y) :
    ((I.mapTo f).pathCons e p).Equiv ((I.pathCons e p).mapTo f) := by
  induction p generalizing e with
  | nil => exact PastingDiagram.equiv_of_eq (I.ofEdge_mapTo f e)
  | cons g p ih =>
    obtain ⟨hg, hp⟩ := S.walk_cons_eq_some.1 h
    have he := I.hasRoundType_ofEdge e
    rw [← hg] at he
    have h₀ := he.pastable (I.pathCons_spec hp).1 (.refl _) dimension_atomPoint
    have h₁ := (h₀.mapTo f).of_equiv (PastingDiagram.equiv_of_eq (I.ofEdge_mapTo f e).symm)
      (ih hp).symm
    have hc : (I.mapTo f).pathCons e (g :: p) = ((I.mapTo f).ofEdge e).paste
      ((I.mapTo f).pathCons g p) 0 h₁ := pasteOr_of h₁
    have hc' : I.pathCons e (g :: p) = (I.ofEdge e).paste (I.pathCons g p) 0 h₀ := pasteOr_of h₀
    rw [hc, hc']
    exact (Equiv.paste (PastingDiagram.equiv_of_eq (I.ofEdge_mapTo f e)) (ih hp) h₁
      (h₀.mapTo f)).trans (paste_mapTo _ _ 0 h₀ f (h₀.mapTo f)).symm

theorem path_mapTo (f : X ⟶ Y) {p : List (Edge S.Pt S.Ed)} (hp : S.IsPath p) :
    ((I.mapTo f).path p hp.ne_nil).Equiv ((I.path p hp.ne_nil).mapTo f) := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp.ne_nil
  obtain ⟨x, y, h⟩ := S.exists_pathEnds_of_isPath hp
  exact I.pathCons_mapTo f (S.pathEnds_cons_eq_some.1 h).2

end Paths

private theorem unitorAt_refl_mapTo (u : PastingDiagram X) (hd : 0 < u.dim) (hu : u.IsRound)
    (σ : Bool) (f : X ⟶ Y) {u' : PastingDiagram Y} (h : u' = u.mapTo f) (hd' : 0 < u'.dim)
    (hu' : u'.IsRound) :
    unitorAt u' hd' hu' σ (Within.refl _)
        (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound hu' _ σ)) =
      (unitorAt u hd hu σ (Within.refl _)
        (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound hu _ σ))).mapTo f := by
  subst h
  exact congrArg (PastingDiagram.mk _) (Category.assoc _ _ _).symm

noncomputable def edgeUnitor (σ : Bool) (e : Edge S.Pt S.Ed) : PastingDiagram X :=
  unitorAt (I.ofEdge e) (by rw [I.dim_ofEdge]; exact Nat.one_pos) (I.isRound_ofEdge e) σ
    (Within.refl _)
    (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound (I.isRound_ofEdge e) _ σ))

theorem isDegenerate_edgeUnitor (σ : Bool) (e : Edge S.Pt S.Ed) :
    (I.edgeUnitor σ e).IsDegenerate :=
  (isDegenerate_unitorAt _ _ _ _ _ _).1

theorem isRound_edgeUnitor (σ : Bool) (e : Edge S.Pt S.Ed) : (I.edgeUnitor σ e).IsRound :=
  (isDegenerate_unitorAt _ _ _ _ _ _).2

theorem path_unitPath (σ : Bool) (e : Edge S.Pt S.Ed) (h : S.unitPath σ e ≠ []) :
    I.path (S.unitPath σ e) h =
      (cond σ (I.ofEdge e) (I.ofEdge (.unit (S.src e)))).pasteOr
        (cond σ (I.ofEdge (.unit (S.tgt e))) (I.ofEdge e)) 0 := by
  cases σ <;> rfl

noncomputable def unitorDiagram : UnitorKind → Edge S.Pt S.Ed → PastingDiagram X
  | .left, e => (I.edgeUnitor false e).reverse (I.isDegenerate_edgeUnitor false e)
  | .leftInverse, e => I.edgeUnitor false e
  | .right, e => I.edgeUnitor true e
  | .rightInverse, e => (I.edgeUnitor true e).reverse (I.isDegenerate_edgeUnitor true e)

theorem edgeUnitor_mapTo (f : X ⟶ Y) (σ : Bool) (e : Edge S.Pt S.Ed) :
    (I.mapTo f).edgeUnitor σ e = (I.edgeUnitor σ e).mapTo f :=
  unitorAt_refl_mapTo _ _ _ σ f (I.ofEdge_mapTo f e) _ _

theorem unitorDiagram_mapTo (f : X ⟶ Y) (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    ((I.mapTo f).unitorDiagram k e).Equiv ((I.unitorDiagram k e).mapTo f) := by
  have h (σ : Bool) := PastingDiagram.equiv_of_eq (I.edgeUnitor_mapTo f σ e)
  cases k
  · exact (h false |>.reverse _ ((I.isDegenerate_edgeUnitor false e).mapTo f)).trans
      (reverse_mapTo _ _ f _).symm
  · exact h false
  · exact h true
  · exact (h true |>.reverse _ ((I.isDegenerate_edgeUnitor true e).mapTo f)).trans
      (reverse_mapTo _ _ f _).symm

theorem isRound_unitorDiagram (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    (I.unitorDiagram k e).IsRound := by
  cases k
  · exact isRound_reverse _ (I.isRound_edgeUnitor false e)
  · exact I.isRound_edgeUnitor false e
  · exact I.isRound_edgeUnitor true e
  · exact isRound_reverse _ (I.isRound_edgeUnitor true e)

variable [DecidableEq S.Pt]

theorem hasRoundType_edgeUnitor (σ : Bool) (e : Edge S.Pt S.Ed) :
    HasRoundType (I.edgeUnitor σ e)
      (cond σ (I.pathRound (S.unitPath σ e) (S.isPath_unitPath σ e))
        (I.pathRound [e] (S.isPath_singleton e)))
      (cond σ (I.pathRound [e] (S.isPath_singleton e))
        (I.pathRound (S.unitPath σ e) (S.isPath_unitPath σ e))) := by
  set u := I.ofEdge e
  have hd : u.dim = 1 := I.dim_ofEdge e
  have hu := I.isRound_ofEdge e
  have hk : u.dim - 1 = 0 := by rw [hd]
  have hself : ((I.edgeUnitor σ e).boundary 1 σ).Equiv u := by
    have h := equiv_boundary_unitorAt u (by rw [hd]; exact Nat.one_pos) hu σ (Within.refl _)
      (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound hu _ σ))
    rw [boundary_congr _ hd σ] at h
    exact h
  set v := u.boundary (u.dim - 1) σ
  have hv : v.dim = u.dim - 1 := dim_boundary u (Nat.sub_le _ _) σ
  have hvu : (v.unit.boundary (u.dim - 1) (!σ)).Equiv v := boundary_unit hv (!σ)
  have hp : (cond σ u v.unit).Pastable (cond σ v.unit u) (u.dim - 1) :=
    Pastable.of_side σ hvu.symm (by omega) (by rw [dim_unit]; omega)
  have hpt : v.Equiv (PastingDiagram.ofCell (I.point (cond σ (S.tgt e) (S.src e)))) := by
    have h := (I.hasRoundType_ofEdge e).equiv_boundary_cond (k := u.dim - 1)
      (by rw [hk]; exact dimension_atomPoint) σ
    cases σ <;> exact h
  have hε : v.unit.Equiv (I.ofEdge (.unit (cond σ (S.tgt e) (S.src e)))) := Equiv.unit hpt
  have hnot : ((I.edgeUnitor σ e).boundary 1 (!σ)).Equiv
      (I.path (S.unitPath σ e) (S.isPath_unitPath σ e).ne_nil) := by
    have h := equiv_boundary_not_unitorAt u (by rw [hd]; exact Nat.one_pos) hu σ (Within.refl _)
      (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound hu _ σ)) hvu
    rw [boundary_congr _ hd (!σ)] at h
    refine h.trans ((equiv_paste_pasteAtBoundary v.unit u _ σ _ _ (Within.image_refl _) hvu
      hp).symm.trans ?_)
    rw [I.path_unitPath σ e]
    refine (Equiv.paste (.cond (.refl _) σ hε) (.cond hε σ (.refl _)) hp ?_).trans ?_
    · exact hp.of_equiv (.cond (.refl _) σ hε) (.cond hε σ (.refl _))
    · cases σ <;> exact PastingDiagram.equiv_of_eq (paste_eq_pasteOr _ hk rfl rfl)
  have hdim : (I.edgeUnitor σ e).dim = 1 + 1 :=
    (dim_cylDiagram u _ (unitorSubset_le_bdryFull u _ hu σ _ _)).trans (by rw [hd])
  cases σ
  · refine .of_equiv_boundary (I.dim_path (S.isPath_singleton e))
      (I.dim_path (S.isPath_unitPath _ e)) hdim fun β => ?_
    cases β
    exacts [hself, hnot]
  · refine .of_equiv_boundary (I.dim_path (S.isPath_unitPath _ e))
      (I.dim_path (S.isPath_singleton e)) hdim fun β => ?_
    cases β
    exacts [hnot, hself]

theorem hasRoundType_unitorDiagram (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    HasRoundType (I.unitorDiagram k e)
      (I.pathRound _ (S.isPath_cellType_unitor_fst k e))
      (I.pathRound _ (S.isPath_cellType_unitor_snd k e)) := by
  cases k
  · exact (I.hasRoundType_edgeUnitor false e).reverse _
  · exact I.hasRoundType_edgeUnitor false e
  · exact I.hasRoundType_edgeUnitor true e
  · exact (I.hasRoundType_edgeUnitor true e).reverse _

end PathInterp

end Signature

end Atoms.Diagrammatic.Layered
