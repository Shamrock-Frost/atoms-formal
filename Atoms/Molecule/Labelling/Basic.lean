import Atoms.Molecule.Path
import Atoms.Molecule.RegularComplex.Basic
import Atoms.ForMathlib.CategoryTheory.Bicategory.Coherence

universe w v u u' u'' u₁

open Order CategoryTheory Bicategory

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

@[implicit_reducible]
def EdgeQuiver (P : OGP.{u}) : Type u := P

instance : Quiver (EdgeQuiver P) where
  Hom v w := {e : P // grade ℕ e = 1 ∧ P.boundary (.Iic e) 0 false = .Iic v ∧
    P.boundary (.Iic e) 0 true = .Iic w}

def pathEdges {v : EdgeQuiver P} : {w : EdgeQuiver P} → Quiver.Path v w → List P
  | _, .nil => []
  | _, .cons p e => pathEdges p ++ [e.1]

@[simp]
theorem pathEdges_nil (v : EdgeQuiver P) : pathEdges (Quiver.Path.nil : Quiver.Path v v) = [] :=
  rfl

@[simp]
theorem pathEdges_cons {u v w : EdgeQuiver P} (p : Quiver.Path u v) (e : v ⟶ w) :
    pathEdges (p.cons e) = pathEdges p ++ [e.1] :=
  rfl

@[simp]
theorem pathEdges_comp {u v : EdgeQuiver P} (p : Quiver.Path u v) :
    ∀ {w : EdgeQuiver P} (q : Quiver.Path v w), pathEdges (p.comp q) = pathEdges p ++ pathEdges q
  | _, .nil => by simp
  | _, .cons q e => by simp [pathEdges_comp p q]

@[simp]
theorem length_pathEdges {v : EdgeQuiver P} :
    ∀ {w : EdgeQuiver P} (p : Quiver.Path v w), (pathEdges p).length = p.length
  | _, .nil => rfl
  | _, .cons p e => by simp [length_pathEdges p]

theorem eq_of_pathEdges_eq {v : EdgeQuiver P} :
    ∀ {w : EdgeQuiver P} {p q : Quiver.Path v w}, pathEdges p = pathEdges q → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons q e, h => by simp at h
  | _, .cons p e, .nil, h => by simp at h
  | _, .cons (b := b) p e, .cons (b := b') q e', h => by
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    have he : e.1 = e'.1 := List.singleton_inj.1 h₂
    obtain rfl : b = b' := LowerSet.Iic_injective (α := P) (e.2.2.1.symm.trans (he ▸ e'.2.2.1))
    rw [eq_of_pathEdges_eq h₁, Subtype.ext he]

private theorem pathEdges_spec {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b), (∀ x ∈ pathEdges p, grade ℕ x = 1) ∧
      (pathEdges p).IsChain (fun x y => P.boundary (.Iic x) 0 true =
        P.boundary (.Iic y) 0 false) ∧
      (∀ x ∈ (pathEdges p).head?, P.boundary (.Iic x) 0 false = .Iic a) ∧
      (∀ x ∈ (pathEdges p).getLast?, P.boundary (.Iic x) 0 true = .Iic b) ∧
      (pathEdges p = [] → a = b)
  | _, .nil => ⟨by simp, .nil, by simp, by simp, fun _ => rfl⟩
  | _, .cons (b := c) p e => by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := pathEdges_spec p
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · simp only [pathEdges_cons, List.mem_append, List.mem_singleton]
      rintro x (hx | rfl)
      exacts [h₁ x hx, e.2.1]
    · refine h₂.append (.singleton _) fun x hx y hy => ?_
      rw [List.head?_singleton, Option.mem_some_iff] at hy
      rw [← hy, h₄ x hx, e.2.2.1]
    · intro x hx
      rw [pathEdges_cons, List.head?_append] at hx
      cases hp : pathEdges p with
      | nil =>
        rw [hp, List.head?_nil, Option.none_or, List.head?_singleton, Option.mem_some_iff] at hx
        rw [← hx, e.2.2.1, h₅ hp]
      | cons y l =>
        rw [hp, List.head?_cons, Option.some_or, Option.mem_some_iff] at hx
        exact h₃ x (by rw [hp, ← hx]; rfl)
    · intro x hx
      rw [pathEdges_cons, List.getLast?_concat, Option.mem_some_iff] at hx
      rw [← hx, e.2.2.2]

theorem grade_of_mem_pathEdges {a b : EdgeQuiver P} (p : Quiver.Path a b) {x : P}
    (hx : x ∈ pathEdges p) : grade ℕ x = 1 :=
  (pathEdges_spec p).1 x hx

section Path

variable [Fintype P] [DecidableLE P]

def vertex (U : LowerSet P) [DecidablePred (· ∈ U)] (hU : IsMoleculeIn P U) (α : Bool) : P :=
  Fintype.choose (· ∈ P.boundary U 0 α) (by
    obtain ⟨v, hv, h⟩ := exists_boundary_zero_eq_Iic hU α
    refine ⟨v, by rw [h]; exact LowerSet.mem_Iic_iff.2 le_rfl, fun y hy => ?_⟩
    rw [h, LowerSet.mem_Iic_iff] at hy
    exact hy.antisymm (hv hy))

theorem boundary_zero_eq_Iic_vertex (U : LowerSet P) [DecidablePred (· ∈ U)]
    (hU : IsMoleculeIn P U) (α : Bool) : P.boundary U 0 α = .Iic (vertex U hU α) := by
  obtain ⟨v, hv, h⟩ := exists_boundary_zero_eq_Iic hU α
  have hmem : vertex U hU α ∈ P.boundary U 0 α := Fintype.choose_spec (· ∈ P.boundary U 0 α) _
  rw [h, LowerSet.mem_Iic_iff] at hmem
  rw [h, hmem.antisymm (hv hmem)]

omit [Fintype P] [DecidableLE P] in
theorem grade_eq_zero_of_boundary_zero_eq_Iic {U : LowerSet P} {α : Bool} {v : P}
    (h : P.boundary U 0 α = .Iic v) : grade ℕ v = 0 := by
  have hd := krullDim_boundary_le U 0 α
  rw [h, LowerSet.krullDim_Iic] at hd
  exact Nat.le_zero.1 (by exact_mod_cast hd)

theorem vertex_eq_of_boundary_zero_eq_Iic (U : LowerSet P) [DecidablePred (· ∈ U)]
    (hU : IsMoleculeIn P U) {α : Bool} {v : P} (h : P.boundary U 0 α = .Iic v) :
    vertex U hU α = v :=
  LowerSet.Iic_injective ((boundary_zero_eq_Iic_vertex U hU α).symm.trans h)

theorem vertex_Iic_of_boundary_Iic {x v : P} {β : Bool} (hv : P.boundary (.Iic x) 0 β = .Iic v)
    (hv' : IsMoleculeIn P (.Iic v)) : vertex (.Iic v) hv' false = v :=
  vertex_eq_of_boundary_zero_eq_Iic _ hv' (boundary_Iic_of_isMin
    (grade_eq_zero_iff.1 (grade_eq_zero_of_boundary_zero_eq_Iic hv)) 0 false)

private def IsWalk : P → List P → P → Prop
  | a, [], b => a = b
  | a, x :: l, b => IsMoleculeIn P (.Iic x) ∧ grade ℕ x = 1 ∧
      P.boundary (.Iic x) 0 false = .Iic a ∧
      ∀ hx : IsMoleculeIn P (.Iic x), IsWalk (vertex (.Iic x) hx true) l b

private def pathOfList : (l : List P) → (a b : P) → IsWalk a l b →
    Quiver.Path (V := EdgeQuiver P) a b
  | [], _, _, h => h ▸ .nil
  | x :: l, a, b, h =>
    (Quiver.Hom.toPath (V := EdgeQuiver P) (a := a) (b := vertex (.Iic x) h.1 true)
      (Subtype.mk x ⟨h.2.1, h.2.2.1, boundary_zero_eq_Iic_vertex _ h.1 true⟩)).comp
      (pathOfList l _ b (h.2.2.2 h.1))

private theorem pathEdges_pathOfList :
    ∀ (l : List P) (a b : P) (h : IsWalk a l b), pathEdges (pathOfList l a b h) = l
  | [], a, _, h => by
    cases h
    rfl
  | x :: l, a, b, h => by
    rw [pathOfList, pathEdges_comp, pathEdges_pathOfList l]
    rfl

private theorem isWalk_of_isChain {b : P} :
    ∀ (l : List P) (a : P), (∀ x ∈ l, IsMoleculeIn P (.Iic x) ∧ grade ℕ x = 1) →
      l.IsChain (fun x y => P.boundary (.Iic x) 0 true = P.boundary (.Iic y) 0 false) →
      (∀ x ∈ l.head?, P.boundary (.Iic x) 0 false = .Iic a) →
      (∀ x ∈ l.getLast?, P.boundary (.Iic x) 0 true = .Iic b) → (l = [] → a = b) →
      IsWalk a l b
  | [], _, _, _, _, _, hn => hn rfl
  | x :: l, a, hl, hc, hh, ht, _ => by
    have hx := hl x List.mem_cons_self
    refine ⟨hx.1, hx.2, hh x rfl, fun hx' => isWalk_of_isChain l _
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hc.tail (fun y hy => ?_) (fun y hy => ?_)
      fun hnil => ?_⟩
    · rw [← (List.isChain_cons.1 hc).1 y hy, boundary_zero_eq_Iic_vertex _ hx' true]
    · refine ht y ?_
      rw [Option.mem_def] at hy ⊢
      rw [List.getLast?_cons, hy]
      rfl
    · subst hnil
      exact LowerSet.Iic_injective ((boundary_zero_eq_Iic_vertex _ hx' true).symm.trans (ht x rfl))

def pathOf (U : LowerSet P) [DecidablePred (· ∈ U)] (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) {v w : P} (hv : P.boundary U 0 false = .Iic v)
    (hw : P.boundary U 0 true = .Iic w) : Quiver.Path (V := EdgeQuiver P) v w :=
  pathOfList (edgeList U) v w (isWalk_of_isChain _ _
    (fun x hx => ⟨(hU.isAtomIn_Iic ((mem_edgeList_iff hU hd).1 hx).1).isMoleculeIn,
      ((mem_edgeList_iff hU hd).1 hx).2⟩)
    (edgeList_isChain hU hd) (fun x hx => (boundary_Iic_of_mem_head?_edgeList hU hd hx).trans hv)
    (fun x hx => (boundary_Iic_of_mem_getLast?_edgeList hU hd hx).trans hw)
    fun hnil => by
      obtain ⟨n, hn⟩ : ∃ n, (edgeList U).length = n := ⟨_, rfl⟩
      have h₀ := segment_cond_zero hU hd false
      have h₁ := segment_cond_zero hU hd true
      rw [hnil] at h₀ h₁
      exact LowerSet.Iic_injective (hv.symm.trans (h₀.symm.trans (h₁.trans hw))))

variable {U : LowerSet P} [DecidablePred (· ∈ U)]

@[simp]
theorem pathEdges_pathOf (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {v w : P}
    (hv : P.boundary U 0 false = .Iic v) (hw : P.boundary U 0 true = .Iic w) :
    pathEdges (pathOf U hU hd hv hw) = edgeList U :=
  pathEdges_pathOfList _ _ _ _

theorem length_pathOf (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {v w : P}
    (hv : P.boundary U 0 false = .Iic v) (hw : P.boundary U 0 true = .Iic w) :
    (pathOf U hU hd hv hw).length = (edgeList U).length := by
  rw [← length_pathEdges, pathEdges_pathOf]

theorem eq_pathOf_of_forall_mem (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {v w : P}
    (hv : P.boundary U 0 false = .Iic v) (hw : P.boundary U 0 true = .Iic w)
    (q : Quiver.Path (V := EdgeQuiver P) v w) (hq : ∀ x ∈ pathEdges q, x ∈ U) :
    q = pathOf U hU hd hv hw := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := pathEdges_spec q
  refine eq_of_pathEdges_eq ?_
  rw [pathEdges_pathOf]
  refine edgeList_eq_of_isChain hU hd (fun x hx => ⟨hq x hx, h₁ x hx⟩) h₂
    (fun x hx => (h₃ x hx).trans hv.symm) (fun x hx => (h₄ x hx).trans hw.symm) fun hn => ?_
  rw [hv, hw, h₅ hn]

theorem pathOf_eq_comp {V W : LowerSet P} [DecidablePred (· ∈ V)] [DecidablePred (· ∈ W)]
    (hp : P.IsPastingIn 0 V W U) (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hdV : krullDim V ≤ 1) (hW : IsMoleculeIn P W)
    (hdW : krullDim W ≤ 1) {v x w : P} (hv : P.boundary U 0 false = .Iic v)
    (hw : P.boundary U 0 true = .Iic w) (hv' : P.boundary V 0 false = .Iic v)
    (hx : P.boundary V 0 true = .Iic x) (hx' : P.boundary W 0 false = .Iic x)
    (hw' : P.boundary W 0 true = .Iic w) :
    pathOf U hU hd hv hw = (pathOf V hV hdV hv' hx).comp (pathOf W hW hdW hx' hw') := by
  refine (eq_pathOf_of_forall_mem hU hd hv hw _ fun y hy => ?_).symm
  rw [pathEdges_comp, List.mem_append, pathEdges_pathOf, pathEdges_pathOf] at hy
  rcases hy with hy | hy
  · exact hp.left_le ((mem_edgeList_iff hV hdV).1 hy).1
  · exact hp.right_le ((mem_edgeList_iff hW hdW).1 hy).1

theorem pathOf_congr {V : LowerSet P} [DecidablePred (· ∈ V)] (e : U = V)
    {hU : IsMoleculeIn P U} {hd : krullDim U ≤ 1} {hV : IsMoleculeIn P V} {hdV : krullDim V ≤ 1}
    {v w : P} {hv : P.boundary U 0 false = .Iic v} {hw : P.boundary U 0 true = .Iic w}
    {hv' : P.boundary V 0 false = .Iic v} {hw' : P.boundary V 0 true = .Iic w} :
    pathOf U hU hd hv hw = pathOf V hV hdV hv' hw' := by
  refine eq_pathOf_of_forall_mem hV hdV hv' hw' _ fun y hy => ?_
  rw [pathEdges_pathOf] at hy
  exact e ▸ ((mem_edgeList_iff hU hd).1 hy).1

theorem pathOf_Iic_of_grade_eq_one {x : P} (hx : grade ℕ x = 1)
    [DecidablePred (· ∈ LowerSet.Iic x)] (hU : IsMoleculeIn P (.Iic x))
    (hd : krullDim (LowerSet.Iic x) ≤ 1) {v w : P} (hv : P.boundary (.Iic x) 0 false = .Iic v)
    (hw : P.boundary (.Iic x) 0 true = .Iic w) :
    pathOf (.Iic x) hU hd hv hw = Quiver.Hom.toPath (V := EdgeQuiver P)
      (⟨x, hx, hv, hw⟩ : Quiver.Hom (V := EdgeQuiver P) v w) :=
  (eq_pathOf_of_forall_mem hU hd hv hw _ fun y hy => by
    simp only [Quiver.Hom.toPath, pathEdges_cons, pathEdges_nil, List.nil_append,
      List.mem_singleton] at hy
    exact hy ▸ LowerSet.mem_Iic_iff.2 le_rfl).symm

variable {V : LowerSet P} [DecidablePred (· ∈ V)]

private theorem boundary_segment_of_add_le (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    {i m : ℕ} (him : i + m ≤ (edgeList U).length) (α : Bool) :
    P.boundary (segment U i m) 0 α = segment U (i + cond α m 0) 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [boundary_segment_zero hU hd (by omega)]
    cases α <;> rfl
  · exact boundary_segment hU hd hm him α

omit [DecidablePred (· ∈ V)] in
private theorem exists_segment_pos (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hVd : krullDim V = 1) (hVU : V ≤ U) :
    ∃ i, ∃ m < (edgeList U).length + 1, i + m ≤ (edgeList U).length ∧
      ∀ y, y ∈ segment U i m ↔ y ∈ V := by
  obtain ⟨i, m, -, him, rfl⟩ := exists_segment_eq hU hd hV hVd hVU
  exact ⟨i, m, by omega, him, fun _ => Iff.rfl⟩

private def segPos (h : ∃ i, ∃ m < (edgeList U).length + 1, i + m ≤ (edgeList U).length ∧
    ∀ y, y ∈ segment U i m ↔ y ∈ V) : ℕ :=
  Nat.find h

private def segLen (h : ∃ i, ∃ m < (edgeList U).length + 1, i + m ≤ (edgeList U).length ∧
    ∀ y, y ∈ segment U i m ↔ y ∈ V) : ℕ :=
  Nat.find (by
    obtain ⟨m, -, hm⟩ := Nat.find_spec h
    exact ⟨m, hm⟩ : ∃ m, segPos h + m ≤ (edgeList U).length ∧ ∀ y, y ∈ segment U (segPos h) m ↔
      y ∈ V)

private theorem segPos_spec (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) (hVd : krullDim V = 1)
    (h : ∃ i, ∃ m < (edgeList U).length + 1, i + m ≤ (edgeList U).length ∧
      ∀ y, y ∈ segment U i m ↔ y ∈ V) :
    0 < segLen h ∧ segPos h + segLen h ≤ (edgeList U).length ∧
      segment U (segPos h) (segLen h) = V := by
  have hs := Nat.find_spec (by
    obtain ⟨m, -, hm⟩ := Nat.find_spec h
    exact ⟨m, hm⟩ : ∃ m, segPos h + m ≤ (edgeList U).length ∧ ∀ y, y ∈ segment U (segPos h) m ↔
      y ∈ V)
  have he : segment U (segPos h) (segLen h) = V := SetLike.ext hs.2
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hs.1, he⟩
  have hb := boundary_segment_zero hU hd (i := segPos h) (by have := hs.1; omega) 0 false
  rw [h0] at he
  rw [he] at hb
  have := krullDim_boundary_le V 0 false
  rw [hb, hVd] at this
  exact absurd this (by simp)

def pathBefore (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) (hV : IsMoleculeIn P V)
    (hVd : krullDim V = 1) (hVU : V ≤ U) {s a : P} (hs : P.boundary U 0 false = .Iic s)
    (ha : P.boundary V 0 false = .Iic a) : Quiver.Path (V := EdgeQuiver P) s a :=
  have h := exists_segment_pos hU hd hV hVd hVU
  have hp := segPos_spec hU hd hVd h
  pathOf (segment U 0 (segPos h)) (isMoleculeIn_segment hU hd (by omega))
    ((LowerSet.krullDim_mono (segment_le hU hd (by omega))).trans hd)
    (by
      rw [boundary_segment_of_add_le hU hd (by omega)]
      exact (segment_cond_zero hU hd false).trans hs)
    (by
      rw [boundary_segment_of_add_le hU hd (by omega), ← ha,
        ← congrArg (P.boundary · 0 false) hp.2.2, boundary_segment_of_add_le hU hd hp.2.1]
      simp only [cond_true, cond_false, Nat.zero_add, Nat.add_zero])

def pathAfter (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) (hV : IsMoleculeIn P V)
    (hVd : krullDim V = 1) (hVU : V ≤ U) {b t : P} (hb : P.boundary V 0 true = .Iic b)
    (ht : P.boundary U 0 true = .Iic t) : Quiver.Path (V := EdgeQuiver P) b t :=
  have h := exists_segment_pos hU hd hV hVd hVU
  have hp := segPos_spec hU hd hVd h
  pathOf (segment U (segPos h + segLen h) ((edgeList U).length - (segPos h + segLen h)))
    (isMoleculeIn_segment hU hd (by omega))
    ((LowerSet.krullDim_mono (segment_le hU hd (by omega))).trans hd)
    (by
      rw [boundary_segment_of_add_le hU hd (by omega), ← hb,
        ← congrArg (P.boundary · 0 true) hp.2.2, boundary_segment_of_add_le hU hd hp.2.1]
      simp only [cond_true, cond_false, Nat.add_zero])
    (by
      rw [boundary_segment_of_add_le hU hd (by omega), ← ht, ← segment_cond_zero hU hd true]
      congr 1
      simp only [cond_true]
      omega)

theorem pathOf_eq_pathBefore_comp (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hVd : krullDim V = 1) (hVU : V ≤ U) {s a b t : P}
    (hs : P.boundary U 0 false = .Iic s) (ha : P.boundary V 0 false = .Iic a)
    (hb : P.boundary V 0 true = .Iic b) (ht : P.boundary U 0 true = .Iic t) :
    pathOf U hU hd hs ht = (pathBefore hU hd hV hVd hVU hs ha).comp
      ((pathOf V hV hVd.le ha hb).comp (pathAfter hU hd hV hVd hVU hb ht)) := by
  refine (eq_pathOf_of_forall_mem hU hd hs ht _ fun y hy => ?_).symm
  simp only [pathEdges_comp, List.mem_append, pathBefore, pathAfter, pathEdges_pathOf] at hy
  have h := exists_segment_pos hU hd hV hVd hVU
  have hp := segPos_spec hU hd hVd h
  rcases hy with hy | hy | hy
  · exact segment_le hU hd (by omega) ((mem_edgeList_iff (isMoleculeIn_segment hU hd (by omega))
      ((LowerSet.krullDim_mono (segment_le hU hd (by omega))).trans hd)).1 hy).1
  · exact hVU ((mem_edgeList_iff hV hVd.le).1 hy).1
  · exact segment_le hU hd (by omega) ((mem_edgeList_iff (isMoleculeIn_segment hU hd (by omega))
      ((LowerSet.krullDim_mono (segment_le hU hd (by omega))).trans hd)).1 hy).1

theorem length_pathOf_ne_zero (hU : IsMoleculeIn P U) (hd : krullDim U = 1) {v w : P}
    (hv : P.boundary U 0 false = .Iic v) (hw : P.boundary U 0 true = .Iic w) :
    (pathOf U hU hd.le hv hw).length ≠ 0 := by
  rw [length_pathOf]
  exact fun h => edgeList_ne_nil hU hd (List.eq_nil_of_length_eq_zero h)

end Path

private theorem exists_eq_comp_of_comp_eq {V : Type*} [Quiver V] {a b b' : V} {p : Quiver.Path a b}
    {p' : Quiver.Path a b'} :
    ∀ {c : V} {q₁ : Quiver.Path b c} {q₂ : Quiver.Path b' c}, p.comp q₁ = p'.comp q₂ →
      p.length ≤ p'.length → ∃ m : Quiver.Path b b', p' = p.comp m ∧ q₁ = m.comp q₂
  | _, q₁, .nil, h, _ => ⟨q₁, h.symm, rfl⟩
  | _, .nil, .cons q₂ e, h, hl => by
    have := congrArg Quiver.Path.length h
    simp only [Quiver.Path.comp_nil, Quiver.Path.comp_cons, Quiver.Path.length_cons,
      Quiver.Path.length_comp] at this
    omega
  | _, .cons q₁ e, .cons q₂ e', h, hl => by
    simp only [Quiver.Path.comp_cons] at h
    obtain rfl := Quiver.Path.obj_eq_of_cons_eq_cons h
    have h' := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
    obtain rfl := eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h)
    obtain ⟨m, rfl, rfl⟩ := exists_eq_comp_of_comp_eq h' hl
    exact ⟨m, rfl, rfl⟩

private theorem getElem?_pathEdges_comp_comp {s a b t : EdgeQuiver P} (p : Quiver.Path s a)
    (q : Quiver.Path a b) (r : Quiver.Path b t) {j : ℕ} (hj : j < q.length) :
    (pathEdges (p.comp (q.comp r)))[p.length + j]? = (pathEdges q)[j]? := by
  rw [pathEdges_comp, pathEdges_comp, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simpa using hj), length_pathEdges, Nat.add_sub_cancel_left]

theorem eq_and_eq_of_comp_comp_eq {s a b t : EdgeQuiver P} {p p' : Quiver.Path s a}
    {q : Quiver.Path a b} {r r' : Quiver.Path b t} (hn : (pathEdges (p.comp (q.comp r))).Nodup)
    (hq : q.length ≠ 0) (h : p.comp (q.comp r) = p'.comp (q.comp r')) : p = p' ∧ r = r' := by
  have hl : p.length = p'.length := by
    have e₁ := getElem?_pathEdges_comp_comp p q r (j := 0) (by omega)
    have e₂ := getElem?_pathEdges_comp_comp p' q r' (j := 0) (by omega)
    rw [← h, ← e₁] at e₂
    refine ((List.getElem?_inj ?_ hn).1 e₂).symm
    rw [h]
    simp only [pathEdges_comp, List.length_append, length_pathEdges]
    omega
  obtain ⟨rfl, h'⟩ := Quiver.Path.comp_inj' hl |>.1 h
  exact ⟨rfl, Quiver.Path.comp_inj_right.1 h'⟩

theorem exists_eq_comp_comp_or_exists_eq_comp_comp {s a b c d t : EdgeQuiver P}
    {p : Quiver.Path s a} {q : Quiver.Path a b} {r : Quiver.Path b t} {p' : Quiver.Path s c}
    {q' : Quiver.Path c d} {r' : Quiver.Path d t} (h : p.comp (q.comp r) = p'.comp (q'.comp r'))
    (hn : (pathEdges (p.comp (q.comp r))).Nodup) (hq : q.length ≠ 0) (hq' : q'.length ≠ 0)
    (hd : ∀ x ∈ pathEdges q, x ∉ pathEdges q') :
    (∃ m : Quiver.Path b c, p' = p.comp (q.comp m) ∧ r = m.comp (q'.comp r')) ∨
      ∃ m : Quiver.Path d a, p = p'.comp (q'.comp m) ∧ r' = m.comp (q.comp r) := by
  by_cases h₁ : p.length + q.length ≤ p'.length
  · obtain ⟨m, hm, rfl⟩ := exists_eq_comp_of_comp_eq (q₁ := r)
      ((Quiver.Path.comp_assoc p q r).trans h) (by simpa using h₁)
    exact .inl ⟨m, hm.trans (Quiver.Path.comp_assoc p q m), rfl⟩
  by_cases h₂ : p'.length + q'.length ≤ p.length
  · obtain ⟨m, hm, rfl⟩ := exists_eq_comp_of_comp_eq (q₁ := r')
      ((Quiver.Path.comp_assoc p' q' r').trans h.symm) (by simpa using h₂)
    exact .inr ⟨m, hm.trans (Quiver.Path.comp_assoc p' q' m), rfl⟩
  exfalso
  have e₁ := getElem?_pathEdges_comp_comp p q r (j := max p.length p'.length - p.length)
    (by omega)
  have e₂ := getElem?_pathEdges_comp_comp p' q' r' (j := max p.length p'.length - p'.length)
    (by omega)
  rw [Nat.add_sub_cancel' (le_max_left _ _)] at e₁
  rw [Nat.add_sub_cancel' (le_max_right _ _), ← h, e₁] at e₂
  have hj : max p.length p'.length - p.length < (pathEdges q).length := by
    rw [length_pathEdges]
    omega
  have hx := List.getElem?_eq_getElem hj
  exact hd _ (List.getElem_mem hj) (List.mem_of_getElem? (e₂.symm.trans hx))

structure Labelling (B : Type u₁) [Bicategory.{w, v} B] (P : OGP.{u}) [Fintype P]
    [DecidableLE P] (hP : P.IsRDC) where
  toPrefunctor : Prefunctor (EdgeQuiver P) B
  obj_eq_of_boundary_Iic (x : P) {v : P} (hv : P.boundary (.Iic x) 0 false = .Iic v) :
    toPrefunctor.obj x = toPrefunctor.obj v
  cell (x : P) (hx : grade ℕ x = 2) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    pathComp toPrefunctor (pathOf (P.boundary (.Iic x) 1 false) ((hP x).boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)) ⟶
      pathComp toPrefunctor (pathOf (P.boundary (.Iic x) 1 true) ((hP x).boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht))

section Path

variable [Fintype P] [DecidableLE P] {U V W : LowerSet P} [DecidablePred (· ∈ U)]
  [DecidablePred (· ∈ V)] [DecidablePred (· ∈ W)]

theorem exists_pathOf_eq_comp_comp_or (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hVd : krullDim V = 1) (hVU : V ≤ U) (hW : IsMoleculeIn P W)
    (hWd : krullDim W = 1) (hWU : W ≤ U) (hVW : ∀ e ∈ V, e ∈ W → grade ℕ e ≠ 1) {s a b c d t : P}
    (hs : P.boundary U 0 false = .Iic s) (ht : P.boundary U 0 true = .Iic t)
    (ha : P.boundary V 0 false = .Iic a) (hb : P.boundary V 0 true = .Iic b)
    (hc : P.boundary W 0 false = .Iic c) (hd' : P.boundary W 0 true = .Iic d) :
    (∃ (p : Quiver.Path (V := EdgeQuiver P) s a) (m : Quiver.Path (V := EdgeQuiver P) b c)
        (r : Quiver.Path (V := EdgeQuiver P) d t), pathOf U hU hd hs ht = p.comp
          ((pathOf V hV hVd.le ha hb).comp (m.comp ((pathOf W hW hWd.le hc hd').comp r)))) ∨
      ∃ (p : Quiver.Path (V := EdgeQuiver P) s c) (m : Quiver.Path (V := EdgeQuiver P) d a)
        (r : Quiver.Path (V := EdgeQuiver P) b t), pathOf U hU hd hs ht = p.comp
          ((pathOf W hW hWd.le hc hd').comp (m.comp ((pathOf V hV hVd.le ha hb).comp r))) := by
  have e₁ := pathOf_eq_pathBefore_comp hU hd hV hVd hVU hs ha hb ht
  have e₂ := pathOf_eq_pathBefore_comp hU hd hW hWd hWU hs hc hd' ht
  have hn := nodup_edgeList hU hd
  rw [← pathEdges_pathOf hU hd hs ht, e₁] at hn
  rcases exists_eq_comp_comp_or_exists_eq_comp_comp (e₁.symm.trans e₂) hn
      (length_pathOf_ne_zero hV hVd ha hb) (length_pathOf_ne_zero hW hWd hc hd')
      (fun e he he' => by
        rw [pathEdges_pathOf] at he he'
        obtain ⟨heV, he1⟩ := (mem_edgeList_iff hV hVd.le).1 he
        exact hVW e heV ((mem_edgeList_iff hW hWd.le).1 he').1 he1) with
    ⟨m, -, hr⟩ | ⟨m, -, hr⟩
  · exact .inl ⟨_, m, _, e₁.trans (by rw [hr])⟩
  · exact .inr ⟨_, m, _, e₂.trans (by rw [hr])⟩

end Path

variable {Q : OGP.{u'}}

namespace Map

variable (f : Map P Q)

theorem isMap_coe : IsMap (f : P → Q) :=
  f.isMap

theorem boundary_Iic_apply {x : P} {n : ℕ} {α : Bool} {v : P}
    (h : P.boundary (.Iic x) n α = .Iic v) : Q.boundary (.Iic (f x)) n α = .Iic (f v) :=
  SetLike.coe_injective (by
    rw [← f.isMap_coe.image_boundary, h, LowerSet.coe_Iic, LowerSet.coe_Iic]
    exact f.isMap_coe.image_Iic v)

theorem boundary_boundary_Iic_apply (hP : P.IsRDC) (hQ : Q.IsRDC) {x : P} {α β : Bool} {v : P}
    (h : P.boundary (P.boundary (.Iic x) 1 α) 0 β = .Iic v) :
    Q.boundary (Q.boundary (.Iic (f x)) 1 α) 0 β = .Iic (f v) := by
  rw [(hQ (f x)).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)]
  rw [(hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)] at h
  exact f.boundary_Iic_apply h

theorem apply_eq_of_grade_ne {v w : EdgeQuiver P} (e : v ⟶ w) (he : grade ℕ (f e.1) ≠ 1) :
    f v = f w := by
  have h0 : grade ℕ (f e.1) = 0 := by
    have := f.isMap_coe.grade_le e.1
    rw [e.2.1] at this
    omega
  have hb (α : Bool) : Q.boundary (.Iic (f e.1)) 0 α = .Iic (f e.1) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic, h0]) α
  exact (LowerSet.Iic_injective ((f.boundary_Iic_apply e.2.2.1).symm.trans (hb false))).trans
    (LowerSet.Iic_injective ((hb true).symm.trans (f.boundary_Iic_apply e.2.2.2)))

def mapEdge {v w : EdgeQuiver P} (e : v ⟶ w) (he : grade ℕ (f e.1) = 1) :
    Quiver.Hom (V := EdgeQuiver Q) (f v) (f w) :=
  ⟨f e.1, he, f.boundary_Iic_apply e.2.2.1, f.boundary_Iic_apply e.2.2.2⟩

def mapPath {a : EdgeQuiver P} :
    {b : EdgeQuiver P} → Quiver.Path a b → Quiver.Path (V := EdgeQuiver Q) (f a) (f b)
  | _, .nil => .nil
  | _, .cons p e =>
    if he : grade ℕ (f e.1) = 1 then (mapPath p).cons (f.mapEdge e he)
    else Quiver.Path.cast rfl (f.apply_eq_of_grade_ne e he) (mapPath p)

private theorem pathEdges_cast {R : OGP.{u''}} {a b c : EdgeQuiver R}
    (p : Quiver.Path (V := EdgeQuiver R) a b) (h : b = c) :
    pathEdges (Quiver.Path.cast rfl h p) = pathEdges p := by
  subst h
  rfl

theorem exists_mem_pathEdges_of_mem_pathEdges_mapPath {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b) {y : Q}, y ∈ pathEdges (f.mapPath p) →
      ∃ e ∈ pathEdges p, f e = y
  | _, .nil, _, hy => by simp [mapPath] at hy
  | _, .cons p e, y, hy => by
    rw [mapPath] at hy
    split_ifs at hy with he
    · rw [pathEdges_cons, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · obtain ⟨e', he', rfl⟩ := exists_mem_pathEdges_of_mem_pathEdges_mapPath p hy
        exact ⟨e', by simp [he'], rfl⟩
      · exact ⟨e.1, by simp, rfl⟩
    · rw [pathEdges_cast] at hy
      obtain ⟨e', he', rfl⟩ := exists_mem_pathEdges_of_mem_pathEdges_mapPath p hy
      exact ⟨e', by simp [he'], rfl⟩

private theorem comp_cast {R : OGP.{u''}} {a b c d : EdgeQuiver R}
    (p : Quiver.Path (V := EdgeQuiver R) a b) (q : Quiver.Path (V := EdgeQuiver R) b c)
    (h : c = d) : p.comp (Quiver.Path.cast rfl h q) = Quiver.Path.cast rfl h (p.comp q) := by
  subst h
  rfl

theorem mapPath_comp {a b : EdgeQuiver P} (p : Quiver.Path a b) :
    ∀ {c : EdgeQuiver P} (q : Quiver.Path b c),
      f.mapPath (p.comp q) = (f.mapPath p).comp (f.mapPath q)
  | _, .nil => rfl
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, mapPath, mapPath, mapPath_comp p q]
    split_ifs
    · rfl
    · exact (comp_cast _ _ _).symm

variable [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q]

theorem mapPath_pathOf_boundary (hP : P.IsRDC) (hQ : Q.IsRDC) (x : P) (α : Bool) {v w : P}
    (hv : P.boundary (P.boundary (.Iic x) 1 α) 0 false = .Iic v)
    (hw : P.boundary (P.boundary (.Iic x) 1 α) 0 true = .Iic w) :
    f.mapPath (pathOf (P.boundary (.Iic x) 1 α) ((hP x).boundary 1 α)
        ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one) hv hw) =
      pathOf (Q.boundary (.Iic (f x)) 1 α) ((hQ (f x)).boundary 1 α)
        ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        (f.boundary_boundary_Iic_apply hP hQ hv) (f.boundary_boundary_Iic_apply hP hQ hw) := by
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun y hy => ?_
  obtain ⟨e, he, rfl⟩ := f.exists_mem_pathEdges_of_mem_pathEdges_mapPath _ hy
  rw [pathEdges_pathOf] at he
  have he' := ((mem_edgeList_iff ((hP x).boundary 1 α)
    ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)).1 he).1
  have h := f.isMap_coe.image_boundary x 1 α
  exact (h ▸ Set.mem_image_of_mem f he' : f e ∈ (Q.boundary (.Iic (f x)) 1 α : Set Q))

end Map

end Atoms.Molecule.OGP
