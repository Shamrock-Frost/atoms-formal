import Atoms.Serialize.Json
import Atoms.Molecule.Construction.Basic

open Atoms.Molecule (OGP)

namespace Atoms.Serialize

universe u

inductive Term : Type
  | point
  | globe (n : ℕ)
  | simplex (n : ℕ)
  | cube (n : ℕ)
  | suspend (t : Term)
  | dual (t : Term) (dims : List ℕ)
  | gray (a b : Term)
  | join (a b : Term)
  | paste (n : ℕ) (a b : Term)
  | atom (a b : Term)
  deriving DecidableEq, Inhabited, Repr

namespace Term

def Constructible : Term → Prop
  | .point | .globe _ | .simplex _ | .cube _ => True
  | .suspend t | .dual t _ => t.Constructible
  | .gray a b | .join a b => a.Constructible ∧ b.Constructible
  | .paste _ _ _ | .atom _ _ => False

instance decidableConstructible : (t : Term) → Decidable t.Constructible
  | .point | .globe _ | .simplex _ | .cube _ => inferInstanceAs (Decidable True)
  | .suspend t | .dual t _ => decidableConstructible t
  | .gray a b | .join a b =>
      letI := decidableConstructible a
      letI := decidableConstructible b
      inferInstanceAs (Decidable (_ ∧ _))
  | .paste _ _ _ | .atom _ _ => inferInstanceAs (Decidable False)

def eval : Term → Option OGP.{u}
  | .point => some OGP.point
  | .globe n => some (OGP.globe n)
  | .simplex n => some (OGP.simplex n)
  | .cube n => some (OGP.cube n)
  | .suspend t => (eval t).map OGP.suspension
  | .dual t ds => (eval t).map fun U => OGP.dual U fun k => decide (k ∈ ds)
  | .gray a b => do let U ← eval a; let V ← eval b; some (OGP.grayProduct U V)
  | .join a b => do let U ← eval a; let V ← eval b; some (OGP.join U V)
  | .paste _ _ _ => none
  | .atom _ _ => none

theorem isSome_eval_iff_constructible (t : Term) :
    (eval.{u} t).isSome = true ↔ t.Constructible := by
  induction t with
  | point | globe _ | simplex _ | cube _ | paste _ _ _ | atom _ _ => simp [eval, Constructible]
  | suspend t ih | dual t _ ih =>
      cases h : eval.{u} t <;> simpa [eval, Constructible, h] using ih
  | gray a b iha ihb | join a b iha ihb =>
      cases ha : eval.{u} a <;> cases hb : eval.{u} b <;> simp_all only [Option.isSome_none,
          Bool.false_eq_true, false_iff, eval, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, Constructible, and_self, Option.isSome_some, true_iff,
          Option.bind_some, and_true, and_false]

def word : Parser (List Char) := fun cs =>
  let (w, r) := (cs.dropWhile Char.isWhitespace).span Char.isLower
  if w.isEmpty then none else some (w, r)

def nat : Parser ℕ := fun cs =>
  let (ds, r) := (cs.dropWhile Char.isWhitespace).span Char.isDigit
  if ds.isEmpty then none else some (natOfDigits ds, r)

def dimsRest (n : ℕ) : List ℕ → Parser (List ℕ) :=
  Nat.repeat (fun self acc cs =>
    match cs.dropWhile Char.isWhitespace with
    | ']' :: r => some (acc.reverse, r)
    | ',' :: r => do let (v, r') ← nat r; self (v :: acc) r'
    | _ => none) n (fun _ _ => none)

def dims : Parser (List ℕ) := fun cs =>
  match cs.dropWhile Char.isWhitespace with
  | '[' :: r =>
      match r.dropWhile Char.isWhitespace with
      | ']' :: r' => some ([], r')
      | r' => do let (v, r'') ← nat r'; dimsRest r''.length [v] r''
  | _ => none

def foldRest (prev : Parser Term) (f : Term → Term → Term) (n : ℕ) :
    Term → List Char → Term × List Char :=
  Nat.repeat (fun self acc cs =>
    match prev cs with
    | some (t, r) => self (f acc t) r
    | none => (acc, cs)) n (fun acc cs => (acc, cs))

def termStep (prev : Parser Term) : Parser Term := fun cs =>
  match cs.dropWhile Char.isWhitespace with
  | '(' :: r => do
      let (t, r₁) ← prev r
      match r₁.dropWhile Char.isWhitespace with
      | ')' :: r₂ => some (t, r₂)
      | _ => none
  | cs' => do
      let (w, r) ← word cs'
      if w = "point".toList then some (.point, r)
      else if w = "globe".toList then (nat r).map fun p => (Term.globe p.1, p.2)
      else if w = "simplex".toList then (nat r).map fun p => (Term.simplex p.1, p.2)
      else if w = "cube".toList then (nat r).map fun p => (Term.cube p.1, p.2)
      else if w = "suspend".toList then (prev r).map fun p => (Term.suspend p.1, p.2)
      else if w = "dual".toList then do
        let (t, r₁) ← prev r
        let (ds, r₂) ← dims r₁
        some (.dual t ds, r₂)
      else if w = "gray".toList then do
        let (a, r₁) ← prev r
        let (b, r₂) ← prev r₁
        some (foldRest prev Term.gray r₂.length (.gray a b) r₂)
      else if w = "join".toList then do
        let (a, r₁) ← prev r
        let (b, r₂) ← prev r₁
        some (foldRest prev Term.join r₂.length (.join a b) r₂)
      else if w = "paste".toList then do
        let (n, r₁) ← nat r
        let (a, r₂) ← prev r₁
        let (b, r₃) ← prev r₂
        some (.paste n a b, r₃)
      else if w = "atom".toList then do
        let (a, r₁) ← prev r
        let (b, r₂) ← prev r₁
        some (.atom a b, r₂)
      else none

def parse (cs : List Char) : Option Term := do
  let (t, r) ← fuel termStep (cs.length + 1) cs
  if (r.dropWhile Char.isWhitespace).isEmpty then some t else none

def printDims : List ℕ → List Char
  | [] => []
  | [n] => Nat.toDigits 10 n
  | n :: ns => Nat.toDigits 10 n ++ ',' :: printDims ns

def wrap : Term → List Char → List Char
  | .point, s => s
  | _, s => '(' :: (s ++ [')'])

def print : Term → List Char
  | .point => "point".toList
  | .globe n => "globe ".toList ++ Nat.toDigits 10 n
  | .simplex n => "simplex ".toList ++ Nat.toDigits 10 n
  | .cube n => "cube ".toList ++ Nat.toDigits 10 n
  | .suspend t => "suspend ".toList ++ wrap t (print t)
  | .dual t ds => "dual ".toList ++ wrap t (print t) ++ ' ' :: '[' :: (printDims ds ++ [']'])
  | .gray a b => "gray ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b)
  | .join a b => "join ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b)
  | .paste n a b =>
      "paste ".toList ++ Nat.toDigits 10 n ++ ' ' :: wrap a (print a) ++ ' ' :: wrap b (print b)
  | .atom a b => "atom ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b)

private def Closes (s : List Char) : Prop := s = [] ∨ ∃ r, s = ')' :: r

private theorem eq_of_mem_head?_cons {c x : Char} {X : List Char} (h : c ∈ (x :: X).head?) :
    c = x := by
  rw [List.head?_cons, Option.mem_some_iff] at h
  exact h.symm

private theorem Closes.isLower {s : List Char} (hs : Closes s) :
    ∀ c ∈ s.head?, c.isLower = false := by
  rcases hs with rfl | ⟨r, rfl⟩
  · exact fun c hc => absurd hc (by simp)
  · exact fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl

private theorem Closes.isDigit {s : List Char} (hs : Closes s) :
    ∀ c ∈ s.head?, c.isDigit = false := by
  rcases hs with rfl | ⟨r, rfl⟩
  · exact fun c hc => absurd hc (by simp)
  · exact fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl

private theorem span_append {p : Char → Bool} {xs : List Char} (hx : ∀ c ∈ xs, p c = true)
    {X : List Char} (hX : ∀ c ∈ X.head?, p c = false) : (xs ++ X).span p = (xs, X) := by
  rw [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_of_pos hx,
    List.dropWhile_append_of_pos hx]
  cases X with
  | nil => rw [List.takeWhile_nil, List.dropWhile_nil, List.append_nil]
  | cons c X =>
      rw [List.takeWhile_cons_of_neg (by rw [hX c rfl]; decide),
        List.dropWhile_cons_of_neg (by rw [hX c rfl]; decide), List.append_nil]

private theorem toDigits_eq_cons (k : ℕ) :
    ∃ d ds, Nat.toDigits 10 k = d :: ds ∧ d.isDigit = true ∧ d.isWhitespace = false := by
  obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := k) (b := 10))
  have h := isDigit_of_mem_toDigits (hd ▸ List.mem_cons_self)
  exact ⟨d, ds, hd, h, Char.isWhitespace_eq_false_of_isDigit h⟩

private theorem nat_toDigits (k : ℕ) {s : List Char} (hs : ∀ c ∈ s.head?, c.isDigit = false) :
    nat (Nat.toDigits 10 k ++ s) = some (k, s) := by
  obtain ⟨d, ds, hd, -, hw⟩ := toDigits_eq_cons k
  have hsp := span_append (fun _ => isDigit_of_mem_toDigits (n := k)) hs
  rw [nat, hd, List.cons_append, List.dropWhile_cons_of_neg (by rw [hw]; decide),
    ← List.cons_append, ← hd, hsp]
  dsimp only
  rw [if_neg (by rw [hd]; exact Bool.false_ne_true), natOfDigits_toDigits]

private theorem fuel_termStep_space (k : ℕ) (X : List Char) :
    fuel termStep k (' ' :: X) = fuel termStep k X := by
  cases k <;> rfl

private theorem fuel_termStep_closes (k : ℕ) {s : List Char} (hs : Closes s) :
    fuel termStep k s = none := by
  cases k with
  | zero => rfl
  | succ k => rcases hs with rfl | ⟨r, rfl⟩ <;> rfl

private theorem foldRest_of_eq_none {prev : Parser Term} {cs : List Char} (h : prev cs = none)
    (f : Term → Term → Term) (k : ℕ) (acc : Term) : foldRest prev f k acc cs = (acc, cs) := by
  cases k with
  | zero => rfl
  | succ k => simp only [foldRest, Nat.repeat, h]

private theorem length_le_printDims : ∀ ns : List ℕ, ns.length ≤ (printDims ns).length
  | [] => le_refl _
  | [n] => by
      obtain ⟨d, ds, hd, -⟩ := toDigits_eq_cons n
      simp [printDims, hd]
  | n :: m :: ms => by
      have := length_le_printDims (m :: ms)
      simp only [printDims.eq_3 _ _ (List.cons_ne_nil _ _), List.length_append,
        List.length_cons] at this ⊢
      omega

private theorem dimsRest_printDims (s : List Char) : ∀ (ns : List ℕ) (acc : List ℕ) (k : ℕ),
    ns ≠ [] → ns.length < k →
      dimsRest k acc (',' :: (printDims ns ++ ']' :: s)) = some (acc.reverse ++ ns, s)
  | [], _, _, h, _ => absurd rfl h
  | [n], acc, k + 2, _, _ => by
      have h : dimsRest (k + 2) acc (',' :: (printDims [n] ++ ']' :: s)) =
          (nat (Nat.toDigits 10 n ++ ']' :: s)).bind fun p => dimsRest (k + 1) (p.1 :: acc) p.2 :=
        rfl
      rw [h, nat_toDigits _ fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl, Option.bind_some]
      simp [dimsRest, Nat.repeat]
  | n :: m :: ms, acc, k + 1, _, hk => by
      have h : dimsRest (k + 1) acc (',' :: (printDims (n :: m :: ms) ++ ']' :: s)) =
          (nat (Nat.toDigits 10 n ++ ',' :: (printDims (m :: ms) ++ ']' :: s))).bind
            fun p => dimsRest k (p.1 :: acc) p.2 := by
        rw [printDims.eq_3 _ _ (List.cons_ne_nil _ _), List.append_assoc, List.cons_append]
        rfl
      rw [h, nat_toDigits _ fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl, Option.bind_some,
        dimsRest_printDims s (m :: ms) (n :: acc) k (List.cons_ne_nil _ _)
          (by simp only [List.length_cons] at hk ⊢; omega)]
      simp

private theorem dims_printDims (ds : List ℕ) (s : List Char) :
    dims (' ' :: '[' :: (printDims ds ++ ']' :: s)) = some (ds, s) := by
  cases ds with
  | nil => rfl
  | cons n ns =>
      obtain ⟨d, D, hd, hdd, hw⟩ := toDigits_eq_cons n
      have hR : ∃ R, printDims (n :: ns) ++ ']' :: s = Nat.toDigits 10 n ++ R ∧
          (∀ c ∈ R.head?, c.isDigit = false) ∧
          dimsRest R.length [n] R = some (n :: ns, s) := by
        cases ns with
        | nil => exact ⟨']' :: s, rfl, fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl, rfl⟩
        | cons m ms =>
            refine ⟨',' :: (printDims (m :: ms) ++ ']' :: s), ?_,
              fun c hc => by rw [eq_of_mem_head?_cons hc]; rfl, ?_⟩
            · rw [printDims.eq_3 _ _ (List.cons_ne_nil _ _), List.append_assoc, List.cons_append]
            · have := length_le_printDims (m :: ms)
              rw [dimsRest_printDims s (m :: ms) [n] _ (List.cons_ne_nil _ _)
                (by simp only [List.length_cons, List.length_append] at this ⊢; omega)]
              rfl
      obtain ⟨R, hR, hRd, hRk⟩ := hR
      have h : dims (' ' :: '[' :: (Nat.toDigits 10 n ++ R)) =
          (nat (Nat.toDigits 10 n ++ R)).bind fun p => dimsRest p.2.length [p.1] p.2 := by
        have hZ : (d :: (D ++ R)).dropWhile Char.isWhitespace = d :: (D ++ R) :=
          List.dropWhile_cons_of_neg (by rw [hw]; decide)
        have h' : dims (' ' :: '[' :: (d :: (D ++ R))) =
            match (d :: (D ++ R)).dropWhile Char.isWhitespace with
            | ']' :: r' => some ([], r')
            | r' => (nat r').bind fun p => dimsRest p.2.length [p.1] p.2 := rfl
        rw [hd, List.cons_append, h', hZ]
        split
        · rename_i heq
          rw [List.cons.injEq] at heq
          rw [heq.1] at hdd
          exact absurd hdd (by decide)
        · rfl
      rw [hR, h, nat_toDigits _ hRd, Option.bind_some, hRk]

private theorem print_point : print .point = "point".toList := rfl

private theorem print_globe (d : ℕ) : print (.globe d) = "globe ".toList ++ Nat.toDigits 10 d :=
  rfl

private theorem print_simplex (d : ℕ) :
    print (.simplex d) = "simplex ".toList ++ Nat.toDigits 10 d := rfl

private theorem print_cube (d : ℕ) : print (.cube d) = "cube ".toList ++ Nat.toDigits 10 d := rfl

private theorem print_suspend (a : Term) :
    print (.suspend a) = "suspend ".toList ++ wrap a (print a) := rfl

private theorem print_dual (a : Term) (ds : List ℕ) : print (.dual a ds) =
    "dual ".toList ++ wrap a (print a) ++ ' ' :: '[' :: (printDims ds ++ [']']) := rfl

private theorem print_gray (a b : Term) :
    print (.gray a b) = "gray ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b) := rfl

private theorem print_join (a b : Term) :
    print (.join a b) = "join ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b) := rfl

private theorem print_paste (d : ℕ) (a b : Term) : print (.paste d a b) =
    "paste ".toList ++ Nat.toDigits 10 d ++ ' ' :: wrap a (print a) ++ ' ' :: wrap b (print b) :=
  rfl

private theorem print_atom (a b : Term) :
    print (.atom a b) = "atom ".toList ++ wrap a (print a) ++ ' ' :: wrap b (print b) := rfl

private theorem termStep_point (prev : Parser Term) {s : List Char}
    (hs : ∀ c ∈ s.head?, c.isLower = false) :
    termStep prev ("point".toList ++ s) = some (.point, s) := by
  have hd : ("point".toList ++ s).dropWhile Char.isWhitespace = "point".toList ++ s := rfl
  have hw : word ("point".toList ++ s) = some ("point".toList, s) := by
    rw [word, hd, span_append (by decide) hs]
    rfl
  unfold termStep
  rw [hd]
  split
  · rename_i heq
    exact absurd (congrArg List.head? heq) (by simp)
  · rw [hw]
    rfl

private theorem termStep_paren (prev : Parser Term) {X : List Char} {t : Term} {s : List Char}
    (h : prev X = some (t, ')' :: s)) : termStep prev ('(' :: X) = some (t, s) := by
  have e : termStep prev ('(' :: X) = (prev X).bind fun p =>
      match p.2.dropWhile Char.isWhitespace with
      | ')' :: r₂ => some (p.1, r₂)
      | _ => none := rfl
  rw [e, h]
  rfl

private theorem termStep_globe (prev : Parser Term) (X : List Char) :
    termStep prev ("globe ".toList ++ X) = (nat X).map fun p => (Term.globe p.1, p.2) := rfl

private theorem termStep_simplex (prev : Parser Term) (X : List Char) :
    termStep prev ("simplex ".toList ++ X) = (nat X).map fun p => (Term.simplex p.1, p.2) := rfl

private theorem termStep_cube (prev : Parser Term) (X : List Char) :
    termStep prev ("cube ".toList ++ X) = (nat X).map fun p => (Term.cube p.1, p.2) := rfl

private theorem termStep_suspend (prev : Parser Term) (X : List Char) :
    termStep prev ("suspend ".toList ++ X) =
      (prev (' ' :: X)).map fun p => (Term.suspend p.1, p.2) := rfl

private theorem termStep_dual (prev : Parser Term) (X : List Char) :
    termStep prev ("dual ".toList ++ X) = (prev (' ' :: X)).bind fun p =>
      (dims p.2).bind fun q => some (.dual p.1 q.1, q.2) := rfl

private theorem termStep_gray (prev : Parser Term) (X : List Char) :
    termStep prev ("gray ".toList ++ X) = (prev (' ' :: X)).bind fun p =>
      (prev p.2).bind fun q => some (foldRest prev Term.gray q.2.length (.gray p.1 q.1) q.2) :=
  rfl

private theorem termStep_join (prev : Parser Term) (X : List Char) :
    termStep prev ("join ".toList ++ X) = (prev (' ' :: X)).bind fun p =>
      (prev p.2).bind fun q => some (foldRest prev Term.join q.2.length (.join p.1 q.1) q.2) :=
  rfl

private theorem termStep_paste (prev : Parser Term) (X : List Char) :
    termStep prev ("paste ".toList ++ X) = (nat X).bind fun p =>
      (prev p.2).bind fun q => (prev q.2).bind fun r => some (.paste p.1 q.1 r.1, r.2) := rfl

private theorem termStep_atom (prev : Parser Term) (X : List Char) :
    termStep prev ("atom ".toList ++ X) = (prev (' ' :: X)).bind fun p =>
      (prev p.2).bind fun q => some (.atom p.1 q.1, q.2) := rfl

private theorem length_print_pos (t : Term) : 0 < (print t).length := by
  cases t <;> exact Nat.zero_lt_succ _

private theorem length_wrap {t : Term} (ht : t ≠ .point) (x : List Char) :
    (wrap t x).length = x.length + 2 := by
  rw [wrap.eq_2 _ _ ht]
  simp

private theorem head_space (X : List Char) : ∀ c ∈ (' ' :: X).head?, c.isLower = false ∧
    c.isDigit = false :=
  fun c hc => by rw [eq_of_mem_head?_cons hc]; exact ⟨rfl, rfl⟩

private theorem fuel_succ_termStep_wrap (m : ℕ) (t : Term) {s : List Char}
    (hs : ∀ c ∈ s.head?, c.isLower = false)
    (hprint : t ≠ .point → fuel termStep m (print t ++ ')' :: s) = some (t, ')' :: s)) :
    fuel termStep (m + 1) (wrap t (print t) ++ s) = some (t, s) := by
  rw [fuel_succ]
  by_cases ht : t = .point
  · subst ht
    exact termStep_point _ hs
  · rw [wrap.eq_2 _ _ ht, List.cons_append, List.append_assoc, List.singleton_append]
    exact termStep_paren _ (hprint ht)

private theorem fuel_termStep_wrap (k : ℕ)
    (ih : ∀ m < k, ∀ (t : Term) (s : List Char), (print t).length < m → Closes s →
      fuel termStep m (print t ++ s) = some (t, s))
    (a : Term) {s : List Char} (ha : (wrap a (print a)).length < k)
    (hs : ∀ c ∈ s.head?, c.isLower = false) :
    fuel termStep k (' ' :: (wrap a (print a) ++ s)) = some (a, s) := by
  rw [fuel_termStep_space]
  have hpos := length_print_pos a
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by
    by_cases h : a = .point
    · subst h
      rw [wrap.eq_1] at ha
      omega
    · rw [length_wrap h] at ha
      omega⟩
  exact fuel_succ_termStep_wrap m a hs fun h => ih m (by omega) a _
    (by rw [length_wrap h] at ha; omega) (Or.inr ⟨_, rfl⟩)

private theorem fuel_termStep_print (n : ℕ) : ∀ (t : Term) (s : List Char),
    (print t).length < n → Closes s → fuel termStep n (print t ++ s) = some (t, s) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t s hn hs
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := length_print_pos t; omega⟩
  have hw := fuel_termStep_wrap k fun m hm => ih m (by omega)
  have hsp : ∀ X : List Char, ∀ c ∈ (' ' :: X).head?, c.isLower = false :=
    fun X c hc => (head_space X c hc).1
  rw [fuel_succ]
  cases t with
  | point =>
      rw [print_point]
      exact termStep_point _ hs.isLower
  | globe d =>
      rw [print_globe, List.append_assoc, termStep_globe, nat_toDigits _ hs.isDigit]
      rfl
  | simplex d =>
      rw [print_simplex, List.append_assoc, termStep_simplex, nat_toDigits _ hs.isDigit]
      rfl
  | cube d =>
      rw [print_cube, List.append_assoc, termStep_cube, nat_toDigits _ hs.isDigit]
      rfl
  | suspend a =>
      have hL : 0 < "suspend ".toList.length := by decide
      rw [print_suspend, List.length_append] at hn
      rw [print_suspend, List.append_assoc, termStep_suspend, hw a (by omega) hs.isLower]
      rfl
  | dual a ds =>
      simp only [print_dual, List.length_append, List.length_cons] at hn
      simp only [print_dual, List.append_assoc, List.cons_append]
      rw [termStep_dual, hw a (by omega) (hsp _), Option.bind_some, dims_printDims]
      rfl
  | gray a b =>
      simp only [print_gray, List.length_append, List.length_cons] at hn
      simp only [print_gray, List.append_assoc, List.cons_append]
      rw [termStep_gray, hw a (by omega) (hsp _), Option.bind_some, hw b (by omega) hs.isLower,
        Option.bind_some, foldRest_of_eq_none (fuel_termStep_closes k hs)]
  | join a b =>
      simp only [print_join, List.length_append, List.length_cons] at hn
      simp only [print_join, List.append_assoc, List.cons_append]
      rw [termStep_join, hw a (by omega) (hsp _), Option.bind_some, hw b (by omega) hs.isLower,
        Option.bind_some, foldRest_of_eq_none (fuel_termStep_closes k hs)]
  | paste d a b =>
      simp only [print_paste, List.length_append, List.length_cons] at hn
      simp only [print_paste, List.append_assoc, List.cons_append]
      rw [termStep_paste, nat_toDigits _ fun c hc => (head_space _ c hc).2, Option.bind_some,
        hw a (by omega) (hsp _), Option.bind_some, hw b (by omega) hs.isLower, Option.bind_some]
  | atom a b =>
      simp only [print_atom, List.length_append, List.length_cons] at hn
      simp only [print_atom, List.append_assoc, List.cons_append]
      rw [termStep_atom, hw a (by omega) (hsp _), Option.bind_some, hw b (by omega) hs.isLower,
        Option.bind_some]

theorem parse_print (t : Term) : parse (print t) = some t := by
  have h := fuel_termStep_print ((print t).length + 1) t [] (Nat.lt_succ_self _) (Or.inl rfl)
  rw [List.append_nil] at h
  rw [parse, h]
  rfl

theorem print_injective : Function.Injective print := fun a b h =>
  Option.some_injective _ ((parse_print a).symm.trans (h ▸ parse_print b))

def pointText : List Char :=
  ['p', 'o', 'i', 'n', 't']

example : parse pointText = some (Term.point) := by decide

example : print (Term.point) = pointText := by decide

def squareText : List Char :=
  ['g', 'r', 'a', 'y', ' ', '(', 'g', 'l', 'o', 'b', 'e', ' ', '1', ')', ' ', '(', 'g', 'l', 'o', 
   'b', 'e', ' ', '1', ')']

example : parse squareText = some (Term.gray (.globe 1) (.globe 1)) := by decide

example : print (Term.gray (.globe 1) (.globe 1)) = squareText := by decide

def grayThreeText : List Char :=
  ['g', 'r', 'a', 'y', ' ', 'p', 'o', 'i', 'n', 't', ' ', 'p', 'o', 'i', 'n', 't', ' ', 'p', 'o', 
   'i', 'n', 't']

example : parse grayThreeText = some (Term.gray (.gray .point .point) .point) := by decide

example : print (Term.gray (.gray .point .point) .point) ≠ grayThreeText := by decide

def dualText : List Char :=
  ['d', 'u', 'a', 'l', ' ', '(', 's', 'i', 'm', 'p', 'l', 'e', 'x', ' ', '2', ')', ' ', '[', '0', 
   ',', '2', ']']

example : parse dualText = some (Term.dual (.simplex 2) [0, 2]) := by decide

example : print (Term.dual (.simplex 2) [0, 2]) = dualText := by decide

def joinText : List Char :=
  ['j', 'o', 'i', 'n', ' ', 'p', 'o', 'i', 'n', 't', ' ', 'p', 'o', 'i', 'n', 't']

example : parse joinText = some (Term.join .point .point) := by decide

example : print (Term.join .point .point) = joinText := by decide

def suspendText : List Char :=
  ['s', 'u', 's', 'p', 'e', 'n', 'd', ' ', '(', 'c', 'u', 'b', 'e', ' ', '2', ')']

example : parse suspendText = some (Term.suspend (.cube 2)) := by decide

example : print (Term.suspend (.cube 2)) = suspendText := by decide

def pasteText : List Char :=
  ['p', 'a', 's', 't', 'e', ' ', '0', ' ', '(', 'g', 'r', 'a', 'y', ' ', '(', 'g', 'l', 'o', 'b', 
   'e', ' ', '1', ')', ' ', '(', 'g', 'l', 'o', 'b', 'e', ' ', '1', ')', ')', ' ', '(', 'g', 'l', 
   'o', 'b', 'e', ' ', '1', ')']

example : parse pasteText = some (Term.paste 0 (.gray (.globe 1) (.globe 1)) (.globe 1)) := by
  decide

example : print (Term.paste 0 (.gray (.globe 1) (.globe 1)) (.globe 1)) = pasteText := by decide

example : parse (print (Term.paste 0 (.gray (.globe 1) (.globe 1)) (.globe 1)))
    = some (Term.paste 0 (.gray (.globe 1) (.globe 1)) (.globe 1)) := by decide

example : parse (print (Term.join (.dual (.simplex 2) [0, 2]) .point))
    = some (Term.join (.dual (.simplex 2) [0, 2]) .point) := by decide

example : eval.{0} (.gray (.globe 1) (.globe 1))
    = some (OGP.grayProduct (OGP.globe 1) (OGP.globe 1)) := rfl

example : eval.{0} (.suspend (.cube 2)) = some (OGP.suspension (OGP.cube 2)) := rfl

example : eval.{0} (.paste 0 .point .point) = none := rfl

example : eval.{0} (.atom .point .point) = none := rfl

example : ¬ (Term.paste 0 .point .point).Constructible ∧
    (Term.gray (.globe 1) (.simplex 2)).Constructible := by decide

end Term

end Atoms.Serialize
