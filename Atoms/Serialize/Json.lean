import Atoms.ForMathlib.Data.Char
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Notation
import Lean.Data.Json.Basic

namespace Atoms.Serialize

abbrev JString : Type := List Char

inductive Json : Type
  | null
  | bool (b : Bool)
  | num (n : Lean.JsonNumber)
  | str (s : JString)
  | arr (elems : List Json)
  | obj (fields : List (JString × Json))

instance : Inhabited Json := ⟨Json.null⟩

namespace Json

mutual

def decEq : (a b : Json) → Decidable (a = b)
  | .null, b => match b with
      | .null => isTrue rfl
      | .bool _ | .num _ | .str _ | .arr _ | .obj _ => isFalse (by simp)
  | .bool x, b => match b with
      | .bool y => if h : x = y then isTrue (by rw [h]) else isFalse (by simp [h])
      | .null | .num _ | .str _ | .arr _ | .obj _ => isFalse (by simp)
  | .num x, b => match b with
      | .num y => if h : x = y then isTrue (by rw [h]) else isFalse (by simp [h])
      | .null | .bool _ | .str _ | .arr _ | .obj _ => isFalse (by simp)
  | .str x, b => match b with
      | .str y => if h : x = y then isTrue (by rw [h]) else isFalse (by simp [h])
      | .null | .bool _ | .num _ | .arr _ | .obj _ => isFalse (by simp)
  | .arr x, b => match b with
      | .arr y => match decEqList x y with
          | isTrue h => isTrue (by rw [h])
          | isFalse h => isFalse (by simp [h])
      | .null | .bool _ | .num _ | .str _ | .obj _ => isFalse (by simp)
  | .obj x, b => match b with
      | .obj y => match decEqFields x y with
          | isTrue h => isTrue (by rw [h])
          | isFalse h => isFalse (by simp [h])
      | .null | .bool _ | .num _ | .str _ | .arr _ => isFalse (by simp)

def decEqList : (a b : List Json) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | x :: xs, y :: ys => match decEq x y, decEqList xs ys with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse h₁, _ => isFalse (by simp [h₁])
      | _, isFalse h₂ => isFalse (by simp [h₂])

def decEqFields : (a b : List (JString × Json)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      if hk : k₁ = k₂ then
        match decEq v₁ v₂, decEqFields xs ys with
        | isTrue h₁, isTrue h₂ => isTrue (by rw [hk, h₁, h₂])
        | isFalse h₁, _ => isFalse (by simp [h₁])
        | _, isFalse h₂ => isFalse (by simp [h₂])
      else isFalse (by simp [hk])

end

instance : DecidableEq Json := decEq

def asArray : Json → Option (List Json)
  | .arr l => some l
  | _ => none

def asString : Json → Option JString
  | .str s => some s
  | _ => none

def asObject : Json → Option (List (JString × Json))
  | .obj fs => some fs
  | _ => none

end Json

def padDigits (w n : ℕ) : List Char :=
  let ds := Nat.toDigits 10 n
  List.replicate (w - ds.length) '0' ++ ds

def normalizeNum : Int → ℕ → Int × ℕ
  | m, 0 => (m, 0)
  | m, e + 1 => if m % 10 = 0 then normalizeNum (m / 10) e else (m, e + 1)

def printNumber (n : Lean.JsonNumber) : List Char :=
  let (m, e) := normalizeNum n.mantissa n.exponent
  let sign : List Char := if m < 0 then ['-'] else []
  let a := m.natAbs
  if e = 0 then sign ++ Nat.toDigits 10 a
  else
    let p := 10 ^ e
    sign ++ Nat.toDigits 10 (a / p) ++ '.' :: padDigits e (a % p)

def escapeChar (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\r' then ['\\', 'r']
  else if c == '\t' then ['\\', 't']
  else if c == '\x08' then ['\\', 'b']
  else if c == '\x0c' then ['\\', 'f']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
  else [c]

def printString (s : JString) : List Char :=
  '"' :: (s.flatMap escapeChar ++ ['"'])

mutual

def printJson : Json → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .num n => printNumber n
  | .str s => printString s
  | .arr l => '[' :: (printElems l ++ [']'])
  | .obj fs => '{' :: (printFields fs ++ ['}'])

def printElems : List Json → List Char
  | [] => []
  | [j] => printJson j
  | j :: js => printJson j ++ ',' :: printElems js

def printFields : List (JString × Json) → List Char
  | [] => []
  | [(k, v)] => printString k ++ ':' :: printJson v
  | (k, v) :: fs => printString k ++ ':' :: (printJson v ++ ',' :: printFields fs)

end

def normalizeNumber (n : Lean.JsonNumber) : Lean.JsonNumber :=
  ⟨(normalizeNum n.mantissa n.exponent).1, (normalizeNum n.mantissa n.exponent).2⟩

mutual

def normalizeJson : Json → Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num (normalizeNumber n)
  | .str s => .str s
  | .arr l => .arr (normalizeElems l)
  | .obj fs => .obj (normalizeFields fs)

def normalizeElems : List Json → List Json
  | [] => []
  | j :: js => normalizeJson j :: normalizeElems js

def normalizeFields : List (JString × Json) → List (JString × Json)
  | [] => []
  | (k, v) :: fs => (k, normalizeJson v) :: normalizeFields fs

end

abbrev Parser (α : Type) : Type := List Char → Option (α × List Char)

def fuel {α β : Type} (step : (α → Option β) → α → Option β) (n : ℕ) :
    α → Option β :=
  Nat.repeat step n fun _ => none

def unescapeChar (c : Char) : Option Char :=
  if c == '"' then some '"'
  else if c == '\\' then some '\\'
  else if c == '/' then some '/'
  else if c == 'b' then some '\x08'
  else if c == 'f' then some '\x0c'
  else if c == 'n' then some '\n'
  else if c == 'r' then some '\r'
  else if c == 't' then some '\t'
  else none

def hexVal (c : Char) : Option ℕ :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

def unescapeHex (a b c d : Char) : Option Char := do
  let va ← hexVal a
  let vb ← hexVal b
  let vc ← hexVal c
  let vd ← hexVal d
  let v := ((va * 16 + vb) * 16 + vc) * 16 + vd
  if 0xd800 ≤ v && v ≤ 0xdfff then none
  else if v.isValidChar then some (Char.ofNat v) else none

def stringBody : Parser JString
  | [] => none
  | '"' :: r => some ([], r)
  | '\\' :: 'u' :: a :: b :: c :: d :: r => do
      let ch ← unescapeHex a b c d
      let (s, r') ← stringBody r
      some (ch :: s, r')
  | '\\' :: e :: r => do
      let ch ← unescapeChar e
      let (s, r') ← stringBody r
      some (ch :: s, r')
  | c :: r => do
      let (s, r') ← stringBody r
      some (c :: s, r')

def natOfDigits (ds : List Char) : ℕ :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

def parseNumber : Parser Lean.JsonNumber := fun cs => do
  let (neg, cs₁) := match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (ds, cs₂) := cs₁.span Char.isDigit
  if ds.isEmpty then none else
  let (fs, cs₃) ← match cs₂ with
    | '.' :: r => let (f, r') := r.span Char.isDigit; if f.isEmpty then none else some (f, r')
    | _ => some ([], cs₂)
  let (eneg, ev, cs₄) ← match cs₃ with
    | 'e' :: r | 'E' :: r =>
        let (sg, r₁) := match r with
          | '+' :: r' => (false, r')
          | '-' :: r' => (true, r')
          | _ => (false, r)
        let (eds, r₂) := r₁.span Char.isDigit
        if eds.isEmpty then none else some (sg, natOfDigits eds, r₂)
    | _ => some (false, 0, cs₃)
  let mant : Int := if neg then -(natOfDigits (ds ++ fs) : Int) else (natOfDigits (ds ++ fs) : Int)
  let shift : Int := (fs.length : Int) + (if eneg then (ev : Int) else -(ev : Int))
  if 0 ≤ shift then some (⟨mant, shift.toNat⟩, cs₄)
  else some (⟨mant * 10 ^ (-shift).toNat, 0⟩, cs₄)

def elemsStep (prev : Parser Json) (self : Parser (List Json)) : Parser (List Json) :=
  fun cs => do
    let (v, r) ← prev cs
    match r.dropWhile Char.isWhitespace with
    | ',' :: r' => do let (vs, r'') ← self r'; some (v :: vs, r'')
    | ']' :: r' => some ([v], r')
    | _ => none

def fieldsStep (prev : Parser Json) (self : Parser (List (JString × Json))) :
    Parser (List (JString × Json)) := fun cs => do
  let (k, r) ← match cs.dropWhile Char.isWhitespace with
    | '"' :: r => stringBody r
    | _ => none
  let r₁ ← match r.dropWhile Char.isWhitespace with
    | ':' :: r' => some r'
    | _ => none
  let (v, r₂) ← prev r₁
  match r₂.dropWhile Char.isWhitespace with
  | ',' :: r' => do let (fs, r'') ← self r'; some ((k, v) :: fs, r'')
  | '}' :: r' => some ([(k, v)], r')
  | _ => none

def valueStep (prev : Parser Json) : Parser Json := fun cs =>
  match cs.dropWhile Char.isWhitespace with
  | 'n' :: 'u' :: 'l' :: 'l' :: r => some (Json.null, r)
  | 't' :: 'r' :: 'u' :: 'e' :: r => some (Json.bool true, r)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => some (Json.bool false, r)
  | '"' :: r => (stringBody r).map fun p => (Json.str p.1, p.2)
  | '[' :: r =>
      match r.dropWhile Char.isWhitespace with
      | ']' :: r' => some (Json.arr [], r')
      | r' => (fuel (elemsStep prev) r'.length r').map fun p => (Json.arr p.1, p.2)
  | '{' :: r =>
      match r.dropWhile Char.isWhitespace with
      | '}' :: r' => some (Json.obj [], r')
      | r' => (fuel (fieldsStep prev) r'.length r').map fun p => (Json.obj p.1, p.2)
  | cs' => (parseNumber cs').map fun p => (Json.num p.1, p.2)

def parseJson (cs : List Char) : Option Json := do
  let (v, r) ← fuel valueStep (cs.length + 1) cs
  if (r.dropWhile Char.isWhitespace).isEmpty then some v else none

@[simp] theorem normalizeElems_eq_map (l : List Json) : normalizeElems l = l.map normalizeJson := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [normalizeElems, ih, List.map_cons]

@[simp] theorem normalizeFields_eq_map (fs : List (JString × Json)) :
    normalizeFields fs = fs.map fun p => (p.1, normalizeJson p.2) := by
  induction fs with
  | nil => rfl
  | cons p fs ih => rw [normalizeFields, ih, List.map_cons]

private def Stops (r : List Char) : Prop := ∀ c ∈ r.head?, c = ',' ∨ c = ']' ∨ c = '}'

private theorem foldl_digits (acc : ℕ) (ds : List Char) :
    ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) acc =
      acc * 10 ^ ds.length + natOfDigits ds := by
  induction ds generalizing acc with
  | nil => simp [natOfDigits]
  | cons c ds ih =>
      rw [natOfDigits, List.foldl_cons, List.foldl_cons, ih, ih (0 * 10 + _), List.length_cons,
        Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
        Nat.mul_comm 10]

private theorem natOfDigits_append (xs ys : List Char) :
    natOfDigits (xs ++ ys) = natOfDigits xs * 10 ^ ys.length + natOfDigits ys := by
  rw [natOfDigits, List.foldl_append, foldl_digits]
  rfl

private theorem natOfDigits_singleton (c : Char) : natOfDigits [c] = c.toNat - 48 := by
  simp [natOfDigits]

theorem natOfDigits_toDigits (n : ℕ) : natOfDigits (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [Nat.toDigits_eq_if (by decide)]
      split_ifs with h
      · rw [natOfDigits_singleton, Nat.toNat_digitChar_sub_48_of_lt_ten h]
      · rw [natOfDigits_append, ih _ (Nat.div_lt_self (by omega) (by decide)),
          natOfDigits_singleton, Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt _ (by decide)),
          List.length_singleton, Nat.pow_one]
        exact Nat.div_add_mod' n 10

private theorem natOfDigits_replicate_append (k : ℕ) (ds : List Char) :
    natOfDigits (List.replicate k '0' ++ ds) = natOfDigits ds := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, ← List.singleton_append, natOfDigits_append, ih,
        natOfDigits_singleton]
      simp

private theorem natOfDigits_padDigits (w n : ℕ) : natOfDigits (padDigits w n) = n := by
  rw [padDigits, natOfDigits_replicate_append, natOfDigits_toDigits]

private theorem length_padDigits {w n : ℕ} (hw : 0 < w) (hn : n < 10 ^ w) :
    (padDigits w n).length = w := by
  have := (Nat.length_toDigits_le_iff (by decide) hw).2 hn
  rw [padDigits, List.length_append, List.length_replicate]
  omega

theorem isDigit_of_mem_toDigits {n : ℕ} {c : Char} (h : c ∈ Nat.toDigits 10 n) :
    c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

private theorem isDigit_of_mem_padDigits {w n : ℕ} {c : Char} (h : c ∈ padDigits w n) :
    c.isDigit = true := by
  rw [padDigits, List.mem_append] at h
  rcases h with h | h
  · rw [List.eq_of_mem_replicate h]
    rfl
  · exact isDigit_of_mem_toDigits h

private theorem hexVal_digitChar {k : ℕ} (h : k < 16) : hexVal (Nat.digitChar k) = some k := by
  have key : ∀ k < 16, hexVal (Nat.digitChar k) = some k := by decide
  exact key k h

private theorem unescapeHex_escape {c : Char} (h : c.toNat < 32) :
    unescapeHex '0' '0' (Nat.digitChar (c.toNat / 16)) (Nat.digitChar (c.toNat % 16)) =
      some c := by
  have h0 : hexVal '0' = some 0 := rfl
  have hv : ((0 * 16 + 0) * 16 + c.toNat / 16) * 16 + c.toNat % 16 = c.toNat := by omega
  simp only [unescapeHex, h0, hexVal_digitChar (show c.toNat / 16 < 16 by omega),
    hexVal_digitChar (Nat.mod_lt c.toNat (show 16 > 0 by decide)), Option.bind_eq_bind,
    Option.bind_some, hv]
  rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; omega),
    if_pos (show c.toNat.isValidChar from Or.inl (by omega)), Char.ofNat_toNat]

private theorem stringBody_escapeChar_append (c : Char) (X : List Char) :
    stringBody (escapeChar c ++ X) = (stringBody X).map fun p => (c :: p.1, p.2) := by
  have hbs : ∀ e : Char, e ≠ 'u' → stringBody ('\\' :: e :: X) =
      (unescapeChar e).bind fun ch => (stringBody X).map fun p => (ch :: p.1, p.2) := by
    intro e he
    rw [stringBody.eq_4 _ _ (by simp [he])]
    cases unescapeChar e <;> cases stringBody X <;> rfl
  rw [escapeChar]
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  all_goals try
    obtain rfl := beq_iff_eq.1 ‹(c == _) = true›
    rw [List.cons_append, List.cons_append, List.nil_append, hbs _ (by decide)]
    rfl
  · simp only [List.cons_append, List.nil_append]
    rw [stringBody.eq_3, unescapeHex_escape h₈]
    cases stringBody X <;> rfl
  · rw [beq_iff_eq] at h₁ h₂
    rw [List.cons_append, List.nil_append, stringBody.eq_5 _ _ h₁ (by simp [h₂]) (by simp [h₂])]
    cases stringBody X <;> rfl

private theorem stringBody_printString (s : JString) (r : List Char) :
    stringBody (s.flatMap escapeChar ++ '"' :: r) = some (s, r) := by
  induction s with
  | nil => rw [List.flatMap_nil, List.nil_append, stringBody]
  | cons c s ih =>
      rw [List.flatMap_cons, List.append_assoc, stringBody_escapeChar_append, ih]
      rfl

private theorem Stops.isDigit {r : List Char} (hr : Stops r) :
    ∀ c ∈ r.head?, c.isDigit = false := by
  intro c hc
  rcases hr c hc with rfl | rfl | rfl <;> rfl

private theorem takeWhile_isDigit_append {ds : List Char} (hds : ∀ c ∈ ds, c.isDigit = true)
    {X : List Char} (hX : ∀ c ∈ X.head?, c.isDigit = false) :
    (ds ++ X).takeWhile Char.isDigit = ds := by
  rw [List.takeWhile_append_of_pos hds]
  cases X with
  | nil => rw [List.takeWhile_nil, List.append_nil]
  | cons c X =>
      rw [List.takeWhile_cons_of_neg (by rw [hX c rfl]; decide), List.append_nil]

private theorem dropWhile_isDigit_append {ds : List Char} (hds : ∀ c ∈ ds, c.isDigit = true)
    {X : List Char} (hX : ∀ c ∈ X.head?, c.isDigit = false) :
    (ds ++ X).dropWhile Char.isDigit = X := by
  rw [List.dropWhile_append_of_pos hds]
  cases X with
  | nil => rfl
  | cons c X => rw [List.dropWhile_cons_of_neg (by rw [hX c rfl]; decide)]

private theorem Stops.ne_cons {r : List Char} (hr : Stops r) {c : Char}
    (hc : c = '.' ∨ c = 'e' ∨ c = 'E') (r' : List Char) : (r = c :: r') = False := by
  refine eq_false fun h => ?_
  subst h
  rcases hr c rfl with rfl | rfl | rfl <;> rcases hc with h | h | h <;> exact absurd h (by decide)

private theorem append_ne_minus_cons {ds : List Char} (hds : ds ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) (X r' : List Char) : (ds ++ X = '-' :: r') = False := by
  refine eq_false fun h => ?_
  obtain ⟨d, ds', rfl⟩ := List.exists_cons_of_ne_nil hds
  have hd₀ := hd d List.mem_cons_self
  rw [List.cons_append, List.cons.injEq] at h
  rw [h.1] at hd₀
  exact absurd hd₀ (by decide)

private theorem parseNumber_int (neg : Bool) {ds r : List Char} (hds : ds ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) (hr : Stops r) :
    parseNumber ((if neg then ['-'] else []) ++ ds ++ r) =
      some (⟨if neg then -(natOfDigits ds : Int) else natOfDigits ds, 0⟩, r) := by
  have ht := takeWhile_isDigit_append hd hr.isDigit
  have hdr := dropWhile_isDigit_append hd hr.isDigit
  have hdot := hr.ne_cons (c := '.') (by decide)
  have he := hr.ne_cons (c := 'e') (by decide)
  have hE := hr.ne_cons (c := 'E') (by decide)
  cases neg
  · simp [parseNumber, append_ne_minus_cons hds hd, ht, hdr, hdot, he, hE, hds]
  · simp [parseNumber, ht, hdr, hdot, he, hE, hds]

private theorem parseNumber_frac (neg : Bool) {ds fs r : List Char} (hds : ds ≠ []) (hfs : fs ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) (hf : ∀ c ∈ fs, c.isDigit = true) (hr : Stops r) :
    parseNumber ((if neg then ['-'] else []) ++ ds ++ '.' :: fs ++ r) =
      some (⟨if neg then -(natOfDigits (ds ++ fs) : Int) else natOfDigits (ds ++ fs),
        fs.length⟩, r) := by
  have ht := takeWhile_isDigit_append (X := '.' :: (fs ++ r)) hd (by simp)
  have hdr := dropWhile_isDigit_append (X := '.' :: (fs ++ r)) hd (by simp)
  have htf := takeWhile_isDigit_append hf hr.isDigit
  have hdf := dropWhile_isDigit_append hf hr.isDigit
  have he := hr.ne_cons (c := 'e') (by decide)
  have hE := hr.ne_cons (c := 'E') (by decide)
  cases neg
  · simp [parseNumber, append_ne_minus_cons hds hd, ht, hdr, htf, hdf, he, hE, hds, hfs]
  · simp [parseNumber, ht, hdr, htf, hdf, he, hE, hds, hfs]

private theorem printNumber_eq_cons (n : Lean.JsonNumber) :
    ∃ c t, printNumber n = c :: t ∧ (c = '-' ∨ c.isDigit = true) := by
  have key : ∀ (m : Int) (x : ℕ) (X : List Char), ∃ c t,
      (if m < 0 then ['-'] else []) ++ Nat.toDigits 10 x ++ X = c :: t ∧
        (c = '-' ∨ c.isDigit = true) := by
    intro m x X
    split_ifs
    · exact ⟨'-', _, rfl, Or.inl rfl⟩
    · obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := x) (b := 10))
      refine ⟨d, ds ++ X, by rw [List.nil_append, hds, List.cons_append], Or.inr ?_⟩
      exact isDigit_of_mem_toDigits (hds ▸ List.mem_cons_self)
  rw [printNumber]
  generalize normalizeNum n.mantissa n.exponent = p
  obtain ⟨m, e⟩ := p
  dsimp only
  by_cases he : e = 0
  · rw [if_pos he]
    simpa only [List.append_nil] using key m m.natAbs []
  · rw [if_neg he]
    exact key m _ _

private theorem parseNumber_printNumber (n : Lean.JsonNumber) {r : List Char} (hr : Stops r) :
    parseNumber (printNumber n ++ r) = some (normalizeNumber n, r) := by
  rw [printNumber, normalizeNumber]
  generalize normalizeNum n.mantissa n.exponent = p
  obtain ⟨m, e⟩ := p
  dsimp only
  have hsign : (if m < 0 then ['-'] else []) = if decide (m < 0) then ['-'] else [] := by simp
  have hm : (if decide (m < 0) then -(m.natAbs : Int) else (m.natAbs : Int)) = m := by
    split_ifs with h <;> simp only [decide_eq_true_eq] at h <;> omega
  by_cases he : e = 0
  · subst he
    rw [if_pos rfl, hsign, parseNumber_int _ Nat.toDigits_ne_nil
      (fun _ => isDigit_of_mem_toDigits) hr, natOfDigits_toDigits, hm]
  · rw [if_neg he]
    have hp : 0 < 10 ^ e := Nat.pos_of_ne_zero (by simp)
    have hlen := length_padDigits (Nat.pos_of_ne_zero he) (Nat.mod_lt m.natAbs hp)
    rw [hsign, parseNumber_frac _ Nat.toDigits_ne_nil
      (List.ne_nil_of_length_pos (by omega)) (fun _ => isDigit_of_mem_toDigits)
      (fun _ => isDigit_of_mem_padDigits) hr, natOfDigits_append, natOfDigits_toDigits,
      natOfDigits_padDigits, hlen, Nat.div_add_mod', hm]

private theorem normalizeNum_normalizeNum (m : Int) (e : ℕ) :
    normalizeNum (normalizeNum m e).1 (normalizeNum m e).2 = normalizeNum m e := by
  induction e generalizing m with
  | zero => rfl
  | succ e ih =>
      rw [normalizeNum]
      split_ifs with h
      · exact ih _
      · rw [normalizeNum, if_neg h]

private theorem printNumber_normalizeNumber (n : Lean.JsonNumber) :
    printNumber (normalizeNumber n) = printNumber n := by
  rw [printNumber, printNumber, normalizeNumber]
  dsimp only
  rw [normalizeNum_normalizeNum]

private theorem printJson_eq_cons (v : Json) :
    ∃ c t, printJson v = c :: t ∧ c.isWhitespace = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | null => exact ⟨_, _, by rw [printJson], rfl, by decide, by decide⟩
  | bool b => cases b <;> exact ⟨_, _, by rw [printJson], rfl, by decide, by decide⟩
  | num n =>
      obtain ⟨c, t, h, hc⟩ := printNumber_eq_cons n
      refine ⟨c, t, by rw [printJson, h], ?_⟩
      rcases hc with rfl | hc
      · exact ⟨rfl, by decide, by decide⟩
      · refine ⟨Char.isWhitespace_eq_false_of_isDigit hc, ?_, ?_⟩ <;> rintro rfl <;>
          exact absurd hc (by decide)
  | str s => exact ⟨_, _, by rw [printJson, printString], rfl, by decide, by decide⟩
  | arr l => exact ⟨_, _, by rw [printJson], rfl, by decide, by decide⟩
  | obj fs => exact ⟨_, _, by rw [printJson], rfl, by decide, by decide⟩

private theorem length_printJson_pos (v : Json) : 0 < (printJson v).length := by
  obtain ⟨c, t, h, -⟩ := printJson_eq_cons v
  rw [h, List.length_cons]
  exact Nat.succ_pos _

private theorem printElems_eq_cons {l : List Json} (hl : l ≠ []) :
    ∃ c t, printElems l = c :: t ∧ c.isWhitespace = false ∧ c ≠ ']' := by
  obtain ⟨j, js, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨c, t, h, hc, hc', -⟩ := printJson_eq_cons j
  cases js with
  | nil => exact ⟨c, t, by rw [printElems, h], hc, hc'⟩
  | cons j' js =>
      exact ⟨c, _, by rw [printElems.eq_3 _ _ (List.cons_ne_nil _ _), h, List.cons_append], hc, hc'⟩

private theorem length_printJson_le_printElems {j : Json} :
    ∀ {l : List Json}, j ∈ l → (printJson j).length ≤ (printElems l).length
  | [_], h => by
      rw [List.mem_singleton.1 h, printElems]
      exact Nat.le_refl _
  | j' :: j'' :: js, h => by
      rw [printElems.eq_3 _ _ (List.cons_ne_nil _ _), List.length_append, List.length_cons]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := length_printJson_le_printElems h
        omega

private theorem length_le_printElems : ∀ l : List Json, l.length ≤ (printElems l).length
  | [] => Nat.le_refl _
  | [j] => by
      rw [printElems, List.length_singleton]
      exact length_printJson_pos j
  | j :: j' :: js => by
      have h₁ := length_le_printElems (j' :: js)
      have h₂ := length_printJson_pos j
      simp only [printElems.eq_3 _ _ (List.cons_ne_nil _ _), List.length_append,
        List.length_cons] at h₁ ⊢
      omega

private theorem printFields_eq_cons {fs : List (JString × Json)} (hfs : fs ≠ []) :
    ∃ t, printFields fs = '"' :: t := by
  obtain ⟨⟨k, v⟩, fs, rfl⟩ := List.exists_cons_of_ne_nil hfs
  cases fs with
  | nil => exact ⟨_, by rw [printFields, printString, List.cons_append]⟩
  | cons p fs =>
      exact ⟨_, by rw [printFields.eq_3 _ _ _ (List.cons_ne_nil _ _), printString,
        List.cons_append]⟩

private theorem length_printJson_le_printFields {p : JString × Json} :
    ∀ {fs : List (JString × Json)}, p ∈ fs → (printJson p.2).length ≤ (printFields fs).length
  | [(k, v)], h => by
      rw [List.mem_singleton.1 h, printFields, List.length_append, List.length_cons]
      dsimp only
      omega
  | (k, v) :: q :: fs, h => by
      simp only [printFields.eq_3 _ _ _ (List.cons_ne_nil _ _), List.length_append,
        List.length_cons]
      rcases List.mem_cons.1 h with rfl | h
      · dsimp only
        omega
      · have := length_printJson_le_printFields h
        omega

private theorem length_le_printFields : ∀ fs : List (JString × Json),
    fs.length ≤ (printFields fs).length
  | [] => Nat.le_refl _
  | [(k, v)] => by
      rw [printFields, List.length_singleton, List.length_append, List.length_cons]
      omega
  | (k, v) :: q :: fs => by
      have h := length_le_printFields (q :: fs)
      simp only [printFields.eq_3 _ _ _ (List.cons_ne_nil _ _), List.length_append,
        List.length_cons] at h ⊢
      omega

theorem fuel_succ {α β : Type} (step : (α → Option β) → α → Option β) (n : ℕ) :
    fuel step (n + 1) = step (fuel step n) := rfl

private theorem fuel_elemsStep (prev : Parser Json) :
    ∀ (l : List Json), l ≠ [] →
      (∀ j ∈ l, ∀ r, Stops r → prev (printJson j ++ r) = some (normalizeJson j, r)) →
      ∀ m, l.length ≤ m → ∀ r,
        fuel (elemsStep prev) m (printElems l ++ ']' :: r) = some (normalizeElems l, r)
  | [], hl, _, _, _, _ => absurd rfl hl
  | [j], _, hprev, m + 1, _, r => by
      rw [fuel_succ, elemsStep, printElems, hprev j List.mem_cons_self _ (fun _ h => by
        rw [List.head?_cons, Option.mem_some_iff] at h; exact Or.inr (Or.inl h.symm))]
      simp [normalizeElems]
  | j :: j' :: js, _, hprev, m + 1, hm, r => by
      have ih := fuel_elemsStep prev (j' :: js) (List.cons_ne_nil _ _)
        (fun x hx => hprev x (List.mem_cons_of_mem _ hx)) m
        (by simp only [List.length_cons] at hm ⊢; omega) r
      rw [fuel_succ, elemsStep, printElems.eq_3 _ _ (List.cons_ne_nil _ _), List.append_assoc,
        List.cons_append,
        hprev j List.mem_cons_self _ (fun _ h => by
          rw [List.head?_cons, Option.mem_some_iff] at h; exact Or.inl h.symm)]
      simp [ih, normalizeElems]

private theorem fuel_fieldsStep (prev : Parser Json) :
    ∀ (fs : List (JString × Json)), fs ≠ [] →
      (∀ p ∈ fs, ∀ r, Stops r → prev (printJson p.2 ++ r) = some (normalizeJson p.2, r)) →
      ∀ m, fs.length ≤ m → ∀ r,
        fuel (fieldsStep prev) m (printFields fs ++ '}' :: r) = some (normalizeFields fs, r)
  | [], hfs, _, _, _, _ => absurd rfl hfs
  | [(k, v)], _, hprev, m + 1, _, r => by
      have hv := hprev (k, v) List.mem_cons_self ('}' :: r) (fun _ h => by
        rw [List.head?_cons, Option.mem_some_iff] at h; exact Or.inr (Or.inr h.symm))
      dsimp only at hv
      rw [fuel_succ, fieldsStep, printFields, printString]
      simp [stringBody_printString, hv, normalizeFields]
  | (k, v) :: q :: fs, _, hprev, m + 1, hm, r => by
      have ih := fuel_fieldsStep prev (q :: fs) (List.cons_ne_nil _ _)
        (fun x hx => hprev x (List.mem_cons_of_mem _ hx)) m
        (by simp only [List.length_cons] at hm ⊢; omega) r
      have hv := hprev (k, v) List.mem_cons_self (',' :: (printFields (q :: fs) ++ '}' :: r))
        (fun _ h => by rw [List.head?_cons, Option.mem_some_iff] at h; exact Or.inl h.symm)
      dsimp only at hv
      rw [fuel_succ, fieldsStep, printFields.eq_3 _ _ _ (List.cons_ne_nil _ _), printString]
      simp [stringBody_printString, hv, ih, normalizeFields]

private theorem valueStep_cons_of_number (prev : Parser Json) {c : Char} (t : List Char)
    (hw : c.isWhitespace = false) (hn : c ≠ 'n') (ht : c ≠ 't') (hf : c ≠ 'f') (hq : c ≠ '"')
    (ha : c ≠ '[') (ho : c ≠ '{') :
    valueStep prev (c :: t) = (parseNumber (c :: t)).map fun p => (Json.num p.1, p.2) := by
  simp [valueStep, hw, hn, ht, hf, hq, ha, ho]

private theorem valueStep_cons_of_arr (prev : Parser Json) {c : Char} (t : List Char)
    (hw : c.isWhitespace = false) (hb : c ≠ ']') :
    valueStep prev ('[' :: c :: t) =
      (fuel (elemsStep prev) (c :: t).length (c :: t)).map fun p => (Json.arr p.1, p.2) := by
  simp [valueStep, hw, hb]

private theorem valueStep_cons_of_obj (prev : Parser Json) (t : List Char) :
    valueStep prev ('{' :: '"' :: t) =
      (fuel (fieldsStep prev) ('"' :: t).length ('"' :: t)).map fun p => (Json.obj p.1, p.2) := by
  simp [valueStep]

private theorem fuel_valueStep_printJson (n : ℕ) : ∀ (v : Json) (r : List Char),
    (printJson v).length < n → Stops r →
      fuel valueStep n (printJson v ++ r) = some (normalizeJson v, r) := by
  induction n with
  | zero => exact fun v r h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro v r hn hr
      rw [fuel_succ]
      cases v with
      | null => simp [valueStep, printJson, normalizeJson]
      | bool b => cases b <;> simp [valueStep, printJson, normalizeJson]
      | num x =>
          obtain ⟨c, t, hct, hc⟩ := printNumber_eq_cons x
          have hd : ∀ d : Char, d.isDigit = false → d ≠ '-' → c ≠ d := by
            rintro d hd hm rfl
            rcases hc with rfl | hc
            · exact hm rfl
            · rw [hc] at hd
              exact absurd hd (by decide)
          have hw : c.isWhitespace = false := by
            rcases hc with rfl | hc
            · rfl
            · exact Char.isWhitespace_eq_false_of_isDigit hc
          rw [printJson, hct, List.cons_append, valueStep_cons_of_number _ _ hw
            (hd _ rfl (by decide)) (hd _ rfl (by decide)) (hd _ rfl (by decide))
            (hd _ rfl (by decide)) (hd _ rfl (by decide)) (hd _ rfl (by decide)),
            ← List.cons_append, ← hct,
            parseNumber_printNumber x hr]
          rfl
      | str s =>
          rw [printJson, printString]
          simp [valueStep, stringBody_printString, normalizeJson]
      | arr l =>
          rw [printJson, List.length_cons, List.length_append, List.length_singleton] at hn
          rw [printJson, List.cons_append, List.append_assoc, List.singleton_append]
          by_cases hl : l = []
          · subst hl
            simp [valueStep, printElems, normalizeJson, normalizeElems]
          · obtain ⟨c, t, hct, hw, hb⟩ := printElems_eq_cons hl
            have hlen : l.length ≤ (printElems l ++ ']' :: r).length := by
              have := length_le_printElems l
              rw [List.length_append, List.length_cons]
              omega
            rw [hct, List.cons_append, valueStep_cons_of_arr _ _ hw hb, ← List.cons_append, ← hct,
              fuel_elemsStep _ l hl (fun j hj r hr => ih j r (by
                have := length_printJson_le_printElems hj
                omega) hr) _ hlen r]
            rfl
      | obj fs =>
          rw [printJson, List.length_cons, List.length_append, List.length_singleton] at hn
          rw [printJson, List.cons_append, List.append_assoc, List.singleton_append]
          by_cases hfs : fs = []
          · subst hfs
            simp [valueStep, printFields, normalizeJson, normalizeFields]
          · obtain ⟨t, ht⟩ := printFields_eq_cons hfs
            have hlen : fs.length ≤ (printFields fs ++ '}' :: r).length := by
              have := length_le_printFields fs
              rw [List.length_append, List.length_cons]
              omega
            rw [ht, List.cons_append, valueStep_cons_of_obj, ← List.cons_append, ← ht,
              fuel_fieldsStep _ fs hfs (fun p hp r hr => ih p.2 r (by
                have := length_printJson_le_printFields hp
                omega) hr) _ hlen r]
            rfl

theorem parseJson_printJson (v : Json) : parseJson (printJson v) = some (normalizeJson v) := by
  have h := fuel_valueStep_printJson ((printJson v).length + 1) v [] (Nat.lt_succ_self _)
    (fun _ h => absurd h (by simp))
  rw [List.append_nil] at h
  rw [parseJson, h]
  rfl

mutual

theorem printJson_normalizeJson : ∀ v : Json, printJson (normalizeJson v) = printJson v
  | .null => rfl
  | .bool _ => rfl
  | .num n => by rw [normalizeJson, printJson, printJson, printNumber_normalizeNumber]
  | .str _ => rfl
  | .arr l => by rw [normalizeJson, printJson, printJson, printElems_normalizeElems l]
  | .obj fs => by rw [normalizeJson, printJson, printJson, printFields_normalizeFields fs]

private theorem printElems_normalizeElems :
    ∀ l : List Json, printElems (normalizeElems l) = printElems l
  | [] => rfl
  | j :: js => by
      have hj := printJson_normalizeJson j
      have ih := printElems_normalizeElems js
      cases js with
      | nil => rw [normalizeElems, normalizeElems, printElems, printElems, hj]
      | cons j' js =>
          rw [normalizeElems, normalizeElems] at *
          rw [printElems.eq_3 _ _ (List.cons_ne_nil _ _),
            printElems.eq_3 _ _ (List.cons_ne_nil _ _), hj, ih]

private theorem printFields_normalizeFields :
    ∀ fs : List (JString × Json), printFields (normalizeFields fs) = printFields fs
  | [] => rfl
  | (k, v) :: fs => by
      have hv := printJson_normalizeJson v
      have ih := printFields_normalizeFields fs
      cases fs with
      | nil => rw [normalizeFields, normalizeFields, printFields, printFields, hv]
      | cons q fs =>
          obtain ⟨k', v'⟩ := q
          rw [normalizeFields, normalizeFields] at *
          rw [printFields.eq_3 _ _ _ (List.cons_ne_nil _ _),
            printFields.eq_3 _ _ _ (List.cons_ne_nil _ _), hv, ih]

end

end Atoms.Serialize
