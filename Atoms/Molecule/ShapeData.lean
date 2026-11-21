import Atoms.Molecule.OrientedGradedPoset
import Mathlib.Data.List.GetD
import Mathlib.Tactic.DeriveCountable

namespace Atoms.Molecule

structure FaceData : Type where
  minus : List ℕ
  plus : List ℕ
  deriving DecidableEq, Inhabited, Repr, Countable

structure ShapeData : Type where
  faces : List (List FaceData)
  deriving DecidableEq, Inhabited, Repr, Countable

namespace ShapeData

def WellFormed (d : ShapeData) : Prop :=
  (d.faces = [] ∨ ∀ fs ∈ d.faces, fs ≠ []) ∧
  (∀ f ∈ d.faces.getD 0 [], f.minus = [] ∧ f.plus = []) ∧
  (∀ n ∈ List.range d.faces.length, ∀ f ∈ d.faces.getD (n + 1) [],
    (∀ i ∈ f.minus, i < (d.faces.getD n []).length) ∧
    (∀ i ∈ f.plus, i < (d.faces.getD n []).length)) ∧
  (∀ n ∈ List.range d.faces.length, ∀ f ∈ d.faces.getD (n + 1) [],
    ¬ (f.minus = [] ∧ f.plus = [])) ∧
  (∀ fs ∈ d.faces, ∀ f ∈ fs, ∀ i ∈ f.minus, i ∉ f.plus)

instance decidableWellFormed (d : ShapeData) : Decidable d.WellFormed :=
  inferInstanceAs <| Decidable <|
    (d.faces = [] ∨ ∀ fs ∈ d.faces, fs ≠ []) ∧
    (∀ f ∈ d.faces.getD 0 [], f.minus = [] ∧ f.plus = []) ∧
    (∀ n ∈ List.range d.faces.length, ∀ f ∈ d.faces.getD (n + 1) [],
      (∀ i ∈ f.minus, i < (d.faces.getD n []).length) ∧
      (∀ i ∈ f.plus, i < (d.faces.getD n []).length)) ∧
    (∀ n ∈ List.range d.faces.length, ∀ f ∈ d.faces.getD (n + 1) [],
      ¬ (f.minus = [] ∧ f.plus = [])) ∧
    (∀ fs ∈ d.faces, ∀ f ∈ fs, ∀ i ∈ f.minus, i ∉ f.plus)

def CanonicalFaces (d : ShapeData) : Prop :=
  ∀ fs ∈ d.faces, ∀ f ∈ fs, f.minus.Pairwise (· < ·) ∧ f.plus.Pairwise (· < ·)

instance decidableCanonicalFaces (d : ShapeData) : Decidable d.CanonicalFaces :=
  inferInstanceAs <| Decidable <|
    ∀ fs ∈ d.faces, ∀ f ∈ fs, f.minus.Pairwise (· < ·) ∧ f.plus.Pairwise (· < ·)

def Valid (d : ShapeData) : Prop := d.CanonicalFaces ∧ d.WellFormed

instance decidableValid (d : ShapeData) : Decidable d.Valid :=
  inferInstanceAs <| Decidable <|
    d.CanonicalFaces ∧ d.WellFormed

abbrev Element (d : ShapeData) : Type :=
  (n : Fin d.faces.length) × Fin (d.faces[n.1]'n.2).length

theorem element_ext {d : ShapeData} {e e' : Element d} (h₁ : e.1.val = e'.1.val)
    (h₂ : e.2.val = e'.2.val) : e = e' := by
  obtain ⟨⟨n, hn⟩, ⟨k, hk⟩⟩ := e
  obtain ⟨⟨n', hn'⟩, ⟨k', hk'⟩⟩ := e'
  dsimp only at h₁ h₂
  subst h₁
  subst h₂
  rfl

def mkElement (d : ShapeData) (n k : ℕ) : Option (Element d) :=
  if hn : n < d.faces.length then
    if hk : k < (d.faces[n]'hn).length then some ⟨⟨n, hn⟩, ⟨k, hk⟩⟩ else none
  else none

theorem mkElement_eq {d : ShapeData} {n k : ℕ} {z : Element d} (h : mkElement d n k = some z) :
    z.1.val = n ∧ z.2.val = k := by
  unfold mkElement at h
  split at h
  · split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

def facesOf {d : ShapeData} (x : Element d) : FaceData :=
  (d.faces[x.1.1]'x.1.2)[x.2.1]'x.2.2

def facesAt (d : ShapeData) (m : ℕ) (f : FaceData) : List (Element d) :=
  (f.minus ++ f.plus).filterMap (mkElement d m)

def coveredBy {d : ShapeData} (x : Element d) : List (Element d) :=
  if x.1.val = 0 then [] else facesAt d (x.1.val - 1) (facesOf x)

theorem dim_of_mem_coveredBy {d : ShapeData} {x z : Element d} (h : z ∈ coveredBy x) :
    x.1.val = z.1.val + 1 := by
  unfold coveredBy facesAt at h
  split at h
  · simp at h
  · rename_i hne
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 h
    rw [(mkElement_eq hi).1]
    omega

def leAux (d : ShapeData) : ℕ → Element d → Element d → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || (coveredBy y).any (leAux d n x)

@[simp] theorem leAux_zero {d : ShapeData} {x y : Element d} : leAux d 0 x y = true ↔ x = y := by
  simp [leAux]

theorem leAux_self (d : ShapeData) (n : ℕ) (x : Element d) : leAux d n x x = true := by
  cases n <;> simp [leAux]

theorem leAux_of_succ {d : ShapeData} {n : ℕ} {x y : Element d}
    (h : leAux d (n + 1) x y = true) : x = y ∨ ∃ z ∈ coveredBy y, leAux d n x z = true := by
  rw [leAux, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨z, hz, hzz⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, hzz⟩

theorem leAux_succ_of_mem {d : ShapeData} {n : ℕ} {x y z : Element d} (hz : z ∈ coveredBy y)
    (h : leAux d n x z = true) : leAux d (n + 1) x y = true := by
  rw [leAux, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨z, hz, h⟩

theorem leAux_mono (d : ShapeData) : ∀ (n m : ℕ), n ≤ m → ∀ x y : Element d,
    leAux d n x y = true → leAux d m x y = true := by
  intro n
  induction n with
  | zero =>
      intro m _ x y h
      obtain rfl := leAux_zero.1 h
      exact leAux_self d m x
  | succ n ih =>
      intro m hnm x y h
      obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rcases leAux_of_succ h with rfl | ⟨z, hz, hzz⟩
      · exact leAux_self d _ x
      · exact leAux_succ_of_mem hz (ih m' (by omega) x z hzz)

theorem dim_le_of_leAux (d : ShapeData) : ∀ (n : ℕ) (x y : Element d),
    leAux d n x y = true → x.1.val ≤ y.1.val := by
  intro n
  induction n with
  | zero =>
      intro x y h
      obtain rfl := leAux_zero.1 h
      exact le_rfl
  | succ n ih =>
      intro x y h
      rcases leAux_of_succ h with rfl | ⟨z, hz, hzz⟩
      · exact le_rfl
      · have h₁ := ih x z hzz
        have h₂ := dim_of_mem_coveredBy hz
        omega

theorem dim_lt_of_leAux (d : ShapeData) (n : ℕ) (x y : Element d)
    (h : leAux d n x y = true) (hne : x ≠ y) : x.1.val < y.1.val := by
  cases n with
  | zero => exact absurd (leAux_zero.1 h) hne
  | succ n =>
      rcases leAux_of_succ h with rfl | ⟨z, hz, hzz⟩
      · exact absurd rfl hne
      · have h₁ := dim_le_of_leAux d n x z hzz
        have h₂ := dim_of_mem_coveredBy hz
        omega

theorem leAux_saturate (d : ShapeData) : ∀ (n : ℕ) (x y : Element d),
    leAux d n x y = true → leAux d y.1.val x y = true := by
  intro n
  induction n with
  | zero =>
      intro x y h
      obtain rfl := leAux_zero.1 h
      exact leAux_self d _ x
  | succ n ih =>
      intro x y h
      rcases leAux_of_succ h with rfl | ⟨z, hz, hzz⟩
      · exact leAux_self d _ x
      · have hd := dim_of_mem_coveredBy hz
        rw [hd]
        exact leAux_succ_of_mem hz (ih x z hzz)

theorem leAux_trans (d : ShapeData) : ∀ (n m : ℕ) (x y z : Element d),
    leAux d n x y = true → leAux d m y z = true → leAux d (n + m) x z = true := by
  intro n m
  induction m with
  | zero =>
      intro x y z h₁ h₂
      obtain rfl := leAux_zero.1 h₂
      simpa using h₁
  | succ m ih =>
      intro x y z h₁ h₂
      rcases leAux_of_succ h₂ with rfl | ⟨w, hw, hww⟩
      · exact leAux_mono d n (n + (m + 1)) (by omega) _ _ h₁
      · exact leAux_succ_of_mem hw (ih x y w h₁ hww)

def Le (d : ShapeData) (x y : Element d) : Prop := leAux d d.faces.length x y = true

instance decidableLe (d : ShapeData) (x y : Element d) : Decidable (Le d x y) :=
  inferInstanceAs (Decidable (leAux d d.faces.length x y = true))

@[instance_reducible] def partialOrder (d : ShapeData) : PartialOrder (Element d) where
  le := Le d
  le_refl x := leAux_self d _ x
  le_trans x y z h₁ h₂ := by
    have hz := z.1.isLt
    exact leAux_mono d z.1.val d.faces.length (by omega) x z
      (leAux_saturate d _ x z (leAux_trans d _ _ x y z h₁ h₂))
  le_antisymm x y h₁ h₂ := by
    by_contra hne
    have k₁ := dim_lt_of_leAux d _ x y h₁ hne
    have k₂ := dim_lt_of_leAux d _ y x h₂ (Ne.symm hne)
    omega

attribute [local instance] partialOrder

theorem lt_of_mem_coveredBy {d : ShapeData} {x z : Element d} (hz : z ∈ coveredBy x) : z < x := by
  have hd := dim_of_mem_coveredBy hz
  have hlen : 1 ≤ d.faces.length := by have := x.1.isLt; omega
  have hle : z ≤ x :=
    leAux_mono d 1 d.faces.length hlen z x (leAux_succ_of_mem hz (leAux_self d 0 z))
  exact lt_of_le_of_ne hle (by intro he; rw [he] at hd; omega)

theorem mem_coveredBy_iff_covBy {d : ShapeData} (x z : Element d) :
    z ∈ coveredBy x ↔ z ⋖ x := by
  constructor
  · intro hz
    refine ⟨lt_of_mem_coveredBy hz, fun c hzc hcx => ?_⟩
    have hd := dim_of_mem_coveredBy hz
    have k₁ := dim_lt_of_leAux _ _ _ _ hzc.le hzc.ne
    have k₂ := dim_lt_of_leAux _ _ _ _ hcx.le hcx.ne
    omega
  · intro hcov
    obtain ⟨m, hm⟩ : ∃ m, d.faces.length = m + 1 := ⟨d.faces.length - 1, by
      have := x.1.isLt; omega⟩
    have h : leAux d (m + 1) z x = true := by rw [← hm]; exact hcov.1.le
    rcases leAux_of_succ h with he | ⟨w, hw, hww⟩
    · exact absurd he hcov.1.ne
    · have hzw : z ≤ w := leAux_mono d m d.faces.length (by omega) z w hww
      have hwx : w < x := lt_of_mem_coveredBy hw
      have : z = w := by
        by_contra hne
        exact hcov.2 (lt_of_le_of_ne hzw hne) hwx
      rwa [this]

theorem coveredBy_ne_nil {d : ShapeData} (hd : d.WellFormed) {x : Element d}
    (h : 0 < x.1.val) : coveredBy x ≠ [] := by
  obtain ⟨m, hm⟩ : ∃ m, x.1.val = m + 1 := ⟨x.1.val - 1, by omega⟩
  have hx := x.1.isLt
  have hmlen : m < d.faces.length := by omega
  have hrow : d.faces.getD (m + 1) [] = d.faces[x.1.1]'x.1.2 := by
    rw [← hm]; exact List.getD_eq_getElem _ _ x.1.2
  have hmem : facesOf x ∈ d.faces.getD (m + 1) [] := by
    rw [hrow]; exact List.getElem_mem _
  have hne := hd.2.2.2.1 m (List.mem_range.2 hmlen) (facesOf x) hmem
  have hnil : (facesOf x).minus ++ (facesOf x).plus ≠ [] := by
    intro hcon
    exact hne ⟨List.append_eq_nil_iff.1 hcon |>.1, List.append_eq_nil_iff.1 hcon |>.2⟩
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hnil
  have hrange := hd.2.2.1 m (List.mem_range.2 hmlen) (facesOf x) hmem
  have hilt : i < (d.faces[m]'hmlen).length := by
    rw [← List.getD_eq_getElem (l := d.faces) (d := []) hmlen]
    rcases List.mem_append.1 hi with hi' | hi'
    · exact hrange.1 i hi'
    · exact hrange.2 i hi'
  have hsome : mkElement d m i = some ⟨⟨m, hmlen⟩, ⟨i, hilt⟩⟩ := by
    unfold mkElement; rw [dif_pos hmlen, dif_pos hilt]
  refine List.ne_nil_of_mem (a := (⟨⟨m, hmlen⟩, ⟨i, hilt⟩⟩ : Element d)) ?_
  unfold coveredBy facesAt
  rw [if_neg (by omega), hm]
  exact List.mem_filterMap.2 ⟨i, hi, by simpa using hsome⟩

@[instance_reducible] def gradeMinOrder (d : ShapeData) (hd : d.WellFormed) :
    GradeMinOrder ℕ (Element d) where
  grade x := x.1.val
  grade_strictMono x y h := dim_lt_of_leAux d _ x y h.le h.ne
  covBy_grade x y h :=
    Nat.covBy_iff_add_one_eq.2 (dim_of_mem_coveredBy ((mem_coveredBy_iff_covBy y x).2 h)).symm
  isMin_grade x h := by
    have hx : x.1.val = 0 := by
      by_contra hne
      obtain ⟨z, hz⟩ :=
        List.exists_mem_of_ne_nil _ (coveredBy_ne_nil hd (Nat.pos_of_ne_zero hne))
      exact (lt_of_mem_coveredBy hz).not_ge (h (lt_of_mem_coveredBy hz).le)
    exact hx ▸ isMin_bot

def toOGP (d : ShapeData) (hd : d.WellFormed) : OGP.{0} where
  carrier := Element d
  partialOrderCarrier := partialOrder d
  gradeMinOrderCarrier := gradeMinOrder d hd
  orient {x y} _ := decide (y.2.val ∈ (facesOf x).plus)

variable (d : ShapeData) (hd : d.WellFormed) in
transfer_instances toOGP d hd with FinEnum Fintype DecidableEq

instance instDecidableLEToOGP (d : ShapeData) (hd : d.WellFormed) : DecidableLE (toOGP d hd) :=
  decidableLe d

end ShapeData

@[ext] structure FiniteOGP : Type where
  data : ShapeData
  valid : data.Valid

namespace FiniteOGP

instance : DecidableEq FiniteOGP := fun P Q =>
  decidable_of_iff (P.data = Q.data) FiniteOGP.ext_iff.symm

def ogp (P : FiniteOGP) : OGP.{0} := P.data.toOGP P.valid.2

variable (P : FiniteOGP) in
transfer_instances P.ogp with FinEnum Fintype DecidableEq DecidableLE

instance : Countable FiniteOGP :=
  Function.Injective.countable (f := FiniteOGP.data) fun _ _ => FiniteOGP.ext

end FiniteOGP

end Atoms.Molecule
