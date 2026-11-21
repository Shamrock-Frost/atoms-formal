import Atoms.ForMathlib.Data.FinEnum.Basic
import Atoms.ForMathlib.Order.Cover
import Atoms.Molecule.Category
import Atoms.Molecule.ShapeData

universe u

open Order

namespace Atoms.Molecule.ShapeData

variable (P : OGP.{u}) [FinEnum P] [DecidableLE P]

def elementsOfDim (n : ℕ) : List P :=
  (FinEnum.toList P).filter fun x => decide (grade ℕ x = n)

omit [DecidableLE P] in
def dimensionCount : ℕ :=
  Finset.univ.sup fun x : P => grade ℕ x + 1

def facePositions (m : ℕ) (x : P) (α : Bool) : List ℕ :=
  (elementsOfDim P m).zipIdx.filterMap fun p =>
    if ∃ h : p.1 ⋖ x, P.orient h = α then some p.2 else none

def faceDataOf (x : P) : FaceData :=
  if grade ℕ x = 0 then ⟨[], []⟩
  else ⟨facePositions P (grade ℕ x - 1) x false, facePositions P (grade ℕ x - 1) x true⟩

def ofOGP : ShapeData where
  faces := (List.range (dimensionCount P)).map fun n => (elementsOfDim P n).map (faceDataOf P)

omit [DecidableLE P] in
theorem mem_elementsOfDim {n : ℕ} {x : P} : x ∈ elementsOfDim P n ↔ grade ℕ x = n := by
  simp [elementsOfDim, FinEnum.mem_toList]

omit [DecidableLE P] in
theorem nodup_elementsOfDim (n : ℕ) : (elementsOfDim P n).Nodup :=
  List.Nodup.filter _ FinEnum.nodup_toList

omit [DecidableLE P] in
theorem grade_lt_dimensionCount (x : P) : grade ℕ x < dimensionCount P :=
  Finset.le_sup (f := fun x : P => grade ℕ x + 1) (Finset.mem_univ x)

omit [DecidableLE P] in
theorem elementsOfDim_ne_nil {n : ℕ} (h : n < dimensionCount P) : elementsOfDim P n ≠ [] := by
  have hne : (Finset.univ : Finset P).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro he
    simp [dimensionCount, he] at h
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup _ hne fun x : P => grade ℕ x + 1
  rw [← dimensionCount] at hx
  obtain ⟨y, hy⟩ : ∃ y : P, grade ℕ y = n := by
    rcases (show n ≤ grade ℕ x by omega).eq_or_lt with hn | hn
    · exact ⟨x, hn.symm⟩
    · obtain ⟨y, -, hy⟩ := exists_lt_grade_eq hn
      exact ⟨y, hy⟩
  exact List.ne_nil_of_mem ((mem_elementsOfDim P).2 hy)

theorem mem_facePositions {m : ℕ} {x : P} {α : Bool} {i : ℕ} :
    i ∈ facePositions P m x α ↔ ∃ h : i < (elementsOfDim P m).length,
      ∃ hc : (elementsOfDim P m)[i] ⋖ x, P.orient hc = α := by
  unfold facePositions
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨y, j⟩, hp, he⟩
    obtain ⟨hj, hy⟩ := List.mem_zipIdx' hp
    dsimp only at he
    split_ifs at he with hc
    · obtain rfl := Option.some.inj he
      exact ⟨hj, by rw [← hy]; exact hc⟩
  · rintro ⟨h, hc⟩
    refine ⟨((elementsOfDim P m)[i], i), ?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem h)
    · exact if_pos hc

theorem lt_length_of_mem_facePositions {m : ℕ} {x : P} {α : Bool} {i : ℕ}
    (h : i ∈ facePositions P m x α) : i < (elementsOfDim P m).length := by
  obtain ⟨hi, -⟩ := (mem_facePositions P).1 h
  exact hi

theorem notMem_facePositions_true_of_mem_false {m : ℕ} {x : P} {i : ℕ}
    (h : i ∈ facePositions P m x false) : i ∉ facePositions P m x true := by
  intro h'
  obtain ⟨_, _, ho⟩ := (mem_facePositions P).1 h
  obtain ⟨_, _, ho'⟩ := (mem_facePositions P).1 h'
  exact Bool.false_ne_true (ho.symm.trans ho')

theorem pairwise_facePositions (m : ℕ) (x : P) (α : Bool) :
    (facePositions P m x α).Pairwise (· < ·) := by
  have hsnd : ((elementsOfDim P m).zipIdx.map Prod.snd).Pairwise (· < ·) := by
    rw [List.zipIdx_map_snd]
    exact List.pairwise_lt_range'
  rw [List.pairwise_map] at hsnd
  have key : ∀ (p : P × ℕ) (c : ℕ),
      (if ∃ h : p.1 ⋖ x, P.orient h = α then some p.2 else none) = some c → p.2 = c := by
    intro p c hc
    split at hc
    · exact Option.some.inj hc
    · simp at hc
  unfold facePositions
  rw [List.pairwise_filterMap]
  refine hsnd.imp ?_
  intro a a' h b hb b' hb'
  rw [← key a b hb, ← key a' b' hb']
  exact h

theorem faceDataOf_of_grade_eq_zero {x : P} (h : grade ℕ x = 0) :
    faceDataOf P x = ⟨[], []⟩ := by
  rw [faceDataOf, if_pos h]

theorem faceDataOf_of_grade_eq_add_one {x : P} {n : ℕ} (h : grade ℕ x = n + 1) :
    faceDataOf P x = ⟨facePositions P n x false, facePositions P n x true⟩ := by
  rw [faceDataOf, if_neg (by omega), h, Nat.add_sub_cancel]

theorem faceDataOf_not_nil_and_nil {x : P} (h : 0 < grade ℕ x) :
    ¬ ((faceDataOf P x).minus = [] ∧ (faceDataOf P x).plus = []) := by
  obtain ⟨n, hn⟩ : ∃ n, grade ℕ x = n + 1 := ⟨grade ℕ x - 1, by omega⟩
  obtain ⟨z, hzx, hdz⟩ := exists_lt_grade_eq (a := x) (n := n) (by omega)
  have hz : z ⋖ x := GradeOrder.covBy_of_le_of_grade_eq_add_one hzx.le (by omega)
  obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.1 ((mem_elementsOfDim P).2 hdz)
  have hmem : i ∈ facePositions P n x (P.orient hz) :=
    (mem_facePositions P).2 ⟨hi, by rw [hiz]; exact ⟨hz, rfl⟩⟩
  rw [faceDataOf_of_grade_eq_add_one P hn]
  rintro ⟨h1, h2⟩
  have h1' : facePositions P n x false = [] := h1
  have h2' : facePositions P n x true = [] := h2
  cases ho : P.orient hz
  · rw [ho, h1'] at hmem
    exact List.not_mem_nil hmem
  · rw [ho, h2'] at hmem
    exact List.not_mem_nil hmem

theorem faces_ofOGP : (ofOGP P).faces =
    (List.range (dimensionCount P)).map fun n => (elementsOfDim P n).map (faceDataOf P) := rfl

theorem length_faces_ofOGP : (ofOGP P).faces.length = dimensionCount P := by
  simp [faces_ofOGP]

theorem mem_faces_ofOGP {fs : List FaceData} :
    fs ∈ (ofOGP P).faces ↔
      ∃ n < dimensionCount P, (elementsOfDim P n).map (faceDataOf P) = fs := by
  simp [faces_ofOGP]

theorem getD_faces_ofOGP (n : ℕ) : (ofOGP P).faces.getD n [] =
    if n < dimensionCount P then (elementsOfDim P n).map (faceDataOf P) else [] := by
  rw [faces_ofOGP]
  split_ifs with h
  · have hl : n < ((List.range (dimensionCount P)).map
        fun n => (elementsOfDim P n).map (faceDataOf P)).length := by simpa using h
    rw [List.getD_eq_getElem _ _ hl]
    simp
  · have hl : ((List.range (dimensionCount P)).map
        fun n => (elementsOfDim P n).map (faceDataOf P)).length ≤ n := by simpa using h
    rw [List.getD_eq_default _ _ hl]

theorem exists_of_mem_getD_faces_ofOGP {n : ℕ} {f : FaceData}
    (hf : f ∈ (ofOGP P).faces.getD n []) : ∃ y : P, grade ℕ y = n ∧ faceDataOf P y = f := by
  rw [getD_faces_ofOGP] at hf
  split_ifs at hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hf
    exact ⟨y, (mem_elementsOfDim P).1 hy, rfl⟩
  · exact absurd hf List.not_mem_nil

theorem canonicalFaces_ofOGP : (ofOGP P).CanonicalFaces := by
  intro fs hfs f hf
  obtain ⟨n, -, rfl⟩ := (mem_faces_ofOGP P).1 hfs
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hf
  rcases Nat.eq_zero_or_pos (grade ℕ y) with h0 | hpos
  · rw [faceDataOf_of_grade_eq_zero P h0]
    exact ⟨List.Pairwise.nil, List.Pairwise.nil⟩
  · obtain ⟨m, hm⟩ : ∃ m, grade ℕ y = m + 1 := ⟨grade ℕ y - 1, by omega⟩
    rw [faceDataOf_of_grade_eq_add_one P hm]
    exact ⟨pairwise_facePositions P m y false, pairwise_facePositions P m y true⟩

theorem wellFormed_ofOGP : (ofOGP P).WellFormed := by
  refine ⟨Or.inr ?_, ?_, ?_, ?_, ?_⟩
  · intro fs hfs
    obtain ⟨n, hn, rfl⟩ := (mem_faces_ofOGP P).1 hfs
    rw [Ne, List.map_eq_nil_iff]
    exact elementsOfDim_ne_nil P hn
  · intro f hf
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_getD_faces_ofOGP P hf
    rw [faceDataOf_of_grade_eq_zero P hy]
    exact ⟨rfl, rfl⟩
  · intro n _ f hf
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_getD_faces_ofOGP P hf
    have hlt := grade_lt_dimensionCount P y
    rw [faceDataOf_of_grade_eq_add_one P hy, getD_faces_ofOGP,
      if_pos (by omega), List.length_map]
    exact ⟨fun i hi => lt_length_of_mem_facePositions P hi,
      fun i hi => lt_length_of_mem_facePositions P hi⟩
  · intro n _ f hf
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_getD_faces_ofOGP P hf
    exact faceDataOf_not_nil_and_nil P (by omega)
  · intro fs hfs f hf i hi hi'
    obtain ⟨n, -, rfl⟩ := (mem_faces_ofOGP P).1 hfs
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hf
    rcases Nat.eq_zero_or_pos (grade ℕ y) with h0 | hpos
    · rw [faceDataOf_of_grade_eq_zero P h0] at hi
      exact List.not_mem_nil hi
    · obtain ⟨m, hm⟩ : ∃ m, grade ℕ y = m + 1 := ⟨grade ℕ y - 1, by omega⟩
      rw [faceDataOf_of_grade_eq_add_one P hm] at hi hi'
      exact notMem_facePositions_true_of_mem_false P hi hi'

theorem ofOGP_valid : (ofOGP P).Valid :=
  ⟨canonicalFaces_ofOGP P, wellFormed_ofOGP P⟩

theorem length_getElem_faces_ofOGP {n : ℕ} (h : n < (ofOGP P).faces.length) :
    ((ofOGP P).faces[n]'h).length = (elementsOfDim P n).length := by
  simp [ofOGP]

omit [DecidableLE P] in
theorem idxOf_lt_length_elementsOfDim (x : P) :
    (elementsOfDim P (grade ℕ x)).idxOf x < (elementsOfDim P (grade ℕ x)).length :=
  List.idxOf_lt_length_of_mem ((mem_elementsOfDim P).2 rfl)

omit [DecidableLE P] in
theorem getElem_idxOf_elementsOfDim (x : P) :
    (elementsOfDim P (grade ℕ x))[(elementsOfDim P (grade ℕ x)).idxOf x]'
      (idxOf_lt_length_elementsOfDim P x) = x :=
  List.getElem_idxOf _

def encode (x : P) : Element (ofOGP P) :=
  ⟨⟨grade ℕ x, by rw [length_faces_ofOGP]; exact grade_lt_dimensionCount P x⟩,
    ⟨(elementsOfDim P (grade ℕ x)).idxOf x, by
      rw [length_getElem_faces_ofOGP]
      exact idxOf_lt_length_elementsOfDim P x⟩⟩

def decode (e : Element (ofOGP P)) : P :=
  (elementsOfDim P e.1.val)[e.2.val]'(by rw [← length_getElem_faces_ofOGP P e.1.2]; exact e.2.2)

@[simp] theorem encode_fst_val (x : P) : (encode P x).1.val = grade ℕ x := rfl

@[simp] theorem encode_snd_val (x : P) :
    (encode P x).2.val = (elementsOfDim P (grade ℕ x)).idxOf x := rfl

theorem decode_encode (x : P) : decode P (encode P x) = x :=
  List.getElem_idxOf _

theorem grade_decode (e : Element (ofOGP P)) : grade ℕ (decode P e) = e.1.val :=
  (mem_elementsOfDim P).1 (List.getElem_mem _)

theorem encode_decode (e : Element (ofOGP P)) : encode P (decode P e) = e := by
  refine element_ext (grade_decode P e) ?_
  rw [encode_snd_val, grade_decode]
  exact List.Nodup.idxOf_getElem (nodup_elementsOfDim P _) _ _

theorem facesOf_encode (x : P) : facesOf (encode P x) = faceDataOf P x := by
  simp [facesOf, encode, ofOGP]

theorem mkElement_ofOGP {n i : ℕ} (h : i < (elementsOfDim P n).length) :
    mkElement (ofOGP P) n i = some (encode P ((elementsOfDim P n)[i])) := by
  have hdim : grade ℕ ((elementsOfDim P n)[i]) = n :=
    (mem_elementsOfDim P).1 (List.getElem_mem _)
  have hn : n < (ofOGP P).faces.length := by
    rw [length_faces_ofOGP, ← hdim]; exact grade_lt_dimensionCount P _
  have hk : i < ((ofOGP P).faces[n]'hn).length := by rwa [length_getElem_faces_ofOGP]
  unfold mkElement
  rw [dif_pos hn, dif_pos hk]
  refine congrArg some (element_ext hdim.symm ?_)
  dsimp only
  rw [encode_snd_val, hdim]
  exact ((nodup_elementsOfDim P n).idxOf_getElem i h).symm

theorem encode_mem_coveredBy_iff (x z : P) :
    encode P z ∈ coveredBy (encode P x) ↔ z ⋖ x := by
  constructor
  · intro hz
    have hd : grade ℕ x = grade ℕ z + 1 := dim_of_mem_coveredBy hz
    unfold coveredBy facesAt at hz
    rw [if_neg (by simp [hd]), facesOf_encode, faceDataOf_of_grade_eq_add_one P hd] at hz
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 hz
    have hi' : i = (encode P z).2.val := ((mkElement_eq he).2).symm
    dsimp only at hi
    obtain ⟨α, hα⟩ : ∃ α, i ∈ facePositions P (grade ℕ z) x α := by
      rcases List.mem_append.1 hi with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨hlt, hcov, -⟩ := (mem_facePositions P).1 hα
    have hget : (elementsOfDim P (grade ℕ z))[i] = z := by
      simp only [hi', encode_snd_val]
      exact List.getElem_idxOf _
    rwa [hget] at hcov
  · intro hcov
    have hd : grade ℕ x = grade ℕ z + 1 := (Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)).symm
    have hlt := idxOf_lt_length_elementsOfDim P z
    have hget := getElem_idxOf_elementsOfDim P z
    have hpos : (elementsOfDim P (grade ℕ z)).idxOf z ∈
        facePositions P (grade ℕ z) x (P.orient hcov) :=
      (mem_facePositions P).2 ⟨hlt, by rw [hget]; exact ⟨hcov, rfl⟩⟩
    unfold coveredBy facesAt
    rw [if_neg (by simp [hd]), facesOf_encode, faceDataOf_of_grade_eq_add_one P hd]
    refine List.mem_filterMap.2 ⟨(elementsOfDim P (grade ℕ z)).idxOf z, ?_, ?_⟩
    · dsimp only
      cases ho : P.orient hcov
      · rw [ho] at hpos; exact List.mem_append_left _ hpos
      · rw [ho] at hpos; exact List.mem_append_right _ hpos
    · simp only [encode_fst_val, hd, Nat.add_sub_cancel]
      rw [mkElement_ofOGP P hlt]
      exact congrArg some (congrArg (encode P) hget)

def encodeEquiv : P ≃ (ofOGP P).toOGP (ofOGP_valid P).2 where
  toFun := encode P
  invFun := decode P
  left_inv := decode_encode P
  right_inv := encode_decode P

theorem encodeEquiv_covBy_iff (x z : P) :
    encodeEquiv P z ⋖ encodeEquiv P x ↔ z ⋖ x :=
  (mem_coveredBy_iff_covBy (encode P x) (encode P z)).symm.trans (encode_mem_coveredBy_iff P x z)

theorem orient_encodeEquiv {x z : P} (h : z ⋖ x) :
    ((ofOGP P).toOGP (ofOGP_valid P).2).orient ((encodeEquiv_covBy_iff P x z).2 h) =
      P.orient h := by
  have hd : grade ℕ x = grade ℕ z + 1 := (Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)).symm
  change decide ((encode P z).2.val ∈ (facesOf (encode P x)).plus) = P.orient h
  rw [facesOf_encode, faceDataOf_of_grade_eq_add_one P hd]
  have hlt := idxOf_lt_length_elementsOfDim P z
  have hget := getElem_idxOf_elementsOfDim P z
  have key : (encode P z).2.val ∈ facePositions P (grade ℕ z) x true ↔ P.orient h = true := by
    rw [encode_snd_val, mem_facePositions]
    constructor
    · rintro ⟨_, hc, ho⟩
      exact (P.orient_congr rfl hget hc h).symm.trans ho
    · intro ho
      exact ⟨hlt, by rw [hget]; exact ⟨h, ho⟩⟩
  dsimp only
  rw [Bool.eq_iff_iff, decide_eq_true_iff, key]

theorem isMorphism_encodeEquiv : OGP.IsMorphism (encodeEquiv P) :=
  .of_equiv (encodeEquiv P) (encodeEquiv_covBy_iff P) (orient_encodeEquiv P)

def encodeOrderIso : P ≃o (ofOGP P).toOGP (ofOGP_valid P).2 :=
  ⟨encodeEquiv P, (isMorphism_encodeEquiv P).le_iff_of_injective (encodeEquiv P).injective⟩

def encodingIso (P : OGP.{0}) [FinEnum P] [DecidableLE P] :
    P ≅ (ofOGP P).toOGP (ofOGP_valid P).2 :=
  OGP.isoMk (encodeOrderIso P) (orient_encodeEquiv P)

section Realization

variable {d : ShapeData} (hd : d.WellFormed)

private theorem grade_toOGP (x : d.toOGP hd) : grade ℕ x = x.1.val := rfl

private theorem orient_toOGP {x y : d.toOGP hd} (h : y ⋖ x) :
    (d.toOGP hd).orient h = decide (y.2.val ∈ (facesOf x).plus) := rfl

private theorem filter_toList_element {n : ℕ} (hn : n < d.faces.length) :
    ((FinEnum.toList (Element d)).filter fun x => decide (x.1.val = n)) =
      (List.finRange (d.faces[n]'hn).length).map (Sigma.mk ⟨n, hn⟩) := by
  rw [← FinEnum.toList_fin, ← FinEnum.filter_toList_sigma]
  exact List.filter_congr fun x _ => by rw [decide_eq_decide, Fin.ext_iff]

private theorem length_elementsOfDim_toOGP {n : ℕ} (hn : n < d.faces.length) :
    (elementsOfDim (d.toOGP hd) n).length = (d.faces[n]'hn).length := by
  have h := congrArg List.length (filter_toList_element hn)
  rw [List.length_map, List.length_finRange] at h
  exact h

private theorem getElem_elementsOfDim_toOGP {n i : ℕ} (hn : n < d.faces.length)
    (hi : i < (elementsOfDim (d.toOGP hd) n).length) :
    ((elementsOfDim (d.toOGP hd) n)[i]).1.val = n ∧
      ((elementsOfDim (d.toOGP hd) n)[i]).2.val = i := by
  have hi' : i < ((FinEnum.toList (Element d)).filter fun x => decide (x.1.val = n)).length := hi
  have h := List.getElem_of_eq (filter_toList_element hn) hi'
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] at h
  exact ⟨congrArg (fun x : Element d => x.1.val) h, congrArg (fun x : Element d => x.2.val) h⟩

private theorem facesOf_eq_getElem {y : Element d} {n k : ℕ} (h₁ : y.1.val = n) (h₂ : y.2.val = k)
    (hn : n < d.faces.length) (hk : k < (d.faces[n]'hn).length) :
    facesOf y = (d.faces[n]'hn)[k]'hk := by
  obtain ⟨⟨n', hn'⟩, ⟨k', hk'⟩⟩ := y
  dsimp only at h₁ h₂
  subst h₁ h₂
  rfl

private theorem dimensionCount_toOGP : dimensionCount (d.toOGP hd) = d.faces.length := by
  refine le_antisymm (Finset.sup_le fun x _ => x.1.isLt) ?_
  rcases Nat.eq_zero_or_pos d.faces.length with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · obtain ⟨m, hm⟩ : ∃ m, d.faces.length = m + 1 := ⟨d.faces.length - 1, by omega⟩
    have hrow : d.faces[m]'(by omega) ≠ [] :=
      (hd.1.resolve_left (List.ne_nil_of_length_pos hpos)) _ (List.getElem_mem _)
    have hx : m < dimensionCount (d.toOGP hd) :=
      grade_lt_dimensionCount (d.toOGP hd) ⟨⟨m, by omega⟩, ⟨0, List.length_pos_iff.2 hrow⟩⟩
    omega

private theorem mem_coveredBy_iff_mem_append {x z : Element d} (hx : x.1.val = z.1.val + 1) :
    z ∈ coveredBy x ↔ z.2.val ∈ (facesOf x).minus ++ (facesOf x).plus := by
  rw [coveredBy, if_neg (by omega), hx, Nat.add_sub_cancel, facesAt, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, he⟩
    rwa [(mkElement_eq he).2]
  · intro hz
    refine ⟨z.2.val, hz, ?_⟩
    rw [mkElement, dif_pos z.1.2, dif_pos z.2.2]

private theorem facePositions_toOGP (hc : d.CanonicalFaces) {m : ℕ} (x : d.toOGP hd)
    (hx : x.1.val = m + 1) (α : Bool) :
    facePositions (d.toOGP hd) m x α = cond α (facesOf x).plus (facesOf x).minus := by
  have hm : m < d.faces.length := by have := x.1.isLt; omega
  have hcx : (facesOf x).minus.Pairwise (· < ·) ∧ (facesOf x).plus.Pairwise (· < ·) :=
    hc _ (List.getElem_mem x.1.2) _ (List.getElem_mem x.2.2)
  have hrange := hd.2.2.1 m (List.mem_range.2 hm) (facesOf x)
    (by rw [← hx, List.getD_eq_getElem _ _ x.1.2]; exact List.getElem_mem _)
  have hdisj : ∀ i ∈ (facesOf x).minus, i ∉ (facesOf x).plus :=
    hd.2.2.2.2 _ (List.getElem_mem x.1.2) _ (List.getElem_mem x.2.2)
  refine List.Pairwise.eq_of_mem_iff (pairwise_facePositions _ m x α)
    (by cases α; exacts [hcx.1, hcx.2]) fun i => ?_
  rw [mem_facePositions]
  constructor
  · rintro ⟨hi, hcov, rfl⟩
    obtain ⟨hy₁, hy₂⟩ := getElem_elementsOfDim_toOGP hd hm hi
    have hmem := (mem_coveredBy_iff_mem_append (x := x) (by omega)).1
      ((mem_coveredBy_iff_covBy _ _).2 hcov)
    rw [orient_toOGP]
    rw [hy₂] at hmem ⊢
    by_cases hp : i ∈ (facesOf x).plus
    · rwa [decide_eq_true hp]
    · rw [decide_eq_false hp]
      exact (List.mem_append.1 hmem).resolve_right hp
  · intro hi
    have hil : i < (elementsOfDim (d.toOGP hd) m).length := by
      rw [length_elementsOfDim_toOGP hd hm, ← List.getD_eq_getElem _ [] hm]
      cases α
      · exact hrange.1 i hi
      · exact hrange.2 i hi
    obtain ⟨hy₁, hy₂⟩ := getElem_elementsOfDim_toOGP hd hm hil
    have hmem : (elementsOfDim (d.toOGP hd) m)[i] ∈ coveredBy x := by
      refine (mem_coveredBy_iff_mem_append (by omega)).2 ?_
      rw [hy₂]
      cases α
      · exact List.mem_append_left _ hi
      · exact List.mem_append_right _ hi
    have hcov : (elementsOfDim (d.toOGP hd) m)[i] ⋖ x := (mem_coveredBy_iff_covBy x _).1 hmem
    refine ⟨hil, hcov, ?_⟩
    rw [orient_toOGP, hy₂]
    cases α
    · exact decide_eq_false (hdisj i hi)
    · exact decide_eq_true hi

private theorem faceDataOf_toOGP (hc : d.CanonicalFaces) (x : d.toOGP hd) :
    faceDataOf (d.toOGP hd) x = facesOf x := by
  rcases Nat.eq_zero_or_pos x.1.val with h0 | hpos
  · have hmem : facesOf x ∈ d.faces.getD 0 [] := by
      rw [← h0, List.getD_eq_getElem _ _ x.1.2]
      exact List.getElem_mem _
    obtain ⟨h₁, h₂⟩ := hd.2.1 _ hmem
    rw [faceDataOf_of_grade_eq_zero _ ((grade_toOGP hd x).trans h0)]
    exact (congrArg₂ FaceData.mk h₁ h₂).symm
  · obtain ⟨m, hm⟩ : ∃ m, x.1.val = m + 1 := ⟨x.1.val - 1, by omega⟩
    rw [faceDataOf_of_grade_eq_add_one _ ((grade_toOGP hd x).trans hm),
      facePositions_toOGP hd hc x hm, facePositions_toOGP hd hc x hm]
    rfl

theorem ofOGP_toOGP_eq_iff : ofOGP (d.toOGP hd) = d ↔ d.CanonicalFaces := by
  refine ⟨fun h => h ▸ canonicalFaces_ofOGP _, fun hc => congrArg ShapeData.mk ?_⟩
  rw [dimensionCount_toOGP hd]
  refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range]
  refine List.ext_getElem (by rw [List.length_map, length_elementsOfDim_toOGP hd h₂])
    fun k h₃ h₄ => ?_
  rw [List.getElem_map, faceDataOf_toOGP hd hc]
  obtain ⟨hy₁, hy₂⟩ := getElem_elementsOfDim_toOGP hd h₂ (by simpa using h₃)
  exact facesOf_eq_getElem hy₁ hy₂ h₂ h₄

end Realization

end Atoms.Molecule.ShapeData
