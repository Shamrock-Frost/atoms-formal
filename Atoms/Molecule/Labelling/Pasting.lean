import Atoms.Molecule.Labelling.Composite
import Atoms.ForMathlib.CategoryTheory.Bicategory.Structural

universe w v u u' u₁

open Order CategoryTheory Bicategory

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {M : LowerSet P}

theorem orderPrefix_append_of_le {pre l l' : List P} {j : ℕ} (hj : j ≤ pre.length) :
    orderPrefix M (pre ++ l) j = orderPrefix M (pre ++ l') j := by
  rw [orderPrefix, orderPrefix, List.take_append_of_le_length hj,
    List.take_append_of_le_length hj]

theorem orderPrefix_mono {xs : List P} {j k : ℕ} (hjk : j ≤ k) :
    orderPrefix M xs j ≤ orderPrefix M xs k := fun y hy => by
  rw [SetLike.mem_coe, mem_orderPrefix] at hy ⊢
  exact hy.imp_right fun ⟨x, hx, hyx⟩ => ⟨x, (List.take_prefix_take_left hjk).subset hx, hyx⟩

private theorem notMem_boundary_one {U : LowerSet P} {α : Bool} {x : P} (hx : grade ℕ x = 2) :
    x ∉ P.boundary U 1 α := fun h => by
  have h1 : grade ℕ x ≤ 1 := krullDim_le_coe_iff.1 (krullDim_boundary_le _ 1 α) ⟨x, h⟩
  omega

namespace IsLayerOrder

variable {xs : List P} (h : IsLayerOrder M xs)
include h

theorem getElem_notMem_orderPrefix {j : ℕ} (hj : j < xs.length) :
    xs[j] ∉ orderPrefix M xs j := fun hm => by
  have hb : xs[j] ∈ LowerSet.Iic xs[j] ⊓ orderPrefix M xs j := ⟨le_refl xs[j], hm⟩
  rw [h.Iic_inf_orderPrefix j hj] at hb
  exact notMem_boundary_one (h.grade_eq _ (List.getElem_mem hj)) hb

theorem mem_of_mem {y : P} (hy : y ∈ M) (hy2 : grade ℕ y = 2) : y ∈ xs := by
  rw [← h.orderPrefix_length, mem_orderPrefix, List.take_length] at hy
  rcases hy with hy | ⟨x, hx, hyx⟩
  · exact (notMem_boundary_one hy2 hy).elim
  · obtain rfl : y = x := (le_iff_eq_or_lt.1 hyx).resolve_right fun hlt =>
      (grade_strictMono (𝕆 := ℕ) hlt).ne (by rw [hy2, h.grade_eq x hx])
    exact hx

variable (hM : IsMoleculeIn P M)
include hM

theorem notMem_boundary_orderPrefix_succ {j : ℕ} {e : P} (he : e ∈ orderPrefix M xs j)
    (he' : e ∉ P.boundary (orderPrefix M xs j) 1 true) :
    e ∉ P.boundary (orderPrefix M xs (j + 1)) 1 true := by
  by_cases hj : j < xs.length
  · intro he''
    have hx2 := h.grade_eq _ (List.getElem_mem hj)
    have hkS : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic xs[j]) := by
      rw [LowerSet.krullDim_Iic, hx2]
      exact_mod_cast one_le_two
    have hR := (h.isPastingAtIn hM hj).coe_boundary_eq hkS (h.one_le_krullDim_orderPrefix hM hj)
    have hmem : e ∈ (P.boundary (orderPrefix M xs (j + 1)) 1 true : Set P) := he''
    rw [hR] at hmem
    rcases hmem with ⟨hT, -⟩ | hS
    · exact he' hT
    · have hb : e ∈ LowerSet.Iic xs[j] ⊓ orderPrefix M xs j := ⟨boundary_le _ 1 true hS, he⟩
      rw [h.Iic_inf_orderPrefix j hj] at hb
      exact he' ((h.isSubmoleculeOf j hj).le hb)
  · rwa [orderPrefix_of_length_le (by omega), ← orderPrefix_of_length_le (j := j) (by omega)]

theorem notMem_boundary_orderPrefix_of_le {j k : ℕ} (hjk : j ≤ k) {e : P}
    (he : e ∈ orderPrefix M xs j) (he' : e ∉ P.boundary (orderPrefix M xs j) 1 true) :
    e ∉ P.boundary (orderPrefix M xs k) 1 true := by
  induction k, hjk using Nat.le_induction with
  | base => exact he'
  | succ k hjk ih => exact h.notMem_boundary_orderPrefix_succ hM (orderPrefix_mono hjk he) ih

theorem mem_boundary_orderPrefix_of_le_of_le {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) {e : P}
    (hi : e ∈ P.boundary (orderPrefix M xs i) 1 true)
    (hk : e ∈ P.boundary (orderPrefix M xs k) 1 true) :
    e ∈ P.boundary (orderPrefix M xs j) 1 true :=
  by_contra fun hj => h.notMem_boundary_orderPrefix_of_le hM hjk
    (orderPrefix_mono hij (boundary_le _ 1 true hi)) hj hk

end IsLayerOrder

variable {pre mid post : List P} {y z : P}

private theorem IsLayerOrder.boundary_le_succ (h : IsLayerOrder M (pre ++ (z :: mid ++ y :: post)))
    (hM : IsMoleculeIn P M)
    (hy : P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ (z :: mid ++ y :: post)) pre.length) 1 true) :
    P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ (z :: mid ++ y :: post)) (pre.length + 1)) 1 true := by
  have hk : pre.length + (mid.length + 1) < (pre ++ (z :: mid ++ y :: post)).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hyk : (pre ++ (z :: mid ++ y :: post))[pre.length + (mid.length + 1)] = y := by
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_right (by simp)]
    simp
  have hyM := (h.isSubmoleculeOf _ hk).le
  rw [hyk] at hyM
  exact fun e he => h.mem_boundary_orderPrefix_of_le_of_le hM (by omega) (by omega) (hy he)
    (hyM he)

theorem IsLayerOrder.moveFront [Finite P] (h : IsLayerOrder M (pre ++ (mid ++ y :: post)))
    (hM : IsMoleculeIn P M)
    (hy : P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ (mid ++ y :: post)) pre.length) 1 true) :
    IsLayerOrder M (pre ++ y :: (mid ++ post)) := by
  induction mid generalizing pre with
  | nil => simpa using h
  | cons z mid ih =>
    have h' : IsLayerOrder M (pre ++ [z] ++ (mid ++ y :: post)) := by simpa using h
    have hy' := h.boundary_le_succ hM hy
    have h'' := ih h' (by simpa using hy')
    have h₃ : IsLayerOrder M (pre ++ z :: y :: (mid ++ post)) := by simpa using h''
    have hy₃ : P.boundary (.Iic y) 1 false ≤
        P.boundary (orderPrefix M (pre ++ z :: y :: (mid ++ post)) pre.length) 1 true := by
      rwa [orderPrefix_append_of_le (l' := z :: mid ++ y :: post) le_rfl]
    simpa using h₃.swap hM hy₃

section Composite

variable [Fintype P] [DecidableLE P] [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {s t : P}
  (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
  {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} (ℓ : Labelling B P hP)

private theorem Labelling.compositeAlong_congr {xs ys : List P} (e : xs = ys)
    (hxs : IsLayerOrder M xs) (hys : IsLayerOrder M ys) :
    ℓ.compositeAlong hM hxs hs ht = ℓ.compositeAlong hM hys hs ht := by
  subst e
  rfl

theorem Labelling.compositeAlong_moveFront (h : IsLayerOrder M (pre ++ (mid ++ y :: post)))
    (hy : P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ (mid ++ y :: post)) pre.length) 1 true) :
    ℓ.compositeAlong hM h hs ht = ℓ.compositeAlong hM (h.moveFront hM hy) hs ht := by
  induction mid generalizing pre with
  | nil => exact ℓ.compositeAlong_congr hM hs ht (by simp) _ _
  | cons z mid ih =>
    have h' : IsLayerOrder M (pre ++ [z] ++ (mid ++ y :: post)) := by simpa using h
    have hy' : P.boundary (.Iic y) 1 false ≤
        P.boundary (orderPrefix M (pre ++ [z] ++ (mid ++ y :: post)) (pre ++ [z]).length) 1
          true := by simpa using h.boundary_le_succ hM hy
    have h₃ : IsLayerOrder M (pre ++ z :: y :: (mid ++ post)) := by
      simpa using h'.moveFront hM hy'
    have hy₃ : P.boundary (.Iic y) 1 false ≤
        P.boundary (orderPrefix M (pre ++ z :: y :: (mid ++ post)) pre.length) 1 true := by
      rwa [orderPrefix_append_of_le (l' := z :: mid ++ y :: post) le_rfl]
    rw [ℓ.compositeAlong_congr hM hs ht (by simp) h h', ih h' hy',
      ℓ.compositeAlong_congr hM hs ht (by simp) _ h₃, ℓ.compositeAlong_swap hs ht hM h₃ hy₃]

private theorem Labelling.compositeAlong_append_eq (pre suf rest : List P)
    (h : IsLayerOrder M (pre ++ rest)) (h' : IsLayerOrder M (pre ++ suf)) :
    ℓ.compositeAlong hM h hs ht = ℓ.compositeAlong hM h' hs ht := by
  induction suf generalizing pre rest with
  | nil =>
    rcases rest with _ | ⟨r, rest⟩
    · rfl
    have hk : pre.length < (pre ++ r :: rest).length := by simp
    have hr := h.getElem_notMem_orderPrefix hk
    simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at hr
    rw [orderPrefix_append_of_le (l' := []) le_rfl, List.append_nil] at hr
    have hM' := h'.orderPrefix_length
    rw [List.append_nil] at hM'
    rw [hM'] at hr
    exact (hr (h.mem (by simp))).elim
  | cons y suf ih =>
    have hk : pre.length < (pre ++ y :: suf).length := by simp
    have hyk : (pre ++ y :: suf)[pre.length] = y := by simp
    have hyM := h'.mem (by simp : y ∈ pre ++ y :: suf)
    have hy2 := h'.grade_eq y (by simp)
    have hyr : y ∈ rest := by
      rcases List.mem_append.1 (h.mem_of_mem hyM hy2) with hyp | hyr
      · refine (h'.getElem_notMem_orderPrefix hk).elim ?_
        rw [hyk, mem_orderPrefix, List.take_left]
        exact .inr ⟨y, hyp, le_rfl⟩
      · exact hyr
    obtain ⟨mid, post, rfl⟩ := List.append_of_mem hyr
    have hy : P.boundary (.Iic y) 1 false ≤
        P.boundary (orderPrefix M (pre ++ (mid ++ y :: post)) pre.length) 1 true := by
      have := (h'.isSubmoleculeOf _ hk).le
      rwa [hyk, orderPrefix_append_of_le (l' := mid ++ y :: post) le_rfl] at this
    have h₂ : IsLayerOrder M (pre ++ [y] ++ (mid ++ post)) := by simpa using h.moveFront hM hy
    have h₂' : IsLayerOrder M (pre ++ [y] ++ suf) := by simpa using h'
    rw [ℓ.compositeAlong_moveFront hM hs ht h hy,
      ℓ.compositeAlong_congr hM hs ht (by simp) _ h₂, ih _ _ h₂ h₂']
    exact ℓ.compositeAlong_congr hM hs ht (by simp) _ _

theorem Labelling.compositeAlong_eq {xs ys : List P} (hxs : IsLayerOrder M xs)
    (hys : IsLayerOrder M ys) : ℓ.compositeAlong hM hxs hs ht = ℓ.compositeAlong hM hys hs ht :=
  ℓ.compositeAlong_append_eq hM hs ht [] ys xs hxs hys

theorem Labelling.exists_forall_compositeAlong_eq (hd : krullDim M = 2) :
    ∃ c, ∀ (xs : List P) (hxs : IsLayerOrder M xs), ℓ.compositeAlong hM hxs hs ht = c :=
  have ⟨_, hys⟩ := exists_isLayerOrder hM hd
  ⟨_, fun _ hxs => ℓ.compositeAlong_eq hM hs ht hxs hys⟩

end Composite

section PasteOne

variable {M₁ M₂ : LowerSet P} {xs₁ xs₂ : List P}

theorem orderPrefix_append_of_le_length (hp : P.IsPastingIn 1 M₁ M₂ M) {j : ℕ}
    (hj : j ≤ xs₁.length) : orderPrefix M (xs₁ ++ xs₂) j = orderPrefix M₁ xs₁ j := by
  rw [orderPrefix, orderPrefix, List.take_append_of_le_length hj, hp.boundary_input]

theorem IsLayerOrder.orderPrefix_le {xs : List P} (h : IsLayerOrder M xs) (j : ℕ) :
    orderPrefix M xs j ≤ M :=
  (orderPrefix_mono (le_max_left j xs.length)).trans_eq
    ((orderPrefix_of_length_le (le_max_right _ _)).trans h.orderPrefix_length)

theorem IsLayerOrder.orderPrefix_length_add (hp : P.IsPastingIn 1 M₁ M₂ M)
    (h₁ : IsLayerOrder M₁ xs₁) (i : ℕ) :
    orderPrefix M (xs₁ ++ xs₂) (xs₁.length + i) = M₁ ⊔ orderPrefix M₂ xs₂ i := by
  have hle : P.boundary M₂ 1 false ≤ M₁ := hp.inf_eq_input.symm.trans_le inf_le_left
  refine SetLike.ext fun y => ?_
  have hM₁ := mem_orderPrefix (M := M₁) (xs := xs₁) (j := xs₁.length) (y := y)
  rw [h₁.orderPrefix_length, List.take_length] at hM₁
  rw [LowerSet.mem_sup_iff, mem_orderPrefix, mem_orderPrefix, List.take_length_add_append,
    hp.boundary_input, hM₁]
  simp only [List.mem_append]
  constructor
  · rintro (hy | ⟨x, hx | hx, hyx⟩)
    exacts [.inl (.inl hy), .inl (.inr ⟨x, hx, hyx⟩), .inr (.inr ⟨x, hx, hyx⟩)]
  · rintro ((hy | ⟨x, hx, hyx⟩) | hy | ⟨x, hx, hyx⟩)
    · exact .inl hy
    · exact .inr ⟨x, .inl hx, hyx⟩
    · exact (hM₁.1 (hle hy)).imp_right fun ⟨x, hx, hyx⟩ => ⟨x, .inl hx, hyx⟩
    · exact .inr ⟨x, .inr hx, hyx⟩

variable (hp : P.IsPastingIn 1 M₁ M₂ M) (h₁ : IsLayerOrder M₁ xs₁) (h₂ : IsLayerOrder M₂ xs₂)
include hp h₁ h₂

theorem IsLayerOrder.boundary_orderPrefix_length_add (i : ℕ) :
    P.boundary (orderPrefix M (xs₁ ++ xs₂) (xs₁.length + i)) 1 true =
      P.boundary (orderPrefix M₂ xs₂ i) 1 true := by
  rw [h₁.orderPrefix_length_add hp, sup_comm]
  refine boundary_sup_of_inf_eq_boundary (le_antisymm ?_ ?_)
  · rw [inf_comm, hp.inf_eq_output.symm.trans hp.inf_eq_input, ← hp.inf_eq_input]
    exact inf_le_inf_left _ (h₂.orderPrefix_le i)
  · rw [← hp.inf_eq_output, hp.inf_eq_input]
    refine le_inf ?_ (hp.inf_eq_input.symm.trans_le inf_le_left)
    rw [← orderPrefix_zero (xs := xs₂)]
    exact orderPrefix_mono (Nat.zero_le i)

theorem IsLayerOrder.append_of_isPastingIn_one : IsLayerOrder M (xs₁ ++ xs₂) := by
  refine ⟨fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    exacts [h₁.grade_eq x hx, h₂.grade_eq x hx]
  · by_cases hj₁ : j < xs₁.length
    · rw [List.getElem_append_left hj₁, orderPrefix_append_of_le_length hp hj₁.le]
      exact h₁.Iic_inf_orderPrefix j hj₁
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj₁)
    have hi : i < xs₂.length := by simp only [List.length_append] at hj; omega
    have hx : (xs₁ ++ xs₂)[xs₁.length + i] = xs₂[i] := by simp
    rw [hx, h₁.orderPrefix_length_add hp, inf_sup_left, sup_eq_right.2 ?_]
    · exact h₂.Iic_inf_orderPrefix i hi
    rintro z ⟨hzx, hz₁⟩
    refine ⟨hzx, ?_⟩
    have hz : z ∈ M₁ ⊓ M₂ := ⟨hz₁, M₂.lower hzx (h₂.mem (List.getElem_mem hi))⟩
    rw [hp.inf_eq_input, ← orderPrefix_zero (xs := xs₂)] at hz
    exact orderPrefix_mono (Nat.zero_le i) hz
  · by_cases hj₁ : j < xs₁.length
    · rw [List.getElem_append_left hj₁, orderPrefix_append_of_le_length hp hj₁.le]
      exact h₁.isSubmoleculeOf j hj₁
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj₁)
    have hi : i < xs₂.length := by simp only [List.length_append] at hj; omega
    have hx : (xs₁ ++ xs₂)[xs₁.length + i] = xs₂[i] := by simp
    rw [hx, h₁.boundary_orderPrefix_length_add hp h₂]
    exact h₂.isSubmoleculeOf i hi
  · rw [List.length_append, h₁.orderPrefix_length_add hp, h₂.orderPrefix_length, hp.sup_eq]

end PasteOne

section CompositeOne

variable {M₁ M₂ : LowerSet P} {xs₁ xs₂ : List P} [Fintype P] [DecidableLE P]
  [DecidablePred (· ∈ M)] [DecidablePred (· ∈ M₁)]
  [DecidablePred (· ∈ M₂)] (hM : IsMoleculeIn P M) (hM₁ : IsMoleculeIn P M₁)
  (hM₂ : IsMoleculeIn P M₂) (hp : P.IsPastingIn 1 M₁ M₂ M) (h₁ : IsLayerOrder M₁ xs₁)
  (h₂ : IsLayerOrder M₂ xs₂) {s t : P} (hs : P.boundary M 0 false = .Iic s)
  (ht : P.boundary M 0 true = .Iic t) (hs₁ : P.boundary M₁ 0 false = .Iic s)
  (ht₁ : P.boundary M₁ 0 true = .Iic t) (hs₂ : P.boundary M₂ 0 false = .Iic s)
  (ht₂ : P.boundary M₂ 0 true = .Iic t)
  {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} (ℓ : Labelling B P hP)

theorem Labelling.compositeAlong_append :
    ℓ.compositeAlong hM (h₁.append_of_isPastingIn_one hp h₂) hs ht =
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr hp.boundary_input)) ≫
        ℓ.compositeAlong hM₁ h₁ hs₁ ht₁ ≫
          eqToHom (congrArg (pathComp ℓ.toPrefunctor)
            (pathOf_congr (hp.inf_eq_output.symm.trans hp.inf_eq_input))) ≫
            ℓ.compositeAlong hM₂ h₂ hs₂ ht₂ ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor)
                (pathOf_congr hp.boundary_output.symm)) := by
  have h := h₁.append_of_isPastingIn_one hp h₂
  have hA (j : ℕ) (hj : j ≤ xs₁.length) : stagePath hM h hs ht j = stagePath hM₁ h₁ hs₁ ht₁ j :=
    stagePath_eq_of_boundary_eq hs ht hM h hM₁ h₁ hs₁ ht₁
      (by rw [orderPrefix_append_of_le_length hp hj])
  have hB (i m : ℕ) (hm : m = xs₁.length + i) :
      stagePath hM h hs ht m = stagePath hM₂ h₂ hs₂ ht₂ i :=
    stagePath_eq_of_boundary_eq hs ht hM h hM₂ h₂ hs₂ ht₂
      (by rw [hm, h₁.boundary_orderPrefix_length_add hp h₂])
  have cA (n : ℕ) (hn : n ≤ xs₁.length) :
      ℓ.compositeUpTo hM h hs ht n (by simp only [List.length_append]; omega) =
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA 0 (Nat.zero_le _))) ≫
          ℓ.compositeUpTo hM₁ h₁ hs₁ ht₁ n hn ≫
            eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA n hn).symm) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ, ih (by omega),
        ℓ.layerComp_eq_of_stagePath_eq hs ht hM h hM₁ h₁ hs₁ ht₁ _ hn
          (List.getElem_append_left hn) (hA n (by omega)) (hA (n + 1) hn)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have cB (i : ℕ) (hi : i ≤ xs₂.length) (m : ℕ) (hm : m = xs₁.length + i) :
      ℓ.compositeUpTo hM h hs ht m (by simp only [List.length_append]; omega) =
        ℓ.compositeUpTo hM h hs ht xs₁.length (by simp) ≫
          eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB 0 _ rfl)) ≫
            ℓ.compositeUpTo hM₂ h₂ hs₂ ht₂ i hi ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB i m hm).symm) := by
    induction i generalizing m with
    | zero =>
      obtain rfl : m = xs₁.length := hm
      simp
    | succ i ih =>
      obtain rfl : m = xs₁.length + i + 1 := hm
      have hk : xs₁.length + i < (xs₁ ++ xs₂).length := by simp only [List.length_append]; omega
      have hx : (xs₁ ++ xs₂)[xs₁.length + i] = xs₂[i] := by simp
      rw [ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ, ih (by omega) _ rfl,
        ℓ.layerComp_eq_of_stagePath_eq hs ht hM h hM₂ h₂ hs₂ ht₂ hk hi hx (hB i _ rfl)
          (hB (i + 1) _ rfl)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Labelling.compositeAlong, cB xs₂.length le_rfl _ List.length_append, cA _ le_rfl,
    Labelling.compositeAlong, Labelling.compositeAlong]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

theorem Labelling.pathCell_append_of_isPastingIn_one {a b : B} {p q r : Quiver.Path (V := B) a b}
    {φ : pathComp (𝟭q B) p ⟶ pathComp (𝟭q B) q} {χ : pathComp (𝟭q B) q ⟶ pathComp (𝟭q B) r}
    (h₁' : ℓ.pathCell hM₁ h₁ hs₁ ht₁ = ⟨a, b, p, q, φ⟩)
    (h₂' : ℓ.pathCell hM₂ h₂ hs₂ ht₂ = ⟨a, b, q, r, χ⟩) :
    ℓ.pathCell hM (h₁.append_of_isPastingIn_one hp h₂) hs ht = ⟨a, b, p, r, φ ≫ χ⟩ := by
  unfold Labelling.pathCell at h₁' h₂' ⊢
  obtain ⟨rfl, rfl, hp', hq', hφ⟩ := PathCell.mk.inj h₁'
  obtain rfl := eq_of_heq hp'
  obtain rfl := eq_of_heq hq'
  obtain ⟨-, -, -, hr', hχ⟩ := PathCell.mk.inj h₂'
  obtain rfl := eq_of_heq hr'
  refine PathCell.ext rfl rfl (heq_of_eq (congrArg _ (pathOf_congr hp.boundary_input)))
    (heq_of_eq (congrArg _ (pathOf_congr hp.boundary_output))) ?_
  dsimp only
  rw [ℓ.compositeAlong_append hM hM₁ hM₂ hp h₁ h₂ hs ht hs₁ ht₁ hs₂ ht₂]
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ((eqToHom_comp_heq _ _).trans
    (heq_comp (pathComp_mapPath ℓ.toPrefunctor _).symm
    (pathComp_mapPath ℓ.toPrefunctor _).symm ((congrArg (pathComp ℓ.toPrefunctor)
      (pathOf_congr hp.boundary_output)).trans (pathComp_mapPath ℓ.toPrefunctor _).symm)
    (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans hφ) ?_)))
  exact (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans
    (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans hχ))

end CompositeOne

section PasteZero

variable {M₁ M₂ : LowerSet P} {xs₁ xs₂ : List P}

private theorem boundary_zero_boundary {U : LowerSet P} (hU : IsMoleculeIn P U) (α β : Bool) :
    P.boundary (P.boundary U 1 β) 0 α = P.boundary U 0 α :=
  hU.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)

private theorem isPastingIn_zero_of_le (hp : P.IsPastingIn 0 M₁ M₂ M) {S T : LowerSet P}
    (hS : S ≤ M₁) (hT : T ≤ M₂)
    (hS' : P.boundary S 0 true = P.boundary M₁ 0 true)
    (hT' : P.boundary T 0 false = P.boundary M₂ 0 false) : P.IsPastingIn 0 S T (S ⊔ T) := by
  have hm : M₁ ⊓ M₂ = P.boundary S 0 true := hS' ▸ hp.inf_eq_output
  have hm' : M₁ ⊓ M₂ = P.boundary T 0 false := hT' ▸ hp.inf_eq_input
  have hST : S ⊓ T = M₁ ⊓ M₂ := le_antisymm (inf_le_inf hS hT)
    (le_inf (hm ▸ boundary_le _ 0 true) (hm' ▸ boundary_le _ 0 false))
  exact ⟨rfl, hST.trans hm, hST.trans hm'⟩

variable (hM₁ : IsMoleculeIn P M₁) (hM₂ : IsMoleculeIn P M₂) (hp : P.IsPastingIn 0 M₁ M₂ M)
include hM₁ hM₂ hp

private theorem isPastingIn_boundary (α : Bool) :
    P.IsPastingIn 0 (P.boundary M₁ 1 α) (P.boundary M₂ 1 α) (P.boundary M 1 α) :=
  hp.boundary_of_lt hM₁.isGlobular hM₂.isGlobular zero_lt_one α

variable (h₁ : IsLayerOrder M₁ xs₁) (h₂ : IsLayerOrder M₂ xs₂)
include h₁ h₂

omit h₂ in
theorem IsLayerOrder.isPastingIn_orderPrefix_append_of_le_length {j : ℕ} (hj : j ≤ xs₁.length) :
    P.IsPastingIn 0 (orderPrefix M₁ xs₁ j) (P.boundary M₂ 1 false)
      (orderPrefix M (xs₁ ++ xs₂) j) := by
  have hq := isPastingIn_zero_of_le hp (h₁.orderPrefix_le j) (boundary_le _ 1 false)
    (by rw [← boundary_zero_boundary (h₁.isMoleculeIn_orderPrefix hM₁ j) true false,
      h₁.boundary_false_orderPrefix hM₁, boundary_zero_boundary hM₁])
    (boundary_zero_boundary hM₂ false false)
  convert hq using 1
  refine SetLike.ext fun y => ?_
  rw [mem_orderPrefix, List.take_append_of_le_length hj, LowerSet.mem_sup_iff, mem_orderPrefix,
    ← (isPastingIn_boundary hM₁ hM₂ hp false).sup_eq, LowerSet.mem_sup_iff]
  exact or_right_comm

theorem IsLayerOrder.isPastingIn_orderPrefix_length_add (i : ℕ) :
    P.IsPastingIn 0 M₁ (orderPrefix M₂ xs₂ i) (orderPrefix M (xs₁ ++ xs₂) (xs₁.length + i)) := by
  have hq := isPastingIn_zero_of_le hp le_rfl (h₂.orderPrefix_le i) rfl
    (by rw [← boundary_zero_boundary (h₂.isMoleculeIn_orderPrefix hM₂ i) false false,
      h₂.boundary_false_orderPrefix hM₂, boundary_zero_boundary hM₂])
  convert hq using 1
  have hb := (isPastingIn_boundary hM₁ hM₂ hp false).sup_eq
  refine SetLike.ext fun y => ?_
  have hy := mem_orderPrefix (M := M₁) (xs := xs₁) (j := xs₁.length) (y := y)
  rw [h₁.orderPrefix_length, List.take_length] at hy
  rw [mem_orderPrefix, List.take_length_add_append, LowerSet.mem_sup_iff, mem_orderPrefix, ← hb,
    LowerSet.mem_sup_iff, hy]
  simp only [List.mem_append]
  constructor
  · rintro ((hy | hy) | ⟨x, hx | hx, hyx⟩)
    exacts [.inl (.inl hy), .inr (.inl hy), .inl (.inr ⟨x, hx, hyx⟩), .inr (.inr ⟨x, hx, hyx⟩)]
  · rintro ((hy | ⟨x, hx, hyx⟩) | hy | ⟨x, hx, hyx⟩)
    exacts [.inl (.inl hy), .inr ⟨x, .inl hx, hyx⟩, .inl (.inr hy), .inr ⟨x, .inr hx, hyx⟩]

omit h₂ in
theorem IsLayerOrder.isPastingIn_boundary_orderPrefix_append_of_le_length {j : ℕ}
    (hj : j ≤ xs₁.length) :
    P.IsPastingIn 0 (P.boundary (orderPrefix M₁ xs₁ j) 1 true) (P.boundary M₂ 1 false)
      (P.boundary (orderPrefix M (xs₁ ++ xs₂) j) 1 true) := by
  have hq := (h₁.isPastingIn_orderPrefix_append_of_le_length hM₁ hM₂ hp (xs₂ := xs₂)
    hj).boundary_of_lt (h₁.isMoleculeIn_orderPrefix hM₁ j).isGlobular
      (hM₂.boundary 1 false).isGlobular zero_lt_one true
  rwa [boundary_boundary_of_le le_rfl true false] at hq

theorem IsLayerOrder.isPastingIn_boundary_orderPrefix_length_add (i : ℕ) :
    P.IsPastingIn 0 (P.boundary M₁ 1 true) (P.boundary (orderPrefix M₂ xs₂ i) 1 true)
      (P.boundary (orderPrefix M (xs₁ ++ xs₂) (xs₁.length + i)) 1 true) :=
  (h₁.isPastingIn_orderPrefix_length_add hM₁ hM₂ hp h₂ i).boundary_of_lt hM₁.isGlobular
    (h₂.isMoleculeIn_orderPrefix hM₂ i).isGlobular zero_lt_one true

theorem IsLayerOrder.append_of_isPastingIn_zero [Finite P] : IsLayerOrder M (xs₁ ++ xs₂) := by
  have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
    (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
  have hm₁ (j : ℕ) : M₁ ⊓ M₂ ≤ orderPrefix M₁ xs₁ j := by
    rw [hp.inf_eq_output, ← boundary_zero_boundary hM₁ true false,
      ← h₁.boundary_false_orderPrefix hM₁ j, boundary_zero_boundary
        (h₁.isMoleculeIn_orderPrefix hM₁ j)]
    exact boundary_le _ 0 true
  have hm₂ (i : ℕ) : M₁ ⊓ M₂ ≤ orderPrefix M₂ xs₂ i := by
    rw [hp.inf_eq_input, ← boundary_zero_boundary hM₂ false false, ← orderPrefix_zero (xs := xs₂)]
    exact (boundary_le _ 0 false).trans (orderPrefix_mono (Nat.zero_le i))
  refine ⟨fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    exacts [h₁.grade_eq x hx, h₂.grade_eq x hx]
  · by_cases hj₁ : j < xs₁.length
    · have hxM := h₁.mem (List.getElem_mem hj₁)
      rw [List.getElem_append_left hj₁,
        ← (h₁.isPastingIn_orderPrefix_append_of_le_length hM₁ hM₂ hp hj₁.le).sup_eq, inf_sup_left,
        sup_eq_left.2 ?_]
      · exact h₁.Iic_inf_orderPrefix j hj₁
      rintro z ⟨hzx, hz₂⟩
      exact ⟨hzx, hm₁ j ⟨M₁.lower hzx hxM, boundary_le _ 1 false hz₂⟩⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj₁)
    have hi : i < xs₂.length := by simp only [List.length_append] at hj; omega
    have hx : (xs₁ ++ xs₂)[xs₁.length + i] = xs₂[i] := by simp
    rw [hx, ← (h₁.isPastingIn_orderPrefix_length_add hM₁ hM₂ hp h₂ i).sup_eq, inf_sup_left,
      sup_eq_right.2 ?_]
    · exact h₂.Iic_inf_orderPrefix i hi
    rintro z ⟨hzx, hz₁⟩
    exact ⟨hzx, hm₂ i ⟨hz₁, M₂.lower hzx (h₂.mem (List.getElem_mem hi))⟩⟩
  · by_cases hj₁ : j < xs₁.length
    · have hq := h₁.isPastingIn_boundary_orderPrefix_append_of_le_length hM₁ hM₂ hp (xs₂ := xs₂)
        hj₁.le
      rw [List.getElem_append_left hj₁]
      exact isSubmoleculeOf_of_le (hq.isMoleculeIn ((h₁.isMoleculeIn_orderPrefix hM₁ j).boundary
        1 true) (hM₂.boundary 1 false)) (hd₁ _ true)
        ((h₁.isMoleculeIn_Iic hM₁ hj₁).boundary 1 false) (h₁.krullDim_boundary_Iic hM₁ hj₁ false)
        ((h₁.isSubmoleculeOf j hj₁).le.trans hq.left_le)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj₁)
    have hi : i < xs₂.length := by simp only [List.length_append] at hj; omega
    have hx : (xs₁ ++ xs₂)[xs₁.length + i] = xs₂[i] := by simp
    have hq := h₁.isPastingIn_boundary_orderPrefix_length_add hM₁ hM₂ hp h₂ i
    rw [hx]
    exact isSubmoleculeOf_of_le (hq.isMoleculeIn (hM₁.boundary 1 true)
      ((h₂.isMoleculeIn_orderPrefix hM₂ i).boundary 1 true)) (hd₁ _ true)
      ((h₂.isMoleculeIn_Iic hM₂ hi).boundary 1 false) (h₂.krullDim_boundary_Iic hM₂ hi false)
      ((h₂.isSubmoleculeOf i hi).le.trans hq.right_le)
  · rw [List.length_append, ← (h₁.isPastingIn_orderPrefix_length_add hM₁ hM₂ hp h₂ _).sup_eq,
      h₂.orderPrefix_length, hp.sup_eq]

end PasteZero

section CompositeZero

variable {M₁ M₂ : LowerSet P} {xs₁ xs₂ : List P} [Fintype P] [DecidableLE P]
  [DecidablePred (· ∈ M)] [DecidablePred (· ∈ M₁)] [DecidablePred (· ∈ M₂)]
  (hM : IsMoleculeIn P M) (hM₁ : IsMoleculeIn P M₁) (hM₂ : IsMoleculeIn P M₂)
  (hp : P.IsPastingIn 0 M₁ M₂ M) (h₁ : IsLayerOrder M₁ xs₁) (h₂ : IsLayerOrder M₂ xs₂)
  {s m t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
  (hs₁ : P.boundary M₁ 0 false = .Iic s) (hm₁ : P.boundary M₁ 0 true = .Iic m)
  (hm₂ : P.boundary M₂ 0 false = .Iic m) (ht₂ : P.boundary M₂ 0 true = .Iic t)
  {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} (ℓ : Labelling B P hP)

theorem Labelling.compositeAlong_append_of_isPastingIn_zero :
    ℓ.compositeAlong hM (h₁.append_of_isPastingIn_zero hM₁ hM₂ hp h₂) hs ht =
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_eq_comp
        (hp.boundary_of_lt hM₁.isGlobular hM₂.isGlobular zero_lt_one false) _ _ _ _ _ _ _ _ _ _ _
          _)) ≫
        (pathCompCompIso ℓ.toPrefunctor _ _).hom ≫
          (ℓ.compositeAlong hM₁ h₁ hs₁ hm₁ ▷ _ ≫ _ ◁ ℓ.compositeAlong hM₂ h₂ hm₂ ht₂) ≫
            (pathCompCompIso ℓ.toPrefunctor _ _).inv ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_eq_comp
                (hp.boundary_of_lt hM₁.isGlobular hM₂.isGlobular zero_lt_one true) _ _ _ _ _ _ _ _ _
                  _ _ _).symm) := by
  have h := h₁.append_of_isPastingIn_zero hM₁ hM₂ hp h₂
  have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
    (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
  have e₂s := (boundary_zero_boundary hM₂ false false).trans hm₂
  have e₂t := (boundary_zero_boundary hM₂ true false).trans ht₂
  have e₁s := (boundary_zero_boundary hM₁ false true).trans hs₁
  have e₁t := (boundary_zero_boundary hM₁ true true).trans hm₁
  have hA (j : ℕ) (hj : j ≤ xs₁.length) : stagePath hM h hs ht j =
      (stagePath hM₁ h₁ hs₁ hm₁ j).comp
        (pathOf _ (hM₂.boundary 1 false) (hd₁ _ false) e₂s e₂t) := by
    have hq := h₁.isPastingIn_boundary_orderPrefix_append_of_le_length hM₁ hM₂ hp (xs₂ := xs₂) hj
    refine (eq_stagePath_of_forall_mem hM h hs ht _ fun e he => ?_).symm
    rw [pathEdges_comp, List.mem_append, pathEdges_stagePath, pathEdges_pathOf] at he
    rcases he with he | he
    · exact hq.left_le ((mem_edgeList_iff ((h₁.isMoleculeIn_orderPrefix hM₁ j).boundary 1 true)
        (hd₁ _ true)).1 he).1
    · exact hq.right_le ((mem_edgeList_iff (hM₂.boundary 1 false) (hd₁ _ false)).1 he).1
  have hB (i n : ℕ) (hn : n = xs₁.length + i) : stagePath hM h hs ht n =
      (pathOf _ (hM₁.boundary 1 true) (hd₁ _ true) e₁s e₁t).comp (stagePath hM₂ h₂ hm₂ ht₂ i) := by
    subst hn
    have hq := h₁.isPastingIn_boundary_orderPrefix_length_add hM₁ hM₂ hp h₂ i
    refine (eq_stagePath_of_forall_mem hM h hs ht _ fun e he => ?_).symm
    rw [pathEdges_comp, List.mem_append, pathEdges_stagePath, pathEdges_pathOf] at he
    rcases he with he | he
    · exact hq.left_le ((mem_edgeList_iff (hM₁.boundary 1 true) (hd₁ _ true)).1 he).1
    · exact hq.right_le ((mem_edgeList_iff ((h₂.isMoleculeIn_orderPrefix hM₂ i).boundary 1 true)
        (hd₁ _ true)).1 he).1
  have cQ {r r' : Quiver.Path (V := EdgeQuiver P) s m} (e : r = r') :
      r.comp (pathOf _ (hM₂.boundary 1 false) (hd₁ _ false) e₂s e₂t) =
        r'.comp (pathOf _ (hM₂.boundary 1 false) (hd₁ _ false) e₂s e₂t) := by
    rw [e]
  have lA (j : ℕ) (hj : j < xs₁.length) :
      ℓ.layerComp hM h hs ht j (by simp only [List.length_append]; omega) =
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA j hj.le)) ≫
          (pathCompCompIso ℓ.toPrefunctor _ _).hom ≫
            ℓ.layerComp hM₁ h₁ hs₁ hm₁ j hj ▷ _ ≫ (pathCompCompIso ℓ.toPrefunctor _ _).inv ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA (j + 1) hj).symm) := by
    have hx := hP xs₁[j]
    have ha := boundary_zero_eq_Iic_vertex _ hx false
    have hb := boundary_zero_eq_Iic_vertex _ hx true
    obtain ⟨p, c, e⟩ := h₁.exists_stagePath_eq hs₁ hm₁ hM₁ hj ha hb
    have e' := h₁.comp_comp_eq_stagePath hs₁ hm₁ hM₁ hj rfl hx ha hb p c e
    have E := (hA j hj.le).trans ((cQ e).trans
      ((Quiver.Path.comp_assoc p _ _).trans (congrArg p.comp (Quiver.Path.comp_assoc _ c _))))
    have E' := ((congrArg p.comp (Quiver.Path.comp_assoc _ c _)).symm.trans
      (Quiver.Path.comp_assoc p _ _).symm).trans ((cQ e').trans
        (hA (j + 1) hj).symm)
    rw [ℓ.layerComp_eq hM h hs ht _ (List.getElem_append_left hj) ha hb p _ E E',
      ℓ.layerComp_eq hM₁ h₁ hs₁ hm₁ hj rfl ha hb p c e e', pathWhisker_comp_right]
    simp only [comp_whiskerRight, Category.assoc]
    rw [pathCompCompIso_hom_eqToHom_whiskerRight_assoc _ e,
      eqToHom_whiskerRight_pathCompCompIso_inv_assoc _ e']
    simp only [eqToHom_trans_assoc, eqToHom_trans]
  have cQ' {r r' : Quiver.Path (V := EdgeQuiver P) m t} (e : r = r') :
      (pathOf _ (hM₁.boundary 1 true) (hd₁ _ true) e₁s e₁t).comp r =
        (pathOf _ (hM₁.boundary 1 true) (hd₁ _ true) e₁s e₁t).comp r' := by
    rw [e]
  have lB (i : ℕ) (hi : i < xs₂.length) :
      ℓ.layerComp hM h hs ht (xs₁.length + i) (by simp only [List.length_append]; omega) =
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB i _ rfl)) ≫
          (pathCompCompIso ℓ.toPrefunctor _ _).hom ≫
            _ ◁ ℓ.layerComp hM₂ h₂ hm₂ ht₂ i hi ≫ (pathCompCompIso ℓ.toPrefunctor _ _).inv ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB (i + 1) _ rfl).symm) := by
    have hx := hP xs₂[i]
    have ha := boundary_zero_eq_Iic_vertex _ hx false
    have hb := boundary_zero_eq_Iic_vertex _ hx true
    obtain ⟨p, c, e⟩ := h₂.exists_stagePath_eq hm₂ ht₂ hM₂ hi ha hb
    have e' := h₂.comp_comp_eq_stagePath hm₂ ht₂ hM₂ hi rfl hx ha hb p c e
    have E := (hB i _ rfl).trans ((cQ' e).trans (Quiver.Path.comp_assoc _ p _).symm)
    have E' := (Quiver.Path.comp_assoc _ p _).trans ((cQ' e').trans (hB (i + 1) _ rfl).symm)
    have hxi : (xs₁ ++ xs₂)[xs₁.length + i]'(by simp only [List.length_append]; omega) =
        xs₂[i] := by simp
    rw [ℓ.layerComp_eq hM h hs ht _ hxi ha hb _ c E E',
      ℓ.layerComp_eq hM₂ h₂ hm₂ ht₂ hi rfl ha hb p c e e', pathWhisker_comp_left]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← eqToHom_pathCompCompIso_hom_assoc _ _ e,
      whiskerLeft_eqToHom_pathCompCompIso_inv_assoc _ _ e']
    simp only [eqToHom_trans_assoc, eqToHom_trans]
  have cA (n : ℕ) (hn : n ≤ xs₁.length) :
      ℓ.compositeUpTo hM h hs ht n (by simp only [List.length_append]; omega) =
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA 0 (Nat.zero_le _))) ≫
          (pathCompCompIso ℓ.toPrefunctor _ _).hom ≫
            ℓ.compositeUpTo hM₁ h₁ hs₁ hm₁ n hn ▷ _ ≫ (pathCompCompIso ℓ.toPrefunctor _ _).inv ≫
              eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hA n hn).symm) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ, ih (by omega), lA n hn, comp_whiskerRight]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Iso.inv_hom_id_assoc]
  have cB (i : ℕ) (hi : i ≤ xs₂.length) (n : ℕ) (hn : n = xs₁.length + i) :
      ℓ.compositeUpTo hM h hs ht n (by simp only [List.length_append]; omega) =
        ℓ.compositeUpTo hM h hs ht xs₁.length (by simp) ≫
          eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB 0 _ rfl)) ≫
            (pathCompCompIso ℓ.toPrefunctor _ _).hom ≫
              _ ◁ ℓ.compositeUpTo hM₂ h₂ hm₂ ht₂ i hi ≫ (pathCompCompIso ℓ.toPrefunctor _ _).inv ≫
                eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hB i n hn).symm) := by
    induction i generalizing n with
    | zero =>
      obtain rfl : n = xs₁.length := hn
      simp
    | succ i ih =>
      obtain rfl : n = xs₁.length + i + 1 := hn
      rw [ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ, ih (by omega) _ rfl, lB i hi,
        whiskerLeft_comp]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Iso.inv_hom_id_assoc]
  rw [Labelling.compositeAlong, cB xs₂.length le_rfl _ List.length_append, cA _ le_rfl,
    Labelling.compositeAlong, Labelling.compositeAlong]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc, eqToHom_trans_assoc]
  rw [pathCompCompIso_inv_eqToHom_hom_assoc _ (stagePath_length hM₁ h₁ hs₁ hm₁)
      (stagePath_zero hM₂ h₂ hm₂ ht₂).symm ((hA _ le_rfl).symm.trans (hB 0 _ rfl)),
    pathCompCompIso_hom_eqToHom_whiskerRight_assoc _ (stagePath_zero hM₁ h₁ hs₁ hm₁).symm,
    whiskerLeft_eqToHom_pathCompCompIso_inv_assoc _ _ (stagePath_length hM₂ h₂ hm₂ ht₂),
    eqToHom_whiskerRight, whiskerLeft_eqToHom]
  simp only [eqToHom_trans, eqToHom_trans_assoc]

theorem Labelling.pathCell_append_of_isPastingIn_zero {a c b : B}
    {p q : Quiver.Path (V := B) a c} {p' q' : Quiver.Path (V := B) c b}
    {φ : pathComp (𝟭q B) p ⟶ pathComp (𝟭q B) q} {χ : pathComp (𝟭q B) p' ⟶ pathComp (𝟭q B) q'}
    (h₁' : ℓ.pathCell hM₁ h₁ hs₁ hm₁ = ⟨a, c, p, q, φ⟩)
    (h₂' : ℓ.pathCell hM₂ h₂ hm₂ ht₂ = ⟨c, b, p', q', χ⟩) :
    ℓ.pathCell hM (h₁.append_of_isPastingIn_zero hM₁ hM₂ hp h₂) hs ht =
      ⟨a, b, p.comp p', q.comp q', (pathCompCompIso (𝟭q B) p p').hom ≫
        (φ ▷ pathComp (𝟭q B) p' ≫ pathComp (𝟭q B) q ◁ χ) ≫ (pathCompCompIso (𝟭q B) q q').inv⟩ := by
  have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
    (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
  have hb (α : Bool) := hp.boundary_of_lt hM₁.isGlobular hM₂.isGlobular zero_lt_one α
  have hc (α : Bool) := pathOf_eq_comp (hb α) (hM.boundary 1 α) (hd₁ _ α) (hM₁.boundary 1 α)
    (hd₁ _ α) (hM₂.boundary 1 α) (hd₁ _ α)
    ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
    ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
    ((hM₁.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs₁)
    ((hM₁.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hm₁)
    ((hM₂.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hm₂)
    ((hM₂.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht₂)
  unfold Labelling.pathCell at h₁' h₂' ⊢
  obtain ⟨rfl, rfl, hp₁, hq₁, hφ⟩ := PathCell.mk.inj h₁'
  obtain rfl := eq_of_heq hp₁
  obtain rfl := eq_of_heq hq₁
  obtain ⟨-, rfl, hp₂, hq₂, hχ⟩ := PathCell.mk.inj h₂'
  obtain rfl := eq_of_heq hp₂
  obtain rfl := eq_of_heq hq₂
  refine PathCell.ext rfl rfl
    (heq_of_eq ((congrArg _ (hc false)).trans (ℓ.toPrefunctor.mapPath_comp _ _)))
    (heq_of_eq ((congrArg _ (hc true)).trans (ℓ.toPrefunctor.mapPath_comp _ _))) ?_
  dsimp only
  rw [ℓ.compositeAlong_append_of_isPastingIn_zero hM hM₁ hM₂ hp h₁ h₂ hs ht hs₁ hm₁ hm₂ ht₂]
  have hφ' := ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans hφ
  have hχ' := ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans hχ
  have e (U : LowerSet P) [DecidablePred (· ∈ U)] (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
      {v w : P} (hv : P.boundary U 0 false = .Iic v) (hw : P.boundary U 0 true = .Iic w) :=
    (pathComp_mapPath ℓ.toPrefunctor (pathOf U hU hd hv hw)).symm
  have e₂ {x y z : EdgeQuiver P} (r : Quiver.Path x y) (r' : Quiver.Path y z) :=
    (pathComp_mapPath ℓ.toPrefunctor (r.comp r')).symm.trans
      (congrArg (pathComp (𝟭q B)) (ℓ.toPrefunctor.mapPath_comp r r'))
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ((eqToHom_comp_heq _ _).trans
    (heq_comp ?_ ?_ ?_ (FreeBicategory.pathCompCompIso_hom_mapPath_heq _ _ _).symm
      (heq_comp ?_ ?_ ?_ (heq_comp ?_ ?_ ?_ ?_ ?_) ?_))))
  any_goals exact congrArg₂ (· ≫ ·) (e _ _ _ _ _) (e _ _ _ _ _)
  any_goals exact e₂ _ _
  any_goals exact (congrArg (pathComp ℓ.toPrefunctor) (hc true)).trans (e₂ _ _)
  · exact whiskerRight_heq (e _ _ _ _ _) (e _ _ _ _ _) (e _ _ _ _ _) hφ'
  · exact whiskerLeft_heq (e _ _ _ _ _) (e _ _ _ _ _) (e _ _ _ _ _) hχ'
  · exact (comp_eqToHom_heq _ _).trans (FreeBicategory.pathCompCompIso_inv_mapPath_heq _ _ _).symm

end CompositeZero

section LocalIso

variable {Q : OGP.{u'}}

private theorem image_orderPrefix (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {y : P} (α : Bool)
    (xs : List P) (j : ℕ) :
    f '' (orderPrefix (P.boundary (.Iic y) 2 α) xs j : Set P) =
      orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j := by
  rw [orderPrefix, orderPrefix, LowerSet.coe_sup, LowerSet.coe_sup, Set.image_union,
    (hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two),
    (hQ (f y)).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two),
    f.isMap_coe.image_boundary, f.isMap_coe.fibration.image_lowerClosure f.isMap_coe.monotone,
    ← List.map_take]
  congr 3
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]

private theorem coe_interior_eq {R : OGP.{u}} {U : LowerSet R} (hU : krullDim U = 1) :
    R.interior U = (U : Set R) \ (R.boundary U 0 false ∪ R.boundary U 0 true : Set R) := by
  have h : R.properBoundary U = R.boundaryFull U 0 :=
    le_antisymm (iSup₂_le fun n hn => by
      have : n = 0 := by
        rw [hU] at hn
        exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast hn)
      subst this
      exact le_rfl) (le_iSup₂_of_le 0 (by rw [hU]; exact_mod_cast zero_lt_one) le_rfl)
  rw [OGP.interior, h, boundaryFull, LowerSet.coe_sup]

variable [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q]

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
private theorem image_interior_boundary (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {y x : P}
    (hinj : Set.InjOn f (Set.Iic y)) (hxy : x ≤ y) (hx : grade ℕ x = 2)
    (hfx : grade ℕ (f x) = 2) :
    f '' P.interior (P.boundary (.Iic x) 1 false) =
      Q.interior (Q.boundary (.Iic (f x)) 1 false) := by
  have hUP : krullDim (P.boundary (.Iic x) 1 false) = 1 :=
    ((hP x).krullDim_boundary (by rw [LowerSet.krullDim_Iic, hx]; exact_mod_cast one_le_two)
      false).trans Nat.cast_one
  have hUQ : krullDim (Q.boundary (.Iic (f x)) 1 false) = 1 :=
    ((hQ (f x)).krullDim_boundary (by rw [LowerSet.krullDim_Iic, hfx]; exact_mod_cast one_le_two)
      false).trans Nat.cast_one
  have hb (β : Bool) : f '' (P.boundary (P.boundary (.Iic x) 1 false) 0 β : Set P) =
      Q.boundary (Q.boundary (.Iic (f x)) 1 false) 0 β := by
    rw [(hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one),
      (hQ (f x)).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one),
      f.isMap_coe.image_boundary]
  have hsub : (P.boundary (.Iic x) 1 false : Set P) ⊆ Set.Iic y := fun z hz =>
    (LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hz)).trans hxy
  rw [coe_interior_eq hUP, coe_interior_eq hUQ, (hinj.mono hsub).image_sdiff,
    Set.inter_eq_right.2 (Set.union_subset (boundary_le _ _ _) (boundary_le _ _ _)),
    Set.image_union, hb, hb, f.isMap_coe.image_boundary]

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
private theorem Iic_inf_orderPrefix_map (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {y : P}
    (hinj : Set.InjOn f (Set.Iic y)) {α : Bool} {xs : List P}
    (h : IsLayerOrder (P.boundary (.Iic y) 2 α) xs) {j : ℕ} (hj : j < xs.length) :
    .Iic (f xs[j]) ⊓ orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j =
      Q.boundary (.Iic (f xs[j])) 1 false := by
  have hle : (orderPrefix (P.boundary (.Iic y) 2 α) xs j : Set P) ⊆ Set.Iic y := fun z hz =>
    boundary_le _ _ _ (h.orderPrefix_le j hz)
  have hxy : xs[j] ≤ y := boundary_le _ _ _ (h.mem (List.getElem_mem hj))
  refine SetLike.coe_injective ?_
  rw [LowerSet.coe_inf, ← image_orderPrefix f hP hQ, LowerSet.coe_Iic, ← f.isMap_coe.image_Iic,
    ← hinj.image_inter (s := Set.Iic xs[j]) (fun z hz => le_trans hz hxy) hle, ← LowerSet.coe_Iic,
    ← LowerSet.coe_inf,
    h.Iic_inf_orderPrefix j hj, f.isMap_coe.image_boundary]

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
private theorem isSubmoleculeOf_boundary_map [Finite Q] (f : Map P Q) (hQ : Q.IsRDC) {y : P}
    {α : Bool}
    {xs : List P} (h : IsLayerOrder (P.boundary (.Iic y) 2 α) xs) {j : ℕ} (hj : j < xs.length)
    (hfx2 : grade ℕ (f xs[j]) = 2)
    (h₁ : IsMoleculeIn Q (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j))
    (h₂ : (Q.boundary (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) 1 true : Set Q) =
      f '' P.boundary (orderPrefix (P.boundary (.Iic y) 2 α) xs j) 1 true) :
    Q.IsSubmoleculeOf (Q.boundary (.Iic (f xs[j])) 1 false)
      (Q.boundary (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) 1 true) := by
  refine isSubmoleculeOf_of_le (h₁.boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) ((hQ (f xs[j])).boundary 1 false)
    (((hQ (f xs[j])).krullDim_boundary (by
      rw [LowerSet.krullDim_Iic, hfx2]; exact_mod_cast one_le_two) false).trans
        Nat.cast_one) fun z hz => ?_
  have hz' : z ∈ (Q.boundary (.Iic (f xs[j])) 1 false : Set Q) := hz
  rw [← f.isMap_coe.image_boundary] at hz'
  obtain ⟨w, hw, rfl⟩ := hz'
  have : f w ∈ (Q.boundary (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) 1 true :
      Set Q) := by
    rw [h₂]
    exact Set.mem_image_of_mem f ((h.isSubmoleculeOf j hj).le hw)
  exact this

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
private theorem isMoleculeIn_and_boundary_orderPrefix_map [Finite Q] (f : Map P Q)
    (hP : P.IsRDC) (hQ : Q.IsRDC)
    {y : P} (hinj : Set.InjOn f (Set.Iic y)) (hgr : ∀ x ≤ y, grade ℕ (f x) = grade ℕ x)
    {α : Bool} {xs : List P} (h : IsLayerOrder (P.boundary (.Iic y) 2 α) xs) :
    ∀ j ≤ xs.length, IsMoleculeIn Q (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) ∧
      (Q.boundary (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) 1 true : Set Q) =
        f '' P.boundary (orderPrefix (P.boundary (.Iic y) 2 α) xs j) 1 true
  | 0, _ => by
    refine ⟨?_, ?_⟩
    · rw [orderPrefix_zero]
      exact ((hQ (f y)).boundary 2 α).boundary 1 false
    · rw [orderPrefix_zero, orderPrefix_zero, boundary_boundary_of_le le_rfl true false,
        boundary_boundary_of_le le_rfl true false,
        (hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two),
        (hQ (f y)).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two),
        f.isMap_coe.image_boundary]
  | j + 1, hj => by
    obtain ⟨ih₁, ih₂⟩ := isMoleculeIn_and_boundary_orderPrefix_map f hP hQ hinj hgr h j (by omega)
    have hjl : j < xs.length := by omega
    have hxy : xs[j] ≤ y := boundary_le _ _ _ (h.mem (List.getElem_mem hjl))
    have hx2 : grade ℕ xs[j] = 2 := h.grade_eq _ (List.getElem_mem hjl)
    have hfx2 : grade ℕ (f xs[j]) = 2 := (hgr _ hxy).trans hx2
    have hM := (hP y).boundary 2 α
    have hp := h.isPastingAtIn hM hjl
    have hinf := Iic_inf_orderPrefix_map f hP hQ hinj h hjl
    have hsub : P.boundary (.Iic xs[j]) 1 false ≤
        P.boundary (orderPrefix (P.boundary (.Iic y) 2 α) xs j) 1 true :=
      (h.isSubmoleculeOf j hjl).le
    have hp' : Q.IsPastingAtIn 1 true (.Iic (f xs[j]))
        (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j)
        (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) (j + 1)) := by
      refine ⟨hQ (f xs[j]), ih₁, ?_, hinf, ?_⟩
      · rw [orderPrefix_succ (by simpa using hjl), List.getElem_map, sup_comm]
      · rw [hinf]
        exact isSubmoleculeOf_boundary_map f hQ h hjl hfx2 ih₁ ih₂
    refine ⟨hp'.isMoleculeIn, ?_⟩
    have hkS : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic xs[j]) := by
      rw [LowerSet.krullDim_Iic, hx2]
      exact_mod_cast one_le_two
    have hkS' : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic (f xs[j])) := by
      rw [LowerSet.krullDim_Iic, hfx2]
      exact_mod_cast one_le_two
    have hkT' : ((1 : ℕ) : WithBot ℕ∞) ≤
        krullDim (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) := by
      rw [Nat.cast_one, ← ((hQ (f xs[j])).krullDim_boundary hkS' false).trans
        Nat.cast_one]
      exact LowerSet.krullDim_mono (hinf ▸ inf_le_right)
    have hA : (P.boundary (orderPrefix (P.boundary (.Iic y) 2 α) xs j) 1 true : Set P) ⊆
        Set.Iic y := fun z hz =>
      boundary_le _ _ _ (h.orderPrefix_le j (boundary_le _ _ _ hz))
    have hI : P.interior (P.boundary (.Iic xs[j]) 1 false) ⊆ Set.Iic y := fun z hz =>
      (LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hz.1)).trans hxy
    rw [hp'.coe_boundary_eq hkS' hkT', hp.coe_boundary_eq hkS
      (h.one_le_krullDim_orderPrefix hM hjl), hp.inf_eq, hinf, Set.image_union,
      Bool.not_true, (hinj.mono hA).image_sdiff, hinj.image_inter hA hI,
      Set.sdiff_self_inter, ← ih₂,
      image_interior_boundary f hP hQ hinj hxy hx2 hfx2, f.isMap_coe.image_boundary]

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem IsLayerOrder.map_of_injOn [Finite Q] (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {y : P}
    (hinj : Set.InjOn f (Set.Iic y)) (hgr : ∀ x ≤ y, grade ℕ (f x) = grade ℕ x) {α : Bool}
    {xs : List P} (h : IsLayerOrder (P.boundary (.Iic y) 2 α) xs) :
    IsLayerOrder (Q.boundary (.Iic (f y)) 2 α) (xs.map f) where
  grade_eq x hx := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    rw [hgr z (boundary_le _ _ _ (h.mem hz)), h.grade_eq z hz]
  Iic_inf_orderPrefix j hj := by
    rw [List.getElem_map]
    exact Iic_inf_orderPrefix_map f hP hQ hinj h (by simpa using hj)
  isSubmoleculeOf j hj := by
    have hjl : j < xs.length := by simpa using hj
    have h' := isMoleculeIn_and_boundary_orderPrefix_map f hP hQ hinj hgr h j hjl.le
    rw [List.getElem_map]
    exact isSubmoleculeOf_boundary_map f hQ h hjl
      ((hgr _ (boundary_le _ _ _ (h.mem (List.getElem_mem hjl)))).trans
        (h.grade_eq _ (List.getElem_mem hjl))) h'.1 h'.2
  orderPrefix_length := by
    refine SetLike.coe_injective ?_
    rw [List.length_map, ← image_orderPrefix f hP hQ, h.orderPrefix_length,
      f.isMap_coe.image_boundary]

theorem mapPath_stagePath_map (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {y : P}
    (hinj : Set.InjOn f (Set.Iic y)) (hgr : ∀ x ≤ y, grade ℕ (f x) = grade ℕ x) {α : Bool}
    {xs : List P} (h : IsLayerOrder (P.boundary (.Iic y) 2 α) xs) {s t : P}
    (hs : P.boundary (P.boundary (.Iic y) 2 α) 0 false = .Iic s)
    (ht : P.boundary (P.boundary (.Iic y) 2 α) 0 true = .Iic t)
    (hs' : Q.boundary (Q.boundary (.Iic (f y)) 2 α) 0 false = .Iic (f s))
    (ht' : Q.boundary (Q.boundary (.Iic (f y)) 2 α) 0 true = .Iic (f t)) {j : ℕ}
    (hj : j ≤ xs.length) :
    f.mapPath (stagePath ((hP y).boundary 2 α) h hs ht j) =
      stagePath ((hQ (f y)).boundary 2 α) (h.map_of_injOn f hP hQ hinj hgr) hs' ht' j := by
  refine eq_stagePath_of_forall_mem _ _ _ _ _ fun e he => ?_
  obtain ⟨d, hd, rfl⟩ := f.exists_mem_pathEdges_of_mem_pathEdges_mapPath _ he
  rw [pathEdges_stagePath] at hd
  have he' := ((mem_edgeList_iff ((h.isMoleculeIn_orderPrefix ((hP y).boundary 2 α) j).boundary 1
    true) ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hd).1
  have : f d ∈ (Q.boundary (orderPrefix (Q.boundary (.Iic (f y)) 2 α) (xs.map f) j) 1 true :
      Set Q) := by
    rw [(isMoleculeIn_and_boundary_orderPrefix_map f hP hQ hinj hgr h j hj).2]
    exact Set.mem_image_of_mem f he'
  exact this

end LocalIso

end Atoms.Molecule.OGP
