import Atoms.ForMathlib.Data.Fin.SuccPred
import Atoms.Homotopical.Simplicial.Subdivision

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

namespace SdHorn

@[ext]
structure Subsets (n : ℕ) : Type u where
  val : Finset (Fin (n + 2))
  nonempty : val.Nonempty

instance (n : ℕ) : PartialOrder (Subsets.{u} n) :=
  PartialOrder.lift Subsets.val fun _ _ ↦ Subsets.ext

variable {n : ℕ} (k : Fin (n + 2))

def IsKIdx {m : ℕ} (g : Fin m → Subsets.{u} n) (J : ℕ) : Prop :=
  ∀ i : Fin m, k ∈ (g i).1 ↔ J ≤ i.val

def below {m : ℕ} (g : Fin m → Subsets.{u} n) (J : ℕ) : Finset (Fin (n + 2)) :=
  if h : 0 < J ∧ J - 1 < m then (g ⟨J - 1, h.2⟩).1 else ∅

variable {k}

theorem IsKIdx.unique {m : ℕ} {g : Fin m → Subsets.{u} n} {J J' : ℕ} (h : IsKIdx k g J)
    (h' : IsKIdx k g J') (hJ : J ≤ m) (hJ' : J' ≤ m) : J = J' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := (h' ⟨J, by omega⟩).1 ((h ⟨J, by omega⟩).2 le_rfl)
    simp at this
    omega
  · have := (h ⟨J', by omega⟩).1 ((h' ⟨J', by omega⟩).2 le_rfl)
    simp at this
    omega

theorem exists_isKIdx {m : ℕ} {g : Fin m → Subsets.{u} n} (hg : Monotone g) :
    ∃ J ≤ m, IsKIdx k g J := by
  classical
  by_cases h : ∃ J, ∃ hJ : J < m, k ∈ (g ⟨J, hJ⟩).1
  · refine ⟨Nat.find h, (Nat.find_spec h).1.le, fun i ↦
      ⟨fun hi ↦ Nat.find_min' h ⟨i.2, hi⟩, fun hi ↦ ?_⟩⟩
    obtain ⟨hJ, hk⟩ := Nat.find_spec h
    exact (hg (show (⟨Nat.find h, hJ⟩ : Fin m) ≤ i from hi)) hk
  · simp only [not_exists] at h
    exact ⟨m, le_rfl, fun i ↦ ⟨fun hi ↦ absurd hi (h i i.2), fun hi ↦ absurd hi (by omega)⟩⟩

theorem IsKIdx.notMem_below {m : ℕ} {g : Fin m → Subsets.{u} n} {J : ℕ} (h : IsKIdx k g J) :
    k ∉ below g J := by
  unfold below
  split_ifs with hJ
  · rw [h]
    simp only
    omega
  · simp

theorem le_below {m : ℕ} {g : Fin m → Subsets.{u} n} (hg : Monotone g) {J : ℕ} (hJ : J ≤ m)
    (i : Fin m) (hi : i.val < J) : (g i).1 ⊆ below g J := by
  unfold below
  rw [dif_pos ⟨by omega, by omega⟩]
  exact hg (show i ≤ ⟨J - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))

theorem below_le {m : ℕ} {g : Fin m → Subsets.{u} n} (hg : Monotone g) {J : ℕ} (i : Fin m)
    (hi : J ≤ i.val) : below g J ⊆ (g i).1 := by
  unfold below
  split_ifs with hJ
  · exact hg (show (⟨J - 1, hJ.2⟩ : Fin m) ≤ i from Fin.mk_le_mk.2 (by omega))
  · exact Finset.empty_subset _

theorem below_comp_succAbove {m : ℕ} (f : Fin (m + 1) → Subsets.{u} n) (j : Fin (m + 1)) {J : ℕ}
    (hJ : J ≤ j.val) : below (f ∘ j.succAbove) J = below f J := by
  unfold below
  by_cases h : 0 < J
  · rw [dif_pos ⟨h, by omega⟩, dif_pos ⟨h, by omega⟩]
    simp only [Function.comp_apply]
    rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simp; omega))]
    rfl
  · rw [dif_neg (by omega), dif_neg (by omega)]

theorem IsKIdx.comp_succAbove {m : ℕ} {f : Fin (m + 1) → Subsets.{u} n} {j : Fin (m + 1)}
    (h : IsKIdx k f j.val) : IsKIdx k (f ∘ j.succAbove) j.val := by
  intro i
  rw [Function.comp_apply, h, Fin.val_succAbove]
  split_ifs <;> omega

theorem IsKIdx.comp_succAbove_of_lt {m : ℕ} {f : Fin (m + 1) → Subsets.{u} n} {J : ℕ}
    (h : IsKIdx k f J) {i : Fin (m + 1)} (hi : i.val < J) :
    IsKIdx k (f ∘ i.succAbove) (J - 1) := by
  intro i'
  rw [Function.comp_apply, h, Fin.val_succAbove]
  split_ifs <;> omega

theorem IsKIdx.comp_succAbove_of_gt {m : ℕ} {f : Fin (m + 1) → Subsets.{u} n} {J : ℕ}
    (h : IsKIdx k f J) {i : Fin (m + 1)} (hi : J < i.val) :
    IsKIdx k (f ∘ i.succAbove) J := by
  intro i'
  rw [Function.comp_apply, h, Fin.val_succAbove]
  split_ifs <;> omega

variable (k) in
def fill {m : ℕ} (g : Fin (m + 1) → Subsets.{u} n) (j : Fin (m + 2)) :
    Fin (m + 2) → Subsets.{u} n :=
  Fin.insertNth (α := fun _ ↦ Subsets.{u} n) j
    ⟨insert k (below g j.val), Finset.insert_nonempty _ _⟩ g

@[simp]
theorem fill_comp_succAbove {m : ℕ} (g : Fin (m + 1) → Subsets.{u} n) (j : Fin (m + 2)) :
    fill k g j ∘ j.succAbove = g :=
  Fin.insertNth_comp_succAbove _ _ _

@[simp]
theorem fill_apply_self {m : ℕ} (g : Fin (m + 1) → Subsets.{u} n) (j : Fin (m + 2)) :
    (fill k g j j).1 = insert k (below g j.val) := by
  simp [fill]

variable (k n) in
structure TypeI where
  d : ℕ
  f : Fin (d + 2) → Subsets.{u} n
  strictMono : StrictMono f
  notMem : ∃ i, insert k (f i).1 = Finset.univ
  j : Fin (d + 2)
  isKIdx : IsKIdx k f j.val
  eq_insert : (f j).1 = insert k (below f j.val)

theorem TypeI.f_eq (s : TypeI.{u} n k) : s.f = fill k (s.f ∘ s.j.succAbove) s.j := by
  symm
  rw [fill, Fin.insertNth_eq_iff]
  refine ⟨Subsets.ext ?_, rfl⟩
  change insert k (below (s.f ∘ s.j.succAbove) s.j.val) = (s.f s.j).1
  rw [s.eq_insert, below_comp_succAbove _ _ le_rfl]

theorem TypeI.not_isTypeI_face (s : TypeI.{u} n k) (J : ℕ) (hJ : IsKIdx k (s.f ∘ s.j.succAbove) J)
    (hJd : J < s.d + 1)
    (h : ((s.f ∘ s.j.succAbove) ⟨J, hJd⟩).1 = insert k (below (s.f ∘ s.j.succAbove) J)) :
    False := by
  obtain rfl : J = s.j.val := hJ.unique s.isKIdx.comp_succAbove (by omega) (by omega)
  rw [below_comp_succAbove _ _ le_rfl, ← s.eq_insert, Function.comp_apply,
    Fin.succAbove_of_le_castSucc _ _ (by simp)] at h
  have := s.strictMono (show s.j < (⟨s.j.val, hJd⟩ : Fin (s.d + 1)).succ from
    Fin.lt_def.2 (by simp))
  exact (ne_of_lt this) (Subsets.ext h.symm)

def TypeI.ofFill {e : ℕ} (c : Fin (e + 1) → Subsets.{u} n) (hc : StrictMono c)
    (hA : ∃ i, insert k (c i).1 = Finset.univ) (J : ℕ) (hJe : J ≤ e + 1) (hJ : IsKIdx k c J)
    (hI : ¬ ∃ h : J < e + 1, (c ⟨J, h⟩).1 = insert k (below c J)) : TypeI.{u} n k where
  d := e
  f := fill k c ⟨J, by omega⟩
  strictMono := by
    refine (Fin.strictMono_insertNth_iff _ _ _).2 ⟨hc, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [Fin.lt_def] at hi
      change (c i).1 ⊂ insert k (below c J)
      exact lt_of_le_of_lt (le_below hc.monotone hJe i hi)
        (Finset.ssubset_insert hJ.notMem_below)
    · rw [Fin.le_def] at hi
      change insert k (below c J) ⊂ (c i).1
      have hsub : insert k (below c J) ⊆ (c i).1 :=
        Finset.insert_subset ((hJ i).2 hi) (below_le hc.monotone i hi)
      rcases (show J ≤ i.val from hi).lt_or_eq with hlt | heq
      · have h₁ : insert k (below c J) ⊆ (c ⟨J, by omega⟩).1 :=
          Finset.insert_subset ((hJ _).2 le_rfl) (below_le hc.monotone _ le_rfl)
        exact lt_of_le_of_lt h₁ (hc (Fin.mk_lt_mk.2 hlt))
      · refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h ↦ hI ⟨by omega, ?_⟩⟩
        have hi' : (⟨J, by omega⟩ : Fin (e + 1)) = i := Fin.ext heq
        rw [hi']
        exact h.symm
  notMem := by
    obtain ⟨i, hi⟩ := hA
    refine ⟨Fin.succAbove ⟨J, by omega⟩ i, ?_⟩
    rw [fill, Fin.insertNth_apply_succAbove]
    exact hi
  j := ⟨J, by omega⟩
  isKIdx := by
    intro i
    obtain hi | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove ⟨J, by omega⟩ i
    · rw [hi, fill_apply_self]
      simp
    · rw [fill, Fin.insertNth_apply_succAbove, hJ, Fin.val_succAbove]
      dsimp only
      split_ifs with h <;> omega
  eq_insert := by
    rw [fill_apply_self, ← below_comp_succAbove _ _ le_rfl, fill_comp_succAbove]

theorem TypeI.ofFill_f_comp {e : ℕ} (c : Fin (e + 1) → Subsets.{u} n) (hc : StrictMono c)
    (hA : ∃ i, insert k (c i).1 = Finset.univ) (J : ℕ) (hJe : J ≤ e + 1) (hJ : IsKIdx k c J)
    (hI : ¬ ∃ h : J < e + 1, (c ⟨J, h⟩).1 = insert k (below c J)) :
    (TypeI.ofFill c hc hA J hJe hJ hI).f ∘ (TypeI.ofFill c hc hA J hJe hJ hI).j.succAbove = c :=
  fill_comp_succAbove _ _

def mkChain {P : Type u} [PartialOrder P] {m : ℕ} (f : Fin (m + 1) → P) (hf : Monotone f) :
    (nerve P) _⦋m⦌ :=
  hf.functor

theorem δ_mkChain {P : Type u} [PartialOrder P] {m : ℕ} (f : Fin (m + 2) → P) (hf : Monotone f)
    (j : Fin (m + 2)) :
    (nerve P).δ j (mkChain f hf) =
      mkChain (f ∘ j.succAbove) (hf.comp (Fin.strictMono_succAbove j).monotone) :=
  nerve.ext_of_isThin (funext fun _ ↦ rfl)

theorem mkChain_obj {P : Type u} [PartialOrder P] {m : ℕ} (c : (nerve P) _⦋m⦌) :
    mkChain c.obj (fun _ _ h ↦ (c.map (homOfLE h)).le) = c :=
  nerve.ext_of_isThin (funext fun _ ↦ rfl)

theorem mkChain_injective {P : Type u} [PartialOrder P] {m : ℕ} {f f' : Fin (m + 1) → P}
    {hf : Monotone f} {hf' : Monotone f'} (h : mkChain f hf = mkChain f' hf') : f = f' :=
  funext fun i ↦ congrArg (fun c : (nerve P) _⦋m⦌ ↦ c.obj i) h

theorem TypeI.notMem_face (s : TypeI.{u} n k) :
    ∃ i, insert k ((s.f ∘ s.j.succAbove) i).1 = Finset.univ := by
  obtain ⟨i₀, hi₀⟩ := s.notMem
  obtain hi | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove s.j i₀
  · rw [hi, s.eq_insert, Finset.insert_idem] at hi₀
    unfold below at hi₀
    have hj2 := s.j.isLt
    split_ifs at hi₀ with h
    · refine ⟨⟨s.j.val - 1, by omega⟩, ?_⟩
      rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by
        simp only [Fin.val_castSucc]
        omega))]
      exact hi₀
    · exact absurd hi₀ (by rw [insert_empty_eq]; exact Finset.singleton_ne_univ k)
  · exact ⟨i, hi₀⟩

variable (k) in
def hornChains : (nerve (Subsets.{u} n)).Subcomplex where
  obj _ := {c | ∀ i, insert k (c.obj i).1 ≠ Finset.univ}
  map _ := by
    intro c hc i
    exact hc _

variable (k) in
def pairingCore : (hornChains k).PairingCore where
  ι := TypeI.{u} n k
  dim s := s.d
  simplex s := mkChain s.f s.strictMono.monotone
  index s := s.j
  nonDegenerate₁ s := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 s.strictMono
  nonDegenerate₂ s := by
    rw [δ_mkChain, PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
    exact s.strictMono.comp (Fin.strictMono_succAbove _)
  notMem₁ s h := by
    obtain ⟨i, hi⟩ := s.notMem
    exact h i hi
  notMem₂ s h := by
    rw [δ_mkChain] at h
    obtain ⟨i, hi⟩ := s.notMem_face
    exact h i hi
  injective_type₁' {s t} h := by
    obtain ⟨d, f, hf, hA, j, hj, he⟩ := s
    obtain ⟨d', f', hf', hA', j', hj', he'⟩ := t
    obtain rfl : d = d' := by simpa using SSet.S.dim_eq_of_mk_eq h
    obtain rfl : f = f' := mkChain_injective ((SSet.S.ext_iff _ _).1 h)
    obtain rfl : j = j' := Fin.ext (hj.unique hj' (by omega) (by omega))
    rfl
  injective_type₂' {s t} h := by
    obtain ⟨d, f, hf, hA, j, hj, he⟩ := s
    obtain ⟨d', f', hf', hA', j', hj', he'⟩ := t
    obtain rfl : d = d' := SSet.S.dim_eq_of_mk_eq h
    have h' := (SSet.S.ext_iff _ _).1 h
    rw [δ_mkChain, δ_mkChain] at h'
    have hff := mkChain_injective h'
    have hjj : j = j' := Fin.ext (hj.comp_succAbove.unique (hff ▸ hj'.comp_succAbove)
      (by omega) (by omega))
    subst hjj
    have hff' : f ∘ j.succAbove = f' ∘ j.succAbove := hff
    obtain rfl : f = f' := calc
      f = fill k (f ∘ j.succAbove) j := TypeI.f_eq ⟨d, f, hf, hA, j, hj, he⟩
      _ = fill k (f' ∘ j.succAbove) j := by rw [hff']
      _ = f' := (TypeI.f_eq ⟨d, f', hf', hA', j, hj', he'⟩).symm
    rfl
  type₁_ne_type₂' s t h := by
    obtain ⟨dt, ft, hft, hAt, jt, hjt, het⟩ := t
    obtain rfl : dt = s.d + 1 := (SSet.S.dim_eq_of_mk_eq h).symm
    have h' := (SSet.S.ext_iff _ _).1 h
    rw [δ_mkChain] at h'
    have hff := mkChain_injective h'
    refine TypeI.not_isTypeI_face ⟨s.d + 1, ft, hft, hAt, jt, hjt, het⟩ s.j.val
      (hff ▸ s.isKIdx) s.j.2 ?_
    have := s.eq_insert
    rw [hff] at this
    exact this
  surjective' x := by
    obtain ⟨e, c, hnd, hnA, rfl⟩ := SSet.Subcomplex.N.mk_surjective x
    have hc := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono c).1 hnd
    have hA : ∃ i, insert k (c.obj i).1 = Finset.univ := by
      by_contra h
      exact hnA (fun i hi ↦ h ⟨i, hi⟩)
    obtain ⟨J, hJe, hJ⟩ := exists_isKIdx (k := k) hc.monotone
    by_cases hI : ∃ h : J < e + 1, (c.obj ⟨J, h⟩).1 = insert k (below c.obj J)
    · obtain ⟨hJ', heq⟩ := hI
      cases e with
      | zero =>
        exfalso
        obtain rfl : J = 0 := by omega
        obtain ⟨i, hi⟩ := hA
        have hi0 : i = ⟨0, hJ'⟩ := Fin.ext (by
          have := i.isLt
          simp only [Opposite.unop_op, SimplexCategory.len_mk] at this
          simp only
          omega)
        rw [hi0, heq, below, dif_neg (by omega), insert_empty_eq,
          Finset.insert_eq_of_mem (Finset.mem_singleton_self k)] at hi
        exact Finset.singleton_ne_univ k hi
      | succ d =>
        refine ⟨⟨d, c.obj, hc, hA, ⟨J, hJ'⟩, hJ, heq⟩, Or.inl ?_⟩
        change SSet.S.mk c = SSet.S.mk (mkChain c.obj _)
        rw [mkChain_obj]
    · refine ⟨TypeI.ofFill c.obj hc hA J hJe hJ hI, Or.inr ?_⟩
      change SSet.S.mk c = SSet.S.mk ((nerve _).δ _ (mkChain _ _))
      rw [δ_mkChain]
      congr 1
      exact (nerve.ext_of_isThin (TypeI.ofFill_f_comp c.obj hc hA J hJe hJ hI)).symm

variable (k) in
def weakRankFunction : (pairingCore k).WeakRankFunction ℕ where
  rank s := s.j.val
  lt {s t} hst hd := by
    obtain ⟨hne, hlt⟩ := hst
    have hle := hlt.le
    rw [SSet.Subcomplex.N.le_iff, SSet.N.le_iff_exists_mono] at hle
    obtain ⟨g, hg, hδ⟩ := hle
    obtain ⟨d, fs, hfs, hAs, js, hjs, hes⟩ := s
    obtain ⟨d', ft, hft, hAt, jt, hjt, het⟩ := t
    obtain rfl : d = d' := hd
    obtain ⟨i, rfl⟩ := @SimplexCategory.eq_δ_of_mono d g hg
    change (nerve (Subsets.{u} n)).δ i (mkChain ft hft.monotone) =
      (nerve (Subsets.{u} n)).δ js (mkChain fs hfs.monotone) at hδ
    rw [δ_mkChain, δ_mkChain] at hδ
    have hfun := mkChain_injective hδ
    change js.val < jt.val
    rcases lt_trichotomy i.val jt.val with hi | hi | hi
    · have h₁ := hjt.comp_succAbove_of_lt hi
      rw [hfun] at h₁
      have := hjs.comp_succAbove.unique h₁ (by omega) (by omega)
      omega
    · obtain rfl : i = jt := Fin.ext hi
      refine (hne ((pairingCore k).injective_type₂' ?_)).elim
      change SSet.S.mk ((nerve (Subsets.{u} n)).δ js (mkChain fs hfs.monotone)) =
        SSet.S.mk ((nerve (Subsets.{u} n)).δ i (mkChain ft hft.monotone))
      rw [δ_mkChain, δ_mkChain]
      congr 1
      exact nerve.ext_of_isThin (funext fun a ↦ (congrFun hfun a).symm)
    · exfalso
      have hjd : jt.val < d + 1 := by omega
      refine TypeI.not_isTypeI_face ⟨d, fs, hfs, hAs, js, hjs, hes⟩ jt.val
        (hfun ▸ hjt.comp_succAbove_of_gt hi) hjd ?_
      change ((fs ∘ js.succAbove) ⟨jt.val, hjd⟩).1 = insert k (below (fs ∘ js.succAbove) jt.val)
      rw [← hfun, below_comp_succAbove _ _ hi.le, Function.comp_apply,
        Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simpa using hi))]
      exact het

instance : (pairingCore k).IsRegular :=
  (weakRankFunction k).isRegular

theorem insert_simplexVertices_ne_univ_iff {d : ℕ} (x : (Δ[n + 1] : SSet.{u}) _⦋d⦌) :
    insert k (simplexVertices x) ≠ Finset.univ ↔ x ∈ (SSet.horn.{u} (n + 1) k).obj _ := by
  rw [SSet.mem_horn_iff_notMem_range, Ne, Finset.eq_univ_iff_forall]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := not_forall.1 h
    rw [Finset.mem_insert, not_or] at hj
    exact ⟨j, hj.1, fun ⟨i, hi⟩ ↦ hj.2 ((mem_simplexVertices x j).2 ⟨i, hi⟩)⟩
  · rintro ⟨j, hjk, hj⟩ hall
    rcases Finset.mem_insert.1 (hall j) with h | h
    · exact hjk h
    · obtain ⟨i, hi⟩ := (mem_simplexVertices x j).1 h
      exact hj ⟨i, hi⟩

variable (n) in
noncomputable def stdSimplexSubsetsIso : (Δ[n + 1] : SSet.{u}).N ≃o Subsets.{u} n :=
  (stdSimplexNOrderIso (n + 1)).trans
    { toFun S := ⟨S.1, S.2⟩
      invFun S := ⟨S.1, S.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }

variable (k) in
noncomputable def hornEmbedding :
    (SSet.horn.{u} (n + 1) k : SSet.{u}).N ↪o Subsets.{u} n :=
  (nMapEmbedding (SSet.horn.{u} (n + 1) k).ι).trans (stdSimplexSubsetsIso n).toOrderEmbedding

theorem range_nerveMap_hornEmbedding :
    SSet.Subcomplex.range (nerveMap (hornEmbedding.{u} k).toOrderHom.monotone.functor) =
      hornChains k := by
  ext d c
  change c ∈ Set.range _ ↔ ∀ i, insert k (c.obj i).1 ≠ Finset.univ
  constructor
  · rintro ⟨c₀, rfl⟩ i
    change insert k (simplexVertices
      (nMap (SSet.horn.{u} (n + 1) k).ι (c₀.obj i)).simplex) ≠ _
    rw [nMap_of_mono]
    exact (insert_simplexVertices_ne_univ_iff _).2 (c₀.obj i).simplex.2
  · intro hc
    obtain ⟨c', hc'⟩ := exists_nerveMap_app_eq (hornEmbedding k) c (fun i ↦ by
      obtain ⟨y, hy⟩ := (stdSimplexSubsetsIso n).surjective (c.obj i)
      have hmem := (insert_simplexVertices_ne_univ_iff y.simplex).1 (by
        have := hc i
        rw [← hy] at this
        exact this)
      refine ⟨SSet.N.mk (⟨y.simplex, hmem⟩ : (SSet.horn.{u} (n + 1) k : SSet.{u}) _⦋y.dim⦌)
        ((SSet.nonDegenerate_iff_of_mono (SSet.horn.{u} (n + 1) k).ι _).1 y.nonDegenerate), ?_⟩
      rw [← hy]
      change stdSimplexSubsetsIso n (nMap _ _) = _
      rw [nMap_of_mono]
      rfl)
    exact ⟨c', hc'⟩

theorem strongAnodyneExtensions_nerveMap_hornEmbedding :
    SSet.strongAnodyneExtensions (nerveMap (hornEmbedding.{u} k).toOrderHom.monotone.functor) := by
  refine ⟨mono_nerveMap_of_injective _ (hornEmbedding k).injective, ?_⟩
  rw [range_nerveMap_hornEmbedding]
  exact ⟨(pairingCore k).pairing, inferInstance⟩

theorem sd_map_horn_ι_comp :
    SSet.sd.map (SSet.horn.{u} (n + 1) k).ι ≫ (sdIsoNerveN Δ[n + 1]).hom ≫
        nerveMap (stdSimplexSubsetsIso n).monotone.functor =
      (sdIsoNerveN _).hom ≫ nerveMap (hornEmbedding k).toOrderHom.monotone.functor := by
  rw [← Category.assoc, sd_map_sdIsoNerveN_hom, Category.assoc]
  rfl

end SdHorn

open SdHorn in
theorem strongAnodyneExtensions_sd_map_horn_ι (n : ℕ) (k : Fin (n + 2)) :
    SSet.strongAnodyneExtensions (SSet.sd.map (SSet.horn.{u} (n + 1) k).ι) := by
  refine (MorphismProperty.cancel_right_of_respectsIso SSet.strongAnodyneExtensions _
    ((sdIsoNerveN Δ[n + 1]).hom ≫ nerveMap (stdSimplexSubsetsIso.{u} n).monotone.functor)).1 ?_
  rw [sd_map_horn_ι_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
    strongAnodyneExtensions_nerveMap_hornEmbedding

theorem J_rlp_ex_map {X Y : SSet.{u}} {p : X ⟶ Y} (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp (SSet.ex.map p) := by
  intro A B j hj
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  rw [← SSet.sdExAdjunction.hasLiftingProperty_iff]
  have := SSet.strongAnodyneExtensions_le_anodyneExtensions _
    (strongAnodyneExtensions_sd_map_horn_ι n k)
  rw [SSet.anodyneExtensions_eq_llp_rlp] at this
  exact this _ hp

theorem anodyneExtensions_sd_map {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.anodyneExtensions f) : SSet.anodyneExtensions (SSet.sd.map f) := by
  rw [SSet.anodyneExtensions_eq_llp_rlp] at hf ⊢
  intro A B p hp
  rw [SSet.sdExAdjunction.hasLiftingProperty_iff]
  exact hf _ (J_rlp_ex_map hp)

end Atoms.Homotopical
