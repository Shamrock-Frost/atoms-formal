import Atoms.ForMathlib.Data.Fintype.Basic
import Atoms.ForMathlib.Order
import Atoms.Molecule.Cartesian
import Atoms.Molecule.Molecule
import Mathlib.Data.ENat.Basic

universe u v

open Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} [Fintype P] [DecidableEq P] [DecidableLE P]

instance decidableMemFaces (α : Bool) (x : P) : DecidablePred (· ∈ P.faces α x) := fun y =>
  inferInstanceAs (Decidable (∃ h : y ⋖ x, P.orient h = α))

instance decidableMemCofaces (α : Bool) (x : P) : DecidablePred (· ∈ P.cofaces α x) := fun y =>
  inferInstanceAs (Decidable (∃ h : x ⋖ y, P.orient h = α))

instance decidableMemBoundary (U : LowerSet P) [DecidablePred (· ∈ U)] (n : ℕ) (α : Bool) :
    DecidablePred (· ∈ P.boundary U n α) := fun x =>
  decidable_of_iff (∃ z, ((z ∈ U ∧ grade ℕ z = n ∧ ∀ c, c ∈ P.cofaces (!α) z → c ∉ U) ∨
      (Maximal (· ∈ U) z ∧ grade ℕ z < n)) ∧ x ≤ z)
    (mem_boundary.trans (by simp [facesIn, Set.disjoint_left])).symm

instance decidableMemBoundaryFull (U : LowerSet P) [DecidablePred (· ∈ U)] (n : ℕ) :
    DecidablePred (· ∈ P.boundaryFull U n) := fun x =>
  inferInstanceAs (Decidable (x ∈ P.boundary U n false ⊔ P.boundary U n true))

def gradeBound (P : OGP.{u}) [Fintype P] : ℕ := Finset.univ.sup fun x : P => grade ℕ x

omit [DecidableEq P] [DecidableLE P] in
theorem krullDim_le_gradeBound (U : LowerSet P) : krullDim U ≤ P.gradeBound :=
  krullDim_le_coe_iff.2 fun x => Finset.le_sup (f := fun x : P => grade ℕ x) (Finset.mem_univ x.1)

omit [DecidableEq P] [DecidableLE P] in
theorem lt_gradeBound_of_krullDim_eq {U : LowerSet P} {n : ℕ} (h : krullDim U = n + 1) :
    n < P.gradeBound :=
  Nat.lt_of_succ_le (by exact_mod_cast h ▸ krullDim_le_gradeBound U)

instance decidableMemBdry (U : LowerSet P) [DecidablePred (· ∈ U)] (α : Bool) :
    DecidablePred (· ∈ P.bdry U α) := fun x =>
  decidable_of_iff (∃ n < P.gradeBound, krullDim U = ((n + 1 : ℕ) : WithBot ℕ∞) ∧
      x ∈ P.boundary U n α) (by
    simp only [bdry, LowerSet.mem_iSup₂_iff, Nat.cast_add, Nat.cast_one]
    exact ⟨fun ⟨n, _, h, hx⟩ => ⟨n, h, hx⟩, fun ⟨n, h, hx⟩ =>
      ⟨n, lt_gradeBound_of_krullDim_eq h, h, hx⟩⟩)

instance decidableMemBdryFull (U : LowerSet P) [DecidablePred (· ∈ U)] :
    DecidablePred (· ∈ P.bdryFull U) := fun x =>
  inferInstanceAs (Decidable (x ∈ P.bdry U false ⊔ P.bdry U true))

omit [DecidableEq P] [DecidableLE P] in
theorem isGlobular_iff_forall_lt_gradeBound {U : LowerSet P} : P.IsGlobular U ↔
    ∀ n < P.gradeBound + 1, ∀ k < n, ∀ α β : Bool,
      P.boundary (P.boundary U n β) k α = P.boundary U k α := by
  refine ⟨fun h n _ k hk α β => h k n hk α β, fun h k n hk α β => ?_⟩
  by_cases hn : n < P.gradeBound + 1
  · exact h n hn k hk α β
  · rw [boundary_eq_self ((krullDim_le_gradeBound U).trans (by exact_mod_cast (by omega)))]

instance decidableIsGlobular (U : LowerSet P) [DecidablePred (· ∈ U)] :
    Decidable (P.IsGlobular U) :=
  decidable_of_iff _ isGlobular_iff_forall_lt_gradeBound.symm

instance decidableIsRound (U : LowerSet P) [DecidablePred (· ∈ U)] : Decidable (P.IsRound U) :=
  haveI : ∀ n : ℕ, Decidable (((n + 1 : ℕ) : WithBot ℕ∞) < krullDim U →
      P.boundary U (n + 1) false ⊓ P.boundary U (n + 1) true = P.boundaryFull U n) :=
    fun _ => inferInstance
  decidable_of_iff (P.IsGlobular U ∧
      (0 < krullDim U → P.boundary U 0 false ⊓ P.boundary U 0 true = ⊥) ∧
      ∀ n < P.gradeBound, ((n + 1 : ℕ) : WithBot ℕ∞) < krullDim U →
        P.boundary U (n + 1) false ⊓ P.boundary U (n + 1) true = P.boundaryFull U n) (by
    refine ⟨fun ⟨hg, h₀, hs⟩ => ⟨hg, h₀, fun n hn => hs n ?_ hn⟩,
      fun h => ⟨h.isGlobular, h.inf_boundary_zero, fun n _ hn => h.inf_boundary_succ n hn⟩⟩
    have h' := hn.trans_le (krullDim_le_gradeBound U)
    have : n + 1 < P.gradeBound := by exact_mod_cast h'
    omega)

instance decidableIsPastingIn (k : ℕ) (V W U : LowerSet P) [DecidablePred (· ∈ V)]
    [DecidablePred (· ∈ W)] [DecidablePred (· ∈ U)] : Decidable (P.IsPastingIn k V W U) :=
  decidable_of_iff (V ⊔ W = U ∧ V ⊓ W = P.boundary V k true ∧ V ⊓ W = P.boundary W k false)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun h => ⟨h.sup_eq, h.inf_eq_output, h.inf_eq_input⟩⟩

omit [DecidableEq P] [DecidableLE P] in
theorem isLowerSet_filter_mem (U : LowerSet P) [DecidablePred (· ∈ U)] :
    IsLowerSet ((Finset.univ.filter (· ∈ U) : Finset P) : Set P) := by
  simp [U.lower]

omit [DecidableEq P] [DecidableLE P] in
theorem mk_filter_mem (U : LowerSet P) [DecidablePred (· ∈ U)] :
    (⟨_, isLowerSet_filter_mem U⟩ : LowerSet P) = U :=
  SetLike.ext fun _ => by simp

omit [DecidableEq P] [DecidableLE P] in
theorem filter_mem_ssubset {s : Finset P} {hs : IsLowerSet (s : Set P)} {V : LowerSet P}
    [DecidablePred (· ∈ V)] (h : V < ⟨s, hs⟩) : Finset.univ.filter (· ∈ V) ⊂ s := by
  refine Finset.coe_ssubset.1 ?_
  rw [← LowerSet.coe_ssubset_coe] at h
  simpa using h

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
theorem mk_eq_Iic {s : Finset P} {hs : IsLowerSet (s : Set P)} {t : P}
    (ht : ∀ y, y ∈ s ↔ y ≤ t) : (⟨s, hs⟩ : LowerSet P) = LowerSet.Iic t :=
  SetLike.ext fun y => (ht y).trans LowerSet.mem_Iic_iff.symm

variable (P) in
def finsetTopsAbove (s : Finset P) (k : ℕ) : Finset P :=
  s.filter fun x => Maximal (· ∈ s) x ∧ k < grade ℕ x

variable (P) in
def pastingPart (s : Finset P) (hs : IsLowerSet (s : Set P)) (k : ℕ) (S : Finset P)
    (α : Bool) : LowerSet P :=
  lowerClosure (S : Set P) ⊔ P.boundary ⟨s, hs⟩ k α

instance decidableMemPastingPart (s : Finset P) (hs : IsLowerSet (s : Set P)) (k : ℕ)
    (S : Finset P) (α : Bool) : DecidablePred (· ∈ P.pastingPart s hs k S α) := fun x =>
  inferInstanceAs (Decidable (x ∈ lowerClosure (S : Set P) ⊔ P.boundary ⟨s, hs⟩ k α))

variable (P) in
def moleculeTest (s : Finset P) (hs : IsLowerSet (s : Set P)) : Bool :=
  decide (∃ x ∈ s, grade ℕ x = 0 ∧ ∀ y, y ∈ s ↔ y ≤ x) ||
  (if h : (∃ t ∈ s, ∀ y, y ∈ s ↔ y ≤ t) ∧ P.IsRound ⟨s, hs⟩ then
    have hlt (α : Bool) : P.bdry ⟨s, hs⟩ α < ⟨s, hs⟩ := by
      obtain ⟨t, -, ht⟩ := h.1
      rw [mk_eq_Iic ht]
      exact bdry_Iic_lt t α
    have := Finset.card_lt_card (filter_mem_ssubset (hlt false))
    have := Finset.card_lt_card (filter_mem_ssubset (hlt true))
    moleculeTest (Finset.univ.filter (· ∈ P.bdry ⟨s, hs⟩ false)) (isLowerSet_filter_mem _) &&
      moleculeTest (Finset.univ.filter (· ∈ P.bdry ⟨s, hs⟩ true)) (isLowerSet_filter_mem _)
  else false) ||
  decide (∃ k < P.gradeBound, ∃ S ∈ (P.finsetTopsAbove s k).powerset,
    (if h : P.IsPastingIn k (P.pastingPart s hs k S false)
        (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) ⟨s, hs⟩ ∧
      (k : WithBot ℕ∞) < krullDim (P.pastingPart s hs k S false) ∧
      (k : WithBot ℕ∞) < krullDim (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) then
      have := Finset.card_lt_card (filter_mem_ssubset
        (h.1.lt_cond false h.2.2 : P.pastingPart s hs k S false < _))
      have := Finset.card_lt_card (filter_mem_ssubset
        (h.1.lt_cond true h.2.1 : P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true < _))
      moleculeTest (Finset.univ.filter (· ∈ P.pastingPart s hs k S false))
          (isLowerSet_filter_mem _) &&
        moleculeTest (Finset.univ.filter
          (· ∈ P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true))
          (isLowerSet_filter_mem _)
    else false) = true)
termination_by s.card

theorem isMoleculeIn_of_moleculeTest (s : Finset P) (hs : IsLowerSet (s : Set P))
    (h : P.moleculeTest s hs = true) : IsMoleculeIn P ⟨s, hs⟩ := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rw [moleculeTest] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.dite_else_false, Bool.and_eq_true] at h
  rcases h with (⟨x, hx, h0, hmem⟩ | ⟨⟨⟨t, -, ht⟩, hr⟩, h⟩) | ⟨k, -, S, -, hp, h⟩
  · rw [mk_eq_Iic hmem]
    exact .point x (isMin_grade_iff.1 (isMin_iff_eq_bot.2 h0))
  · have hU := mk_eq_Iic (hs := hs) ht
    have hb (α : Bool) : IsMoleculeIn P (P.bdry ⟨s, hs⟩ α) := by
      have hlt : P.bdry ⟨s, hs⟩ α < ⟨s, hs⟩ := hU ▸ bdry_Iic_lt t α
      have hα := ih _ (filter_mem_ssubset hlt) (isLowerSet_filter_mem _)
      rw [mk_filter_mem] at hα
      cases α
      · exact hα h.1
      · exact hα h.2
    rw [hU] at hr hb ⊢
    exact .atom t hr hb
  · have hV := ih _ (filter_mem_ssubset
      (hp.1.lt_cond false hp.2.2 : P.pastingPart s hs k S false < _)) _ h.1
    have hW := ih _ (filter_mem_ssubset
      (hp.1.lt_cond true hp.2.1 : P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true < _)) _ h.2
    rw [mk_filter_mem] at hV hW
    exact .paste k _ _ _ hp.1 hV hW (lt_min hp.2.1 hp.2.2)

theorem IsPastingIn.pastingPart_filter_cond (α : Bool) {k : ℕ} {A B : LowerSet P} {s : Finset P}
    {hs : IsLowerSet (s : Set P)} [DecidablePred (· ∈ B)]
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) ⟨s, hs⟩) :
    P.pastingPart s hs k ((P.finsetTopsAbove s k).filter (· ∈ B)) α = B := by
  refine Eq.trans ?_ (hp.eq_cond α (krullDim_le_gradeBound _)).symm
  rw [pastingPart]
  congr 2
  ext x
  simp only [finsetTopsAbove, Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq]
  exact ⟨fun ⟨⟨_, hx, hk⟩, hB⟩ => ⟨hx, hk, hB⟩, fun ⟨hx, hk, hB⟩ => ⟨⟨hx.prop, hx, hk⟩, hB⟩⟩

theorem IsPastingIn.pastingPart_sdiff_filter {k : ℕ} {V W : LowerSet P} {s : Finset P}
    {hs : IsLowerSet (s : Set P)} [DecidablePred (· ∈ V)] (hp : P.IsPastingIn k V W ⟨s, hs⟩) :
    P.pastingPart s hs k
      (P.finsetTopsAbove s k \ (P.finsetTopsAbove s k).filter (· ∈ V)) true = W := by
  classical
  rw [← hp.pastingPart_filter_cond true]
  congr 1
  ext x
  simp only [finsetTopsAbove, Finset.mem_sdiff, Finset.mem_filter, not_and]
  exact ⟨fun ⟨hx, hV⟩ => ⟨hx, (hp.mem_right_iff_notMem_left hx.1 hx.2.2).2 (hV hx)⟩,
    fun ⟨hx, hW⟩ => ⟨hx, fun _ => (hp.mem_right_iff_notMem_left hx.1 hx.2.2).1 hW⟩⟩

theorem moleculeTest_of_isMoleculeIn {U : LowerSet P} (h : IsMoleculeIn P U) (s : Finset P)
    (hs : IsLowerSet (s : Set P)) (hsU : (⟨s, hs⟩ : LowerSet P) = U) :
    P.moleculeTest s hs = true := by
  induction h generalizing s with
  | point x hx =>
    rw [moleculeTest]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have hmem (y : P) : y ∈ s ↔ y ≤ x :=
      (SetLike.ext_iff.1 hsU y).trans LowerSet.mem_Iic_iff
    exact Or.inl (Or.inl ⟨x, (hmem x).2 le_rfl, isMin_iff_eq_bot.1 (hx.grade ℕ), hmem⟩)
  | atom t hround _ ih =>
    have hmem (y : P) : y ∈ s ↔ y ≤ t := (SetLike.ext_iff.1 hsU y).trans LowerSet.mem_Iic_iff
    have hr : P.IsRound ⟨s, hs⟩ := hsU ▸ hround
    rw [moleculeTest]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    refine Or.inl (Or.inr ?_)
    rw [dif_pos ⟨⟨t, (hmem t).2 le_rfl, hmem⟩, hr⟩, Bool.and_eq_true]
    exact ⟨ih false _ _ (by rw [mk_filter_mem, hsU]), ih true _ _ (by rw [mk_filter_mem, hsU])⟩
  | paste k V W U hp hV hW hk ihV ihW =>
    subst hsU
    classical
    have hkV : (k : WithBot ℕ∞) < krullDim V := (lt_min_iff.1 hk).1
    have hkW : (k : WithBot ℕ∞) < krullDim W := (lt_min_iff.1 hk).2
    have hkb : k < P.gradeBound := by
      exact_mod_cast (hkV.trans_le (LowerSet.krullDim_mono hp.left_le)).trans_le
        (krullDim_le_gradeBound _)
    have hVeq := hp.pastingPart_filter_cond false (s := s) (hs := hs)
    have hWeq := hp.pastingPart_sdiff_filter (s := s) (hs := hs)
    rw [moleculeTest]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    refine Or.inr ⟨k, hkb, (P.finsetTopsAbove s k).filter (· ∈ V),
      Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    rw [dif_pos (by rw [hVeq, hWeq]; exact ⟨hp, hkV, hkW⟩), Bool.and_eq_true]
    exact ⟨ihV _ _ (by rw [mk_filter_mem, hVeq]), ihW _ _ (by rw [mk_filter_mem, hWeq])⟩

theorem moleculeTest_eq_true_iff (s : Finset P) (hs : IsLowerSet (s : Set P)) :
    P.moleculeTest s hs = true ↔ IsMoleculeIn P ⟨s, hs⟩ :=
  ⟨isMoleculeIn_of_moleculeTest s hs, fun h => moleculeTest_of_isMoleculeIn h s hs rfl⟩

instance decidableMemFacesIn (A : Set P) [DecidablePred (· ∈ A)] (n : ℕ) (α : Bool) :
    DecidablePred (· ∈ P.facesIn A n α) := fun x =>
  decidable_of_iff (x ∈ A ∧ grade ℕ x = n ∧ ∀ c, c ∈ P.cofaces (!α) x → c ∉ A)
    (and_congr_right fun _ => and_congr_right fun _ => Set.disjoint_left.symm)

omit [Fintype P] [DecidableEq P] in
@[instance_reducible]
def decidableCovByOfGrade : DecidableRel (α := P) (· ⋖ ·) := fun x y =>
  decidable_of_iff (x ≤ y ∧ grade ℕ y = grade ℕ x + 1) (by
    beta_reduce
    rw [covBy_iff_lt_covBy_grade (𝕆 := ℕ), Nat.covBy_iff_add_one_eq]
    refine ⟨fun ⟨h, hg⟩ => ⟨h.lt_of_ne ?_, hg.symm⟩, fun ⟨h, hg⟩ => ⟨h.le, hg.symm⟩⟩
    rintro rfl
    omega)

variable (P) in
def boundaryFinset (s : Finset P) (n : ℕ) (α : Bool) : Finset P :=
  letI := decidableCovByOfGrade (P := P)
  let gens := s.filter fun z => (grade ℕ z = n ∧ ∀ c ∈ s, ¬ ∃ h : z ⋖ c, P.orient h = !α) ∨
    (grade ℕ z < n ∧ ∀ w ∈ s, z ≤ w → w = z)
  Finset.univ.filter fun x => ∃ z ∈ gens, x ≤ z

theorem isLowerSet_boundaryFinset (s : Finset P) (n : ℕ) (α : Bool) :
    IsLowerSet (P.boundaryFinset s n α : Set P) := by
  intro x y hyx hx
  simp only [boundaryFinset, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨z, hz, hxz⟩ := hx
  exact ⟨z, hz, hyx.trans hxz⟩

theorem coe_boundaryFinset {s : Finset P} (hs : IsLowerSet (s : Set P)) (n : ℕ) (α : Bool) :
    (P.boundaryFinset s n α : Set P) = (P.boundary ⟨s, hs⟩ n α : Set P) := by
  ext x
  simp only [boundaryFinset, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    SetLike.mem_coe, mem_boundary, facesIn, Set.disjoint_left, mem_cofaces, Finset.mem_filter,
    LowerSet.mem_mk, Maximal]
  refine exists_congr fun z => and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨hz, ⟨hn, hc⟩ | ⟨hn, hm⟩⟩
    · exact .inl ⟨hz, hn, fun c hc' hcs => hc c hcs hc'⟩
    · exact .inr ⟨⟨hz, fun w hw hzw => (hm w hw hzw).le⟩, hn⟩
  · rintro (⟨hz, hn, hc⟩ | ⟨⟨hz, hm⟩, hn⟩)
    · exact ⟨hz, .inl ⟨hn, fun c hcs hc' => hc hc' hcs⟩⟩
    · exact ⟨hz, .inr ⟨hn, fun w hw hzw => le_antisymm (hm hw hzw) hzw⟩⟩

theorem mk_boundaryFinset {s : Finset P} (hs : IsLowerSet (s : Set P)) (n : ℕ) (α : Bool) :
    (⟨_, isLowerSet_boundaryFinset s n α⟩ : LowerSet P) = P.boundary ⟨s, hs⟩ n α :=
  SetLike.coe_injective (coe_boundaryFinset hs n α)

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
private theorem mk_eq_mk_iff {s t : Finset P} (hs : IsLowerSet (s : Set P))
    (ht : IsLowerSet (t : Set P)) : (⟨s, hs⟩ : LowerSet P) = ⟨t, ht⟩ ↔ s = t := by
  rw [LowerSet.mk.injEq, Finset.coe_inj]

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
private theorem coe_lt_krullDim_mk_iff {s : Finset P} (hs : IsLowerSet (s : Set P)) {k : ℕ} :
    (k : WithBot ℕ∞) < krullDim (⟨s, hs⟩ : LowerSet P) ↔ ∃ x ∈ s, k < grade ℕ x := by
  rw [coe_lt_krullDim_iff]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hk⟩ => ⟨⟨x, hx⟩, hk⟩⟩

variable (P) in
def isRoundFinset (s : Finset P) : Bool :=
  decide ((∀ n < P.gradeBound + 1, ∀ k < n, ∀ α β : Bool,
      P.boundaryFinset (P.boundaryFinset s n β) k α = P.boundaryFinset s k α) ∧
    ((∃ x ∈ s, 0 < grade ℕ x) → P.boundaryFinset s 0 false ∩ P.boundaryFinset s 0 true = ∅) ∧
    ∀ n < P.gradeBound, (∃ x ∈ s, n + 1 < grade ℕ x) →
      P.boundaryFinset s (n + 1) false ∩ P.boundaryFinset s (n + 1) true =
        P.boundaryFinset s n false ∪ P.boundaryFinset s n true)

theorem isRoundFinset_eq_true_iff {s : Finset P} (hs : IsLowerSet (s : Set P)) :
    P.isRoundFinset s = true ↔ P.IsRound ⟨s, hs⟩ := by
  have hbb (n k : ℕ) (α β : Bool) :
      P.boundaryFinset (P.boundaryFinset s n β) k α = P.boundaryFinset s k α ↔
        P.boundary (P.boundary ⟨s, hs⟩ n β) k α = P.boundary ⟨s, hs⟩ k α := by
    rw [← mk_eq_mk_iff (isLowerSet_boundaryFinset _ k α) (isLowerSet_boundaryFinset s k α),
      mk_boundaryFinset (isLowerSet_boundaryFinset s n β), mk_boundaryFinset hs,
      mk_boundaryFinset hs]
  have h0 : P.boundaryFinset s 0 false ∩ P.boundaryFinset s 0 true = ∅ ↔
      P.boundary ⟨s, hs⟩ 0 false ⊓ P.boundary ⟨s, hs⟩ 0 true = ⊥ := by
    simp only [SetLike.ext'_iff, Finset.coe_inter, Finset.coe_empty,
      LowerSet.coe_inf, LowerSet.coe_bot, coe_boundaryFinset hs]
  have hsucc (n : ℕ) : P.boundaryFinset s (n + 1) false ∩ P.boundaryFinset s (n + 1) true =
        P.boundaryFinset s n false ∪ P.boundaryFinset s n true ↔
      P.boundary ⟨s, hs⟩ (n + 1) false ⊓ P.boundary ⟨s, hs⟩ (n + 1) true =
        P.boundaryFull ⟨s, hs⟩ n := by
    simp only [SetLike.ext'_iff, Finset.coe_inter, Finset.coe_union,
      LowerSet.coe_inf, boundaryFull, LowerSet.coe_sup, coe_boundaryFinset hs]
  rw [isRoundFinset, decide_eq_true_iff]
  simp only [hbb, h0, hsucc, ← coe_lt_krullDim_mk_iff hs, Nat.cast_zero]
  refine ⟨fun ⟨hg, h₀, hn⟩ => ⟨isGlobular_iff_forall_lt_gradeBound.2 hg, h₀,
      fun n hk => hn n ?_ hk⟩,
    fun h => ⟨isGlobular_iff_forall_lt_gradeBound.1 h.isGlobular, h.inf_boundary_zero,
      fun n _ hn => h.inf_boundary_succ n hn⟩⟩
  have : n + 1 < P.gradeBound := by
    exact_mod_cast hk.trans_le (krullDim_le_gradeBound _)
  omega

variable (P) in
def bdryFinset (s : Finset P) (α : Bool) : Finset P :=
  match s.sup fun x => grade ℕ x with
  | 0 => ∅
  | n + 1 => P.boundaryFinset s n α

omit [Fintype P] [DecidableEq P] [DecidableLE P] in
private theorem krullDim_mk_of_sup_eq {s : Finset P} (hs : IsLowerSet (s : Set P)) {n : ℕ}
    (h : (s.sup fun x => grade ℕ x) = n + 1) :
    krullDim (⟨s, hs⟩ : LowerSet P) = (n + 1 : ℕ) := by
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 fun he => by simp [he] at h
  obtain ⟨x, hx, hxn⟩ := Finset.exists_mem_eq_sup s hne fun x => grade ℕ x
  refine le_antisymm (krullDim_le_coe_iff.2 fun y => ?_) ?_
  · exact h ▸ Finset.le_sup (f := fun x => grade ℕ x) y.2
  · exact (grade_le_krullDim (⟨x, hx⟩ : (⟨s, hs⟩ : LowerSet P))).trans' (by rw [← h, hxn]; rfl)

theorem filter_mem_bdry {s : Finset P} (hs : IsLowerSet (s : Set P)) (α : Bool) :
    Finset.univ.filter (· ∈ P.bdry ⟨s, hs⟩ α) = P.bdryFinset s α := by
  ext x
  rw [Finset.mem_filter_univ, bdryFinset]
  split
  · next h =>
    rw [bdry_eq_bot (krullDim_le_coe_iff.2 fun y => ?_)]
    · simp
    · exact h ▸ Finset.le_sup (f := fun x => grade ℕ x) y.2
  · next n h =>
    rw [bdry_eq_boundary (by exact_mod_cast krullDim_mk_of_sup_eq hs h), ← Finset.mem_coe,
      coe_boundaryFinset hs, SetLike.mem_coe]

variable (P) in
def pastingPartFinset (s : Finset P) (k : ℕ) (S : Finset P) (α : Bool) : Finset P :=
  Finset.univ.filter (fun x => ∃ z ∈ S, x ≤ z) ∪ P.boundaryFinset s k α

theorem filter_mem_pastingPart {s : Finset P} (hs : IsLowerSet (s : Set P)) (k : ℕ)
    (S : Finset P) (α : Bool) :
    Finset.univ.filter (· ∈ P.pastingPart s hs k S α) = P.pastingPartFinset s k S α := by
  rw [pastingPartFinset, ← Finset.coe_inj, Finset.coe_union, coe_boundaryFinset hs]
  ext x
  simp [pastingPart, mem_lowerClosure]

variable (P) in
def isPastingFinset (k : ℕ) (v w s : Finset P) : Bool :=
  decide (v ∪ w = s ∧ v ∩ w = P.boundaryFinset v k true ∧ v ∩ w = P.boundaryFinset w k false ∧
    (∃ x ∈ v, k < grade ℕ x) ∧ ∃ x ∈ w, k < grade ℕ x)

theorem isPastingFinset_eq_true_iff {k : ℕ} {v w s : Finset P} (hv : IsLowerSet (v : Set P))
    (hw : IsLowerSet (w : Set P)) (hs : IsLowerSet (s : Set P)) :
    P.isPastingFinset k v w s = true ↔ P.IsPastingIn k ⟨v, hv⟩ ⟨w, hw⟩ ⟨s, hs⟩ ∧
      (k : WithBot ℕ∞) < krullDim (⟨v, hv⟩ : LowerSet P) ∧
      (k : WithBot ℕ∞) < krullDim (⟨w, hw⟩ : LowerSet P) := by
  have hsup : v ∪ w = s ↔ (⟨v, hv⟩ ⊔ ⟨w, hw⟩ : LowerSet P) = ⟨s, hs⟩ := by
    rw [SetLike.ext'_iff (A := LowerSet P), LowerSet.coe_sup, ← Finset.coe_inj, Finset.coe_union]
    rfl
  have hinf {u : Finset P} (hu : IsLowerSet (u : Set P)) (α : Bool) :
      v ∩ w = P.boundaryFinset u k α ↔
        (⟨v, hv⟩ ⊓ ⟨w, hw⟩ : LowerSet P) = P.boundary ⟨u, hu⟩ k α := by
    rw [SetLike.ext'_iff (A := LowerSet P), LowerSet.coe_inf, ← Finset.coe_inj, Finset.coe_inter,
      coe_boundaryFinset hu]
    rfl
  rw [isPastingFinset, decide_eq_true_iff, coe_lt_krullDim_mk_iff, coe_lt_krullDim_mk_iff, hsup,
    hinf hv, hinf hw]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨⟨h₁, h₂, h₃⟩, h₄⟩, fun ⟨h, h₄⟩ =>
    ⟨h.sup_eq, h.inf_eq_output, h.inf_eq_input, h₄⟩⟩

variable (P) in
def fastMoleculeTestAux : ℕ → Finset P → Bool
  | 0, _ => false
  | n + 1, s =>
    decide (∃ x ∈ s, grade ℕ x = 0 ∧ ∀ y ∈ s, y ≤ x) ||
    (decide (∃ t ∈ s, ∀ y ∈ s, y ≤ t) && P.isRoundFinset s &&
      fastMoleculeTestAux n (P.bdryFinset s false) &&
        fastMoleculeTestAux n (P.bdryFinset s true)) ||
    decide (∃ k < P.gradeBound, ∃ S ∈ (P.finsetTopsAbove s k).powerset,
      (P.isPastingFinset k (P.pastingPartFinset s k S false)
          (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) s &&
        fastMoleculeTestAux n (P.pastingPartFinset s k S false) &&
        fastMoleculeTestAux n (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true)) = true)

theorem fastMoleculeTestAux_eq_moleculeTest {n : ℕ} {s : Finset P} (hs : IsLowerSet (s : Set P))
    (hn : s.card < n) : P.fastMoleculeTestAux n s = P.moleculeTest s hs := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
  have hrec {t : Finset P} (ht : IsLowerSet (t : Set P)) (hts : t ⊂ s) :
      P.fastMoleculeTestAux n t = P.moleculeTest t ht :=
    ih ht (by have := Finset.card_lt_card hts; omega)
  have hiff (x : P) (hx : x ∈ s) : (∀ y ∈ s, y ≤ x) ↔ ∀ y, y ∈ s ↔ y ≤ x :=
    ⟨fun h y => ⟨h y, fun hy => hs hy hx⟩, fun h y hy => (h y).1 hy⟩
  have hpt : (∃ x ∈ s, grade ℕ x = 0 ∧ ∀ y ∈ s, y ≤ x) ↔
      ∃ x ∈ s, grade ℕ x = 0 ∧ ∀ y, y ∈ s ↔ y ≤ x :=
    exists_congr fun x => and_congr_right fun hx => and_congr_right' (hiff x hx)
  have htop : (∃ t ∈ s, ∀ y ∈ s, y ≤ t) ↔ ∃ t ∈ s, ∀ y, y ∈ s ↔ y ≤ t :=
    exists_congr fun x => and_congr_right (hiff x)
  have hatom : (decide (∃ t ∈ s, ∀ y ∈ s, y ≤ t) && P.isRoundFinset s &&
      P.fastMoleculeTestAux n (P.bdryFinset s false) &&
        P.fastMoleculeTestAux n (P.bdryFinset s true)) =
      if (∃ t ∈ s, ∀ y, y ∈ s ↔ y ≤ t) ∧ P.IsRound ⟨s, hs⟩ then
        P.moleculeTest (Finset.univ.filter (· ∈ P.bdry ⟨s, hs⟩ false)) (isLowerSet_filter_mem _) &&
          P.moleculeTest (Finset.univ.filter (· ∈ P.bdry ⟨s, hs⟩ true)) (isLowerSet_filter_mem _)
      else false := by
    split_ifs with h
    · have hlt (α : Bool) : P.bdry ⟨s, hs⟩ α < ⟨s, hs⟩ := by
        obtain ⟨t, -, ht⟩ := h.1
        rw [mk_eq_Iic ht]
        exact bdry_Iic_lt t α
      rw [decide_eq_true (htop.2 h.1), (isRoundFinset_eq_true_iff hs).2 h.2, ← filter_mem_bdry hs,
        ← filter_mem_bdry hs, hrec _ (filter_mem_ssubset (hlt false)),
        hrec _ (filter_mem_ssubset (hlt true))]
      rfl
    · have : (decide (∃ t ∈ s, ∀ y ∈ s, y ≤ t) && P.isRoundFinset s) = false := by
        rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_iff, htop,
          isRoundFinset_eq_true_iff hs]
        exact h
      rw [this, Bool.false_and, Bool.false_and]
  have hpaste (k : ℕ) (S : Finset P) :
      (P.isPastingFinset k (P.pastingPartFinset s k S false)
          (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true) s &&
        P.fastMoleculeTestAux n (P.pastingPartFinset s k S false) &&
        P.fastMoleculeTestAux n (P.pastingPartFinset s k (P.finsetTopsAbove s k \ S) true)) =
      if h : P.IsPastingIn k (P.pastingPart s hs k S false)
          (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) ⟨s, hs⟩ ∧
        (k : WithBot ℕ∞) < krullDim (P.pastingPart s hs k S false) ∧
        (k : WithBot ℕ∞) < krullDim (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true) then
        P.moleculeTest (Finset.univ.filter (· ∈ P.pastingPart s hs k S false))
            (isLowerSet_filter_mem _) &&
          P.moleculeTest (Finset.univ.filter
            (· ∈ P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true))
            (isLowerSet_filter_mem _)
      else false := by
    rw [← filter_mem_pastingPart hs, ← filter_mem_pastingPart hs]
    have hC := isPastingFinset_eq_true_iff (k := k) (isLowerSet_filter_mem
      (P.pastingPart s hs k S false)) (isLowerSet_filter_mem
        (P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true)) hs
    rw [mk_filter_mem, mk_filter_mem] at hC
    split_ifs with h
    · rw [hC.2 h, hrec _ (filter_mem_ssubset
          (h.1.lt_cond false h.2.2 : P.pastingPart s hs k S false < _)),
        hrec _ (filter_mem_ssubset (h.1.lt_cond true h.2.1 :
          P.pastingPart s hs k (P.finsetTopsAbove s k \ S) true < _))]
      rfl
    · rw [Bool.eq_false_iff.2 (mt hC.1 h), Bool.false_and, Bool.false_and]
  rw [fastMoleculeTestAux, moleculeTest, decide_eq_decide.2 hpt, hatom]
  congr 1
  exact decide_eq_decide.2 (exists_congr fun k => and_congr_right' (exists_congr fun S =>
    and_congr_right' (by rw [hpaste k S])))

theorem fastMoleculeTestAux_succ {n : ℕ} {s : Finset P} (hs : IsLowerSet (s : Set P))
    (hn : s.card < n) : P.fastMoleculeTestAux (n + 1) s = P.fastMoleculeTestAux n s := by
  rw [fastMoleculeTestAux_eq_moleculeTest hs hn, fastMoleculeTestAux_eq_moleculeTest hs (by omega)]

variable (P) in
def fastMoleculeTest (s : Finset P) : Bool :=
  P.fastMoleculeTestAux (s.card + 1) s

theorem fastMoleculeTest_eq_moleculeTest (s : Finset P) (hs : IsLowerSet (s : Set P)) :
    P.fastMoleculeTest s = P.moleculeTest s hs :=
  fastMoleculeTestAux_eq_moleculeTest hs (Nat.lt_succ_self _)

theorem fastMoleculeTest_eq_true_iff (s : Finset P) (hs : IsLowerSet (s : Set P)) :
    P.fastMoleculeTest s = true ↔ IsMoleculeIn P ⟨s, hs⟩ := by
  rw [fastMoleculeTest_eq_moleculeTest s hs, moleculeTest_eq_true_iff]

instance decidableIsMoleculeIn (U : LowerSet P) [DecidablePred (· ∈ U)] :
    Decidable (IsMoleculeIn P U) :=
  decidable_of_iff (P.fastMoleculeTest (Finset.univ.filter (· ∈ U)) = true)
    (by rw [fastMoleculeTest_eq_true_iff _ (isLowerSet_filter_mem U), mk_filter_mem])

instance decidableIsMolecule : Decidable P.IsMolecule :=
  decidableIsMoleculeIn ⊤

section Maps

variable {Q : OGP.{v}} [Fintype Q] [DecidableEq Q] [DecidableLE Q] {f : P → Q}

omit [DecidableEq P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
instance decidableMemMap {Q : OGP.{u}} [DecidableEq Q] (f : P ⟶ Q) (U : LowerSet P)
    [DecidablePred (· ∈ U)] : DecidablePred (· ∈ map f U) := fun y =>
  decidable_of_iff (∃ x ∈ U, f x = y) Iff.rfl

omit [Fintype P] [DecidableEq P] [DecidableLE P] [Fintype Q] [DecidableEq Q] [DecidableLE Q] in
instance decidableMemComap {Q : OGP.{u}} (f : P ⟶ Q) (V : LowerSet Q)
    [DecidablePred (· ∈ V)] : DecidablePred (· ∈ comap f V) := fun x =>
  inferInstanceAs (Decidable (f x ∈ V))

instance decidableIsMorphism (f : P → Q) : Decidable (IsMorphism f) :=
  decidable_of_iff (∀ x α, Set.BijOn f (P.faces α x) (Q.faces α (f x)))
    ⟨fun h => ⟨h⟩, fun h => h.bijOn_faces⟩

omit [DecidableEq P] [DecidableLE P] [DecidableEq Q] [DecidableLE Q] [Fintype Q] in
theorem isMap_iff_forall_le_gradeBound : IsMap f ↔ IsClosedMap f ∧
    ∀ (x : P), ∀ n ≤ P.gradeBound, ∀ α : Bool,
      FinalOn f (P.boundary (.Iic x) n α) (Q.boundary (.Iic (f x)) n α) := by
  refine ⟨fun hf => ⟨hf.isClosedMap, fun x n _ α => hf.finalOn x n α⟩,
    fun ⟨hc, hfin⟩ => ⟨hc, fun x n α => ?_⟩⟩
  rcases le_or_gt n P.gradeBound with hn | hn
  · exact hfin x n hn α
  have hx : grade ℕ x ≤ P.gradeBound :=
    Finset.le_sup (f := fun x : P => grade ℕ x) (Finset.mem_univ x)
  have hfx : grade ℕ (f x) ≤ P.gradeBound :=
    ((IsUpperSet.isClosedMap_iff_fibration.1 hc).grade_apply_le x).trans hx
  have h := hfin x P.gradeBound le_rfl α
  rw [boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hx),
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hfx)] at h
  rwa [boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hx.trans hn.le),
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hfx.trans hn.le)]

instance decidableIsMap (f : P → Q) : Decidable (IsMap f) :=
  decidable_of_iff _ isMap_iff_forall_le_gradeBound.symm

end Maps

end Atoms.Molecule.OGP
