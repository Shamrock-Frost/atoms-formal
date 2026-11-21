import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.Construction.Dual
import Atoms.Molecule.Interior

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {U V : LowerSet P} {k n : ℕ} {α : Bool} {x : P}

structure IsRewritableSubmolecule (P : OGP.{u}) (V U : LowerSet P) : Prop where
  isSubmoleculeOf : P.IsSubmoleculeOf V U
  krullDim_eq : krullDim V = krullDim U
  isRound : P.IsRound V

theorem isRewritableSubmolecule_iff : P.IsRewritableSubmolecule V U ↔
    P.IsSubmoleculeOf V U ∧ krullDim V = krullDim U ∧ P.IsRound V :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

theorem isRewritableSubmolecule_dual (J : ℕ → Bool) :
    (dual P J).IsRewritableSubmolecule V U ↔ P.IsRewritableSubmolecule V U := by
  rw [isRewritableSubmolecule_iff, isRewritableSubmolecule_iff, isSubmoleculeOf_dual,
    isRound_dual]

theorem isRewritableSubmolecule_map_iff (f : P ⟶ Q) [IsInclusion f] (V U : LowerSet P) :
    Q.IsRewritableSubmolecule (map f V) (map f U) ↔ P.IsRewritableSubmolecule V U := by
  rw [isRewritableSubmolecule_iff, isRewritableSubmolecule_iff, isSubmoleculeOf_map_iff,
    isRound_map_iff, krullDim_map, krullDim_map]

private theorem isLowerSet_diff_interior_of_sup {A B : LowerSet P} {β : Bool} (hU : U = A ⊔ B)
    (hAB : A ⊓ B ≤ P.boundary A k β) (hBA : krullDim B ≤ k → B ≤ A)
    (hVA : P.IsSubmoleculeOf V A) (hd : krullDim V = krullDim U)
    (ih : IsLowerSet ((A : Set P) \ P.interior V)) :
    IsLowerSet ((U : Set P) \ P.interior V) := by
  have hdA : krullDim V = krullDim A :=
    le_antisymm (LowerSet.krullDim_mono hVA.le) (hd ▸ LowerSet.krullDim_mono (hU ▸ le_sup_left))
  by_cases hk : (k : WithBot ℕ∞) < krullDim A
  · have hdis := hVA.disjoint_interior_of_inf_le_boundary hdA hk hAB
    intro x y hyx hx
    refine ⟨U.lower hyx hx.1, fun hy => ?_⟩
    rcases LowerSet.mem_sup_iff.1 (hU ▸ hx.1 : x ∈ A ⊔ B) with hxA | hxB
    · exact (ih hyx ⟨hxA, hx.2⟩).2 hy
    · exact disjoint_left.1 hdis hy (B.lower hyx hxB)
  · have hBU : krullDim B ≤ krullDim U := LowerSet.krullDim_mono (hU ▸ le_sup_right)
    have hBk : krullDim B ≤ k := hBU.trans (hd ▸ hdA.le.trans (not_lt.1 hk))
    rw [hU, sup_eq_left.2 (hBA hBk)]
    exact ih

theorem IsSubmoleculeOf.isLowerSet_diff_interior (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) : IsLowerSet ((U : Set P) \ P.interior V) := by
  induction h.2 with
  | refl =>
    rw [diff_interior]
    exact (P.properBoundary V).lower
  | @tail Y U hVY hYU ih =>
    have hY := hYU.isMoleculeIn_left
    have hdY : krullDim V = krullDim Y :=
      le_antisymm (LowerSet.krullDim_mono (IsSubmoleculeOf.le ⟨hY, hVY⟩))
        (hd ▸ LowerSet.krullDim_mono hYU.le)
    obtain ⟨k, α, W, hp, -, -⟩ := hYU
    replace hp := (isPastingIn_cond_comm α).1 hp
    obtain ⟨hs, -, hi⟩ := (isPastingIn_cond_iff (!α)).1 hp
    exact isLowerSet_diff_interior_of_sup hs.symm hi.le (hp.le_of_krullDim_le_cond (!α))
      ⟨hY, hVY⟩ hd (ih ⟨hY, hVY⟩ hdY)

theorem IsRewritableSubmolecule.isLowerSet_diff_interior (hV : P.IsRewritableSubmolecule V U) :
    IsLowerSet ((U : Set P) \ P.interior V) :=
  hV.isSubmoleculeOf.isLowerSet_diff_interior hV.krullDim_eq

def IsSubmoleculeOf.complement (h : P.IsSubmoleculeOf V U) (hd : krullDim V = krullDim U) :
    LowerSet P :=
  ⟨(U : Set P) \ P.interior V, h.isLowerSet_diff_interior hd⟩

@[simp] theorem IsSubmoleculeOf.mem_complement (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) : x ∈ h.complement hd ↔ x ∈ U ∧ x ∉ P.interior V :=
  Iff.rfl

@[simp] theorem IsSubmoleculeOf.coe_complement (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) : (h.complement hd : Set P) = (U : Set P) \ P.interior V :=
  rfl

instance IsSubmoleculeOf.decidableMemComplement (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) [DecidablePred (· ∈ U)] [DecidablePred (· ∈ P.interior V)] :
    DecidablePred (· ∈ h.complement hd) := fun x =>
  inferInstanceAs (Decidable (x ∈ U ∧ x ∉ P.interior V))

theorem IsSubmoleculeOf.map_complement (f : P ⟶ Q) [IsInclusion f] (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) (h' : Q.IsSubmoleculeOf (map f V) (map f U))
    (hd' : krullDim (map f V) = krullDim (map f U)) : map f (h.complement hd) = h'.complement hd' :=
  SetLike.coe_injective (by
    rw [coe_map, IsSubmoleculeOf.coe_complement, IsSubmoleculeOf.coe_complement,
      image_sdiff IsInclusion.injective, image_interior, coe_map])

abbrev IsRewritableSubmolecule.complement (hV : P.IsRewritableSubmolecule V U) : LowerSet P :=
  hV.isSubmoleculeOf.complement hV.krullDim_eq

theorem IsRewritableSubmolecule.complement_dual (hV : P.IsRewritableSubmolecule V U)
    (J : ℕ → Bool) : ((isRewritableSubmolecule_dual J).2 hV).complement = hV.complement :=
  SetLike.coe_injective (by
    rw [IsSubmoleculeOf.coe_complement, IsSubmoleculeOf.coe_complement, interior_dual])

theorem IsRewritableSubmolecule.complement_eq_bot_of_krullDim_eq_zero
    (hV : P.IsRewritableSubmolecule V U) (h0 : krullDim U = 0) : hV.complement = ⊥ := by
  obtain ⟨x, hx, rfl⟩ := hV.isSubmoleculeOf.isMoleculeIn_right.exists_eq_Iic_of_krullDim_eq_zero h0
  obtain ⟨y, -, rfl⟩ := hV.isSubmoleculeOf.isMoleculeIn.exists_eq_Iic_of_krullDim_eq_zero
    (hV.krullDim_eq.trans h0)
  have hyx : y ≤ x := hV.isSubmoleculeOf.le (LowerSet.mem_Iic_iff.2 le_rfl)
  obtain rfl : y = x := le_antisymm hyx (hx hyx)
  exact SetLike.coe_injective (by
    rw [IsSubmoleculeOf.coe_complement, interior_eq_self h0.le, Set.sdiff_self, LowerSet.coe_bot])

theorem IsRewritableSubmolecule.bdryFull_le_complement (hV : P.IsRewritableSubmolecule V U) :
    P.bdryFull U ≤ hV.complement := fun _ hx =>
  ⟨properBoundary_le U (bdryFull_le_properBoundary U hx), fun hi =>
    (OGP.mem_interior.1 (hV.isSubmoleculeOf.interior_subset_interior hV.krullDim_eq hi)).2
      (bdryFull_le_properBoundary U hx)⟩

theorem krullDim_pos_of_isSubmoleculeOf_bdry (hV : P.IsSubmoleculeOf V (P.bdry ⊤ α)) :
    0 < krullDim (⊤ : LowerSet P) := by
  by_contra h
  obtain ⟨x, hx⟩ := hV.isMoleculeIn.nonempty
  have hxb := hV.le hx
  rw [bdry_eq_bot (not_lt.1 h)] at hxb
  exact LowerSet.notMem_bot hxb

section HornSetAt

variable (hP : P.IsMolecule) (hr : P.IsRound ⊤) (hk : (k : WithBot ℕ∞) < krullDim (⊤ : LowerSet P))
  (hV : P.IsSubmoleculeOf V (P.boundary ⊤ k α)) (hdV : krullDim V = krullDim (P.boundary ⊤ k α))

include hP hr hk hV hdV in
theorem coe_boundaryFull_diff_interior : (P.boundaryFull ⊤ k : Set P) \ P.interior V =
    (hV.complement hdV : Set P) ∪ P.boundary ⊤ k (!α) := by
  have hint := hV.interior_subset_interior hdV
  have hmeet := hr.inf_boundary_eq_properBoundary hP hk α
  ext x
  rw [mem_sdiff, SetLike.mem_coe, mem_boundaryFull, mem_union, SetLike.mem_coe,
    hV.mem_complement, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨δ, hx⟩, hxi⟩
    rcases Bool.eq_or_eq_not δ α with rfl | rfl
    · exact Or.inl ⟨hx, hxi⟩
    · exact Or.inr hx
  · rintro (⟨hx, hxi⟩ | hx)
    · exact ⟨⟨α, hx⟩, hxi⟩
    · refine ⟨⟨!α, hx⟩, fun hxi => ?_⟩
      have h := hint hxi
      exact h.2 (hmeet ▸ ⟨h.1, hx⟩)

def IsSubmoleculeOf.hornSetAt : LowerSet P :=
  ⟨(P.boundaryFull ⊤ k : Set P) \ P.interior V, by
    rw [coe_boundaryFull_diff_interior hP hr hk hV hdV]
    exact (hV.complement hdV).lower.union (P.boundary ⊤ k (!α)).lower⟩

@[simp] theorem IsSubmoleculeOf.mem_hornSetAt :
    x ∈ hV.hornSetAt hP hr hk hdV ↔ x ∈ P.boundaryFull ⊤ k ∧ x ∉ P.interior V :=
  Iff.rfl

@[simp] theorem IsSubmoleculeOf.coe_hornSetAt :
    (hV.hornSetAt hP hr hk hdV : Set P) = (P.boundaryFull ⊤ k : Set P) \ P.interior V :=
  rfl

instance IsSubmoleculeOf.decidableMemHornSetAt [Fintype P] [DecidableLE P]
    [DecidablePred (· ∈ V)] : DecidablePred (· ∈ hV.hornSetAt hP hr hk hdV) := fun x =>
  inferInstanceAs (Decidable (x ∈ P.boundaryFull ⊤ k ∧ x ∉ P.interior V))

theorem IsSubmoleculeOf.hornSetAt_eq_sup :
    hV.hornSetAt hP hr hk hdV = hV.complement hdV ⊔ P.boundary ⊤ k (!α) :=
  SetLike.coe_injective (coe_boundaryFull_diff_interior hP hr hk hV hdV)

theorem IsSubmoleculeOf.boundary_not_le_hornSetAt :
    P.boundary ⊤ k (!α) ≤ hV.hornSetAt hP hr hk hdV := by
  rw [hV.hornSetAt_eq_sup hP hr hk hdV]
  exact le_sup_right

theorem IsSubmoleculeOf.bdryFull_le_hornSetAt : P.bdryFull V ≤ hV.hornSetAt hP hr hk hdV :=
  fun _ hx =>
    ⟨boundary_le_boundaryFull ⊤ k α (hV.le (properBoundary_le V (bdryFull_le_properBoundary V hx))),
      fun hi => hi.2 (bdryFull_le_properBoundary V hx)⟩

theorem IsSubmoleculeOf.mem_hornSetAt_iff_of_mem (hx : x ∈ V) :
    x ∈ hV.hornSetAt hP hr hk hdV ↔ x ∈ P.bdryFull V := by
  rw [← hV.isMoleculeIn.properBoundary_eq_bdryFull, hV.mem_hornSetAt]
  exact mem_diff_interior_iff_of_mem
    (fun _ hy => boundary_le_boundaryFull ⊤ k α (hV.le (properBoundary_le V hy))) hx

theorem IsSubmoleculeOf.mem_of_mem_boundary_of_notMem_hornSetAt (hx : x ∈ P.boundary ⊤ k α)
    (hxK : x ∉ hV.hornSetAt hP hr hk hdV) : x ∈ V := by
  by_contra hxV
  exact hxK ⟨boundary_le_boundaryFull ⊤ k α hx, fun h => hxV h.1⟩

end HornSetAt

section HornSet

variable (hP : P.IsMolecule) (hr : P.IsRound ⊤) (hV : P.IsSubmoleculeOf V (P.bdry ⊤ α))
  (hdV : krullDim V = krullDim (P.bdry ⊤ α))

include hP hV in
private theorem exists_krullDim_eq_succ : ∃ n : ℕ, krullDim (⊤ : LowerSet P) = n + 1 := by
  obtain ⟨n, hn⟩ := hP.exists_krullDim_eq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by
    rintro rfl
    exact absurd (hn ▸ krullDim_pos_of_isSubmoleculeOf_bdry hV) (lt_irrefl _))
  exact ⟨m, by rw [hn]; push_cast; rfl⟩

private theorem lt_krullDim (hn : krullDim (⊤ : LowerSet P) = n + 1) :
    (n : WithBot ℕ∞) < krullDim (⊤ : LowerSet P) := by
  rw [hn]
  exact_mod_cast n.lt_succ_self

def IsSubmoleculeOf.hornSet : LowerSet P :=
  ⟨(P.bdryFull ⊤ : Set P) \ P.interior V, by
    obtain ⟨n, hn⟩ := exists_krullDim_eq_succ hP hV
    have h := ((bdry_eq_boundary hn α ▸ hV : P.IsSubmoleculeOf V (P.boundary ⊤ n α)).hornSetAt hP
      hr (lt_krullDim hn) (bdry_eq_boundary hn α ▸ hdV)).lower
    rwa [IsSubmoleculeOf.coe_hornSetAt, boundaryFull, ← bdry_eq_boundary hn,
      ← bdry_eq_boundary hn] at h⟩

abbrev IsRewritableSubmolecule.hornSet (hV : P.IsRewritableSubmolecule V (P.bdry ⊤ α)) :
    LowerSet P :=
  hV.isSubmoleculeOf.hornSet hP hr hV.krullDim_eq

@[simp] theorem IsSubmoleculeOf.mem_hornSet :
    x ∈ hV.hornSet hP hr hdV ↔ x ∈ P.bdryFull ⊤ ∧ x ∉ P.interior V :=
  Iff.rfl

@[simp] theorem IsSubmoleculeOf.coe_hornSet :
    (hV.hornSet hP hr hdV : Set P) = (P.bdryFull ⊤ : Set P) \ P.interior V :=
  rfl

instance IsSubmoleculeOf.decidableMemHornSet [Fintype P] [DecidableLE P]
    [DecidablePred (· ∈ V)] : DecidablePred (· ∈ hV.hornSet hP hr hdV) := fun x =>
  inferInstanceAs (Decidable (x ∈ P.bdryFull ⊤ ∧ x ∉ P.interior V))

theorem IsSubmoleculeOf.hornSet_eq_hornSetAt (hn : krullDim (⊤ : LowerSet P) = n + 1)
    (hV' : P.IsSubmoleculeOf V (P.boundary ⊤ n α))
    (hdV' : krullDim V = krullDim (P.boundary ⊤ n α)) :
    hV.hornSet hP hr hdV = hV'.hornSetAt hP hr (lt_krullDim hn) hdV' :=
  SetLike.coe_injective (by
    rw [IsSubmoleculeOf.coe_hornSet, IsSubmoleculeOf.coe_hornSetAt, boundaryFull, bdryFull,
      bdry_eq_boundary hn, bdry_eq_boundary hn])

theorem IsSubmoleculeOf.bdry_not_le_hornSet (hn : krullDim (⊤ : LowerSet P) = n + 1) :
    P.bdry ⊤ (!α) ≤ hV.hornSet hP hr hdV := by
  rw [hV.hornSet_eq_hornSetAt hP hr hdV hn (bdry_eq_boundary hn α ▸ hV)
    (bdry_eq_boundary hn α ▸ hdV), bdry_eq_boundary hn]
  exact IsSubmoleculeOf.boundary_not_le_hornSetAt hP hr (lt_krullDim hn) _ _

theorem IsSubmoleculeOf.bdryFull_le_hornSet : P.bdryFull V ≤ hV.hornSet hP hr hdV := fun _ hx =>
  ⟨bdry_le_bdryFull ⊤ α (hV.le (properBoundary_le V (bdryFull_le_properBoundary V hx))),
    fun hi => hi.2 (bdryFull_le_properBoundary V hx)⟩

theorem IsSubmoleculeOf.mem_hornSet_iff_of_mem (hx : x ∈ V) :
    x ∈ hV.hornSet hP hr hdV ↔ x ∈ P.bdryFull V := by
  rw [← hV.isMoleculeIn.properBoundary_eq_bdryFull, hV.mem_hornSet]
  exact mem_diff_interior_iff_of_mem
    (fun _ hy => bdry_le_bdryFull ⊤ α (hV.le (properBoundary_le V hy))) hx

omit hV hdV in
theorem IsSubmoleculeOf.hornSet_bdry (hn : krullDim (⊤ : LowerSet P) = n + 1)
    (hB : P.IsSubmoleculeOf (P.bdry ⊤ (!α)) (P.bdry ⊤ (!α)))
    (hdB : krullDim (P.bdry ⊤ (!α)) = krullDim (P.bdry ⊤ (!α))) :
    hB.hornSet hP hr hdB = P.bdry ⊤ α := by
  have hmeet : P.bdry ⊤ (!α) ⊓ P.bdry ⊤ α = P.properBoundary (P.bdry ⊤ (!α)) := by
    have h := hr.inf_boundary_eq_properBoundary hP (lt_krullDim hn) (!α)
    rwa [Bool.not_not, ← bdry_eq_boundary hn, ← bdry_eq_boundary hn] at h
  refine SetLike.ext fun x => ?_
  rw [hB.mem_hornSet, OGP.mem_interior, bdryFull_eq_bdry_sup_bdry_not ⊤ α, LowerSet.mem_sup_iff]
  constructor
  · rintro ⟨hx | hx, hxi⟩
    · exact hx
    · exact (hmeet ▸ not_not.1 (fun h => hxi ⟨hx, h⟩) : x ∈ P.bdry ⊤ (!α) ⊓ P.bdry ⊤ α).2
  · exact fun hx => ⟨Or.inl hx, fun hxi => hxi.2 (hmeet ▸ ⟨hxi.1, hx⟩)⟩

theorem IsSubmoleculeOf.map_hornSet (f : P ⟶ Q) [IsIso f] (hQ : Q.IsMolecule)
    (hr' : Q.IsRound ⊤) (hV' : Q.IsSubmoleculeOf (map f V) (Q.bdry ⊤ α))
    (hdV' : krullDim (map f V) = krullDim (Q.bdry ⊤ α)) :
    map f (hV.hornSet hP hr hdV) = hV'.hornSet hQ hr' hdV' :=
  SetLike.coe_injective (by
    rw [coe_map, IsSubmoleculeOf.coe_hornSet, IsSubmoleculeOf.coe_hornSet,
      image_sdiff IsInclusion.injective, image_interior, ← coe_map, map_bdryFull,
      map_top_of_isIso])

end HornSet

theorem isRewritableSubmolecule_bdry_self (hP : P.IsMolecule) (hr : P.IsRound ⊤)
    (hn : krullDim (⊤ : LowerSet P) = n + 1) (α : Bool) :
    P.IsRewritableSubmolecule (P.bdry ⊤ α) (P.bdry ⊤ α) := by
  refine ⟨.refl (hP.bdry (by rw [hn]; exact_mod_cast n.succ_pos) α), rfl, ?_⟩
  rw [bdry_eq_boundary hn]
  exact hr.boundary n α

end Atoms.Molecule.OGP
