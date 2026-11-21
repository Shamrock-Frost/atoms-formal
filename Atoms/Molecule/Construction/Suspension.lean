import Atoms.Molecule.Construction.Basic
import Atoms.Molecule.Rewritable.Basic

universe u

open Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

section Order

variable {X : Type u} [PartialOrder X]

def _root_.LowerSet.susp (V : LowerSet X) : LowerSet (SuspCarrier X) where
  carrier := {w | ∀ x, w = SuspCarrier.susp x → x ∈ V}
  lower' := by
    rintro (β | y) _ hwy hy x rfl
    · exact absurd hwy (not_susp_le_pole x β)
    · exact V.lower hwy (hy y rfl)

variable {V W : LowerSet X}

@[simp] theorem pole_mem_susp (V : LowerSet X) (α : Bool) :
    (pole α : SuspCarrier X) ∈ V.susp :=
  fun _ h => nomatch h

@[simp] theorem susp_mem_susp {x : X} : susp x ∈ V.susp ↔ x ∈ V :=
  ⟨fun h => h x rfl, fun h _ hy => susp.inj hy ▸ h⟩

theorem susp_sup (V W : LowerSet X) :
    (V ⊔ W).susp = V.susp ⊔ W.susp :=
  SetLike.ext fun w => by cases w <;> simp

theorem susp_inf (V W : LowerSet X) :
    (V ⊓ W).susp = V.susp ⊓ W.susp :=
  SetLike.ext fun w => by cases w <;> simp

theorem _root_.LowerSet.susp_injective : Function.Injective (LowerSet.susp (X := X)) :=
  fun V W h => SetLike.ext fun x => by rw [← susp_mem_susp, h, susp_mem_susp]

@[simp] theorem susp_top : (⊤ : LowerSet X).susp = ⊤ :=
  SetLike.ext fun w => by cases w <;> simp

theorem susp_bot :
    (⊥ : LowerSet X).susp = LowerSet.Iic (pole false) ⊔ LowerSet.Iic (pole true) :=
  SetLike.ext fun w => by
    rcases w with (_ | _) | x <;> simp

theorem susp_lowerClosure {A : Set X} (hA : A.Nonempty) :
    (lowerClosure A).susp = lowerClosure (susp '' A) := by
  refine SetLike.ext fun w => ?_
  cases w with
  | pole α =>
    obtain ⟨a, ha⟩ := hA
    exact iff_of_true (pole_mem_susp _ α)
      (mem_lowerClosure.2 ⟨susp a, mem_image_of_mem susp ha, pole_le_susp α a⟩)
  | susp x => simp [mem_lowerClosure]

theorem susp_Iic (x : X) :
    (LowerSet.Iic x).susp = LowerSet.Iic (susp x) := by
  rw [← lowerClosure_singleton, susp_lowerClosure (singleton_nonempty x), image_singleton,
    lowerClosure_singleton]

theorem krullDim_susp (hV : (V : Set X).Nonempty) :
    krullDim V.susp = krullDim V + 1 := by
  have : Nonempty V := hV.to_subtype
  rw [← krullDim_withBot]
  refine le_antisymm (krullDim_le_of_strictMono
    (fun w : V.susp => match w with
      | ⟨pole _, _⟩ => (⊥ : WithBot V)
      | ⟨susp x, hx⟩ => ((⟨x, susp_mem_susp.1 hx⟩ : V) : WithBot V)) ?_)
    (krullDim_le_of_strictMono
      (fun a : WithBot V => match a with
        | ⊥ => (⟨pole false, pole_mem_susp V false⟩ : V.susp)
        | (x : V) => ⟨susp x.1, susp_mem_susp.2 x.2⟩) ?_)
  · rintro ⟨(α | x), hx⟩ ⟨(β | y), hy⟩ h
    · exact absurd (Subtype.coe_lt_coe.2 h) ((isMin_pole β).not_lt)
    · exact WithBot.bot_lt_coe _
    · exact absurd (Subtype.coe_lt_coe.2 h) ((isMin_pole β).not_lt)
    · exact WithBot.coe_lt_coe.2 (susp_lt_susp.1 (Subtype.coe_lt_coe.2 h))
  · intro a b h
    induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe
    · exact absurd h (lt_irrefl _)
    · exact Subtype.coe_lt_coe.1 (pole_lt_susp false _)
    · exact absurd h (not_lt_bot)
    · exact Subtype.coe_lt_coe.1 (susp_lt_susp.2 (Subtype.coe_lt_coe.2 (WithBot.coe_lt_coe.1 h)))

theorem coe_lt_krullDim_susp_iff [GradeMinOrder ℕ X] {n : ℕ} :
    ((n + 1 : ℕ) : WithBot ℕ∞) < krullDim V.susp ↔ (n : WithBot ℕ∞) < krullDim V := by
  rw [coe_lt_krullDim_iff, coe_lt_krullDim_iff]
  constructor
  · rintro ⟨⟨(α | x), hx⟩, h⟩
    · exact absurd (h : n + 1 < 0) (Nat.not_lt_zero _)
    · exact ⟨⟨x, susp_mem_susp.1 hx⟩,
        Nat.lt_of_add_lt_add_right (h : n + 1 < grade ℕ x + 1)⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    exact ⟨⟨susp x, susp_mem_susp.2 hx⟩, Nat.add_lt_add_right (h : n < grade ℕ x) 1⟩

end Order

variable {P : OGP.{u}} {U V W : LowerSet P} {n : ℕ} {α : Bool}

private theorem exists_isMin_mem (hV : (V : Set P).Nonempty) : ∃ y ∈ V, IsMin y := by
  obtain ⟨x, hx⟩ := hV
  obtain ⟨y, -, hy⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ V) x hx
  exact ⟨y, hy.prop, fun c hc => hy.2 (V.lower hc hy.prop) hc⟩

theorem susp_mem_facesIn_susp {x : P} :
    (susp x : suspension P) ∈ (suspension P).facesIn V.susp (n + 1) α ↔
      x ∈ P.facesIn V n α := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, susp_mem_susp, grade_susp,
    Nat.add_right_cancel_iff, disjoint_left]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h y hy => ?_, fun h w hw => ?_⟩
  · exact susp_mem_susp.not.1 (h (susp_mem_faces_suspension.2 hy))
  · cases w with
    | pole β => exact absurd hw.1 not_covBy_pole
    | susp y => exact susp_mem_susp.not.2 (h (susp_mem_faces_suspension.1 hw))

theorem pole_mem_facesIn_susp (hV : (V : Set P).Nonempty) {β : Bool} :
    (pole β : suspension P) ∈ (suspension P).facesIn V.susp 0 α ↔ β = α := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, pole_mem_susp, grade_pole,
    true_and, disjoint_left]
  constructor
  · intro h
    obtain ⟨y, hyV, hy⟩ := exists_isMin_mem hV
    by_contra hβ
    exact h (pole_mem_faces_suspension.2 ⟨hy, Bool.eq_not_iff.2 hβ⟩)
      (susp_mem_susp.2 hyV)
  · rintro rfl w hw
    cases w with
    | pole γ => exact absurd hw.1 not_covBy_pole
    | susp y => exact absurd (pole_mem_faces_suspension.1 hw).2 (Bool.not_ne_self β).symm

theorem maximal_susp_mem_susp_iff {x : P} :
    Maximal (· ∈ V.susp) (susp x : suspension P) ↔ Maximal (· ∈ V) x := by
  refine ⟨fun h => ⟨susp_mem_susp.1 h.prop, fun y hy hxy =>
    susp_le_susp.1 (h.2 (susp_mem_susp.2 hy) (susp_le_susp.2 hxy))⟩,
    fun h => ⟨susp_mem_susp.2 h.prop, fun w hw hxw => ?_⟩⟩
  cases w with
  | pole β => exact absurd hxw (not_susp_le_pole x β)
  | susp y => exact susp_le_susp.2 (h.2 (susp_mem_susp.1 hw) (susp_le_susp.1 hxw))

theorem not_maximal_pole_mem_susp (hV : (V : Set P).Nonempty) (β : Bool) :
    ¬ Maximal (· ∈ V.susp) (pole β : suspension P) := by
  obtain ⟨x, hx⟩ := hV
  exact fun h => not_susp_le_pole x β (h.2 (susp_mem_susp.2 hx) (pole_le_susp β x))

theorem boundary_susp_zero (hV : (V : Set P).Nonempty) (α : Bool) :
    (suspension P).boundary V.susp 0 α = LowerSet.Iic (pole α) := by
  have hgen : (suspension P).facesIn V.susp 0 α ∪
      {w | Maximal (· ∈ V.susp) w ∧ grade ℕ w < 0} = {pole α} := by
    ext w
    cases w with
    | pole β => simp [pole_mem_facesIn_susp hV]
    | susp x => simp [facesIn]
  rw [boundary, hgen, lowerClosure_singleton]

private theorem boundary_susp_succ_eq_lowerClosure (hV : (V : Set P).Nonempty) :
    (suspension P).boundary V.susp (n + 1) α =
      lowerClosure (susp '' (P.facesIn V n α ∪ {x | Maximal (· ∈ V) x ∧ grade ℕ x < n})) := by
  rw [boundary]
  congr 1
  ext w
  cases w with
  | pole β =>
    refine iff_of_false (fun h => h.elim (fun h' => ?_) fun h' => ?_) (by simp)
    · exact absurd h'.2.1 (by simp)
    · exact not_maximal_pole_mem_susp hV β h'.1
  | susp x =>
    have hinj : Function.Injective (susp : P → SuspCarrier P) := fun _ _ => susp.inj
    rw [hinj.mem_set_image, mem_union, mem_union, mem_ofPred_eq,
      mem_ofPred_eq, susp_mem_facesIn_susp, maximal_susp_mem_susp_iff,
      grade_susp, Nat.add_lt_add_iff_right]

theorem susp_mem_boundary_susp_succ (hV : (V : Set P).Nonempty) {x : P} :
    (susp x : suspension P) ∈ (suspension P).boundary V.susp (n + 1) α ↔
      x ∈ P.boundary V n α := by
  rw [boundary_susp_succ_eq_lowerClosure hV, boundary, mem_lowerClosure,
    mem_lowerClosure]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨y, hy, susp_le_susp.1 hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨susp y, ⟨y, hy, rfl⟩, susp_le_susp.2 hxy⟩

theorem boundary_susp_succ (hne : (P.boundary V n α : Set P).Nonempty) :
    (suspension P).boundary V.susp (n + 1) α = (P.boundary V n α).susp := by
  have hV : (V : Set P).Nonempty := hne.mono (boundary_le V n α)
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, -⟩ := mem_boundary.1 hy
  rw [boundary_susp_succ_eq_lowerClosure hV, boundary, ← susp_lowerClosure ⟨z, hz⟩]

theorem bdry_susp (hne : (P.bdry V α : Set P).Nonempty) :
    (suspension P).bdry V.susp α = (P.bdry V α).susp := by
  obtain ⟨n, hn, -⟩ : ∃ n : ℕ, krullDim V = n + 1 ∧ hne.some ∈ P.boundary V n α := by
    simpa [bdry] using hne.some_mem
  rw [bdry_eq_boundary hn] at hne ⊢
  have hV : (V : Set P).Nonempty := hne.mono (boundary_le V n α)
  rw [bdry_eq_boundary (n := n + 1) (by rw [krullDim_susp hV, hn]; norm_cast),
    boundary_susp_succ hne]

theorem bdry_susp_of_krullDim_eq_zero (h : krullDim V = 0) (α : Bool) :
    (suspension P).bdry V.susp α = LowerSet.Iic (pole α) := by
  obtain ⟨⟨x, hx⟩, -⟩ := exists_grade_eq_of_krullDim_eq (n := 0) (by rw [h]; rfl)
  have hV : (V : Set P).Nonempty := ⟨x, hx⟩
  rw [bdry_eq_boundary (n := 0) (by rw [krullDim_susp hV, h]; rfl),
    boundary_susp_zero hV]

theorem bdryFull_susp (h : IsMoleculeIn P V) :
    (suspension P).bdryFull V.susp = (P.bdryFull V).susp := by
  obtain ⟨m, hm⟩ := h.exists_krullDim_eq
  rcases m with _ | m
  · rw [bdryFull, bdryFull, bdry_susp_of_krullDim_eq_zero hm,
      bdry_susp_of_krullDim_eq_zero hm, bdry_eq_bot hm.le, bdry_eq_bot hm.le, sup_bot_eq,
      susp_bot]
  · have hd : 0 < krullDim V := by rw [hm]; exact_mod_cast m.succ_pos
    rw [bdryFull, bdryFull, bdry_susp (h.bdry hd false).nonempty,
      bdry_susp (h.bdry hd true).nonempty, susp_sup]

theorem isGlobular_susp (hU : P.IsGlobular U)
    (hne : ∀ n α, (P.boundary U n α : Set P).Nonempty) :
    (suspension P).IsGlobular U.susp := by
  have hUne : (U : Set P).Nonempty := (hne 0 false).mono (boundary_le U 0 false)
  intro k n hkn α β
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  rw [boundary_susp_succ (hne m β)]
  rcases k with _ | j
  · rw [boundary_susp_zero (hne m β), boundary_susp_zero hUne]
  · have hj : j < m := by omega
    rw [boundary_susp_succ (hU j m hj α β ▸ hne j α), boundary_susp_succ (hne j α),
      hU j m hj α β]

theorem isRound_susp (hU : P.IsRound U)
    (hne : ∀ n α, (P.boundary U n α : Set P).Nonempty) :
    (suspension P).IsRound U.susp where
  isGlobular := isGlobular_susp hU.isGlobular hne
  inf_boundary_zero _ := by
    have hUne : (U : Set P).Nonempty := (hne 0 false).mono (boundary_le U 0 false)
    rw [boundary_susp_zero hUne, boundary_susp_zero hUne]
    refine SetLike.ext fun w => ?_
    rcases w with (_ | _) | x <;> simp
  inf_boundary_succ m hm := by
    have hUne : (U : Set P).Nonempty := (hne 0 false).mono (boundary_le U 0 false)
    rw [coe_lt_krullDim_susp_iff] at hm
    rw [boundary_susp_succ (hne m false), boundary_susp_succ (hne m true),
      ← susp_inf]
    rcases m with _ | j
    · rw [hU.inf_boundary_zero hm, susp_bot, boundaryFull,
        boundary_susp_zero hUne, boundary_susp_zero hUne]
    · rw [hU.inf_boundary_succ j hm, boundaryFull, boundaryFull, susp_sup,
        boundary_susp_succ (hne j false), boundary_susp_succ (hne j true)]

theorem isRound_susp_iff (hne : ∀ n α, (P.boundary U n α : Set P).Nonempty) :
    (suspension P).IsRound U.susp ↔ P.IsRound U := by
  refine ⟨fun h => ⟨fun k n hkn α β => ?_, fun hd => ?_, fun m hm => ?_⟩,
    fun hU => isRound_susp hU hne⟩
  · have hg := h.isGlobular (k + 1) (n + 1) (by omega) α β
    rw [boundary_susp_succ (hne n β), boundary_susp_succ (hne k α)] at hg
    refine SetLike.ext fun x => ?_
    rw [← susp_mem_boundary_susp_succ (hne n β), hg, susp_mem_susp]
  · have hUne : (U : Set P).Nonempty := (hne 0 false).mono (boundary_le U 0 false)
    have h0 := h.inf_boundary_succ 0 (coe_lt_krullDim_susp_iff.2 (by exact_mod_cast hd))
    rw [boundary_susp_succ (hne 0 false), boundary_susp_succ (hne 0 true), ← susp_inf,
      boundaryFull, boundary_susp_zero hUne, boundary_susp_zero hUne, ← susp_bot] at h0
    exact LowerSet.susp_injective h0
  · have h1 := h.inf_boundary_succ (m + 1) (coe_lt_krullDim_susp_iff.2 hm)
    rw [boundary_susp_succ (hne _ false), boundary_susp_succ (hne _ true), ← susp_inf,
      boundaryFull, boundary_susp_succ (hne m false),
      boundary_susp_succ (hne m true), ← susp_sup] at h1
    exact LowerSet.susp_injective h1

theorem isPastingIn_susp {k : ℕ} (hp : P.IsPastingIn k V W U)
    (hne : ((V ⊓ W : LowerSet P) : Set P).Nonempty) :
    (suspension P).IsPastingIn (k + 1) V.susp W.susp U.susp where
  sup_eq := by rw [← susp_sup, hp.sup_eq]
  inf_eq_output := by
    rw [← susp_inf, hp.inf_eq_output, boundary_susp_succ (hp.inf_eq_output ▸ hne)]
  inf_eq_input := by
    rw [← susp_inf, hp.inf_eq_input, boundary_susp_succ (hp.inf_eq_input ▸ hne)]

theorem isMoleculeIn_susp (h : IsMoleculeIn P U) :
    IsMoleculeIn (suspension P) U.susp := by
  induction h with
  | point x hx =>
    have hm : IsMoleculeIn P (.Iic x) := .point x hx
    have h0 : krullDim (LowerSet.Iic x) = 0 := LowerSet.krullDim_Iic_of_isMin hx
    rw [susp_Iic]
    refine .atom (P := suspension P) (susp x) ?_ fun α => ?_
    · rw [← susp_Iic]
      exact isRound_susp (isRound_of_krullDim_le_zero h0.le)
        fun n α => (hm.boundary n α).nonempty
    · rw [← susp_Iic, bdry_susp_of_krullDim_eq_zero h0]
      exact .point _ (isMin_pole α)
  | atom t hround hbdry ih =>
    have hm : IsMoleculeIn P (.Iic t) := .atom t hround hbdry
    rw [susp_Iic]
    refine .atom (P := suspension P) (susp t) ?_ fun α => ?_
    · rw [← susp_Iic]
      exact isRound_susp hround fun n α => (hm.boundary n α).nonempty
    · rw [← susp_Iic, bdry_susp (hbdry α).nonempty]
      exact ih α
  | paste k V W U hp hV _ hk ihV ihW =>
    refine .paste (k + 1) _ _ _ (isPastingIn_susp hp ?_) ihV ihW ?_
    · rw [hp.inf_eq_output]
      exact (hV.boundary k true).nonempty
    · rw [lt_min_iff, coe_lt_krullDim_susp_iff, coe_lt_krullDim_susp_iff]
      exact lt_min_iff.1 hk

theorem isAtomIn_susp (h : P.IsAtomIn U) : (suspension P).IsAtomIn U.susp := by
  obtain ⟨t, rfl⟩ := h.exists_eq_Iic
  exact ⟨isMoleculeIn_susp h.isMoleculeIn, susp t, susp_Iic t⟩

theorem IsPastingFactorOf.susp {X : LowerSet P} (h : P.IsPastingFactorOf X U) :
    (suspension P).IsPastingFactorOf X.susp U.susp := by
  obtain ⟨k, α, Y, hp, hX, hY⟩ := h
  refine ⟨k + 1, α, Y.susp, ?_, isMoleculeIn_susp hX, isMoleculeIn_susp hY⟩
  cases α
  · exact isPastingIn_susp hp (hp.inf_eq_output ▸ (hX.boundary k true).nonempty)
  · exact isPastingIn_susp hp (hp.inf_eq_output ▸ (hY.boundary k true).nonempty)

theorem IsSubmoleculeOf.susp {X : LowerSet P} (h : P.IsSubmoleculeOf X U) :
    (suspension P).IsSubmoleculeOf X.susp U.susp :=
  ⟨isMoleculeIn_susp h.1, h.2.lift _ fun _ _ hf => hf.susp⟩

theorem IsRewritableSubmolecule.susp (h : P.IsRewritableSubmolecule V U) :
    (suspension P).IsRewritableSubmolecule V.susp U.susp where
  isSubmoleculeOf := h.isSubmoleculeOf.susp
  krullDim_eq := by
    rw [krullDim_susp h.isSubmoleculeOf.isMoleculeIn.nonempty,
      krullDim_susp h.isSubmoleculeOf.isMoleculeIn_right.nonempty, h.krullDim_eq]
  isRound := isRound_susp h.isRound fun n α =>
    (h.isSubmoleculeOf.isMoleculeIn.boundary n α).nonempty

theorem susp_mem_interior_susp (hV : IsMoleculeIn P V) {x : P} :
    susp x ∈ (suspension P).interior V.susp ↔ x ∈ P.interior V := by
  rw [OGP.mem_interior, OGP.mem_interior, (isMoleculeIn_susp hV).properBoundary_eq_bdryFull,
    hV.properBoundary_eq_bdryFull, bdryFull_susp hV, susp_mem_susp, susp_mem_susp]

theorem pole_notMem_interior_susp (hV : IsMoleculeIn P V) (β : Bool) :
    pole β ∉ (suspension P).interior V.susp := by
  rw [OGP.mem_interior, (isMoleculeIn_susp hV).properBoundary_eq_bdryFull, bdryFull_susp hV]
  exact fun h => h.2 (pole_mem_susp _ β)

theorem isMolecule_suspension (P : OGP.{u}) (h : IsMolecule P) : IsMolecule (suspension P) := by
  have h' := isMoleculeIn_susp h
  rwa [susp_top] at h'

theorem isAtom_suspension (P : OGP.{u}) (h : IsAtom P) : IsAtom (suspension P) := by
  have h' := isAtomIn_susp h
  rwa [susp_top] at h'

theorem isAtom_globe (n : ℕ) : IsAtom (globe.{u} n) := by
  induction n with
  | zero => exact isAtom_point
  | succ n ih => exact isAtom_suspension _ ih

theorem isRDC_globe (n : ℕ) : IsRDC (globe.{u} n) :=
  isRDC_of_isMolecule (isAtom_globe n).1

end Atoms.Molecule.OGP
