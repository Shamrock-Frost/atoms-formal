import Atoms.Shape.MarkedHorn
import Atoms.Shape.GrayTensorHorn

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

section Staircase

variable {α : Bool} {i e : ℕ} {M L N : LowerSet P} {V : LowerSet Q}

abbrev staircaseStage (α : Bool) (i : ℕ) (M N : LowerSet P) (V : LowerSet Q) (ℓ : ℕ) :
    LowerSet (grayProduct P Q) :=
  M ×ˢ V ⊔ (grayProduct P Q).boundary (N ×ˢ V) (i + ℓ) (!α)

abbrev staircasePiece (α : Bool) (i : ℕ) (L N : LowerSet P) (V : LowerSet Q) (ℓ : ℕ) :
    LowerSet (grayProduct P Q) :=
  L ×ˢ Q.boundary V ℓ (xor i.bodd α) ⊔ (grayProduct P Q).boundary (N ×ˢ V) (i + ℓ) α

private theorem xor_bodd_succ_not : xor (i + 1).bodd (!α) = xor i.bodd α := by
  cases h : i.bodd <;> cases α <;> simp [Nat.bodd_succ, h]

private theorem bodd_add_add_self (ℓ : ℕ) : (i + ℓ + ℓ).bodd = i.bodd := by
  rw [Nat.add_assoc, Nat.bodd_add, ← Nat.two_mul, Nat.bodd_mul]
  simp

variable (hM : IsMoleculeIn P M) (hL : IsMoleculeIn P L) (hV : IsMoleculeIn Q V)
  (hp : P.IsPastingIn i (cond α M L) (cond α L M) N) (hdL : krullDim L ≤ (i + 1 : ℕ))
include hM hL hV hp

omit hV in
private theorem staircase_p1 : ∀ j ≤ i, P.boundary N j (!α) = P.boundary M j (!α) := fun _ hj =>
  ((isPastingIn_cond_comm α).1 hp).boundary_eq_of_le_cond (!α) hL.isGlobular hM.isGlobular hj

omit hV in
include hdL in
private theorem staircase_p2 : ∀ j, i < j → P.boundary N j (!α) = L ⊔ P.boundary M j (!α) :=
  fun j hj => by
    rw [hp.boundary_eq_sup_of_lt_cond α hM.isGlobular hL.isGlobular hj,
      boundary_eq_self (hdL.trans (by exact_mod_cast hj)), sup_comm]

include hdL in
theorem staircaseStage_succ (ℓ : ℕ) :
    staircaseStage α i M N V (ℓ + 1) = M ×ˢ V ⊔ L ×ˢ Q.boundary V ℓ (xor i.bodd α) := by
  have h := boundary_prod_eq_prod_sup_of_le (ℓ := ℓ) hM.isGlobular
    (hp.isGlobular (Bool.cond_rec_prop α hM.isGlobular hL.isGlobular)
      (Bool.cond_rec_prop α hL.isGlobular hM.isGlobular)) hV.isGlobular
    (staircase_p1 hM hL hp) (staircase_p2 hM hL hp hdL)
  rw [xor_bodd_succ_not, show i + 1 + ℓ = i + (ℓ + 1) by omega] at h
  rw [staircaseStage, h]
  exact le_antisymm (sup_le le_sup_left (sup_le le_sup_right
    (le_sup_of_le_left (boundary_le _ _ _)))) (sup_le le_sup_left (le_sup_of_le_right le_sup_left))

theorem staircaseStage_zero : staircaseStage α i M N V 0 = M ×ˢ V := by
  have h := boundary_prod_cond_left_of_le (!α) hL.isGlobular hM.isGlobular hV.isGlobular
    ((isPastingIn_cond_comm α).1 hp) le_rfl
  rw [staircaseStage, Nat.add_zero, ← h]
  exact sup_eq_left.2 (boundary_le _ _ _)

include hdL in
theorem staircaseStage_last (hdV : krullDim V ≤ e) :
    staircaseStage α i M N V (e + 1) = N ×ˢ V := by
  rw [staircaseStage_succ hM hL hV hp hdL, boundary_eq_self hdV, ← LowerSet.sup_prod,
    ((isPastingIn_cond_iff α).1 hp).1]

omit hM hL hV in
private theorem staircase_inf (ℓ : ℕ) :
    L ×ˢ Q.boundary V ℓ (xor i.bodd α) ⊓ M ×ˢ V =
      P.boundary L i (!α) ×ˢ Q.boundary V ℓ (xor i.bodd α) := by
  rw [LowerSet.prod_inf_prod, inf_eq_left.2 (boundary_le V _ _), inf_comm,
    ((isPastingIn_cond_iff α).1 hp).2.1]

omit hM in
private theorem staircase_inf_le_left (ℓ : ℕ) :
    L ×ˢ Q.boundary V ℓ (xor i.bodd α) ⊓ M ×ˢ V ≤
      (grayProduct P Q).boundary (L ×ˢ Q.boundary V ℓ (xor i.bodd α)) (i + ℓ) (!α) := by
  have h := (isSubmoleculeOf_prod_boundary_boundary hL (hV.boundary ℓ (xor i.bodd α))
    (Nat.le_add_right i ℓ) (!α)).le
  rwa [Nat.add_sub_cancel_left, boundary_eq_self (krullDim_boundary_le V ℓ _),
    ← staircase_inf hp] at h

omit hL in
private theorem staircase_inf_le_right (ℓ : ℕ) :
    L ×ˢ Q.boundary V ℓ (xor i.bodd α) ⊓ M ×ˢ V ≤
      (grayProduct P Q).boundary (M ×ˢ V) (i + ℓ) α := by
  have h := (isSubmoleculeOf_prod_boundary_boundary hM hV (Nat.le_add_right i ℓ) α).le
  rwa [Nat.add_sub_cancel_left, ← ((isPastingIn_cond_iff α).1 hp).2.2,
    ((isPastingIn_cond_iff α).1 hp).2.1, ← staircase_inf hp] at h

theorem isMoleculeIn_staircasePiece (ℓ : ℕ) :
    IsMoleculeIn (grayProduct P Q) (staircasePiece α i L N V ℓ) := by
  have hX := isMoleculeIn_prod hL (hV.boundary ℓ (xor i.bodd α))
  have h1 := isSubmoleculeOf_boundary_prod_boundary_right hL hV (i + ℓ) ℓ α
  rw [bodd_add_add_self (i := i)] at h1
  have h2 := isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn α hM hL hV hp (i + ℓ)
  have hXZ := (isSubmoleculeOf_prod_right hL (hV.boundary_isSubmoleculeOf ℓ (xor i.bodd α))).trans
    (isSubmoleculeOf_prod_cond_left α hM hL hV hp)
  exact (IsSubmoleculeOf.isSubmoleculeOf_sup (h1.trans h2) hX (krullDim_boundary_le _ _ _)
    (hXZ.inf_boundary_le _ _)).isMoleculeIn_right

theorem isMoleculeIn_staircaseStage (ℓ : ℕ) :
    IsMoleculeIn (grayProduct P Q) (staircaseStage α i M N V ℓ) := by
  have hp' := (isPastingIn_cond_comm α).1 hp
  have h1 := isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn (!α) hL hM hV hp' (i + ℓ)
  have hMZ := isSubmoleculeOf_prod_cond_left (!α) hL hM hV hp'
  exact (IsSubmoleculeOf.isSubmoleculeOf_sup h1 (isMoleculeIn_prod hM hV)
    (krullDim_boundary_le _ _ _) (hMZ.inf_boundary_le _ _)).isMoleculeIn_right

include hdL in
private theorem isPastingIn_staircase_of {ℓ : ℕ}
    (hb : ∀ γ, (grayProduct P Q).boundary (staircaseStage α i M N V (ℓ + 1)) (i + ℓ) γ =
      (grayProduct P Q).boundary (N ×ˢ V) (i + ℓ) γ) :
    (grayProduct P Q).IsPastingIn (i + ℓ)
      (cond α (staircaseStage α i M N V ℓ) (staircasePiece α i L N V ℓ))
      (cond α (staircasePiece α i L N V ℓ) (staircaseStage α i M N V ℓ))
      (staircaseStage α i M N V (ℓ + 1)) := by
  have h := isPastingIn_sup_boundary_cond (P := grayProduct P Q) α (k := i + ℓ)
    (staircase_inf_le_left hL hV hp ℓ) (staircase_inf_le_right hM hV hp ℓ)
  rw [← sup_comm (M ×ˢ V), ← staircaseStage_succ hM hL hV hp hdL, hb, hb] at h
  exact h

include hdL in
private theorem boundary_staircaseStage (hdV : krullDim V ≤ e) :
    ∀ r ℓ, ℓ + r = e + 1 → ∀ c < i + ℓ, ∀ γ,
      (grayProduct P Q).boundary (staircaseStage α i M N V ℓ) c γ =
        (grayProduct P Q).boundary (N ×ˢ V) c γ := by
  intro r
  induction r with
  | zero =>
    intro ℓ hℓ c _ γ
    rw [Nat.add_zero] at hℓ
    rw [hℓ, staircaseStage_last hM hL hV hp hdL hdV]
  | succ r ih =>
    intro ℓ hℓ c hc γ
    have hS := ih (ℓ + 1) (by omega)
    have hpst := isPastingIn_staircase_of hM hL hV hp hdL (ℓ := ℓ)
      (fun γ => hS (i + ℓ) (by omega) γ)
    have gS := (isMoleculeIn_staircaseStage hM hL hV hp ℓ).isGlobular
    have gD := (isMoleculeIn_staircasePiece hM hL hV hp ℓ).isGlobular
    rw [hpst.boundary_eq_boundary_of_lt_cond α gS gD hc γ,
      ← hpst.boundary_eq_of_lt_cond α gS gD hc γ, hS c (by omega) γ]

include hdL in
theorem isPastingIn_staircase (hdV : krullDim V ≤ e) {ℓ : ℕ} (hℓ : ℓ ≤ e) :
    (grayProduct P Q).IsPastingIn (i + ℓ)
      (cond α (staircaseStage α i M N V ℓ) (staircasePiece α i L N V ℓ))
      (cond α (staircasePiece α i L N V ℓ) (staircaseStage α i M N V ℓ))
      (staircaseStage α i M N V (ℓ + 1)) :=
  isPastingIn_staircase_of hM hL hV hp hdL fun γ =>
    boundary_staircaseStage hM hL hV hp hdL hdV (e - ℓ) (ℓ + 1) (by omega) _ (by omega) γ

omit hM hL hV hp in
include hdL in
private theorem krullDim_staircasePiece_le (ℓ : ℕ) :
    krullDim (staircasePiece α i L N V ℓ) ≤ (i + 1 + ℓ : ℕ) := by
  rw [LowerSet.krullDim_sup]
  exact sup_le (krullDim_prod_le hdL (krullDim_boundary_le V ℓ _))
    ((krullDim_boundary_le _ _ _).trans (by exact_mod_cast (show i + ℓ ≤ i + 1 + ℓ by omega)))

include hdL in
theorem exists_isStagedPasting_staircase (hdV : krullDim V ≤ e) {m : ℕ}
    {Y : LowerSet (grayProduct P Q)} {L₀ R₀ M₀ : ℕ → LowerSet (grayProduct P Q)}
    (hs : (grayProduct P Q).IsStagedPasting m Y L₀ R₀ M₀) (hM₀ : M₀ m = M ×ˢ V)
    {T : grayProduct P Q → Prop} (hT : StagedTops m L₀ R₀ T) :
    ∀ t ≤ e + 1, i + t ≤ m → ∃ L' R' M' : ℕ → LowerSet (grayProduct P Q),
      (grayProduct P Q).IsStagedPasting m Y L' R' M' ∧ M' m = staircaseStage α i M N V t ∧
      StagedTops m L' R' (fun z => T z ∨ (z.1 ∈ L ∧ grade ℕ z.1 = i + 1 ∧
        ∃ ℓ < t, z.2 ∈ Q.boundary V ℓ (xor i.bodd α))) := by
  intro t
  induction t with
  | zero =>
    intro _ _
    exact ⟨L₀, R₀, M₀, hs, hM₀.trans (staircaseStage_zero hM hL hV hp).symm,
      hT.mono fun _ h => Or.inl h⟩
  | succ t ih =>
    intro ht htm
    obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ := ih (by omega) (by omega)
    have ht₁' := ht₁.mono (T' := fun z => T z ∨ (z.1 ∈ L ∧ grade ℕ z.1 = i + 1 ∧
        ∃ ℓ < t + 1, z.2 ∈ Q.boundary V ℓ (xor i.bodd α))) fun z h => h.imp_right
      fun ⟨h1, h2, ℓ, hℓ, h3⟩ => ⟨h1, h2, ℓ, by omega, h3⟩
    refine exists_isStagedPasting_tops _ α m hs₁ ht₁' (isMoleculeIn_staircasePiece hM hL hV hp t)
      ((krullDim_staircasePiece_le hdL t).trans (by exact_mod_cast (show i + 1 + t ≤ m by omega)))
      (j := i + t) (by omega)
      (by rw [hM₁]; exact isPastingIn_staircase hM hL hV hp hdL hdV (ℓ := t) (by omega))
      fun l hl _ y hy hyd => ?_
    rcases LowerSet.mem_sup_iff.1 (boundary_le _ l _ hy) with hy' | hy'
    · rw [LowerSet.mem_prod] at hy'
      have h1 : grade ℕ y.1 ≤ i + 1 := krullDim_le_coe_iff.1 hdL ⟨y.1, hy'.1⟩
      have h2 : grade ℕ y.2 ≤ t := grade_le_of_mem_boundary hy'.2
      have h3 : grade ℕ y = grade ℕ y.1 + grade ℕ y.2 := rfl
      exact Or.inr ⟨hy'.1, by omega, t, Nat.lt_succ_self t, hy'.2⟩
    · have := grade_le_of_mem_boundary hy'
      omega

end Staircase

section Product

variable {U X : LowerSet P} {V : LowerSet Q} {k d : ℕ} {L R M : ℕ → LowerSet P}

private theorem exists_isStagedPasting_prod_stage (hV : IsMoleculeIn Q V)
    (hdV : krullDim V ≤ d) (hs : P.IsStagedPasting k X L R M) {T : P → Prop}
    (ht : StagedTops k L R T) :
    ∀ j ≤ k, ∃ L' R' M' : ℕ → LowerSet (grayProduct P Q),
      (grayProduct P Q).IsStagedPasting (k + d) (X ×ˢ V) L' R' M' ∧
      M' (k + d) = M j ×ˢ V ∧ StagedTops (k + d) L' R' (fun z => T z.1) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hX : IsMoleculeIn P X := hs.stage_zero ▸ hs.isMoleculeIn_stage 0 (Nat.zero_le k)
    refine ⟨_, _, _, isStagedPasting_self (isMoleculeIn_prod hX hV) (k + d),
      by rw [hs.stage_zero], fun i _ y hy hyd => ?_⟩
    rcases hy with hy | hy <;> have := grade_le_of_mem_boundary hy <;> omega
  | succ j ih =>
    intro hj
    obtain ⟨L₀, R₀, M₀, hs₀, hM₀, ht₀⟩ := ih (by omega)
    obtain ⟨h1, h2⟩ := hs.stage_succ j (by omega)
    obtain ⟨hL, dL⟩ := hs.isMoleculeIn_left j (by omega)
    obtain ⟨hR, dR⟩ := hs.isMoleculeIn_right j (by omega)
    have hMj := hs.isMoleculeIn_stage j (by omega)
    have h1' : P.IsPastingIn j (cond false (M j) (L (j + 1))) (cond false (L (j + 1)) (M j))
        (L (j + 1) ⊔ M j) := h1
    have h2' : P.IsPastingIn j (cond true (L (j + 1) ⊔ M j) (R (j + 1)))
        (cond true (R (j + 1)) (L (j + 1) ⊔ M j)) (M (j + 1)) := h2
    obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ := exists_isStagedPasting_staircase hMj hL hV h1' dL hdV
      hs₀ hM₀ ht₀ (d + 1) le_rfl (by omega)
    rw [staircaseStage_last hMj hL hV h1' dL hdV] at hM₁
    obtain ⟨L₂, R₂, M₂, hs₂, hM₂, ht₂⟩ := exists_isStagedPasting_staircase
      (h1.isMoleculeIn hL hMj) hR hV h2' dR hdV hs₁ hM₁
      (ht₁.mono fun z h => h.elim id fun h' => ht j (by omega) z.1 (Or.inl h'.1) h'.2.1)
      (d + 1) le_rfl (by omega)
    rw [staircaseStage_last (h1.isMoleculeIn hL hMj) hR hV h2' dR hdV] at hM₂
    exact ⟨L₂, R₂, M₂, hs₂, hM₂,
      ht₂.mono fun z h => h.elim id fun h' => ht j (by omega) z.1 (Or.inr h'.1) h'.2.1⟩

theorem exists_isStagedPasting_grayProduct_left (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V)
    (hdU : krullDim U ≤ (k + 1 : ℕ)) (hdV : krullDim V ≤ d) {α : Bool}
    (hs : P.IsStagedPasting k X L R M) (hM : M k = P.boundary U k α) {T : P → Prop}
    (ht : StagedTops k L R T) :
    ∃ L' R' M' : ℕ → LowerSet (grayProduct P Q),
      (grayProduct P Q).IsStagedPasting (k + d) (X ×ˢ V) L' R' M' ∧
      M' (k + d) = (grayProduct P Q).boundary (U ×ˢ V) (k + d) α ∧
      StagedTops (k + d) L' R' (fun z => T z.1 ∨ (z.1 ∈ U ∧ grade ℕ z.1 = k + 1 ∧
        ∃ ℓ < d, z.2 ∈ Q.boundary V ℓ (xor k.bodd (!α)))) := by
  obtain ⟨L₀, R₀, M₀, hs₀, hM₀, ht₀⟩ := exists_isStagedPasting_prod_stage hV hdV hs ht k le_rfl
  rw [hM] at hM₀
  have hp : P.IsPastingIn k (cond (!α) (P.boundary U k α) U)
      (cond (!α) U (P.boundary U k α)) U := by
    cases α
    · exact isPastingIn_boundary_false_self U k
    · exact isPastingIn_self_boundary_true U k
  obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ := exists_isStagedPasting_staircase (hU.boundary k α) hU hV
    hp hdU hdV hs₀ hM₀ ht₀ d (Nat.le_succ d) le_rfl
  have hsub := (isSubmoleculeOf_prod_boundary_boundary hU hV (Nat.le_add_right k d) α).le
  rw [Nat.add_sub_cancel_left, boundary_eq_self hdV] at hsub
  rw [staircaseStage, Bool.not_not, sup_eq_right.2 hsub] at hM₁
  exact ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩

end Product

end Atoms.Molecule.OGP

namespace Atoms.Shape

namespace MarkedHornData

variable (h : MarkedHornData) (V : Atom)

def grayTensorFace : (Atom.grayTensor h.atom V).ogp :=
  (Atom.grayTensorIso h.atom V).hom (h.face, V.top)

def grayTensorMarking (marked : Bool) : Set (Atom.grayTensor h.atom V).ogp :=
  {w | ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.marking ∨
    (((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.targetMarking ∧
      ((Atom.grayTensorIso h.atom V).inv w).2 ∈ V.ogp.bdryFull ⊤) ∨
    (marked = true ∧ ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet ∧
      ((Atom.grayTensorIso h.atom V).inv w).2 = V.top)}

theorem Iic_grayTensorFace :
    LowerSet.Iic (h.grayTensorFace V) =
      map (Atom.grayTensorIso h.atom V).hom (LowerSet.Iic h.face ×ˢ (⊤ : LowerSet V.ogp)) := by
  rw [grayTensorFace, ← map_Iic, Iic_grayProduct, V.Iic_top]

theorem dimension_grayTensor_sub_one :
    (Atom.grayTensor h.atom V).dimension - 1 = h.atom.dimension - 1 + V.dimension := by
  have := h.positive
  rw [Atom.dimension_grayTensor]
  omega

theorem exists_isStagedPasting_grayTensorRight :
    ∃ L R M : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp,
      (Atom.grayTensor h.atom V).ogp.IsStagedPasting ((Atom.grayTensor h.atom V).dimension - 1)
        (.Iic (h.grayTensorFace V)) L R M ∧
      M ((Atom.grayTensor h.atom V).dimension - 1) =
        (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side ∧
      ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
        grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false := by
  have hpos := h.positive
  set e := Atom.grayTensorIso h.atom V with he
  have hU := h.atom.toMoleculeShape.krullDim_top_eq (n := h.atom.dimension - 1)
    (Nat.sub_add_cancel hpos).symm
  have hdV : krullDim (⊤ : LowerSet V.ogp) ≤ (V.dimension : ℕ) := by
    rw [LowerSet.krullDim_top, V.krullDim_eq_dimension]
  have hM : h.stage (h.atom.dimension - 1) =
      h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side := by
    rw [h.stage_last, h.atom.bdry_top_eq_boundary hpos]
  obtain ⟨L, R, M, hs, hM', ht⟩ := OGP.exists_isStagedPasting_grayProduct_left (Q := V.ogp)
    h.atom.isMolecule V.isMolecule hU.le hdV h.staged hM h.marked_tops
  have hW : 0 < (Atom.grayTensor h.atom V).dimension :=
    (h.toHornData.grayTensorRight V).positive
  refine ⟨fun i => map e.hom (L i), fun i => map e.hom (R i), fun i => map e.hom (M i), ?_, ?_,
    fun i hi y hy hyd => ?_⟩
  · rw [dimension_grayTensor_sub_one, Iic_grayTensorFace]
    exact hs.map e.hom
  · dsimp only
    rw [dimension_grayTensor_sub_one, hM', (Atom.grayTensor h.atom V).bdry_top_eq_boundary hW,
      dimension_grayTensor_sub_one, map_boundary, LowerSet.top_prod_top, map_top_of_isIso]
  · rw [← OGP.map_sup] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hgz : grade ℕ z = i + 1 := ((isMorphism e.hom).grade_eq z).symm.trans hyd
    rw [dimension_grayTensor_sub_one] at hi
    rw [grayTensorMarking, Set.mem_ofPred_eq, he, Iso.hom_inv_id_apply]
    rcases ht i hi z hz hgz with hm | ⟨-, hzd, ℓ, hℓ, hz2⟩
    · exact Or.inl hm
    · refine Or.inr (Or.inl ⟨h.mem_targetMarking_iff.2 (Or.inl (GradeOrder.eq_of_le_of_grade_le
        (h.atom.le_top _) (by rw [← h.atom.dimension_eq]; omega))), ?_⟩)
      refine (V.mem_bdryFull_top_iff _).2 fun h2 => ?_
      have := grade_le_of_mem_boundary hz2
      rw [h2, ← V.dimension_eq] at this
      omega

theorem grayTensorFace_mem_faces :
    h.grayTensorFace V ∈
      (Atom.grayTensor h.atom V).ogp.faces h.side (Atom.grayTensor h.atom V).top := by
  obtain ⟨L, R, M, hs, hM, -⟩ := h.exists_isStagedPasting_grayTensorRight V
  have hx := hs.stage_le 0 _ (Nat.zero_le _) le_rfl
    (hs.stage_zero ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  rw [hM, ← (Atom.grayTensor h.atom V).Iic_top] at hx
  refine mem_faces_of_mem_bdry_Iic hx ?_
  have h1 : grade ℕ (h.grayTensorFace V) = grade ℕ h.face + grade ℕ V.top :=
    (isMorphism (Atom.grayTensorIso h.atom V).hom).grade_eq _
  rw [h1, ← (Atom.grayTensor h.atom V).dimension_eq, Atom.dimension_grayTensor,
    ← V.dimension_eq, ← h.dim_face_add_one]
  omega

theorem mem_hornSet_grayTensorFace {w : (Atom.grayTensor h.atom V).ogp}
    (hw : ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet ∨
      ((Atom.grayTensorIso h.atom V).inv w).2 ∈ V.ogp.bdryFull ⊤) :
    w ∈ ((Atom.grayTensor h.atom V).isRewritableSubmolecule_Iic_of_mem_faces
        (h.grayTensorFace_mem_faces V)).hornSet (Atom.grayTensor h.atom V).isMolecule
        (Atom.grayTensor h.atom V).isAtom.isRound := by
  have hne : (Atom.grayTensorIso h.atom V).inv w ≠ (h.atom.top, V.top) ∧
      (Atom.grayTensorIso h.atom V).inv w ≠ (h.face, V.top) := by
    rcases hw with hw | hw
    · obtain ⟨hb, hf⟩ := h.mem_hornSet_iff.1 hw
      exact ⟨fun e => (h.atom.mem_bdryFull_top_iff _).1 hb (congrArg Prod.fst e),
        fun e => hf (congrArg Prod.fst e)⟩
    · exact ⟨fun e => (V.mem_bdryFull_top_iff _).1 hw (congrArg Prod.snd e),
        fun e => (V.mem_bdryFull_top_iff _).1 hw (congrArg Prod.snd e)⟩
  refine (mem_hornSet_closure_singleton_iff ⟨Atom.grayTensor h.atom V,
    (h.toHornData.grayTensorRight V).positive, h.side, .Iic (h.grayTensorFace V),
    (Atom.grayTensor h.atom V).isRewritableSubmolecule_Iic_of_mem_faces
      (h.grayTensorFace_mem_faces V)⟩ rfl).2 ⟨fun e => hne.1 ?_, fun e => hne.2 ?_⟩
  · rw [e, Atom.grayTensorIso_inv_top]
  · rw [e, grayTensorFace, Iso.hom_inv_id_apply]

theorem grayTensorMarking_false_subset (marked : Bool) :
    h.grayTensorMarking V false ⊆ h.grayTensorMarking V marked := by
  rintro w (hw | hw | ⟨hw, -⟩)
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact absurd hw Bool.false_ne_true

theorem grayTensorMarking_mem {marked : Bool} (hV : marked = true → 0 < V.dimension) :
    ∀ w ∈ h.grayTensorMarking V marked,
      w ∈ ((Atom.grayTensor h.atom V).isRewritableSubmolecule_Iic_of_mem_faces
          (h.grayTensorFace_mem_faces V)).hornSet (Atom.grayTensor h.atom V).isMolecule
          (Atom.grayTensor h.atom V).isAtom.isRound ∧ 0 < grade ℕ w := by
  intro w hw
  have hg : grade ℕ w = grade ℕ ((Atom.grayTensorIso h.atom V).inv w).1 +
      grade ℕ ((Atom.grayTensorIso h.atom V).inv w).2 :=
    ((isMorphism (Atom.grayTensorIso h.atom V).inv).grade_eq w).symm
  rcases hw with hw | ⟨hw, hw'⟩ | ⟨hm, hw, hw'⟩
  · exact ⟨h.mem_hornSet_grayTensorFace V (Or.inl (h.marking_mem _ hw).1),
      by have := (h.marking_mem _ hw).2; omega⟩
  · exact ⟨h.mem_hornSet_grayTensorFace V (Or.inr hw'),
      by have := (h.targetMarking_mem _ hw).2; omega⟩
  · refine ⟨h.mem_hornSet_grayTensorFace V (Or.inl hw), ?_⟩
    have := hV hm
    rw [hw', ← V.dimension_eq] at hg
    omega

def grayTensorRight (marked : Bool) (hV : marked = true → 0 < V.dimension)
    (L R M : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp)
    (staged : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
      ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R M)
    (stage_last : M ((Atom.grayTensor h.atom V).dimension - 1) =
      (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side)
    (tops : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
      grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false) : MarkedHornData where
  atom := Atom.grayTensor h.atom V
  positive := (h.toHornData.grayTensorRight V).positive
  side := h.side
  face := h.grayTensorFace V
  face_mem := h.grayTensorFace_mem_faces V
  marking := h.grayTensorMarking V marked
  marking_mem := h.grayTensorMarking_mem V hV
  left := L
  right := R
  stage := M
  staged := staged
  stage_last := stage_last
  marked_tops i hi y hy hyd := h.grayTensorMarking_false_subset V marked (tops i hi y hy hyd)

section GrayTensorRight

variable {marked : Bool} {hV : marked = true → 0 < V.dimension}
  {L R M : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp}
  {hs : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
    ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R M}
  {hM : M ((Atom.grayTensor h.atom V).dimension - 1) = (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side}
  {ht : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false}

theorem toHornData_grayTensorRight :
    (h.grayTensorRight V marked hV L R M hs hM ht).toHornData = h.toHornData.grayTensorRight V :=
  HornData.eq_of_removed_eq (h.toHornData.grayTensorRight V) _ _ (h.Iic_grayTensorFace V).symm

theorem mem_hornSet_grayTensorRight_iff {w : (Atom.grayTensor h.atom V).ogp} :
    w ∈ (h.grayTensorRight V marked hV L R M hs hM ht).hornSet ↔
      ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet ∨
        ((Atom.grayTensorIso h.atom V).inv w).2 ∈ V.ogp.bdryFull ⊤ := by
  refine ((h.grayTensorRight V marked hV L R M hs hM ht).mem_hornSet_iff).trans ?_
  change w ∈ (Atom.grayTensor h.atom V).ogp.bdryFull ⊤ ∧ w ≠ h.grayTensorFace V ↔ _
  have hw : w = (Atom.grayTensorIso h.atom V).hom ((Atom.grayTensorIso h.atom V).inv w) :=
    (Iso.inv_hom_id_apply _ w).symm
  have htop : (Atom.grayTensor h.atom V).top =
      (Atom.grayTensorIso h.atom V).hom (h.atom.top, V.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  have hinj : Function.Injective (Atom.grayTensorIso h.atom V).hom :=
    Function.LeftInverse.injective (Iso.hom_inv_id_apply _)
  rw [(Atom.grayTensor h.atom V).mem_bdryFull_top_iff, h.mem_hornSet_iff,
    h.atom.mem_bdryFull_top_iff, V.mem_bdryFull_top_iff, grayTensorFace, htop, hw, hinj.ne_iff,
    hinj.ne_iff, Iso.hom_inv_id_apply]
  set e := Atom.grayTensorIso h.atom V
  by_cases h2 : (e.inv w).2 = V.top
  · rw [← h2]
    exact ⟨fun ⟨h3, h4⟩ => Or.inl ⟨fun h5 => h3 (Prod.ext h5 rfl), fun h5 => h4 (Prod.ext h5 rfl)⟩,
      fun h3 => h3.elim (fun ⟨h4, h5⟩ => ⟨fun h6 => h4 (congrArg Prod.fst h6),
        fun h6 => h5 (congrArg Prod.fst h6)⟩) fun h4 => absurd rfl h4⟩
  · exact ⟨fun _ => Or.inr h2, fun _ => ⟨fun h3 => h2 (congrArg Prod.snd h3),
      fun h3 => h2 (congrArg Prod.snd h3)⟩⟩

private theorem mem_faces_grayTensor_top {β : Bool} {z : (Atom.grayTensor h.atom V).ogp} :
    z ∈ (Atom.grayTensor h.atom V).ogp.faces β (Atom.grayTensor h.atom V).top ↔
      ((Atom.grayTensorIso h.atom V).inv z).1 ∈ h.atom.ogp.faces β h.atom.top ∧
          ((Atom.grayTensorIso h.atom V).inv z).2 = V.top ∨
        ((Atom.grayTensorIso h.atom V).inv z).1 = h.atom.top ∧
          ((Atom.grayTensorIso h.atom V).inv z).2 ∈
            V.ogp.faces (xor (grade ℕ h.atom.top).bodd β) V.top := by
  set e := Atom.grayTensorIso h.atom V
  have hz : z = e.hom (e.inv z) := (Iso.inv_hom_id_apply e z).symm
  have htop : (Atom.grayTensor h.atom V).top = e.hom (h.atom.top, V.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  rw [hz, htop, (isMorphism e.hom).mem_faces_iff_of_injective
    (Function.LeftInverse.injective (Iso.hom_inv_id_apply e)), mem_faces_grayProduct,
    Iso.hom_inv_id_apply]

theorem mem_targetMarking_grayTensorRight_iff {w : (Atom.grayTensor h.atom V).ogp} :
    w ∈ (h.grayTensorRight V marked hV L R M hs hM ht).targetMarking ↔
      ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.targetMarking ∨
        (marked = true ∧ ((Atom.grayTensorIso h.atom V).inv w).2 = V.top) := by
  have hw : w = (Atom.grayTensorIso h.atom V).hom ((Atom.grayTensorIso h.atom V).inv w) :=
    (Iso.inv_hom_id_apply _ w).symm
  have htop : (Atom.grayTensor h.atom V).top =
      (Atom.grayTensorIso h.atom V).hom (h.atom.top, V.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  have hpair (y : h.atom.ogp) : (Atom.grayTensorIso h.atom V).hom (y, V.top) ∈
      h.grayTensorMarking V marked ↔ y ∈ h.marking ∨ (marked = true ∧ y ∈ h.hornSet) := by
    rw [grayTensorMarking, Set.mem_ofPred_eq, Iso.hom_inv_id_apply]
    refine ⟨fun hy => ?_, fun hy => hy.elim Or.inl fun ⟨hm, hy⟩ => Or.inr (Or.inr ⟨hm, hy, rfl⟩)⟩
    rcases hy with hy | ⟨-, hy⟩ | ⟨hm, hy, -⟩
    · exact Or.inl hy
    · exact absurd rfl ((V.mem_bdryFull_top_iff _).1 hy)
    · exact Or.inr ⟨hm, hy⟩
  have hfaces (hy : ∀ y ∈ h.atom.ogp.faces (!h.side) h.atom.top, y ∈ h.marking ∨ marked = true) :
      (Atom.grayTensor h.atom V).ogp.faces (!h.side) (Atom.grayTensor h.atom V).top ⊆
        h.grayTensorMarking V marked := by
    intro z hz
    rcases (h.mem_faces_grayTensor_top V).1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz' : z = (Atom.grayTensorIso h.atom V).hom (((Atom.grayTensorIso h.atom V).inv z).1,
          V.top) := (Iso.inv_hom_id_apply _ z).symm.trans (congrArg _ (Prod.ext rfl h2))
      rw [hz', hpair]
      refine (hy _ h1).imp_right fun hm => ⟨hm, h.mem_hornSet_iff.2
        ⟨(h.atom.mem_bdryFull_top_iff _).2 (mem_faces.1 h1).1.ne, fun h3 => ?_⟩⟩
      exact Set.disjoint_left.1 (disjoint_faces _ h.side) h.face_mem (h3 ▸ h1)
    · exact Or.inr (Or.inl ⟨h.mem_targetMarking_iff.2 (Or.inl h1),
        (V.mem_bdryFull_top_iff _).2 (mem_faces.1 h2).1.ne⟩)
  refine ⟨fun hw' => ?_, fun hw' => ?_⟩
  · rcases (h.grayTensorRight V marked hV L R M hs hM ht).mem_targetMarking_iff.1 hw' with
      h1 | ⟨hsub, h1⟩ | h1
    · change w = (Atom.grayTensor h.atom V).top at h1
      rw [h1, Atom.grayTensorIso_inv_top]
      exact Or.inl (h.mem_targetMarking_iff.2 (Or.inl rfl))
    · change w = (Atom.grayTensorIso h.atom V).hom (h.face, V.top) at h1
      rw [h1, Iso.hom_inv_id_apply]
      by_cases hm : marked = true
      · exact Or.inr ⟨hm, rfl⟩
      refine Or.inl (h.mem_targetMarking_iff.2 (Or.inr (Or.inl ⟨fun y hy => ?_, rfl⟩)))
      have hz : (Atom.grayTensorIso h.atom V).hom (y, V.top) ∈ h.grayTensorMarking V marked :=
        hsub ((h.mem_faces_grayTensor_top V (β := !h.side)).2 (Or.inl (by
        rw [Iso.hom_inv_id_apply]
        exact ⟨hy, rfl⟩)))
      exact ((hpair y).1 hz).resolve_right fun h3 => hm h3.1
    · rcases h1 with h1 | ⟨h1, -⟩ | ⟨hm, -, h2⟩
      · exact Or.inl (h.mem_targetMarking_iff.2 (Or.inr (Or.inr h1)))
      · exact Or.inl h1
      · exact Or.inr ⟨hm, h2⟩
  refine (h.grayTensorRight V marked hV L R M hs hM ht).mem_targetMarking_iff.2 ?_
  rcases hw' with h1 | ⟨hm, h2⟩
  · by_cases h2 : ((Atom.grayTensorIso h.atom V).inv w).2 = V.top
    · rcases h.mem_targetMarking_iff.1 h1 with h3 | ⟨hsub, h3⟩ | h3
      · exact Or.inl (hw.trans ((congrArg _ (Prod.ext h3 h2)).trans htop.symm))
      · exact Or.inr (Or.inl ⟨hfaces fun _ hy => Or.inl (hsub hy),
          hw.trans (congrArg _ (Prod.ext h3 h2))⟩)
      · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, (V.mem_bdryFull_top_iff _).2 h2⟩)))
  · by_cases h3 : ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, h3, h2⟩)))
    by_cases h4 : ((Atom.grayTensorIso h.atom V).inv w).1 = h.face
    · exact Or.inr (Or.inl ⟨hfaces fun _ _ => Or.inr hm,
        hw.trans (congrArg _ (Prod.ext h4 h2))⟩)
    have h5 : ((Atom.grayTensorIso h.atom V).inv w).1 = h.atom.top := not_not.1 fun h5 =>
      h3 (h.mem_hornSet_iff.2 ⟨(h.atom.mem_bdryFull_top_iff _).2 h5, h4⟩)
    exact Or.inl (hw.trans ((congrArg _ (Prod.ext h5 h2)).trans htop.symm))

end GrayTensorRight

end MarkedHornData

end Atoms.Shape
