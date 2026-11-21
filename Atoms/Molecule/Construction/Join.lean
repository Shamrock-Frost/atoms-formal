import Atoms.Molecule.Construction.GrayProductMolecule

universe u

open Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

section BotSusp

variable {U : OGP.{u}}

def botSusp (U : OGP.{u}) : WithBot U → suspension U :=
  WithBot.recBotCoe (.pole true) .susp

@[simp] theorem botSusp_bot : botSusp U ⊥ = .pole true := rfl

@[simp] theorem botSusp_coe (x : U) : botSusp U (x : WithBot U) = .susp x :=
  rfl

@[simp] theorem botSusp_le_botSusp_iff {a b : WithBot U} : botSusp U a ≤ botSusp U b ↔ a ≤ b := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;> simp

theorem botSusp_injective : Function.Injective (botSusp U) := fun _ _ h =>
  le_antisymm (botSusp_le_botSusp_iff.1 h.le) (botSusp_le_botSusp_iff.1 h.ge)

@[simp] theorem grade_botSusp (a : WithBot U) : grade ℕ (botSusp U a) = grade ℕ a := by
  induction a using WithBot.recBotCoe <;> rfl

@[simp] theorem botSusp_mem_faces_iff {α : Bool} {a b : WithBot U} :
    botSusp U a ∈ (suspension U).faces α (botSusp U b) ↔ a ∈ (augmentation U).faces α b := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe
  · simp
  · rw [botSusp_bot, botSusp_coe, pole_mem_faces_suspension, bot_mem_faces_augmentation, eq_comm]
  · simp
  · exact susp_mem_faces_suspension.trans coe_mem_faces_augmentation.symm

theorem ne_pole_false_of_botSusp_le {a : WithBot U} {w : suspension U}
    (h : botSusp U a ≤ w) : w ≠ .pole false := by
  rintro rfl
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe x => exact not_susp_le_pole x false h

theorem exists_botSusp_eq {w : suspension U} (h : w ≠ .pole false) :
    ∃ a, botSusp U a = w := by
  rcases w with ⟨⟨⟩ | ⟨⟩⟩ | x
  exacts [absurd rfl h, ⟨⊥, rfl⟩, ⟨x, rfl⟩]

end BotSusp

section Injection

variable {P Q : OGP.{u}}

def joinToGray (P Q : OGP.{u}) (p : join P Q) :
    grayProduct (suspension P) (suspension Q) :=
  (botSusp P p.1.1, botSusp Q p.1.2)

theorem join_le_iff {p q : join P Q} : p ≤ q ↔ p.1.1 ≤ q.1.1 ∧ p.1.2 ≤ q.1.2 :=
  Iff.rfl

theorem grade_join (p : join P Q) :
    grade ℕ p = grade ℕ p.1.1 + grade ℕ p.1.2 - 1 := rfl

theorem one_le_grade_add_grade (p : join P Q) :
    1 ≤ grade ℕ p.1.1 + grade ℕ p.1.2 :=
  Nat.succ_le_of_lt (grade_strictMono (𝕆 := ℕ) (bot_lt_iff_ne_bot.2 p.2))

@[simp] theorem joinToGray_le_joinToGray_iff {p q : join P Q} :
    joinToGray P Q p ≤ joinToGray P Q q ↔ p ≤ q :=
  and_congr botSusp_le_botSusp_iff botSusp_le_botSusp_iff

theorem joinToGray_injective : Function.Injective (joinToGray P Q) := fun _ _ h =>
  le_antisymm (joinToGray_le_joinToGray_iff.1 h.le) (joinToGray_le_joinToGray_iff.1 h.ge)

@[simp] theorem joinToGray_lt_joinToGray_iff {p q : join P Q} :
    joinToGray P Q p < joinToGray P Q q ↔ p < q := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, joinToGray_le_joinToGray_iff,
    joinToGray_le_joinToGray_iff]

theorem grade_joinToGray (p : join P Q) :
    grade ℕ (joinToGray P Q p) = grade ℕ p + 1 := by
  have := one_le_grade_add_grade p
  change grade ℕ (botSusp P p.1.1) + grade ℕ (botSusp Q p.1.2) = _
  rw [grade_botSusp, grade_botSusp, grade_join]
  omega

theorem exists_joinToGray_eq_of_le {p : join P Q}
    {w : grayProduct (suspension P) (suspension Q)} (h : joinToGray P Q p ≤ w) :
    ∃ q, joinToGray P Q q = w := by
  obtain ⟨w₁, w₂⟩ := w
  obtain ⟨a, rfl⟩ := exists_botSusp_eq (ne_pole_false_of_botSusp_le h.1)
  obtain ⟨b, rfl⟩ := exists_botSusp_eq (ne_pole_false_of_botSusp_le h.2)
  have hne : (a, b) ≠ ((⊥, ⊥) : WithBot P × WithBot Q) := by
    rintro ⟨⟩
    exact p.2 (Prod.ext (le_bot_iff.1 (botSusp_le_botSusp_iff.1 h.1))
      (le_bot_iff.1 (botSusp_le_botSusp_iff.1 h.2)))
  exact ⟨⟨(a, b), hne⟩, rfl⟩

theorem joinToGray_covBy_joinToGray_iff {p q : join P Q} :
    joinToGray P Q q ⋖ joinToGray P Q p ↔ q ⋖ p :=
  Set.OrdConnected.apply_covBy_apply_iff
    (OrderEmbedding.ofMapLEIff (joinToGray P Q) fun _ _ => joinToGray_le_joinToGray_iff)
    (IsUpperSet.ordConnected fun _ _ hle ⟨_, hp⟩ => exists_joinToGray_eq_of_le (hp ▸ hle))

theorem joinToGray_mem_faces_iff {α : Bool} {z p : join P Q} :
    joinToGray P Q z ∈ (grayProduct (suspension P) (suspension Q)).faces α (joinToGray P Q p) ↔
      z ∈ (join P Q).faces α p := by
  rw [mem_faces_join, mem_faces_grayProduct, mem_faces_grayProduct]
  dsimp only [joinToGray]
  rw [botSusp_mem_faces_iff, botSusp_injective.eq_iff, botSusp_injective.eq_iff,
    grade_botSusp, botSusp_mem_faces_iff]

def grayBot (P Q : OGP.{u}) : grayProduct (suspension P) (suspension Q) :=
  (.pole true, .pole true)

theorem grayBot_le_joinToGray (p : join P Q) : grayBot P Q ≤ joinToGray P Q p :=
  ⟨botSusp_le_botSusp_iff.2 (bot_le (a := p.1.1)),
    botSusp_le_botSusp_iff.2 (bot_le (a := p.1.2))⟩

theorem grade_grayBot :
    grade ℕ (grayBot P Q) = 0 := rfl

theorem grayBot_mem_faces_true {c : grayProduct (suspension P) (suspension Q)}
    (h : grayBot P Q ⋖ c) :
    grayBot P Q ∈ (grayProduct (suspension P) (suspension Q)).faces true c := by
  obtain ⟨c₁, c₂⟩ := c
  unfold grayBot at h ⊢
  rw [mem_faces_grayProduct]
  rcases Prod.covBy_iff.1 h with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · cases c₁ with
    | pole b => exact absurd hc not_covBy_pole
    | susp x => exact .inl ⟨pole_mem_faces_suspension.2 ⟨pole_covBy_susp.1 hc, rfl⟩, rfl⟩
  · cases c₂ with
    | pole b => exact absurd hc not_covBy_pole
    | susp y =>
      exact .inr ⟨rfl, by simpa using pole_mem_faces_suspension.2 ⟨pole_covBy_susp.1 hc, rfl⟩⟩

end Injection

section Swap

variable {P Q : OGP.{u}}

private theorem orient_join {p q : join P Q} (h : q ⋖ p) :
    (join P Q).orient h =
      (grayProduct (augmentation P) (augmentation Q)).orient (Subtype.coe_covBy_coe_ne_bot.2 h) :=
  rfl

private theorem bodd_grade_join (p : join P Q) :
    (grade ℕ p).bodd = xor (grade ℕ p.1.1 + 1).bodd (grade ℕ p.1.2).bodd := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (one_le_grade_add_grade p)
  rw [grade_join, ← Nat.bodd_add, Nat.add_right_comm, hk, Nat.add_sub_cancel, Nat.bodd_succ,
    Nat.bodd_succ, Bool.not_not]

private theorem orient_augmentation_dual {a a' : WithBot P} (h : a' ⋖ a) :
    (augmentation (dual P Nat.bodd)).orient h =
      xor (grade ℕ a + 1).bodd ((augmentation P).orient h) := by
  induction a using WithBot.recBotCoe with
  | bot => exact (not_lt_bot h.lt).elim
  | coe x =>
    induction a' using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.grade_coe, grade_eq_zero_iff.2 (WithBot.bot_covBy_coe.1 h)]
      rfl
    | coe y =>
      rw [WithBot.grade_coe, Nat.bodd_succ, Nat.bodd_succ, Bool.not_not]
      exact orient_dual Nat.bodd (WithBot.coe_covBy_coe.1 h)

def joinSwap (P Q : OGP.{u}) :
    dual (join P Q) Nat.bodd ≅ join (dual Q Nat.bodd) (dual P Nat.bodd) :=
  isoMk ⟨⟨fun p => ⟨p.1.swap, fun h => p.2 (congrArg Prod.swap h)⟩,
      fun p => ⟨p.1.swap, fun h => p.2 (congrArg Prod.swap h)⟩, fun _ => rfl, fun _ => rfl⟩,
    Prod.swap_le_swap⟩ fun {p q} h => by
    rw [orient_dual, orient_join, orient_join, bodd_grade_join]
    obtain ⟨⟨a, b⟩, hab⟩ := p
    obtain ⟨⟨a', b'⟩, hab'⟩ := q
    rcases Prod.covBy_iff.1 (Subtype.coe_covBy_coe_ne_bot.2 h) with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · obtain rfl : b' = b := hb
      rw [grayProduct_orient_of_covBy_snd (P := augmentation (dual Q Nat.bodd))
          (Q := augmentation (dual P Nat.bodd)) b' ha, grayProduct_orient_of_covBy_fst ha b',
        orient_augmentation_dual ha, Bool.xor_assoc, Bool.xor_left_comm]
    · obtain rfl : a' = a := ha
      rw [grayProduct_orient_of_covBy_fst (P := augmentation (dual Q Nat.bodd))
          (Q := augmentation (dual P Nat.bodd)) hb a', grayProduct_orient_of_covBy_snd a' hb,
        orient_augmentation_dual hb, Nat.bodd_succ, Nat.bodd_succ]
      cases (grade ℕ a').bodd <;> cases (grade ℕ b).bodd <;> simp

end Swap

section GraySuspension

variable {P Q : OGP.{u}}

local notation "𝔾" => grayProduct (suspension P) (suspension Q)

section Preimage

def joinPre (P Q : OGP.{u}) (W : LowerSet (grayProduct (suspension P) (suspension Q))) :
    LowerSet (join P Q) where
  carrier := joinToGray P Q ⁻¹' W
  lower' _ _ h hx := W.lower (joinToGray_le_joinToGray_iff.2 h) hx

@[simp] theorem mem_joinPre {W : LowerSet 𝔾} {z : join P Q} :
    z ∈ joinPre P Q W ↔ joinToGray P Q z ∈ W := Iff.rfl

theorem joinPre_sup (V W : LowerSet 𝔾) :
    joinPre P Q (V ⊔ W) = joinPre P Q V ⊔ joinPre P Q W := rfl

theorem joinPre_inf (V W : LowerSet 𝔾) :
    joinPre P Q (V ⊓ W) = joinPre P Q V ⊓ joinPre P Q W := rfl

theorem joinPre_Iic (z : join P Q) :
    joinPre P Q (.Iic (joinToGray P Q z)) = .Iic z :=
  SetLike.ext fun _ => joinToGray_le_joinToGray_iff

theorem mem_facesIn_joinPre {W : LowerSet 𝔾} {n : ℕ} {α : Bool} {z : join P Q} :
    z ∈ (join P Q).facesIn (joinPre P Q W) n α ↔ joinToGray P Q z ∈ (𝔾).facesIn W (n + 1) α := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_joinPre, disjoint_left]
  rw [grade_joinToGray, Nat.add_right_cancel_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · obtain ⟨p, rfl⟩ := exists_joinToGray_eq_of_le hy.1.le
    exact h (joinToGray_mem_faces_iff.1 hy)
  · exact h (joinToGray_mem_faces_iff.2 hy)

theorem maximal_mem_joinPre_iff {W : LowerSet 𝔾} {z : join P Q} :
    Maximal (· ∈ joinPre P Q W) z ↔ Maximal (· ∈ W) (joinToGray P Q z) := by
  refine ⟨fun h => ⟨h.prop, fun y hy hzy => ?_⟩, fun h => ⟨h.prop, fun y hy hzy => ?_⟩⟩
  · obtain ⟨p, rfl⟩ := exists_joinToGray_eq_of_le hzy
    exact joinToGray_le_joinToGray_iff.2 (h.2 hy (joinToGray_le_joinToGray_iff.1 hzy))
  · exact joinToGray_le_joinToGray_iff.1 (h.2 hy (joinToGray_le_joinToGray_iff.2 hzy))

theorem joinPre_boundary_succ (W : LowerSet 𝔾) (n : ℕ) (α : Bool) :
    joinPre P Q ((𝔾).boundary W (n + 1) α) = (join P Q).boundary (joinPre P Q W) n α := by
  refine SetLike.ext fun z => ?_
  rw [mem_joinPre, mem_boundary, mem_boundary]
  constructor
  · rintro ⟨w, hw, hzw⟩
    obtain ⟨p, rfl⟩ := exists_joinToGray_eq_of_le hzw
    refine ⟨p, ?_, joinToGray_le_joinToGray_iff.1 hzw⟩
    exact hw.imp (fun h => mem_facesIn_joinPre.2 h) fun ⟨h1, h2⟩ =>
      ⟨maximal_mem_joinPre_iff.2 h1, by rw [grade_joinToGray] at h2; omega⟩
  · rintro ⟨p, hp, hzp⟩
    refine ⟨joinToGray P Q p, ?_, joinToGray_le_joinToGray_iff.2 hzp⟩
    exact hp.imp (fun h => mem_facesIn_joinPre.1 h) fun ⟨h1, h2⟩ =>
      ⟨maximal_mem_joinPre_iff.1 h1, by rw [grade_joinToGray]; omega⟩

theorem joinPre_boundary_zero (W : LowerSet 𝔾) (α : Bool) :
    joinPre P Q ((𝔾).boundary W 0 α) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have := grade_le_of_mem_boundary (mem_joinPre.1 hz)
  rw [grade_joinToGray] at this
  omega

theorem coe_add_one_lt_krullDim_of_lt_krullDim_joinPre {W : LowerSet 𝔾} {n : ℕ}
    (h : (n : WithBot ℕ∞) < krullDim (joinPre P Q W)) :
    ((n + 1 : ℕ) : WithBot ℕ∞) < krullDim W := by
  obtain ⟨⟨z, hz⟩, hzn⟩ := coe_lt_krullDim_iff.1 h
  change n < grade ℕ z at hzn
  exact coe_lt_krullDim_iff.2 ⟨⟨joinToGray P Q z, hz⟩,
    by change n + 1 < grade ℕ (joinToGray P Q z); rw [grade_joinToGray]; omega⟩

theorem isGlobular_joinPre {W : LowerSet 𝔾} (hg : (𝔾).IsGlobular W) :
    (join P Q).IsGlobular (joinPre P Q W) := by
  intro k n hkn α β
  rw [← joinPre_boundary_succ, ← joinPre_boundary_succ, ← joinPre_boundary_succ,
    hg (k + 1) (n + 1) (Nat.succ_lt_succ hkn) α β]

theorem isRound_joinPre {W : LowerSet 𝔾} (hr : (𝔾).IsRound W) :
    (join P Q).IsRound (joinPre P Q W) where
  isGlobular := isGlobular_joinPre hr.isGlobular
  inf_boundary_zero h := by
    rw [← joinPre_boundary_succ, ← joinPre_boundary_succ, ← joinPre_inf,
      hr.inf_boundary_succ 0 (coe_add_one_lt_krullDim_of_lt_krullDim_joinPre (n := 0) h),
      boundaryFull, joinPre_sup, joinPre_boundary_zero, joinPre_boundary_zero, sup_bot_eq]
  inf_boundary_succ n h := by
    rw [← joinPre_boundary_succ, ← joinPre_boundary_succ, ← joinPre_inf,
      hr.inf_boundary_succ (n + 1) (coe_add_one_lt_krullDim_of_lt_krullDim_joinPre h),
      boundaryFull, boundaryFull, joinPre_sup, joinPre_boundary_succ, joinPre_boundary_succ]

end Preimage

section Faces

theorem nonempty_faces_join (hP : IsMolecule P) (hQ : IsMolecule Q) (z : join P Q)
    (hz : 0 < grade ℕ z) (α : Bool) : ((join P Q).faces α z).Nonempty := by
  obtain ⟨⟨a, b⟩, hab⟩ := z
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd rfl hab
    | coe y =>
      have hy : 0 < grade ℕ y := by
        change 0 < 0 + (grade ℕ y + 1) - 1 at hz; omega
      obtain ⟨y', hy'⟩ := hQ.nonempty_faces LowerSet.mem_top hy α
      exact ⟨⟨(⊥, (y' : WithBot Q)), by simp [Prod.ext_iff]⟩,
        mem_faces_join.2 (mem_faces_grayProduct.2 (.inr ⟨rfl,
          by simpa using coe_mem_faces_augmentation.2 hy'⟩))⟩
  | coe x =>
    induction b using WithBot.recBotCoe with
    | bot =>
      obtain ⟨x', hx'⟩ := hP.nonempty_faces LowerSet.mem_top (hz : 0 < grade ℕ x) α
      exact ⟨⟨((x' : WithBot P), ⊥), by simp [Prod.ext_iff]⟩,
        mem_faces_join.2 (mem_faces_grayProduct.2 (.inl ⟨coe_mem_faces_augmentation.2 hx', rfl⟩))⟩
    | coe y =>
      rcases Nat.eq_zero_or_pos (grade ℕ x) with hx | hx
      · have hodd : (grade ℕ (x : WithBot P)).bodd = true := by
          rw [WithBot.grade_coe, hx]; rfl
        cases α
        · rcases Nat.eq_zero_or_pos (grade ℕ y) with hy | hy
          · exact ⟨⟨((x : WithBot P), ⊥), by simp [Prod.ext_iff]⟩,
              mem_faces_join.2 (mem_faces_grayProduct.2 (.inr ⟨rfl, by
                rw [hodd]; exact bot_mem_faces_augmentation.2 ⟨grade_eq_zero_iff.1 hy, rfl⟩⟩))⟩
          · obtain ⟨y', hy'⟩ := hQ.nonempty_faces LowerSet.mem_top hy true
            exact ⟨⟨((x : WithBot P), (y' : WithBot Q)), by simp [Prod.ext_iff]⟩,
              mem_faces_join.2 (mem_faces_grayProduct.2 (.inr ⟨rfl, by
                rw [hodd]; exact coe_mem_faces_augmentation.2 hy'⟩))⟩
        · exact ⟨⟨(⊥, (y : WithBot Q)), by simp [Prod.ext_iff]⟩,
            mem_faces_join.2 (mem_faces_grayProduct.2
              (.inl ⟨bot_mem_faces_augmentation.2 ⟨grade_eq_zero_iff.1 hx, rfl⟩, rfl⟩))⟩
      · obtain ⟨x', hx'⟩ := hP.nonempty_faces LowerSet.mem_top hx α
        exact ⟨⟨((x' : WithBot P), (y : WithBot Q)), by simp [Prod.ext_iff]⟩,
          mem_faces_join.2 (mem_faces_grayProduct.2 (.inl ⟨coe_mem_faces_augmentation.2 hx', rfl⟩))⟩

end Faces

section Molecules

theorem isMoleculeIn_joinPre (hP : IsMolecule P) (hQ : IsMolecule Q) {W : LowerSet 𝔾}
    (hW : IsMoleculeIn 𝔾 W) (hne : (joinPre P Q W : Set (join P Q)).Nonempty) :
    IsMoleculeIn (join P Q) (joinPre P Q W) := by
  induction hW with
  | point w hw =>
    obtain ⟨z, hz⟩ := hne
    have hle := grade_mono (𝕆 := ℕ) (LowerSet.mem_Iic_iff.1 (mem_joinPre.1 hz))
    rw [grade_joinToGray, grade_eq_zero_iff.2 hw] at hle
    omega
  | atom t hround _ ihbdry =>
    obtain ⟨z, hz⟩ := hne
    obtain ⟨z₀, rfl⟩ := exists_joinToGray_eq_of_le (LowerSet.mem_Iic_iff.1 (mem_joinPre.1 hz))
    rw [joinPre_Iic]
    rcases Nat.eq_zero_or_pos (grade ℕ z₀) with h0 | hpos
    · exact .point z₀ (grade_eq_zero_iff.1 h0)
    · obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
      refine .atom z₀ (joinPre_Iic z₀ ▸ isRound_joinPre hround) fun α => ?_
      have hbd : (join P Q).bdry (.Iic z₀) α =
          joinPre P Q ((𝔾).bdry (.Iic (joinToGray P Q z₀)) α) := by
        rw [bdry_eq_boundary (n := n) (by rw [LowerSet.krullDim_Iic, hn]; push_cast; rfl),
          bdry_eq_boundary (n := n + 1)
            (by rw [LowerSet.krullDim_Iic, grade_joinToGray, hn]; push_cast; rfl),
          joinPre_boundary_succ, joinPre_Iic]
      obtain ⟨y, hy⟩ := nonempty_faces_join hP hQ z₀ hpos α
      have hne' : ((join P Q).bdry (.Iic z₀) α : Set (join P Q)).Nonempty :=
        ⟨y, by rw [bdry_Iic]; exact subset_lowerClosure hy⟩
      rw [hbd] at hne' ⊢
      exact ihbdry α hne'
  | paste k V W' W hp _ _ _ ihV ihW' =>
    have hU : joinPre P Q W = joinPre P Q V ⊔ joinPre P Q W' := by
      rw [← hp.sup_eq, joinPre_sup]
    by_cases hVe : (joinPre P Q V : Set (join P Q)).Nonempty
    · by_cases hWe : (joinPre P Q W' : Set (join P Q)).Nonempty
      · have hk0 : k ≠ 0 := by
          rintro rfl
          obtain ⟨z₁, hz₁⟩ := hVe
          obtain ⟨z₂, hz₂⟩ := hWe
          have hbV : grayBot P Q ∈ V := V.lower (grayBot_le_joinToGray z₁) (mem_joinPre.1 hz₁)
          have hbW : grayBot P Q ∈ W' := W'.lower (grayBot_le_joinToGray z₂) (mem_joinPre.1 hz₂)
          have hb : grayBot P Q ∈ (𝔾).facesIn W' 0 false :=
            mem_facesIn_of_mem_boundary (hp.inf_eq_input ▸ ⟨hbV, hbW⟩) grade_grayBot
          have hlt : grayBot P Q < joinToGray P Q z₂ :=
            lt_of_le_of_ne (grayBot_le_joinToGray z₂) fun h => by
              have := grade_joinToGray z₂
              rw [← h, grade_grayBot] at this
              omega
          obtain ⟨c, hc, hcz⟩ := exists_covBy_le_of_lt hlt
          exact disjoint_left.1 hb.2.2 (grayBot_mem_faces_true hc)
            (W'.lower hcz (mem_joinPre.1 hz₂))
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        refine IsPastingIn.isMoleculeIn (k := j) ⟨hU.symm, ?_, ?_⟩ (ihV hVe) (ihW' hWe)
        · rw [← joinPre_inf, hp.inf_eq_output, joinPre_boundary_succ]
        · rw [← joinPre_inf, hp.inf_eq_input, joinPre_boundary_succ]
      · rw [not_nonempty_iff_eq_empty, ← LowerSet.coe_bot, SetLike.coe_set_eq] at hWe
        rw [hU, hWe, sup_bot_eq]
        exact ihV hVe
    · rw [not_nonempty_iff_eq_empty, ← LowerSet.coe_bot, SetLike.coe_set_eq] at hVe
      rw [hU, hVe, bot_sup_eq] at hne ⊢
      exact ihW' hne

end Molecules

end GraySuspension

theorem isMolecule_join (P Q : OGP.{u}) (hP : IsMolecule P) (hQ : IsMolecule Q) :
    IsMolecule (join P Q) := by
  have hG : IsMolecule (grayProduct (suspension P) (suspension Q)) :=
    isMolecule_grayProduct (isMolecule_suspension P hP) (isMolecule_suspension Q hQ)
  obtain ⟨x, -⟩ := hP.nonempty
  exact isMoleculeIn_joinPre hP hQ hG
    ⟨⟨((x : WithBot P), ⊥), by simp [Prod.ext_iff]⟩, LowerSet.mem_top⟩

theorem isAtom_join (P Q : OGP.{u}) (hP : IsAtom P) (hQ : IsAtom Q) : IsAtom (join P Q) := by
  obtain ⟨hmP, t, ht⟩ := hP
  obtain ⟨hmQ, t', ht'⟩ := hQ
  refine ⟨isMolecule_join P Q hmP hmQ,
    ⟨((t : WithBot P), (t' : WithBot Q)), by simp [Prod.ext_iff]⟩,
    SetLike.ext fun p => iff_of_true LowerSet.mem_top (LowerSet.mem_Iic_iff.2 ⟨?_, ?_⟩)⟩
  · exact WithBot.le_coe_iff.2 fun _ _ => LowerSet.mem_Iic_iff.1 (ht ▸ LowerSet.mem_top)
  · exact WithBot.le_coe_iff.2 fun _ _ => LowerSet.mem_Iic_iff.1 (ht' ▸ LowerSet.mem_top)

theorem isAtom_simplex (n : ℕ) : IsAtom (simplex.{u} n) := by
  induction n with
  | zero => exact isAtom_point
  | succ n ih => exact isAtom_join _ _ isAtom_point ih

theorem isRDC_simplex (n : ℕ) : IsRDC (simplex.{u} n) :=
  isRDC_of_isMolecule (isAtom_simplex n).1

end Atoms.Molecule.OGP
