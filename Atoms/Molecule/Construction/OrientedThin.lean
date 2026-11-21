import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Molecule.Construction.JoinAssociativity
import Atoms.Molecule.RegularComplex.Thin
import Mathlib.CategoryTheory.Monoidal.Subcategory

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

variable {P Q : OGP.{u}}

private theorem signedDiamond_iff (f : P → Q) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hr : (range f).OrdConnected) (s : ℕ → Bool)
    (ho : ∀ {a a' : P} {α : Bool}, a' ∈ P.faces α a → f a' ∈ Q.faces (xor (s (grade ℕ a)) α) (f a))
    {x y : P} (hd : grade ℕ x = grade ℕ y + 2) :
    P.IsSignedDiamond y x ↔ Q.IsSignedDiamond (f y) (f x) := by
  let e : P ↪o Q := OrderEmbedding.ofMapLEIff f hf
  have hinj : Function.Injective f := e.injective
  have hI : f '' Ioo y x = Ioo (f y) (f x) := e.image_Ioo hr y x
  have hcov {a b : P} (h : a ⋖ b) : f a ⋖ f b := (hr.apply_covBy_apply_iff e).2 h
  have horient {a a' : P} (h : a' ⋖ a) (k : f a' ⋖ f a) :
      Q.orient k = xor (s (grade ℕ a)) (P.orient h) :=
    (ho ⟨h, rfl⟩).2
  have hlow {z : P} (h : y ⋖ z) : grade ℕ z = grade ℕ y + 1 :=
    (Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)).symm
  have xor_beq_xor_ne_iff (b c a₁ a₁' a₂ a₂' : Bool) :
      (xor c a₁ == xor b a₁') ≠ (xor c a₂ == xor b a₂') ↔ (a₁ == a₁') ≠ (a₂ == a₂') := by
    revert b c a₁ a₁' a₂ a₂'
    decide
  constructor
  · rintro ⟨z₁, z₂, hne, hIoo, hsign⟩
    have h₁ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd (hIoo ▸ mem_insert z₁ {z₂})
    have h₂ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd
      (hIoo ▸ mem_insert_of_mem z₁ (mem_singleton z₂))
    refine ⟨f z₁, f z₂, fun h => hne (hinj h), by rw [← hI, hIoo, image_pair],
      fun k₁ k₁' k₂ k₂' => ?_⟩
    rw [horient h₁.1, horient h₁.2, horient h₂.1, horient h₂.2, hlow h₁.1, hlow h₂.1,
      xor_beq_xor_ne_iff]
    exact hsign h₁.1 h₁.2 h₂.1 h₂.2
  · rintro ⟨w₁, w₂, hne, hIoo, hsign⟩
    obtain ⟨z₁, hz₁, rfl⟩ : w₁ ∈ f '' Ioo y x := hI ▸ hIoo ▸ mem_insert w₁ {w₂}
    obtain ⟨z₂, hz₂, rfl⟩ : w₂ ∈ f '' Ioo y x :=
      hI ▸ hIoo ▸ mem_insert_of_mem _ (mem_singleton w₂)
    have h₁ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd hz₁
    have h₂ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd hz₂
    refine ⟨z₁, z₂, fun h => hne (congrArg f h),
      image_injective.2 hinj (by rw [hI, hIoo, image_pair]), fun _ _ _ _ => ?_⟩
    have hs := hsign (hcov h₁.1) (hcov h₁.2) (hcov h₂.1) (hcov h₂.2)
    rwa [horient h₁.1, horient h₁.2, horient h₂.1, horient h₂.2, hlow h₁.1, hlow h₂.1,
      xor_beq_xor_ne_iff] at hs

private theorem lt_iff_eq_or_eq_of_faces_eq {x s t : P} (hx : grade ℕ x = 1)
    (hs : P.faces false x = {s}) (ht : P.faces true x = {t}) {z : P} :
    z < x ↔ z = s ∨ z = t := by
  refine ⟨fun h => ?_, ?_⟩
  · have hz : z ⋖ x := GradeOrder.covBy_of_le_of_grade_eq_add_one h.le (by
      have := grade_strictMono (𝕆 := ℕ) h
      omega)
    have hzf : z ∈ P.faces (P.orient hz) x := ⟨hz, rfl⟩
    cases ho : P.orient hz
    · rw [ho, hs] at hzf
      exact .inl hzf
    · rw [ho, ht] at hzf
      exact .inr hzf
  · rintro (rfl | rfl)
    · exact (hs ▸ mem_singleton z : z ∈ P.faces false x).1.lt
    · exact (ht ▸ mem_singleton z : z ∈ P.faces true x).1.lt

private theorem faces_orient_eq_singleton {x a b : P} (ha : a ⋖ x) (hb : b ⋖ x)
    (hab : ∀ {z}, z < x → z = a ∨ z = b) (hne : P.orient ha ≠ P.orient hb) :
    P.faces (P.orient ha) x = {a} := by
  refine Set.ext fun z => ⟨fun ⟨hz, hoz⟩ => ?_, fun hz => ?_⟩
  · rcases hab hz.lt with rfl | rfl
    · rfl
    · exact absurd hoz.symm hne
  · rw [mem_singleton_iff.1 hz]
    exact ⟨ha, rfl⟩

private theorem forall_exists_faces_eq_singleton_iff {x : P} (hx : grade ℕ x = 1) :
    (∀ α, ∃ y, P.faces α x = {y}) ↔ IsSignedDiamond (augmentation P) ⊥ (x : WithBot P) := by
  have hbot {z : P} (k : (⊥ : WithBot P) ⋖ z) : (augmentation P).orient k = true :=
    (bot_mem_faces_augmentation.1 ⟨k, rfl⟩).2
  have hcoe {z : P} (h : z ⋖ x) (k : (z : WithBot P) ⋖ x) :
      (augmentation P).orient k = P.orient h :=
    (coe_mem_faces_augmentation.1 ⟨k, rfl⟩).2
  have hIoo {w : WithBot P} : w ∈ Ioo ⊥ (x : WithBot P) ↔ ∃ z : P, z < x ∧ w = z := by
    induction w using WithBot.recBotCoe with
    | bot => simp
    | coe z => simp [WithBot.bot_lt_coe]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h false
    obtain ⟨t, ht⟩ := h true
    have hs' : s ∈ P.faces false x := hs ▸ mem_singleton s
    have ht' : t ∈ P.faces true x := ht ▸ mem_singleton t
    refine ⟨s, t, fun e => Set.disjoint_left.1 (P.disjoint_faces x false) hs'
      ((WithBot.coe_injective e : s = t) ▸ ht'), Set.ext fun w => ?_, fun h₁ h₁' h₂ h₂' => ?_⟩
    · rw [hIoo]
      simp only [mem_insert_iff, mem_singleton_iff, lt_iff_eq_or_eq_of_faces_eq hx hs ht]
      constructor
      · rintro ⟨z, rfl | rfl, rfl⟩
        exacts [.inl rfl, .inr rfl]
      · rintro (rfl | rfl)
        exacts [⟨s, .inl rfl, rfl⟩, ⟨t, .inr rfl, rfl⟩]
    · rw [hbot h₁, hbot h₂, hcoe hs'.1 h₁', hcoe ht'.1 h₂', hs'.2, ht'.2]
      decide
  · rintro ⟨w₁, w₂, hne, hI, hsign⟩
    obtain ⟨z₁, hz₁, rfl⟩ := hIoo.1 (hI ▸ mem_insert w₁ {w₂})
    obtain ⟨z₂, hz₂, rfl⟩ := hIoo.1 (hI ▸ mem_insert_of_mem (z₁ : WithBot P) (mem_singleton w₂))
    have hd : grade ℕ (x : WithBot P) = grade ℕ (⊥ : WithBot P) + 2 := by
      simp [hx]
    have k₁ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd (hIoo.2 ⟨z₁, hz₁, rfl⟩)
    have k₂ := GradeOrder.covBy_and_covBy_of_mem_Ioo hd (hIoo.2 ⟨z₂, hz₂, rfl⟩)
    have c₁ := WithBot.coe_covBy_coe.1 k₁.2
    have c₂ := WithBot.coe_covBy_coe.1 k₂.2
    have ho : P.orient c₁ ≠ P.orient c₂ := fun e => by
      have := hsign k₁.1 k₁.2 k₂.1 k₂.2
      rw [hbot k₁.1, hbot k₂.1, hcoe c₁ k₁.2, hcoe c₂ k₂.2, e] at this
      exact this rfl
    have hall {z : P} (hz : z < x) : z = z₁ ∨ z = z₂ := by
      have := hI ▸ hIoo.2 ⟨z, hz, rfl⟩
      simpa using this
    intro α
    rcases Bool.eq_or_eq_not α (P.orient c₁) with rfl | rfl
    · exact ⟨z₁, faces_orient_eq_singleton c₁ c₂ hall ho⟩
    · rw [(Bool.eq_not_iff.2 (Ne.symm ho)).symm]
      exact ⟨z₂, faces_orient_eq_singleton c₂ c₁ (fun hz => (hall hz).symm) (Ne.symm ho)⟩

theorem isOrientedThin_iff_hasSignedDiamonds_augmentation :
    P.IsOrientedThin ↔ (augmentation P).HasSignedDiamonds := by
  have hcoe {x y : P} (hd : grade ℕ x = grade ℕ y + 2) :
      P.IsSignedDiamond y x ↔ IsSignedDiamond (augmentation P) y x :=
    signedDiamond_iff (P := P) (Q := augmentation P) WithBot.some (fun _ _ => WithBot.coe_le_coe)
      (by rw [WithBot.range_coe]; exact ordConnected_Ioi) (fun _ => false)
      (fun h => by rw [Bool.false_xor]; exact coe_mem_faces_augmentation.2 h) hd
  refine ⟨fun h x y hyx hd => ?_, fun h => ⟨fun x hx => ?_, fun x y hyx hd => ?_⟩⟩
  · induction x using WithBot.recBotCoe with
    | bot => exact absurd hyx not_lt_bot
    | coe x =>
      induction y using WithBot.recBotCoe with
      | bot =>
        have hx : grade ℕ x = 1 := by
          rw [WithBot.grade_coe] at hd
          exact Nat.add_right_cancel hd
        exact (forall_exists_faces_eq_singleton_iff hx).1 (h.exists_faces_eq_singleton x hx)
      | coe y =>
        have hd' : grade ℕ x = grade ℕ y + 2 := by
          rw [WithBot.grade_coe, WithBot.grade_coe] at hd
          omega
        exact (hcoe hd').1 (h.diamond x y (WithBot.coe_lt_coe.1 hyx) hd')
  · exact (forall_exists_faces_eq_singleton_iff hx).2
      (h x ⊥ (WithBot.bot_lt_coe x) (by simp [hx]))
  · exact (hcoe hd).2 (h x y (WithBot.coe_lt_coe.2 hyx) (by
      rw [WithBot.grade_coe, WithBot.grade_coe, hd]))

private theorem signedDiamond_grayProduct_of_covBy {x x' : P} {y y' : Q} (hx : x' ⋖ x)
    (hy : y' ⋖ y) : IsSignedDiamond (grayProduct P Q) (x', y') (x, y) := by
  refine ⟨(x', y), (x, y'), fun h => hx.ne (congrArg Prod.fst h),
    Set.ext fun p => ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩, fun k₁ k₁' k₂ k₂' => ?_⟩
  · rcases hx.eq_or_eq h₁.le.1 h₂.le.1 with e₁ | e₁ <;>
      rcases hy.eq_or_eq h₁.le.2 h₂.le.2 with e₂ | e₂
    · exact absurd (Prod.ext e₁ e₂).symm h₁.ne
    · exact .inl (Prod.ext e₁ e₂)
    · exact .inr (Prod.ext e₁ e₂)
    · exact absurd (Prod.ext e₁ e₂) h₂.ne
  · rintro (rfl | rfl)
    · exact ⟨Prod.mk_lt_mk_iff_right.2 hy.lt, Prod.mk_lt_mk_iff_left.2 hx.lt⟩
    · exact ⟨Prod.mk_lt_mk_iff_left.2 hx.lt, Prod.mk_lt_mk_iff_right.2 hy.lt⟩
  · rw [grayProduct_orient_of_covBy_snd x' hy k₁, grayProduct_orient_of_covBy_fst hx y k₁',
      grayProduct_orient_of_covBy_fst hx y' k₂, grayProduct_orient_of_covBy_snd x hy k₂',
      ← Nat.covBy_iff_add_one_eq.1 (hx.grade ℕ), Nat.bodd_succ]
    cases (grade ℕ x').bodd <;> cases P.orient hx <;> cases Q.orient hy <;> decide

theorem HasSignedDiamonds.grayProduct (hP : P.HasSignedDiamonds) (hQ : Q.HasSignedDiamonds) :
    (OGP.grayProduct P Q).HasSignedDiamonds := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hlt hd
  have hx : x' ≤ x := hlt.le.1
  have hy : y' ≤ y := hlt.le.2
  have gx := grade_mono (𝕆 := ℕ) hx
  have gy := grade_mono (𝕆 := ℕ) hy
  simp only [Prod.grade_eq_add] at hd
  obtain ⟨hx₂, hy₀⟩ | ⟨hx₀, hy₂⟩ | ⟨hx₁, hy₁⟩ :
      grade ℕ x = grade ℕ x' + 2 ∧ grade ℕ y = grade ℕ y' ∨
        grade ℕ x = grade ℕ x' ∧ grade ℕ y = grade ℕ y' + 2 ∨
        grade ℕ x = grade ℕ x' + 1 ∧ grade ℕ y = grade ℕ y' + 1 := by
    omega
  · obtain rfl := GradeOrder.eq_of_le_of_grade_le hy hy₀.le
    have hr : (range fun z : P => ((z, y') : OGP.grayProduct P Q)).OrdConnected :=
      ⟨by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c ⟨h₁, h₂⟩
        exact ⟨c.1, Prod.ext rfl (le_antisymm h₁.2 h₂.2)⟩⟩
    exact (signedDiamond_iff (P := P) (Q := OGP.grayProduct P Q) (fun z => (z, y'))
      (fun _ _ => Prod.mk_le_mk_iff_left) hr (fun _ => false)
      (fun h => by rw [Bool.false_xor]; exact mem_faces_grayProduct.2 (.inl ⟨h, rfl⟩)) hx₂).1
      (hP x x' (lt_of_le_of_ne hx (by rintro rfl; omega)) hx₂)
  · obtain rfl := GradeOrder.eq_of_le_of_grade_le hx hx₀.le
    have hr : (range fun z : Q => ((x', z) : OGP.grayProduct P Q)).OrdConnected :=
      ⟨by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c ⟨h₁, h₂⟩
        exact ⟨c.2, Prod.ext (le_antisymm h₁.1 h₂.1) rfl⟩⟩
    exact (signedDiamond_iff (P := Q) (Q := OGP.grayProduct P Q) (fun z => (x', z))
      (fun _ _ => Prod.mk_le_mk_iff_right) hr (fun _ => (grade ℕ x').bodd)
      (fun h => mem_faces_grayProduct.2 (.inr ⟨rfl, by simpa using h⟩)) hy₂).1
      (hQ y y' (lt_of_le_of_ne hy (by rintro rfl; omega)) hy₂)
  · exact signedDiamond_grayProduct_of_covBy (GradeOrder.covBy_of_le_of_grade_eq_add_one hx hx₁)
      (GradeOrder.covBy_of_le_of_grade_eq_add_one hy hy₁)

theorem IsOrientedThin.grayProduct (hP : P.IsOrientedThin) (hQ : Q.IsOrientedThin) :
    (OGP.grayProduct P Q).IsOrientedThin := by
  refine ⟨fun ⟨x, y⟩ hd α => ?_, hP.diamond.grayProduct hQ.diamond⟩
  simp only [Prod.grade_eq_add] at hd
  have hmin {R : OGP.{u}} {w : R} (hw : grade ℕ w = 0) {β : Bool} {v : R} : v ∉ R.faces β w :=
    fun hv => (grade_eq_zero_iff.1 hw).not_lt hv.1.lt
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ : grade ℕ x = 1 ∧ grade ℕ y = 0 ∨ grade ℕ x = 0 ∧ grade ℕ y = 1 := by
    omega
  · obtain ⟨s, hs⟩ := hP.exists_faces_eq_singleton x hx α
    refine ⟨(s, y), Set.ext fun q => ?_⟩
    rw [mem_faces_grayProduct, hs, mem_singleton_iff, mem_singleton_iff, Prod.ext_iff]
    exact or_iff_left fun h => hmin hy h.2
  · obtain ⟨t, ht⟩ := hQ.exists_faces_eq_singleton y hy α
    refine ⟨(x, t), Set.ext fun q => ?_⟩
    rw [mem_faces_grayProduct, hx, Nat.bodd_zero, Bool.false_xor, ht, mem_singleton_iff,
      mem_singleton_iff, Prod.ext_iff]
    exact or_iff_right fun h => hmin hx h.1

private theorem signedDiamond_suspension_pole (hP : P.IsOrientedThin) {x : P}
    (hx : grade ℕ x = 1) (β : Bool) : IsSignedDiamond (suspension P) (pole β) (susp x) := by
  obtain ⟨s, t, hst, hs, ht⟩ := hP.exists_faces_eq hx
  have hs' : s ∈ P.faces false x := hs ▸ mem_singleton s
  have ht' : t ∈ P.faces true x := ht ▸ mem_singleton t
  refine ⟨susp s, susp t, fun h => hst (susp.inj h), Set.ext fun c => ?_,
    fun k₁ k₁' k₂ k₂' => ?_⟩
  · rcases c with γ | z
    · exact iff_of_false (fun h => (isMin_pole γ).not_lt h.1) (by simp)
    · simp only [mem_Ioo, pole_lt_susp, susp_lt_susp, true_and, mem_insert_iff,
        mem_singleton_iff, susp.injEq]
      exact lt_iff_eq_or_eq_of_faces_eq hx hs ht
  · have e₁' := (susp_mem_faces_suspension.2 hs').2
    have e₂' := (susp_mem_faces_suspension.2 ht').2
    rw [← (pole_mem_faces_suspension.1 ⟨k₁, rfl⟩).2, ← (pole_mem_faces_suspension.1 ⟨k₂, rfl⟩).2,
      (e₁' : (suspension P).orient k₁' = false), (e₂' : (suspension P).orient k₂' = true)]
    cases β <;> decide

theorem IsOrientedThin.suspension (hP : P.IsOrientedThin) : (OGP.suspension P).IsOrientedThin := by
  refine ⟨fun x hx α => ?_, fun x y hyx hd => ?_⟩
  · rcases x with β | x
    · simp at hx
    have hmin : IsMin x := grade_eq_zero_iff.1 (by simpa using hx)
    refine ⟨pole α, Set.ext fun z => ?_⟩
    rcases z with γ | z
    · rw [pole_mem_faces_suspension, mem_singleton_iff]
      exact ⟨fun h => congrArg pole h.2, fun h => ⟨hmin, pole.inj h⟩⟩
    · rw [susp_mem_faces_suspension, mem_singleton_iff]
      exact iff_of_false (fun h => hmin.not_lt h.1.lt) nofun
  rcases x with β | x
  · exact absurd hyx (isMin_pole β).not_lt
  rcases y with β | y
  · exact signedDiamond_suspension_pole hP (by simpa using hd) β
  · have hd' : grade ℕ x = grade ℕ y + 2 := by simpa using hd
    have hr : (range fun z : P => (susp z : OGP.suspension P)).OrdConnected :=
      ⟨by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c ⟨h₁, -⟩
        rcases c with γ | c
        · exact absurd h₁ (not_susp_le_pole a γ)
        · exact ⟨c, rfl⟩⟩
    exact (signedDiamond_iff (P := P) (Q := OGP.suspension P) susp
      (fun _ _ => susp_le_susp) hr (fun _ => false)
      (fun h => by rw [Bool.false_xor]; exact susp_mem_faces_suspension.2 h) hd').1
      (hP.diamond x y (susp_lt_susp.1 hyx) hd')

theorem IsOrientedThin.dual (hP : P.IsOrientedThin) (J : ℕ → Bool) :
    (OGP.dual P J).IsOrientedThin := by
  refine ⟨fun x hx α => ?_, fun x y hyx hd => ?_⟩
  · rw [faces_dual]
    exact hP.exists_faces_eq_singleton x hx _
  · exact (signedDiamond_iff (P := P) (Q := OGP.dual P J) (fun z => z) (fun _ _ => Iff.rfl)
      (by rw [range_id']; exact ordConnected_univ) J
      (fun h => by
        rw [faces_dual, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
        exact h) hd).1
      (hP.diamond x y hyx hd)

theorem IsOrientedThin.join (hP : P.IsOrientedThin) (hQ : Q.IsOrientedThin) :
    (OGP.join P Q).IsOrientedThin := by
  have hG := (isOrientedThin_iff_hasSignedDiamonds_augmentation.1 hP).grayProduct
    (isOrientedThin_iff_hasSignedDiamonds_augmentation.1 hQ)
  let f : WithBot (OGP.join P Q) → OGP.grayProduct (augmentation P) (augmentation Q) :=
    fun a => (joinBotFst a, joinBotSnd a)
  have hf (a b : WithBot (OGP.join P Q)) : f a ≤ f b ↔ a ≤ b := joinBot_le_iff.symm
  have hr : (range f).OrdConnected := by
    rw [range_eq_univ.2 fun w => ⟨joinPairBot P Q w.1 w.2, by simp [f]⟩]
    exact ordConnected_univ
  refine isOrientedThin_iff_hasSignedDiamonds_augmentation.2 fun x y hyx hd => ?_
  exact (signedDiamond_iff (P := augmentation (OGP.join P Q))
    (Q := OGP.grayProduct (augmentation P) (augmentation Q)) f hf hr (fun _ => false)
    (fun h => by rw [Bool.false_xor]; exact mem_faces_augmentation_join.1 h) hd).2
    (hG (f x) (f y) ((OrderEmbedding.ofMapLEIff f hf).lt_iff_lt.2 hyx) (by
      simp only [f, Prod.grade_eq_add]
      rw [← grade_joinBot, ← grade_joinBot, hd]))

theorem isOrientedThin_point : point.{u}.IsOrientedThin :=
  ⟨fun x hx => absurd hx (by rw [grade_eq_zero_iff.2 (isMin_point x)]; decide),
    fun x _ hyx => absurd hyx ((isMin_point x).not_lt)⟩

instance isMonoidal_isOrientedThin :
    ObjectProperty.IsMonoidal (IsOrientedThin : ObjectProperty OGP.{u}) where
  prop_unit := isOrientedThin_point
  prop_tensor _ _ hP hQ := hP.grayProduct hQ

end Atoms.Molecule.OGP
