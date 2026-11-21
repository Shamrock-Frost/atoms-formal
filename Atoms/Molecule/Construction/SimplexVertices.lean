import Atoms.Molecule.Construction.Join

universe u

open Order

namespace Atoms.Molecule.OGP

def botVertices : (n : ℕ) → WithBot (simplex.{u} n) → Finset (Fin (n + 1))
  | 0, a => WithBot.recBotCoe ∅ (fun _ => {0}) a
  | n + 1, a => WithBot.recBotCoe ∅ (fun p =>
      WithBot.recBotCoe ∅ (fun _ => {0}) p.1.1 ∪
        (botVertices n p.1.2).map (Fin.succEmb (n + 1))) a

def pairVertices (n : ℕ) (c : WithBot point.{u}) (a : WithBot (simplex.{u} n)) :
    Finset (Fin (n + 2)) :=
  WithBot.recBotCoe ∅ (fun _ => {0}) c ∪ (botVertices n a).map (Fin.succEmb (n + 1))

@[simp] theorem botVertices_bot (n : ℕ) : botVertices.{u} n ⊥ = ∅ := by
  cases n <;> rfl

@[simp] theorem botVertices_zero_coe (x : simplex.{u} 0) :
    botVertices 0 (x : WithBot (simplex.{u} 0)) = {0} := rfl

theorem botVertices_succ_coe (n : ℕ) (p : simplex.{u} (n + 1)) :
    botVertices (n + 1) (p : WithBot (simplex.{u} (n + 1))) =
      pairVertices n p.1.1 p.1.2 := rfl

@[simp] theorem pairVertices_bot_bot (n : ℕ) : pairVertices.{u} n ⊥ ⊥ = ∅ := by
  simp [pairVertices]

@[simp] theorem zero_mem_pairVertices_iff {n : ℕ} {c : WithBot point.{u}}
    {a : WithBot (simplex.{u} n)} :
    (0 : Fin (n + 2)) ∈ pairVertices n c a ↔ c ≠ ⊥ := by
  induction c using WithBot.recBotCoe <;> simp [pairVertices, Fin.coe_succEmb]

@[simp] theorem succ_mem_pairVertices_iff {n : ℕ} {c : WithBot point.{u}}
    {a : WithBot (simplex.{u} n)} {i : Fin (n + 1)} :
    i.succ ∈ pairVertices n c a ↔ i ∈ botVertices n a := by
  induction c using WithBot.recBotCoe <;> simp [pairVertices, Fin.coe_succEmb]

theorem card_pairVertices {n : ℕ}
    (ih : ∀ a, (botVertices.{u} n a).card = grade ℕ a)
    (c : WithBot point.{u}) (a : WithBot (simplex.{u} n)) :
    (pairVertices n c a).card = grade ℕ c + grade ℕ a := by
  induction c using WithBot.recBotCoe <;>
    simp [pairVertices, ih, grade_eq_zero_iff.2 (isMin_point _), Nat.add_comm]

theorem card_botVertices (n : ℕ) (a : WithBot (simplex.{u} n)) :
    (botVertices n a).card = grade ℕ a := by
  induction n with
  | zero => induction a using WithBot.recBotCoe <;> rfl
  | succ n ih =>
    induction a using WithBot.recBotCoe with
    | bot => rfl
    | coe p =>
      let p' : join point.{u} (simplex.{u} n) := p
      change (pairVertices n p'.1.1 p'.1.2).card = grade ℕ p' + 1
      rw [card_pairVertices ih, grade_join]
      have h := one_le_grade_add_grade (P := point.{u}) (Q := simplex.{u} n) p'
      omega

def simplexVertices (n : ℕ) (x : simplex.{u} n) : Finset (Fin (n + 1)) :=
  botVertices n (x : WithBot (simplex.{u} n))

theorem card_simplexVertices (n : ℕ) (x : simplex.{u} n) :
    (simplexVertices n x).card = grade ℕ x + 1 :=
  card_botVertices n x

theorem simplexVertices_nonempty (n : ℕ) (x : simplex.{u} n) :
    (simplexVertices n x).Nonempty := by
  rw [← Finset.card_pos, card_simplexVertices]
  omega

private theorem point_le (u v : point.{u}) : u ≤ v :=
  isMin_point v le_top

private theorem withBot_point_le_iff {c d : WithBot point.{u}} :
    (c ≠ ⊥ → d ≠ ⊥) ↔ c ≤ d := by
  induction c using WithBot.recBotCoe <;> induction d using WithBot.recBotCoe <;> simp [point_le]

theorem pairVertices_subset_pairVertices_iff {n : ℕ}
    (ih : ∀ a b, botVertices.{u} n a ⊆ botVertices n b ↔ a ≤ b)
    {c d : WithBot point.{u}} {a b : WithBot (simplex.{u} n)} :
    pairVertices n c a ⊆ pairVertices n d b ↔ c ≤ d ∧ a ≤ b := by
  rw [Finset.subset_iff, Fin.forall_fin_succ, zero_mem_pairVertices_iff, zero_mem_pairVertices_iff,
    withBot_point_le_iff, ← ih, Finset.subset_iff]
  simp

theorem botVertices_subset_iff_of_coe {n : ℕ}
    (h : ∀ x y : simplex.{u} n,
      botVertices n (x : WithBot (simplex.{u} n)) ⊆ botVertices n (y : WithBot _) ↔ x ≤ y)
    (a b : WithBot (simplex.{u} n)) :
    botVertices n a ⊆ botVertices n b ↔ a ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe x =>
    induction b using WithBot.recBotCoe with
    | bot => simpa [simplexVertices] using (simplexVertices_nonempty n x).ne_empty
    | coe y => rw [WithBot.coe_le_coe]; exact h x y

theorem botVertices_subset_iff (n : ℕ) (a b : WithBot (simplex.{u} n)) :
    botVertices n a ⊆ botVertices n b ↔ a ≤ b := by
  induction n with
  | zero =>
    exact botVertices_subset_iff_of_coe (n := 0)
      (fun x y => iff_of_true (by simp) (point_le x y)) a b
  | succ n ih =>
    refine botVertices_subset_iff_of_coe (fun x y => ?_) a b
    rw [botVertices_succ_coe, botVertices_succ_coe, pairVertices_subset_pairVertices_iff ih]
    exact Iff.rfl

theorem botVertices_injective (n : ℕ) : Function.Injective (botVertices.{u} n) :=
  fun a b h => le_antisymm ((botVertices_subset_iff n a b).1 (h ▸ Finset.Subset.refl _))
    ((botVertices_subset_iff n b a).1 (h ▸ Finset.Subset.refl _))

private def mkSimplexZero : simplex.{u} 0 := (⊤ : point.{u})

private def mkSimplexSucc (n : ℕ) (c : WithBot point.{u}) (a : WithBot (simplex.{u} n))
    (h : (c, a) ≠ ⊥) : simplex.{u} (n + 1) :=
  ⟨(c, a), h⟩

@[simp] private theorem botVertices_mkSimplexSucc (n : ℕ) (c : WithBot point.{u})
    (a : WithBot (simplex.{u} n)) (h : (c, a) ≠ ⊥) :
    botVertices (n + 1) (mkSimplexSucc n c a h : WithBot (simplex.{u} (n + 1))) =
      pairVertices n c a := rfl

def botSimplexCell : (n : ℕ) → Finset (Fin (n + 1)) → WithBot (simplex.{u} n)
  | 0, S =>
    if (0 : Fin 1) ∈ S then (mkSimplexZero : WithBot (simplex.{u} 0)) else ⊥
  | n + 1, S =>
    let a := botSimplexCell n (Finset.univ.filter fun i : Fin (n + 1) => i.succ ∈ S)
    if (0 : Fin (n + 2)) ∈ S then
      (mkSimplexSucc n (⊤ : point.{u}) a
        (fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)) : WithBot (simplex.{u} (n + 1)))
    else
      a.recBotCoe ⊥ fun x =>
        (mkSimplexSucc n ⊥ (x : WithBot (simplex.{u} n))
          (fun h => WithBot.coe_ne_bot (congrArg Prod.snd h)) : WithBot (simplex.{u} (n + 1)))

@[simp] theorem botVertices_botSimplexCell (n : ℕ) (S : Finset (Fin (n + 1))) :
    botVertices.{u} n (botSimplexCell n S) = S := by
  induction n with
  | zero =>
    unfold botSimplexCell
    split_ifs with h <;> ext i <;> obtain rfl := Fin.fin_one_eq_zero i <;> simp [h]
  | succ n ih =>
    unfold botSimplexCell
    dsimp only
    rw [Finset.ext_iff, Fin.forall_fin_succ]
    have ha := ih (Finset.univ.filter fun i : Fin (n + 1) => i.succ ∈ S)
    split_ifs with h0
    · simp [h0, ha]
    · generalize botSimplexCell.{u} n _ = a at ha ⊢
      induction a using WithBot.recBotCoe with
      | bot => simpa [Finset.ext_iff, h0] using ha
      | coe x => simp [h0, ha]

theorem exists_botVertices_eq (n : ℕ) (S : Finset (Fin (n + 1))) :
    ∃ a : WithBot (simplex.{u} n), botVertices n a = S :=
  ⟨botSimplexCell n S, botVertices_botSimplexCell n S⟩

@[simp] theorem botSimplexCell_eq_bot_iff {n : ℕ} {S : Finset (Fin (n + 1))} :
    botSimplexCell.{u} n S = ⊥ ↔ S = ∅ := by
  rw [← (botVertices_injective.{u} n).eq_iff, botVertices_botSimplexCell, botVertices_bot]

def simplexCell (n : ℕ) (S : Finset (Fin (n + 1))) (hS : S.Nonempty) : simplex.{u} n :=
  (botSimplexCell.{u} n S).unbot (botSimplexCell_eq_bot_iff.not.2 hS.ne_empty)

@[simp] theorem coe_simplexCell (n : ℕ) (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    (simplexCell.{u} n S hS : WithBot (simplex.{u} n)) = botSimplexCell n S :=
  WithBot.coe_unbot _ _

@[simp] theorem simplexVertices_simplexCell (n : ℕ) (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    simplexVertices.{u} n (simplexCell n S hS) = S := by
  rw [simplexVertices, coe_simplexCell, botVertices_botSimplexCell]

theorem image_pairVertices {m : ℕ} {n : ℕ} {g : Fin (m + 1) → Fin (n + 1)}
    {h : Fin (m + 2) → Fin (n + 2)} (hz : h 0 = 0) (hs : ∀ k, h k.succ = (g k).succ)
    (c : WithBot point.{u}) {a : WithBot (simplex.{u} m)} {b : WithBot (simplex.{u} n)}
    (hb : botVertices n b = (botVertices m a).image g) :
    (pairVertices m c a).image h = pairVertices n c b := by
  unfold pairVertices
  rw [Finset.image_union, hb, Finset.map_eq_image, Finset.map_eq_image, Finset.image_image,
    Finset.image_image]
  congr 1
  · induction c using WithBot.recBotCoe <;> simp [hz]
  · exact congrArg (Finset.image · _) (funext hs)

private theorem predAbove_zero_zero {m : ℕ} :
    Fin.predAbove (0 : Fin (m + 1)) 0 = 0 := rfl

private theorem predAbove_zero_succ {m : ℕ} (k : Fin (m + 1)) :
    Fin.predAbove (0 : Fin (m + 1)) k.succ = k := by
  simp [Fin.predAbove, Fin.succ_pos]

theorem image_predAbove_zero_pairVertices (n : ℕ) {A : WithBot (simplex.{u} (n + 1))}
    {a : WithBot (simplex.{u} n)} {b c d : WithBot point.{u}}
    (hA : botVertices (n + 1) A = pairVertices n b a) (hd : d ≠ ⊥ ↔ c ≠ ⊥ ∨ b ≠ ⊥) :
    (pairVertices (n + 1) c A).image (Fin.predAbove 0) = pairVertices n d a := by
  unfold pairVertices at hA ⊢
  rw [hA]
  simp only [Finset.map_eq_image, Fin.coe_succEmb, Finset.image_union, Finset.image_image,
    Function.comp_def, predAbove_zero_succ, ← Finset.union_assoc]
  congr 1
  induction b using WithBot.recBotCoe <;> induction c using WithBot.recBotCoe <;>
    induction d using WithBot.recBotCoe <;>
    simp_all only [WithBot.recBotCoe_bot, WithBot.recBotCoe_coe, Finset.image_empty,
      Finset.image_singleton, Finset.empty_union, Finset.union_empty, Finset.singleton_union,
      Finset.insert_eq_of_mem, Finset.mem_singleton, predAbove_zero_zero,
      ne_eq, not_true_eq_false, WithBot.coe_ne_bot, not_false_eq_true, or_self, or_true,
      true_or, iff_true, true_iff]

theorem simplexVertices_subset_iff (n : ℕ) {x y : simplex.{u} n} :
    simplexVertices n x ⊆ simplexVertices n y ↔ x ≤ y := by
  rw [simplexVertices, simplexVertices, botVertices_subset_iff]
  exact WithBot.coe_le_coe

theorem simplexVertices_injective (n : ℕ) : Function.Injective (simplexVertices.{u} n) :=
  (botVertices_injective n).comp WithBot.coe_injective

theorem exists_simplexVertices_eq (n : ℕ) (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    ∃ x : simplex.{u} n, simplexVertices n x = S :=
  ⟨simplexCell n S hS, simplexVertices_simplexCell n S hS⟩

theorem card_filter_grade_simplex (n k : ℕ) :
    (Finset.univ.filter fun x : simplex.{u} n => grade ℕ x = k).card = (n + 1).choose (k + 1) := by
  rw [← Finset.card_fin (n + 1), ← Finset.card_powersetCard]
  refine Finset.card_nbij (simplexVertices n) (fun x hx => ?_)
    (simplexVertices_injective n).injOn fun S hS => ?_
  · rw [Finset.coe_filter] at hx
    exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, by rw [card_simplexVertices, hx.2]⟩
  · obtain ⟨-, hS⟩ := Finset.mem_powersetCard.1 (Finset.mem_coe.1 hS)
    obtain ⟨x, rfl⟩ := exists_simplexVertices_eq n S (Finset.card_pos.1 (by omega))
    rw [card_simplexVertices, Nat.add_right_cancel_iff] at hS
    exact ⟨x, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ x, hS⟩), rfl⟩

theorem exists_simplexVertices_eq_erase_of_covBy {n : ℕ} {x y : simplex.{u} n} (h : y ⋖ x) :
    ∃ v ∈ simplexVertices n x, simplexVertices n y = (simplexVertices n x).erase v := by
  have hsub : simplexVertices n y ⊆ simplexVertices n x := (simplexVertices_subset_iff n).2 h.lt.le
  obtain ⟨v, hvy, hxy⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, by
    rw [card_simplexVertices, card_simplexVertices, Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)]⟩
  exact ⟨v, hxy ▸ Finset.mem_insert_self v _, by rw [← hxy, Finset.erase_insert hvy]⟩

private theorem mem_faces_augmentation_simplex_of_erase {n : ℕ}
    (h : ∀ {x y : simplex.{u} n} {v : Fin (n + 1)},
      v ∈ botVertices n (x : WithBot (simplex.{u} n)) →
      botVertices n (y : WithBot (simplex.{u} n)) =
        (botVertices n (x : WithBot (simplex.{u} n))).erase v →
      y ∈ (simplex.{u} n).faces
        (decide (((botVertices n (x : WithBot (simplex.{u} n))).filter fun w => w < v).card % 2 =
          0)) x)
    {a b : WithBot (simplex.{u} n)} {v : Fin (n + 1)}
    (hv : v ∈ botVertices n a) (hb : botVertices n b = (botVertices n a).erase v) :
    b ∈ (augmentation (simplex.{u} n)).faces
      (decide (((botVertices n a).filter fun w => w < v).card % 2 = 0)) a := by
  induction a using WithBot.recBotCoe with
  | bot => simp at hv
  | coe x =>
    induction b using WithBot.recBotCoe with
    | bot =>
      have hx : botVertices n (x : WithBot (simplex.{u} n)) = {v} :=
        ((Finset.erase_eq_empty_iff _ _).1 (by rw [← hb, botVertices_bot])).resolve_left
          (Finset.ne_empty_of_mem hv)
      have hcard := card_botVertices n x
      rw [hx, Finset.card_singleton, WithBot.grade_coe] at hcard
      rw [bot_mem_faces_augmentation, hx, Finset.filter_singleton, if_neg (lt_irrefl v),
        Finset.card_empty]
      exact ⟨grade_eq_zero_iff.1 (by omega), rfl⟩
    | coe y => exact coe_mem_faces_augmentation.2 (h hv hb)

private theorem card_filter_lt_succ_pairVertices (n : ℕ) (c : WithBot point.{u})
    (a : WithBot (simplex.{u} n)) (i : Fin (n + 1)) :
    ((pairVertices n c a).filter fun w => w < i.succ).card =
      grade ℕ c + ((botVertices n a).filter fun w => w < i).card := by
  induction c using WithBot.recBotCoe <;>
    simp [pairVertices, Finset.filter_insert, Fin.succ_pos, Finset.filter_map, Function.comp_def,
      Fin.succ_lt_succ_iff, grade_eq_zero_iff.2 (isMin_point _), Nat.add_comm]

private theorem bodd_xor_decide_grade_add_mod_two_eq_zero (c : WithBot point.{u}) (k : ℕ) :
    ((grade ℕ c).bodd ^^ decide ((grade ℕ c + k) % 2 = 0)) = decide (k % 2 = 0) := by
  induction c using WithBot.recBotCoe <;> rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
    simp [Nat.add_mod, h, grade_eq_zero_iff.2 (isMin_point _)]

theorem mem_faces_simplex_of_erase (n : ℕ) {x y : simplex.{u} n} {v : Fin (n + 1)}
    (hv : v ∈ simplexVertices n x) (hy : simplexVertices n y = (simplexVertices n x).erase v) :
    y ∈ (simplex.{u} n).faces
      (decide (((simplexVertices n x).filter fun w => w < v).card % 2 = 0)) x := by
  unfold simplexVertices at hv hy ⊢
  induction n with
  | zero =>
    rw [botVertices_zero_coe, Finset.mem_singleton] at hv
    simp [hv] at hy
  | succ n ih =>
    rw [botVertices_succ_coe] at hv ⊢
    rw [botVertices_succ_coe, botVertices_succ_coe] at hy
    rcases x with ⟨⟨c₁, a₁⟩, hx⟩
    rcases y with ⟨⟨c₂, a₂⟩, hy'⟩
    dsimp only at hv hy ⊢
    refine (mem_faces_join (P := point.{u}) (Q := simplex.{u} n)
      (p := ⟨(c₁, a₁), hx⟩) (q := ⟨(c₂, a₂), hy'⟩)).2
      ((mem_faces_grayProduct (P := augmentation point.{u})
        (Q := augmentation (simplex.{u} n))).2 ?_)
    dsimp only
    induction v using Fin.cases with
    | zero =>
      obtain ⟨u, rfl⟩ := WithBot.ne_bot_iff_exists.1 (zero_mem_pairVertices_iff.1 hv)
      obtain rfl : c₂ = ⊥ := by simpa using congrArg ((0 : Fin (n + 2)) ∈ ·) hy
      obtain rfl : a₂ = a₁ := botVertices_injective n <| Finset.ext fun i => by
        simpa using congrArg (i.succ ∈ ·) hy
      rw [Finset.filter_false_of_mem fun w _ => Fin.not_lt_zero w, Finset.card_empty]
      exact .inl ⟨bot_mem_faces_augmentation.2 ⟨isMin_point u, rfl⟩, rfl⟩
    | succ i =>
      rw [succ_mem_pairVertices_iff] at hv
      have ha₂ : botVertices n a₂ = (botVertices n a₁).erase i := Finset.ext fun j => by
        simpa [Fin.succ_inj] using congrArg (j.succ ∈ ·) hy
      have h0 : c₂ ≠ ⊥ ↔ c₁ ≠ ⊥ := by
        simpa [(Fin.succ_ne_zero i).symm] using congrArg ((0 : Fin (n + 2)) ∈ ·) hy
      refine .inr ⟨le_antisymm (withBot_point_le_iff.1 h0.1) (withBot_point_le_iff.1 h0.2), ?_⟩
      rw [card_filter_lt_succ_pairVertices, bodd_xor_decide_grade_add_mod_two_eq_zero]
      exact mem_faces_augmentation_simplex_of_erase ih hv ha₂

theorem covBy_of_simplexVertices_eq_erase {n : ℕ} {x y : simplex.{u} n} {v : Fin (n + 1)}
    (hv : v ∈ simplexVertices n x) (hy : simplexVertices n y = (simplexVertices n x).erase v) :
    y ⋖ x :=
  (mem_faces_simplex_of_erase n hv hy).1

theorem orient_simplex_erase (n : ℕ) {x y : simplex.{u} n} {v : Fin (n + 1)}
    (hv : v ∈ simplexVertices n x) (hy : simplexVertices n y = (simplexVertices n x).erase v)
    (h : y ⋖ x) :
    (simplex.{u} n).orient h =
      decide (((simplexVertices n x).filter fun w => w < v).card % 2 = 0) :=
  (mem_faces_simplex_of_erase n hv hy).2

end Atoms.Molecule.OGP
