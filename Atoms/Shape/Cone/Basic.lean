import Atoms.Shape.Join
import Mathlib.Order.Interval.Finset.Fin

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

def cone (B : Atom) : ℕ → Atom
  | 0 => B
  | r + 1 => atomJoin (cone B r) atomPoint

def coneIncl (B : Atom) : (r : ℕ) → (B ⟶ cone B r)
  | 0 => 𝟙 B
  | r + 1 => coneIncl B r ≫ joinInclLeftHom (cone B r) atomPoint

def conePoint (F : Atom) : (r : ℕ) → Fin r → (atomPoint ⟶ cone F r)
  | 0, i => i.elim0
  | r + 1, i => Fin.lastCases (joinInclRightHom (cone F r) atomPoint)
      (fun j => conePoint F r j ≫ joinInclLeftHom (cone F r) atomPoint) i

def coneMap {B B' : Atom} (f : B ⟶ B') : (r : ℕ) → (cone B r ⟶ cone B' r)
  | 0 => f
  | r + 1 => joinHom (coneMap f r) (𝟙 atomPoint)

@[simp] theorem coneMap_id (B : Atom) (r : ℕ) : coneMap (𝟙 B) r = 𝟙 (cone B r) := by
  induction r with
  | zero => rfl
  | succ r ih => exact (congrArg (joinHom · (𝟙 atomPoint)) ih).trans (joinHom_id _ _)

@[reassoc] theorem coneMap_comp {B B' B'' : Atom} (f : B ⟶ B') (g : B' ⟶ B'') (r : ℕ) :
    coneMap (f ≫ g) r = coneMap f r ≫ coneMap g r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact (congrArg (joinHom · (𝟙 atomPoint)) ih).trans
      ((congrArg (joinHom _) (Category.comp_id (𝟙 atomPoint)).symm).trans
        (joinHom_comp _ _ _ _))

def coneFunctor (r : ℕ) : Atom ⥤ Atom where
  obj B := cone B r
  map f := coneMap f r
  map_id B := coneMap_id B r
  map_comp f g := coneMap_comp f g r

def coneAssoc (F : Atom) (k : ℕ) : (r : ℕ) → (cone (cone F k) r ≅ cone F (k + r))
  | 0 => CategoryTheory.Iso.refl _
  | r + 1 =>
    { hom := joinHom (coneAssoc F k r).hom (𝟙 atomPoint)
      inv := joinHom (coneAssoc F k r).inv (𝟙 atomPoint)
      hom_inv_id := (joinHom_comp _ _ _ _).symm.trans
        (by rw [Iso.hom_inv_id, Category.comp_id, joinHom_id]; rfl)
      inv_hom_id := (joinHom_comp _ _ _ _).symm.trans
        (by rw [Iso.inv_hom_id, Category.comp_id, joinHom_id]; rfl) }

theorem coneAssoc_zero (F : Atom) (k : ℕ) : coneAssoc F k 0 = CategoryTheory.Iso.refl _ :=
  rfl

theorem coneAssoc_succ_hom (F : Atom) (k r : ℕ) :
    (coneAssoc F k (r + 1)).hom = joinHom (coneAssoc F k r).hom (𝟙 atomPoint) :=
  rfl

def coneCoord (F : Atom) : (r : ℕ) → WithBot (cone F r).ogp →
    WithBot F.ogp × Finset (Fin r)
  | 0, a => (a, ∅)
  | r + 1, a => WithBot.recBotCoe (⊥, ∅) (fun x =>
      ((coneCoord F r ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x).1.1).1,
        (coneCoord F r
          ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x).1.1).2.map
            Fin.castSuccEmb ∪
          if ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x).1.2 = ⊥ then ∅
          else {Fin.last r})) a

@[simp] theorem coneCoord_bot (F : Atom) (r : ℕ) : coneCoord F r ⊥ = (⊥, ∅) := by
  cases r <;> rfl

@[simp] theorem coneCoord_zero (F : Atom) (a : WithBot (cone F 0).ogp) :
    coneCoord F 0 a = (a, ∅) :=
  rfl

def conePairCoord (F : Atom) (r : ℕ) (a : WithBot (cone F r).ogp)
    (c : WithBot atomPoint.ogp) : WithBot F.ogp × Finset (Fin (r + 1)) :=
  ((coneCoord F r a).1, (coneCoord F r a).2.map Fin.castSuccEmb ∪ if c = ⊥ then ∅ else
    {Fin.last r})

theorem coneCoord_succ_coe (F : Atom) (r : ℕ) (x : (cone F (r + 1)).ogp) :
    coneCoord F (r + 1) x =
      conePairCoord F r ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x).1.1
        ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x).1.2 :=
  rfl

theorem coneCoord_succ_ofOGPIso (F : Atom) (r : ℕ)
    (y : join (cone F r).ogp atomPoint.ogp) :
    coneCoord F (r + 1)
      (WithBot.some ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).hom y) :
        WithBot (cone F (r + 1)).ogp) = conePairCoord F r y.1.1 y.1.2 :=
  (coneCoord_succ_coe F r _).trans
    (congrArg (fun z : join (cone F r).ogp atomPoint.ogp => conePairCoord F r z.1.1 z.1.2)
      (Iso.hom_inv_id_apply _ y))

theorem withBot_atomPoint_le_iff {c c' : WithBot atomPoint.ogp} :
    c ≤ c' ↔ (c ≠ ⊥ → c' ≠ ⊥) := by
  induction c using WithBot.recBotCoe <;> induction c' using WithBot.recBotCoe <;> simp

@[simp] theorem castSucc_mem_conePairCoord_iff {F : Atom} {r : ℕ}
    {a : WithBot (cone F r).ogp} {c : WithBot atomPoint.ogp} {i : Fin r} :
    Fin.castSucc i ∈ (conePairCoord F r a c).2 ↔ i ∈ (coneCoord F r a).2 := by
  unfold conePairCoord
  split_ifs <;> simp [Fin.castSucc_ne_last]

@[simp] theorem last_mem_conePairCoord_iff {F : Atom} {r : ℕ}
    {a : WithBot (cone F r).ogp} {c : WithBot atomPoint.ogp} :
    Fin.last r ∈ (conePairCoord F r a c).2 ↔ c ≠ ⊥ := by
  have hne : ∀ i : Fin r, Fin.castSucc i ≠ Fin.last r := Fin.castSucc_ne_last
  unfold conePairCoord
  split_ifs with h <;> simp [h, hne]

theorem conePairCoord_le_iff {F : Atom} {r : ℕ} {a a' : WithBot (cone F r).ogp}
    {c c' : WithBot atomPoint.ogp} :
    ((conePairCoord F r a c).1 ≤ (conePairCoord F r a' c').1 ∧
      (conePairCoord F r a c).2 ⊆ (conePairCoord F r a' c').2) ↔
      ((coneCoord F r a).1 ≤ (coneCoord F r a').1 ∧
        (coneCoord F r a).2 ⊆ (coneCoord F r a').2) ∧ c ≤ c' := by
  rw [withBot_atomPoint_le_iff, and_assoc]
  refine and_congr Iff.rfl ⟨fun h => ⟨fun i hi => ?_, fun hc => ?_⟩, fun h j hj => ?_⟩
  · exact castSucc_mem_conePairCoord_iff.1 (h (castSucc_mem_conePairCoord_iff.2 hi))
  · exact last_mem_conePairCoord_iff.1 (h (last_mem_conePairCoord_iff.2 hc))
  · induction j using Fin.lastCases with
    | last => exact last_mem_conePairCoord_iff.2 (h.2 (last_mem_conePairCoord_iff.1 hj))
    | cast i =>
      exact castSucc_mem_conePairCoord_iff.2 (h.1 (castSucc_mem_conePairCoord_iff.1 hj))

theorem grade_withBot_cone (F : Atom) (r : ℕ) (a : WithBot (cone F r).ogp) :
    grade ℕ a = grade ℕ (coneCoord F r a).1 + (coneCoord F r a).2.card := by
  induction r with
  | zero =>
    simp only [coneCoord_zero, Finset.card_empty, add_zero]
    rfl
  | succ r ih =>
    induction a using WithBot.recBotCoe with
    | bot => rfl
    | coe x =>
      have hx : grade ℕ x = grade ℕ
          ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x) :=
        ((isMorphism ((FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv)).grade_eq
          x).symm
      change grade ℕ x + 1 = _
      rw [hx, grade_join, coneCoord_succ_coe]
      generalize (FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).inv x = p
      have h1 := one_le_grade_add_grade p
      have hpt : grade ℕ p.1.2 = if p.1.2 = ⊥ then 0 else 1 := by
        induction p.1.2 using WithBot.recBotCoe with
        | bot => rfl
        | coe v =>
          change grade ℕ v + 1 = if (v : WithBot atomPoint.ogp) = ⊥ then 0 else 1
          simp only [WithBot.coe_ne_bot, ↓reduceIte]
          rw [grade_eq_zero_iff.2 fun y _ => (Subsingleton.elim y v).ge]
      have hcard : ((coneCoord F r p.1.1).2.map Fin.castSuccEmb ∪
          (if p.1.2 = ⊥ then ∅ else {Fin.last r})).card =
          (coneCoord F r p.1.1).2.card + (if p.1.2 = ⊥ then 0 else 1) := by
        rw [Finset.card_union_of_disjoint, Finset.card_map]
        · split_ifs <;> simp
        · split_ifs <;> simp [Fin.castSucc_ne_last]
      have hih := ih p.1.1
      simp only [conePairCoord, hcard]
      by_cases hc : p.1.2 = ⊥ <;> simp only [hc, ↓reduceIte] at hpt h1 ⊢ <;> omega

theorem coneCoord_eq_bot_iff {F : Atom} {r : ℕ} {a : WithBot (cone F r).ogp} :
    coneCoord F r a = (⊥, ∅) ↔ a = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ coneCoord_bot F r⟩
  have hg := grade_withBot_cone F r a
  rw [h] at hg
  induction a using WithBot.recBotCoe with
  | bot => rfl
  | coe x => simp at hg

theorem coneCoord_le_coneCoord_iff {F : Atom} {r : ℕ} {a b : WithBot (cone F r).ogp} :
    ((coneCoord F r a).1 ≤ (coneCoord F r b).1 ∧ (coneCoord F r a).2 ⊆ (coneCoord F r b).2) ↔
      a ≤ b := by
  induction r with
  | zero =>
    simp only [coneCoord_zero, Finset.Subset.refl, and_true]
    exact Iff.rfl
  | succ r ih =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
        simp only [coneCoord_bot, le_bot_iff, Finset.subset_empty]
        exact ⟨fun h => coneCoord_eq_bot_iff.1 (Prod.ext h.1 h.2),
          fun h => absurd h WithBot.coe_ne_bot⟩
      | coe y =>
        rw [coneCoord_succ_coe, coneCoord_succ_coe, conePairCoord_le_iff, ih,
          WithBot.coe_le_coe]
        exact join_le_iff.symm.trans
          (orderIsoOfIso (FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)).symm).le_iff_le

theorem coneCoord_injective (F : Atom) (r : ℕ) : Function.Injective (coneCoord F r) :=
  fun _ _ h => le_antisymm
    (coneCoord_le_coneCoord_iff.1 ⟨(congrArg Prod.fst h).le, (congrArg Prod.snd h).subset⟩)
    (coneCoord_le_coneCoord_iff.1 ⟨(congrArg Prod.fst h).ge, (congrArg Prod.snd h).superset⟩)

theorem exists_coneCoord_eq (F : Atom) (r : ℕ) (b : WithBot F.ogp) (S : Finset (Fin r)) :
    ∃ a, coneCoord F r a = (b, S) := by
  induction r with
  | zero => exact ⟨b, Prod.ext rfl (Finset.eq_empty_of_forall_notMem fun i => i.elim0).symm⟩
  | succ r ih =>
    obtain ⟨a, ha⟩ := ih (S.preimage Fin.castSucc (Fin.castSucc_injective r).injOn)
    let c : WithBot atomPoint.ogp :=
      if Fin.last r ∈ S then ((default : atomPoint.ogp) : WithBot _) else ⊥
    have key : conePairCoord F r a c = (b, S) := by
      refine Prod.ext (by rw [conePairCoord, ha]) (Finset.ext fun j => ?_)
      induction j using Fin.lastCases with
      | last =>
        rw [last_mem_conePairCoord_iff]
        by_cases h : Fin.last r ∈ S <;> simp [c, h]
      | cast i => rw [castSucc_mem_conePairCoord_iff, ha, Finset.mem_preimage]
    by_cases hac : (a, c) = (⊥, ⊥)
    · refine ⟨⊥, ?_⟩
      rw [← key, coneCoord_bot, conePairCoord, (Prod.mk.inj hac).1, (Prod.mk.inj hac).2]
      simp
    · exact ⟨_, (coneCoord_succ_ofOGPIso F r ⟨(a, c), hac⟩).trans key⟩

theorem exists_coneCoord_eq_of_ne (F : Atom) (r : ℕ) (b : WithBot F.ogp) (S : Finset (Fin r))
    (h : (b, S) ≠ (⊥, ∅)) : ∃ x : (cone F r).ogp, coneCoord F r x = (b, S) := by
  obtain ⟨a, ha⟩ := exists_coneCoord_eq F r b S
  induction a using WithBot.recBotCoe with
  | bot => exact absurd ((coneCoord_bot F r).symm.trans ha).symm h
  | coe x => exact ⟨x, ha⟩

theorem coneCoord_joinHom {B B' : Atom} {r r' : ℕ} (f : cone B r ⟶ cone B' r')
    (x : (cone B (r + 1)).ogp) :
    coneCoord B' (r' + 1) (WithBot.some (joinHom f (𝟙 atomPoint) x) :
        WithBot (cone B' (r' + 1)).ogp) =
      conePairCoord B' r'
        (((FiniteOGP.ofOGPIso (join (cone B r).ogp atomPoint.ogp)).inv x).1.1.map f)
        ((FiniteOGP.ofOGPIso (join (cone B r).ogp atomPoint.ogp)).inv x).1.2 := by
  refine (coneCoord_succ_ofOGPIso B' r' _).trans ?_
  rw [joinMap_val]
  exact congrArg _ (congrFun WithBot.map_id _)

theorem coneCoord_joinInclLeftHom (F : Atom) (r : ℕ) (y : (cone F r).ogp) :
    coneCoord F (r + 1) (WithBot.some (joinInclLeftHom (cone F r) atomPoint y) :
        WithBot (cone F (r + 1)).ogp) =
      ((coneCoord F r y).1, (coneCoord F r y).2.map Fin.castSuccEmb) := by
  refine (coneCoord_succ_ofOGPIso F r _).trans ?_
  change conePairCoord F r (joinInclLeft _ _ y).1.1 (joinInclLeft _ _ y).1.2 = _
  simp only [conePairCoord, joinInclLeft, ↓reduceIte, Finset.union_empty]

theorem coneCoord_joinInclRightHom (F : Atom) (r : ℕ) (v : atomPoint.ogp) :
    coneCoord F (r + 1) (WithBot.some (joinInclRightHom (cone F r) atomPoint v) :
        WithBot (cone F (r + 1)).ogp) = (⊥, {Fin.last r}) := by
  refine (coneCoord_succ_ofOGPIso F r _).trans ?_
  change conePairCoord F r (joinInclRight _ _ v).1.1 (joinInclRight _ _ v).1.2 = _
  simp [conePairCoord, joinInclRight]

@[simp] theorem coneCoord_coneIncl (F : Atom) (r : ℕ) (b : F.ogp) :
    coneCoord F r (coneIncl F r b) = ((b : WithBot F.ogp), ∅) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    refine (coneCoord_joinInclLeftHom F r (coneIncl F r b)).trans ?_
    rw [ih]
    simp

theorem conePoint_last (F : Atom) (r : ℕ) :
    conePoint F (r + 1) (Fin.last r) = joinInclRightHom (cone F r) atomPoint :=
  Fin.lastCases_last

theorem conePoint_castSucc (F : Atom) (r : ℕ) (i : Fin r) :
    conePoint F (r + 1) (Fin.castSucc i) =
      conePoint F r i ≫ joinInclLeftHom (cone F r) atomPoint :=
  Fin.lastCases_castSucc _

@[simp] theorem coneCoord_conePoint (F : Atom) (r : ℕ) (i : Fin r) (v : atomPoint.ogp) :
    coneCoord F r (conePoint F r i v) = (⊥, {i}) := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    induction i using Fin.lastCases with
    | last =>
      rw [conePoint_last]
      exact coneCoord_joinInclRightHom F r v
    | cast j =>
      rw [conePoint_castSucc]
      refine (coneCoord_joinInclLeftHom F r (conePoint F r j v)).trans ?_
      rw [ih]
      simp

@[simp] theorem coneCoord_coneMap {B B' : Atom} (f : B ⟶ B') (r : ℕ)
    (a : WithBot (cone B r).ogp) :
    coneCoord B' r (a.map (coneMap f r)) =
      ((coneCoord B r a).1.map f, (coneCoord B r a).2) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      refine (coneCoord_joinHom (coneMap f r) x).trans ?_
      rw [coneCoord_succ_coe, conePairCoord, conePairCoord, ih]

theorem coneCoord_coneAssoc (F : Atom) (k r : ℕ) (a : WithBot (cone (cone F k) r).ogp) :
    coneCoord F (k + r) (a.map (coneAssoc F k r).hom) =
      ((coneCoord F k (coneCoord (cone F k) r a).1).1,
        (coneCoord F k (coneCoord (cone F k) r a).1).2.map (Fin.castAddEmb r) ∪
          (coneCoord (cone F k) r a).2.map (Fin.natAddEmb k)) := by
  induction r with
  | zero =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      refine Prod.ext rfl (Finset.ext fun i => ?_)
      simp only [coneCoord_zero, Finset.map_empty, Finset.union_empty, Finset.mem_map,
        Fin.castAddEmb_apply]
      exact ⟨fun h => ⟨i, h, rfl⟩, fun ⟨j, hj, hji⟩ => by subst hji; exact hj⟩
  | succ r ih =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      refine (coneCoord_joinHom (coneAssoc F k r).hom x).trans ?_
      rw [coneCoord_succ_coe]
      generalize (FiniteOGP.ofOGPIso (join (cone (cone F k) r).ogp atomPoint.ogp)).inv x = p
      rw [conePairCoord, conePairCoord, ih]
      refine Prod.ext rfl ?_
      generalize (coneCoord F k (coneCoord (cone F k) r p.1.1).1).2 = S₁
      generalize (coneCoord (cone F k) r p.1.1).2 = S₂
      generalize p.1.2 = c
      have e₁ : (Fin.castAddEmb r).trans Fin.castSuccEmb =
          (Fin.castAddEmb (r + 1) : Fin k ↪ Fin (k + (r + 1))) := by
        ext; simp
      have e₂ : (Fin.natAddEmb k).trans Fin.castSuccEmb =
          (Fin.castSuccEmb (n := r)).trans (Fin.natAddEmb k) := by
        ext; simp
      dsimp only
      rw [Finset.map_union, Finset.map_map, Finset.map_map, Finset.map_union, Finset.map_map, e₁,
        e₂, Finset.union_assoc]
      congr 2
      split_ifs <;> simp [Fin.natAdd_last]

theorem eq_of_coneCoord_eq {F : Atom} {r : ℕ} {x y : (cone F r).ogp}
    (h : coneCoord F r x = coneCoord F r y) : x = y :=
  WithBot.coe_injective (coneCoord_injective F r h)

theorem exists_coneIncl_eq_of_coneCoord_snd_eq_empty {B : Atom} {r : ℕ}
    {z : (cone B r).ogp} (hz : (coneCoord B r z).2 = ∅) :
    ∃ b, coneIncl B r b = z := by
  obtain ⟨b, hb⟩ : ∃ b : B.ogp, (b : WithBot _) = (coneCoord B r z).1 :=
    WithBot.ne_bot_iff_exists.1 fun h => WithBot.coe_ne_bot (a := z)
      (coneCoord_eq_bot_iff.1 (Prod.ext h hz))
  exact ⟨b, eq_of_coneCoord_eq (by rw [coneCoord_coneIncl, hb, ← hz])⟩

@[reassoc (attr := simp)] theorem conePoint_comp_coneAssoc (F : Atom) (k r : ℕ) (i : Fin r) :
    conePoint (cone F k) r i ≫ (coneAssoc F k r).hom = conePoint F (k + r) (Fin.natAdd k i) := by
  refine Atom.hom_ext fun v => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneAssoc, coneCoord_conePoint,
    coneCoord_conePoint]
  simp

private def simplexRightIso : (r : ℕ) → join (simplex.{0} r) point ≅ simplex.{0} (r + 1)
  | 0 => Iso.refl _
  | r + 1 => joinAssoc point (simplex r) point ≪≫
      join.mapIso (Iso.refl point) (simplexRightIso r)

private theorem simplexVertices_simplexRightIso (r : ℕ) (p : join (simplex.{0} r) point) :
    simplexVertices (r + 1) ((simplexRightIso r).hom p) =
      (botVertices r p.1.1).map Fin.castSuccEmb ∪
        if p.1.2 = ⊥ then ∅ else {Fin.last (r + 1)} := by
  induction r with
  | zero =>
    revert p
    decide
  | succ r ih =>
    set q := (joinAssoc point (simplex r) point).hom p
    have hq : joinRightComponents point (simplex r) point q =
        joinLeftComponents point (simplex r) point p :=
      joinRightComponents_joinAssocFun _ _ _ p
    simp only [joinRightComponents, joinLeftComponents, Prod.mk.injEq] at hq
    have hbw : ∀ w : WithBot (join (simplex.{0} r) point),
        botVertices (r + 1) (w.map (simplexRightIso r).hom) =
          (botVertices r (joinBotFst w)).map Fin.castSuccEmb ∪
            if joinBotSnd w = ⊥ then ∅ else {Fin.last (r + 1)} := by
      intro w
      induction w using WithBot.recBotCoe with
      | bot => simp [joinBotFst, joinBotSnd]
      | coe z => exact ih z
    change pairVertices (r + 1) (q.1.1.map id) (q.1.2.map (simplexRightIso r).hom) = _
    rw [WithBot.map_id, id_eq, pairVertices, hbw, hq.1, hq.2.1, hq.2.2, botVertices_succ,
      pairVertices]
    have e : (Fin.succEmb (r + 1)).trans Fin.castSuccEmb =
        (Fin.castSuccEmb (n := r + 1)).trans (Fin.succEmb (r + 2)) := by
      ext; simp
    rw [Finset.map_union, Finset.map_union, Finset.map_map, Finset.map_map, e,
      Finset.union_assoc]
    congr 1
    · induction joinBotFst p.1.1 using WithBot.recBotCoe <;> simp
    · congr 1
      by_cases h2 : p.1.2 = ⊥ <;> simp [h2]

private theorem simplexVertices_eq_of_simplexRightIso_inv (r : ℕ) (x : simplex.{0} (r + 1)) :
    simplexVertices (r + 1) x =
      (botVertices r ((simplexRightIso r).inv x).1.1).map Fin.castSuccEmb ∪
        if ((simplexRightIso r).inv x).1.2 = ⊥ then ∅ else {Fin.last (r + 1)} :=
  (congrArg (simplexVertices (r + 1))
    (ConcreteCategory.congr_hom (simplexRightIso r).inv_hom_id x).symm).trans
    (simplexVertices_simplexRightIso r ((simplexRightIso r).inv x))

def coneJoinSimplexIso (F : Atom) :
    (r : ℕ) → join F.ogp (simplex r) ≅ (cone F (r + 1)).ogp
  | 0 => join.mapIso (Iso.refl F.ogp) (FiniteOGP.ofOGPIso point : point ≅ atomPoint.ogp) ≪≫
      FiniteOGP.ofOGPIso (join F.ogp atomPoint.ogp)
  | r + 1 => join.mapIso (Iso.refl F.ogp) (simplexRightIso r).symm ≪≫
      (joinAssoc F.ogp (simplex r) point).symm ≪≫
      join.mapIso (coneJoinSimplexIso F r) (FiniteOGP.ofOGPIso point : point ≅ atomPoint.ogp) ≪≫
      FiniteOGP.ofOGPIso (join (cone F (r + 1)).ogp atomPoint.ogp)

theorem coneCoord_coneJoinSimplexIso (F : Atom) (r : ℕ) (p : join F.ogp (simplex r)) :
    coneCoord F (r + 1) ((coneJoinSimplexIso F r).hom p) = (p.1.1, botVertices r p.1.2) := by
  induction r with
  | zero =>
    refine (coneCoord_succ_ofOGPIso F 0 _).trans ?_
    obtain ⟨⟨a, c⟩, hac⟩ := p
    induction a using WithBot.recBotCoe <;> induction c using WithBot.recBotCoe
    · exact absurd rfl hac
    all_goals rfl
  | succ r ih =>
    set p' : join F.ogp (join (simplex r) point) :=
      (join.mapIso (Iso.refl F.ogp) (simplexRightIso r).symm).hom p
    set q := (joinAssoc F.ogp (simplex r) point).inv p'
    refine (coneCoord_succ_ofOGPIso F (r + 1)
      ((join.mapIso (coneJoinSimplexIso F r)
        (FiniteOGP.ofOGPIso point : point ≅ atomPoint.ogp)).hom q)).trans ?_
    have hq : joinLeftComponents F.ogp (simplex r) point q =
        joinRightComponents F.ogp (simplex r) point p' :=
      joinLeftComponents_joinAssocInvFun _ _ _ p'
    simp only [joinLeftComponents, joinRightComponents, Prod.mk.injEq] at hq
    have hcc : coneCoord F (r + 1) (q.1.1.map (coneJoinSimplexIso F r).hom) =
        (joinBotFst q.1.1, botVertices r (joinBotSnd q.1.1)) := by
      induction q.1.1 using WithBot.recBotCoe with
      | bot => simp
      | coe w => exact ih w
    have hp'1 : p'.1.1 = p.1.1 := congrFun WithBot.map_id p.1.1
    have hp'2 : p'.1.2 = p.1.2.map (simplexRightIso r).inv := rfl
    change conePairCoord F (r + 1) (q.1.1.map (coneJoinSimplexIso F r).hom)
      (q.1.2.map (FiniteOGP.ofOGPIso point : point ≅ atomPoint.ogp).hom) = _
    unfold conePairCoord
    rw [hcc]
    refine Prod.ext (hq.1.trans hp'1) ?_
    dsimp only
    rw [hq.2.1, hq.2.2, hp'2]
    induction p.1.2 using WithBot.recBotCoe with
    | bot =>
      change (botVertices r ⊥).map Fin.castSuccEmb ∪
        (if (⊥ : WithBot atomPoint.ogp) = ⊥ then ∅ else {Fin.last (r + 1)}) = ∅
      simp
    | coe x =>
      refine Eq.trans ?_ (simplexVertices_eq_of_simplexRightIso_inv r x).symm
      congr 1
      change (if (((simplexRightIso r).inv x).1.2).map (FiniteOGP.ofOGPIso point).hom = ⊥
        then ∅ else {Fin.last (r + 1)}) = _
      induction ((simplexRightIso r).inv x).1.2 using WithBot.recBotCoe <;> simp

def coneHom (F : Atom) {r s : ℕ} (σ : Fin r →o Fin s) : cone F r ⟶ cone F s :=
  match r, s, σ with
  | 0, s, _ => coneIncl F s
  | _ + 1, 0, σ => (σ 0).elim0
  | r + 1, s + 1, σ =>
    haveI := Monotone.functor_isFibered_id (α := F.ogp)
    haveI := functor_isFibered_simplexMap σ
    haveI := functor_isFibered_joinMap (IsMap.id F.ogp).monotone (isMap_simplexMap σ).monotone
    Atom.conjHom (coneJoinSimplexIso F r) (coneJoinSimplexIso F s)
      (joinMap id (simplexMap σ))
      (isMap_joinMap F.isRDC F.isRDC (isRDC_simplex r) (isRDC_simplex s) (IsMap.id _)
        (isMap_simplexMap σ))

theorem coneCoord_coneHom (F : Atom) {r s : ℕ} (σ : Fin r →o Fin s)
    (a : WithBot (cone F r).ogp) :
    coneCoord F s (a.map (coneHom F σ)) = ((coneCoord F r a).1, (coneCoord F r a).2.image σ) := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe x =>
    match r, s, σ with
    | 0, s, σ =>
      exact (coneCoord_coneIncl F s x).trans rfl
    | _ + 1, 0, σ => exact (σ 0).elim0
    | r + 1, s + 1, σ =>
      set p := (coneJoinSimplexIso F r).inv x
      have hx : coneCoord F (r + 1) x = (p.1.1, botVertices r p.1.2) :=
        Iso.inv_hom_id_apply (coneJoinSimplexIso F r) x ▸ coneCoord_coneJoinSimplexIso F r p
      refine (coneCoord_coneJoinSimplexIso F s (joinMap id (simplexMap σ) p)).trans ?_
      rw [hx]
      exact Prod.ext (congrFun WithBot.map_id _) (botVertices_map_simplexMap σ p.1.2)

@[reassoc (attr := simp)] theorem coneIncl_comp_coneHom (F : Atom) {r s : ℕ}
    (σ : Fin r →o Fin s) : coneIncl F r ≫ coneHom F σ = coneIncl F s := by
  refine Atom.hom_ext fun b => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneHom, coneCoord_coneIncl,
    coneCoord_coneIncl]
  simp

@[reassoc (attr := simp)] theorem conePoint_comp_coneHom (F : Atom) {r s : ℕ}
    (σ : Fin r →o Fin s) (i : Fin r) : conePoint F r i ≫ coneHom F σ = conePoint F s (σ i) := by
  refine Atom.hom_ext fun v => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneHom, coneCoord_conePoint,
    coneCoord_conePoint]
  simp

@[reassoc] theorem coneIncl_comp_coneAssoc (F : Atom) (k r : ℕ) :
    coneIncl (cone F k) r ≫ (coneAssoc F k r).hom =
      coneHom F ⟨Fin.castAdd r, fun _ _ h => h⟩ := by
  refine Atom.hom_ext fun v => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneAssoc, coneCoord_coneIncl,
    ← WithBot.map_coe, coneCoord_coneHom]
  simp [Finset.map_eq_image]
  rfl

theorem coneCoord_map_coneIncl (F : Atom) (r : ℕ) (a : WithBot F.ogp) :
    coneCoord F r (a.map (coneIncl F r)) = (a, ∅) := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe b => exact coneCoord_coneIncl F r b

theorem le_iff_coneCoord {F : Atom} {r : ℕ} {x y : (cone F r).ogp} :
    x ≤ y ↔ (coneCoord F r x).1 ≤ (coneCoord F r y).1 ∧
      (coneCoord F r x).2 ⊆ (coneCoord F r y).2 :=
  WithBot.coe_le_coe.symm.trans coneCoord_le_coneCoord_iff.symm

theorem coneCoord_apply_of_comp_conePoint {B F : Atom} {r s : ℕ} (h : cone B r ⟶ cone F s)
    (τ : Fin r → Fin s) (hτ : ∀ i, conePoint B r i ≫ h = conePoint F s (τ i))
    (z : (cone B r).ogp) :
    coneCoord F s (h z) =
      ((coneCoord F s ((coneCoord B r z).1.map (coneIncl B r ≫ h))).1,
        (coneCoord F s ((coneCoord B r z).1.map (coneIncl B r ≫ h))).2 ∪
          (coneCoord B r z).2.image τ) := by
  set x := (coneCoord B r z).1 with hx
  set S := (coneCoord B r z).2 with hS
  set fK := coneCoord F s (x.map (coneIncl B r ≫ h)) with hfK
  have hpt : ∀ i ∈ S, conePoint B r i default ≤ z := fun i hi => by
    rw [le_iff_coneCoord, coneCoord_conePoint]
    exact ⟨bot_le, Finset.singleton_subset_iff.2 hi⟩
  have hhpt : ∀ i, h (conePoint B r i default) = conePoint F s (τ i) default :=
    fun i => ConcreteCategory.congr_hom (hτ i) default
  have hw : coneCoord B r (x.map (coneIncl B r)) = (x, ∅) := coneCoord_map_coneIncl B r x
  have hwz : x.map (coneIncl B r) ≤ (z : WithBot (cone B r).ogp) := by
    rw [← coneCoord_le_coneCoord_iff, hw]
    exact ⟨le_rfl, Finset.empty_subset _⟩
  have hwh : (x.map (coneIncl B r)).map h = x.map (coneIncl B r ≫ h) :=
    Option.map_map _ _ _
  obtain ⟨y, hy⟩ := exists_coneCoord_eq_of_ne F s fK.1 (fK.2 ∪ S.image τ) fun he => by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    have h2 := Finset.union_eq_empty.1 h₂
    have hS0 : S = ∅ := Finset.image_eq_empty.1 h2.2
    have hfK0 : fK = (⊥, ∅) := Prod.ext h₁ h2.1
    rw [hfK, coneCoord_eq_bot_iff, WithBot.map_eq_bot_iff] at hfK0
    exact WithBot.coe_ne_bot (coneCoord_eq_bot_iff.1 (Prod.ext hfK0 hS0))
  have hyle : y ≤ h z := by
    rw [le_iff_coneCoord, hy]
    have hb : fK.1 ≤ (coneCoord F s (h z)).1 ∧ fK.2 ⊆ (coneCoord F s (h z)).2 := by
      rw [hfK, ← hwh, coneCoord_le_coneCoord_iff]
      exact (Atom.isMap h).monotone.withBot_map hwz
    refine ⟨hb.1, Finset.union_subset hb.2 fun j hj => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    have := (le_iff_coneCoord.1 ((Atom.isMap h).monotone (hpt i hi))).2
    rw [hhpt, coneCoord_conePoint] at this
    exact this (Finset.mem_singleton_self _)
  have := Atom.functor_isFibered h
  obtain ⟨y', hy'z, hy'eq, hmax⟩ := (Atom.isMap h).monotone.exists_lift hyle
  have hzy' : z ≤ y' := by
    rw [le_iff_coneCoord]
    have hwy' : x.map (coneIncl B r) ≤ (y' : WithBot (cone B r).ogp) :=
      WithBot.le_coe_iff.2 fun w hw' => hmax w (WithBot.coe_le_coe.1 (hw' ▸ hwz)) (by
        rw [le_iff_coneCoord, hy, hfK, ← hwh, hw']
        exact ⟨le_rfl, Finset.subset_union_left⟩)
    have hb := coneCoord_le_coneCoord_iff.2 hwy'
    rw [hw] at hb
    refine ⟨hb.1, fun i hi => ?_⟩
    have hle := hmax _ (hpt i hi) (by
      rw [hhpt, le_iff_coneCoord, coneCoord_conePoint, hy]
      exact ⟨bot_le, Finset.singleton_subset_iff.2
        (Finset.mem_union_right _ (Finset.mem_image_of_mem τ hi))⟩)
    have := (le_iff_coneCoord.1 hle).2
    rw [coneCoord_conePoint] at this
    exact this (Finset.mem_singleton_self _)
  rwa [← le_antisymm hy'z hzy', hy'eq]

theorem eq_coneHom {F : Atom} {r s : ℕ} (σ : Fin r →o Fin s) {h : cone F r ⟶ cone F s}
    (h₀ : coneIncl F r ≫ h = coneIncl F s)
    (h₁ : ∀ i, conePoint F r i ≫ h = conePoint F s (σ i)) : h = coneHom F σ := by
  refine Atom.hom_ext fun z => eq_of_coneCoord_eq ?_
  rw [coneCoord_apply_of_comp_conePoint h σ h₁,
    coneCoord_apply_of_comp_conePoint (coneHom F σ) σ (conePoint_comp_coneHom F σ),
    coneIncl_comp_coneHom, h₀]

@[simp] theorem coneHom_id (F : Atom) (r : ℕ) : coneHom F (OrderHom.id : Fin r →o Fin r) = 𝟙 _ :=
  (eq_coneHom _ (Category.comp_id _) fun _ => Category.comp_id _).symm

@[reassoc] theorem coneHom_comp (F : Atom) {r s t : ℕ} (σ : Fin r →o Fin s) (σ' : Fin s →o Fin t) :
    coneHom F σ ≫ coneHom F σ' = coneHom F (σ'.comp σ) :=
  eq_coneHom _ (by simp) (fun i => by simp)

theorem cone_hom_ext {B F : Atom} {r s : ℕ} {h h' : cone B r ⟶ cone F s} (τ : Fin r → Fin s)
    (hτ : ∀ i, conePoint B r i ≫ h = conePoint F s (τ i))
    (hτ' : ∀ i, conePoint B r i ≫ h' = conePoint F s (τ i))
    (h₀ : coneIncl B r ≫ h = coneIncl B r ≫ h') : h = h' := by
  refine Atom.hom_ext fun z => eq_of_coneCoord_eq ?_
  rw [coneCoord_apply_of_comp_conePoint h τ hτ, coneCoord_apply_of_comp_conePoint h' τ hτ', h₀]

theorem isInclusionHom_coneHom (F : Atom) {r s : ℕ} {σ : Fin r →o Fin s}
    (hσ : Function.Injective σ) : IsInclusionHom (coneHom F σ) := by
  intro x y h
  refine eq_of_coneCoord_eq ?_
  have h' := congrArg (coneCoord F s ∘ WithBot.some) h
  simp only [Function.comp_apply] at h'
  rw [← WithBot.map_coe, ← WithBot.map_coe, coneCoord_coneHom, coneCoord_coneHom,
    Prod.mk.injEq] at h'
  exact Prod.ext h'.1 (Finset.image_injective hσ h'.2)

theorem isInclusionHom_coneMap {B B' : Atom} {f : B ⟶ B'} (hf : IsInclusionHom f) (r : ℕ) :
    IsInclusionHom (coneMap f r) := by
  intro x y h
  have hx := coneCoord_coneMap f r (x : WithBot _)
  have hy := coneCoord_coneMap f r (y : WithBot _)
  rw [WithBot.map_coe, h, ← WithBot.map_coe, hy] at hx
  refine eq_of_coneCoord_eq (Prod.ext ?_ (congrArg Prod.snd hx).symm)
  exact Option.map_injective hf (congrArg Prod.fst hx).symm

theorem exists_comp_coneHom_eq {T F : Atom} {r s : ℕ} (g : T ⟶ cone F s) {σ : Fin r →o Fin s}
    (hσ : Function.Injective σ)
    (h : (coneCoord F s (g T.top)).2 ⊆ Finset.univ.image σ) :
    ∃ g' : T ⟶ cone F r, g' ≫ coneHom F σ = g := by
  refine exists_comp_eq_of_isInclusionHom _ (isInclusionHom_coneHom F hσ) g fun t => ?_
  have hS : (coneCoord F s (g t)).2 ⊆ Finset.univ.image σ :=
    ((le_iff_coneCoord.1 ((Atom.isMap g).monotone (T.le_top t))).2).trans h
  obtain ⟨a, ha⟩ := exists_coneCoord_eq F r (coneCoord F s (g t)).1
    (Finset.univ.filter fun i => σ i ∈ (coneCoord F s (g t)).2)
  have him : coneCoord F s (a.map (coneHom F σ)) = coneCoord F s (g t) := by
    rw [coneCoord_coneHom, ha]
    refine Prod.ext rfl (Finset.ext fun j => ?_)
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨i, hi, hij⟩ => hij ▸ hi, fun hj => ?_⟩
    obtain ⟨i, -, hij⟩ := Finset.mem_image.1 (hS hj)
    exact ⟨i, hij ▸ hj, hij⟩
  exact (WithBot.map_eq_some_iff.1 (coneCoord_injective F s him)).imp fun _ => And.right

theorem exists_comp_coneMap_eq {T B B' : Atom} {r : ℕ} (j : B' ⟶ B) (hj : IsInclusionHom j)
    (g : T ⟶ cone B r)
    (h : ∀ c : B.ogp, (coneCoord B r (g T.top)).1 = c → c ≤ j B'.top) :
    ∃ g' : T ⟶ cone B' r, g' ≫ coneMap j r = g := by
  refine exists_comp_eq_of_isInclusionHom _ (isInclusionHom_coneMap hj r) g fun t => ?_
  have hle := (le_iff_coneCoord.1 ((Atom.isMap g).monotone (T.le_top t))).1
  obtain ⟨b', hb'⟩ : ∃ b' : WithBot B'.ogp, b'.map j = (coneCoord B r (g t)).1 := by
    generalize (coneCoord B r (g t)).1 = bt at hle
    induction bt using WithBot.recBotCoe with
    | bot => exact ⟨⊥, rfl⟩
    | coe c₁ =>
      obtain ⟨c, hc, hc₁c⟩ := WithBot.coe_le_iff.1 hle
      obtain ⟨c', -, hc'⟩ := (Atom.isMap j).fibration (hc₁c.trans (h c hc))
      exact ⟨c', by rw [WithBot.map_coe, hc']⟩
  obtain ⟨a, ha⟩ := exists_coneCoord_eq B' r b' (coneCoord B r (g t)).2
  have him : coneCoord B r (a.map (coneMap j r)) = coneCoord B r (g t) := by
    rw [coneCoord_coneMap, ha, hb']
  exact (WithBot.map_eq_some_iff.1 (coneCoord_injective B r him)).imp fun _ => And.right

theorem isCollapseHom_coneMap {B B' : Atom} (f : B ⟶ B') (hf : IsCollapseHom f) (r : ℕ) :
    IsCollapseHom (coneMap f r) := by
  intro x
  obtain ⟨b, hb⟩ : ∃ b : WithBot B.ogp, b.map f = (coneCoord B' r x).1 := by
    induction (coneCoord B' r x).1 using WithBot.recBotCoe with
    | bot => exact ⟨⊥, rfl⟩
    | coe b' =>
      obtain ⟨b, rfl⟩ := hf b'
      exact ⟨b, rfl⟩
  obtain ⟨y, hy⟩ := exists_coneCoord_eq B r b (coneCoord B' r x).2
  have him : coneCoord B' r (y.map (coneMap f r)) = coneCoord B' r x := by
    rw [coneCoord_coneMap, hy, hb]
  exact (WithBot.map_eq_some_iff.1 (coneCoord_injective B' r him)).imp fun _ => And.right

def atomJoinSimplexPointIso (r : ℕ) : atomJoin (atomSimplex r) atomPoint ≅ atomSimplex (r + 1) :=
  Atom.isoOfIso ((FiniteOGP.ofOGPIso (join (atomSimplex r).ogp atomPoint.ogp)).symm ≪≫
    join.mapIso (FiniteOGP.ofOGPIso (simplex r)).symm (FiniteOGP.ofOGPIso point).symm ≪≫
    simplexRightIso r ≪≫
    FiniteOGP.ofOGPIso (simplex (r + 1)))

def coneAtomPointIso : (r : ℕ) → (cone atomPoint r ≅ atomSimplex r)
  | 0 => CategoryTheory.Iso.refl _
  | r + 1 =>
    { hom := joinHom (coneAtomPointIso r).hom (𝟙 atomPoint)
      inv := joinHom (coneAtomPointIso r).inv (𝟙 atomPoint)
      hom_inv_id := (joinHom_comp _ _ _ _).symm.trans
        (by rw [Iso.hom_inv_id, Category.comp_id, joinHom_id]; rfl)
      inv_hom_id := (joinHom_comp _ _ _ _).symm.trans
        (by rw [Iso.inv_hom_id, Category.comp_id, joinHom_id]) } ≪≫
      atomJoinSimplexPointIso r

def conePointVertices (r : ℕ) (c : WithBot atomPoint.ogp × Finset (Fin r)) :
    Finset (Fin (r + 1)) :=
  (if c.1 = ⊥ then ∅ else {0}) ∪ c.2.map (Fin.succEmb r)

theorem conePointVertices_conePairCoord (r : ℕ) (a : WithBot (cone atomPoint r).ogp)
    (c : WithBot atomPoint.ogp) :
    conePointVertices (r + 1) (conePairCoord atomPoint r a c) =
      (conePointVertices r (coneCoord atomPoint r a)).map Fin.castSuccEmb ∪
        if c = ⊥ then ∅ else {Fin.last (r + 1)} := by
  have e : (Fin.castSuccEmb (n := r)).trans (Fin.succEmb (r + 1)) =
      (Fin.succEmb r).trans Fin.castSuccEmb := by
    ext; simp
  simp only [conePointVertices, conePairCoord, Finset.map_union, Finset.map_map, e,
    Finset.union_assoc]
  congr 1
  · by_cases h : (coneCoord atomPoint r a).1 = ⊥ <;> simp [h]
  · congr 1
    by_cases h : c = ⊥ <;> simp [h]

theorem botVertices_coneAtomPointIso (r : ℕ) (a : WithBot (cone atomPoint r).ogp) :
    botVertices r (a.map fun x => (FiniteOGP.ofOGPIso (simplex r)).inv
      ((coneAtomPointIso r).hom x)) = conePointVertices r (coneCoord atomPoint r a) := by
  induction r with
  | zero =>
    induction a using WithBot.recBotCoe with
    | bot => rfl
    | coe x => rfl
  | succ r ih =>
    induction a using WithBot.recBotCoe with
    | bot => simp [conePointVertices]
    | coe x =>
      set p := (FiniteOGP.ofOGPIso (join (cone atomPoint r).ogp atomPoint.ogp)).inv x
      have hel : (FiniteOGP.ofOGPIso (simplex (r + 1))).inv
          ((coneAtomPointIso (r + 1)).hom x) =
          (simplexRightIso r).hom (joinMap (fun y => (FiniteOGP.ofOGPIso (simplex r)).inv
            ((coneAtomPointIso r).hom y)) (FiniteOGP.ofOGPIso point).inv p) := by
        refine (Iso.hom_inv_id_apply _ _).trans (congrArg (simplexRightIso r).hom ?_)
        refine (congrArg (joinMap _ _) (Iso.hom_inv_id_apply _ _)).trans ?_
        exact (congrFun (joinMap_comp _ _ _ _) p).symm
      refine (congrArg (botVertices (r + 1) ∘ WithBot.some) hel).trans
        ((simplexVertices_simplexRightIso r _).trans ?_)
      refine Eq.trans ?_ (conePointVertices_conePairCoord r p.1.1 p.1.2).symm
      congr 1
      · exact congrArg (Finset.map Fin.castSuccEmb) (ih p.1.1)
      · change (if p.1.2.map (FiniteOGP.ofOGPIso point).inv = ⊥ then ∅ else {Fin.last (r + 1)}) = _
        induction p.1.2 using WithBot.recBotCoe <;> rfl

theorem dimension_cone (B : Atom) (r : ℕ) : (cone B r).dimension = B.dimension + r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    refine (dimension_atomJoin (cone B r) atomPoint).trans ?_
    rw [ih, dimension_atomPoint]
    rfl

theorem grade_cone_add_one (F : Atom) (r : ℕ) (x : (cone F r).ogp) :
    grade ℕ x + 1 = grade ℕ (coneCoord F r x).1 + (coneCoord F r x).2.card :=
  grade_withBot_cone F r x

theorem exists_eq_of_grade_eq_zero_cone {B : Atom} {r : ℕ} {v : (cone B r).ogp}
    (hv : grade ℕ v = 0) :
    (∃ b, coneIncl B r b = v) ∨ ∃ i, conePoint B r i default = v := by
  have h := grade_cone_add_one B r v
  rw [hv] at h
  induction hb : (coneCoord B r v).1 using WithBot.recBotCoe with
  | coe b =>
    rw [hb, WithBot.grade_coe] at h
    exact Or.inl (exists_coneIncl_eq_of_coneCoord_snd_eq_empty (Finset.card_eq_zero.1 (by omega)))
  | bot =>
    rw [hb, grade_bot, Nat.bot_eq_zero] at h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (by omega : (coneCoord B r v).2.card = 1)
    refine Or.inr ⟨i, eq_of_coneCoord_eq ?_⟩
    rw [coneCoord_conePoint]
    exact Prod.ext hb.symm hi.symm

theorem coneCoord_top (F : Atom) (r : ℕ) :
    coneCoord F r (cone F r).top = ((F.top : WithBot F.ogp), Finset.univ) := by
  obtain ⟨y, hy⟩ := exists_coneCoord_eq_of_ne F r (F.top : WithBot F.ogp) Finset.univ fun h =>
    absurd (Prod.mk.inj h).1 (by simp)
  have hle : ∀ w, w ≤ y := fun w => by
    rw [le_iff_coneCoord, hy]
    exact ⟨WithBot.le_coe_iff.2 fun b _ => F.le_top b, Finset.subset_univ _⟩
  rwa [le_antisymm ((cone F r).le_top y) (hle _)] at hy

@[reassoc (attr := simp)] theorem coneIncl_comp_coneMap {B B' : Atom} (f : B ⟶ B') (r : ℕ) :
    coneIncl B r ≫ coneMap f r = f ≫ coneIncl B' r := by
  refine Atom.hom_ext fun b => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneMap, coneCoord_coneIncl,
    ConcreteCategory.comp_apply, coneCoord_coneIncl]
  rfl

@[reassoc (attr := simp)] theorem conePoint_comp_coneMap {B B' : Atom} (f : B ⟶ B') (r : ℕ)
    (i : Fin r) : conePoint B r i ≫ coneMap f r = conePoint B' r i := by
  refine Atom.hom_ext fun v => eq_of_coneCoord_eq ?_
  rw [ConcreteCategory.comp_apply, ← WithBot.map_coe, coneCoord_coneMap, coneCoord_conePoint,
    coneCoord_conePoint]
  rfl

@[reassoc] theorem coneHom_comp_coneMap {B B' : Atom} (f : B ⟶ B') {r s : ℕ}
    (σ : Fin r →o Fin s) : coneHom B σ ≫ coneMap f s = coneMap f r ≫ coneHom B' σ :=
  cone_hom_ext σ (fun i => by simp) (fun i => by simp) (by simp)

theorem coneIncl_comp_coneMap_comp_coneHom {B F : Atom} {k r s : ℕ} (q₀ : B ⟶ cone F k)
    (σ : Fin (k + r) →o Fin s) :
    coneIncl B r ≫ coneMap q₀ r ≫ (coneAssoc F k r).hom ≫ coneHom F σ =
      q₀ ≫ coneHom F (σ.comp ⟨Fin.castAdd r, fun _ _ h => h⟩) := by
  rw [coneIncl_comp_coneMap_assoc, ← coneHom_comp, ← coneIncl_comp_coneAssoc, Category.assoc]

theorem conePoint_comp_coneMap_comp_coneHom {B F : Atom} {k r s : ℕ} (q₀ : B ⟶ cone F k)
    (σ : Fin (k + r) →o Fin s) (i : Fin r) :
    conePoint B r i ≫ coneMap q₀ r ≫ (coneAssoc F k r).hom ≫ coneHom F σ =
      conePoint F s (σ (Fin.natAdd k i)) := by
  rw [conePoint_comp_coneMap_assoc, conePoint_comp_coneAssoc_assoc, conePoint_comp_coneHom]

theorem coneCoord_of_mem_boundary_zero_true {F : Atom} {r : ℕ} {x v : (cone F r).ogp}
    (hS : (coneCoord F r x).2.Nonempty)
    (hv : v ∈ (cone F r).ogp.boundary (.Iic x) 0 true) :
    coneCoord F r v = (⊥, {(coneCoord F r x).2.max' hS}) := by
  induction r with
  | zero => exact absurd hS (by simp)
  | succ r ih =>
    let e : join (cone F r).ogp atomPoint.ogp ≅ (cone F (r + 1)).ogp :=
      FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)
    obtain ⟨p, rfl⟩ : ∃ p, e.hom p = x :=
      ⟨e.inv x, ConcreteCategory.congr_hom e.inv_hom_id x⟩
    have hv' : v ∈ e.hom '' ((join (cone F r).ogp atomPoint.ogp).boundary (.Iic p) 0 true) := by
      rw [(isMap_of_isInclusion e.hom).image_boundary p 0 true]
      exact hv
    obtain ⟨w, hw, rfl⟩ := hv'
    have hx := coneCoord_succ_ofOGPIso F r p
    by_cases hc : p.1.2 = ⊥
    · obtain ⟨a, ha⟩ : ∃ a : (cone F r).ogp, (a : WithBot _) = p.1.1 :=
        WithBot.ne_bot_iff_exists.1 fun h => p.2 (Prod.ext h hc)
      obtain rfl : p = join.inl _ _ a := Subtype.ext (Prod.ext ha.symm hc)
      have hw' : w ∈ join.inl (cone F r).ogp atomPoint.ogp ''
          ((cone F r).ogp.boundary (.Iic a) 0 true) := by
        rw [(isMap_of_isInclusion (join.inl (cone F r).ogp atomPoint.ogp)).image_boundary a 0 true]
        exact hw
      obtain ⟨v', hv'', rfl⟩ := hw'
      have hT : (coneCoord F (r + 1) (WithBot.some (e.hom (join.inl _ _ a)) :
          WithBot (cone F (r + 1)).ogp)).2 = (coneCoord F r a).2.map Fin.castSuccEmb :=
        congrArg Prod.snd (coneCoord_joinInclLeftHom F r a)
      have hSa : (coneCoord F r a).2.Nonempty := Finset.map_nonempty.1 (hT ▸ hS)
      refine (coneCoord_joinInclLeftHom F r v').trans ?_
      rw [ih hSa hv'']
      simp only [Finset.map_singleton, Fin.castSuccEmb_apply, Prod.mk.injEq, true_and,
        Finset.singleton_inj]
      generalize (coneCoord F (r + 1) (WithBot.some (e.hom (join.inl _ _ a)) :
        WithBot (cone F (r + 1)).ogp)).2 = T at hS hT
      subst hT
      simp only [Finset.map_eq_image, Fin.coe_castSuccEmb]
      exact (Finset.max'_image Fin.strictMono_castSucc.monotone _ _).symm
    · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 hc
      have hw' : w ∈ (join (cone F r).ogp atomPoint.ogp).boundary (.Iic p) 0 true := hw
      rw [boundary_Iic_join_zero_true p d hd.symm] at hw'
      obtain ⟨d', -, rfl⟩ := hw'
      have hl : Fin.last r ∈ (coneCoord F (r + 1) (e.hom p)).2 :=
        (congrArg Prod.snd hx).symm ▸ last_mem_conePairCoord_iff.2 hc
      refine (coneCoord_joinInclRightHom F r d').trans ?_
      exact Prod.ext rfl (Finset.singleton_inj.2
        (le_antisymm (Finset.le_max' _ _ hl) (Fin.le_last _)))

theorem conePoint_mem_boundary_zero_true {F : Atom} {r : ℕ} {x : (cone F r).ogp}
    (hS : (coneCoord F r x).2.Nonempty) :
    conePoint F r ((coneCoord F r x).2.max' hS) default ∈
      (cone F r).ogp.boundary (.Iic x) 0 true := by
  obtain ⟨u, hu⟩ := boundary_closure_nonempty (cone F r) x 0 true
  have hu' : u = conePoint F r ((coneCoord F r x).2.max' hS) default :=
    eq_of_coneCoord_eq (by rw [coneCoord_conePoint, coneCoord_of_mem_boundary_zero_true hS hu])
  exact hu' ▸ hu

theorem isInclusionHom_coneIncl (F : Atom) (r : ℕ) : IsInclusionHom (coneIncl F r) :=
  fun a b h => WithBot.coe_injective (congrArg Prod.fst
    ((coneCoord_coneIncl F r a).symm.trans ((congrArg (coneCoord F r ∘ WithBot.some) h).trans
      (coneCoord_coneIncl F r b))))

theorem boundary_closure_zero_true_eq_of_max'_eq {F : Atom} {r : ℕ}
    {x y : (cone F r).ogp} (hx : (coneCoord F r x).2.Nonempty)
    (hy : (coneCoord F r y).2.Nonempty)
    (h : (coneCoord F r x).2.max' hx = (coneCoord F r y).2.max' hy) :
    (cone F r).ogp.boundary (.Iic x) 0 true =
      (cone F r).ogp.boundary (.Iic y) 0 true := by
  have key : ∀ {x y : (cone F r).ogp} (hx : (coneCoord F r x).2.Nonempty)
      (hy : (coneCoord F r y).2.Nonempty),
      (coneCoord F r x).2.max' hx = (coneCoord F r y).2.max' hy →
      (cone F r).ogp.boundary (.Iic x) 0 true ≤
        (cone F r).ogp.boundary (.Iic y) 0 true := by
    intro x y hx hy h v hv
    obtain ⟨w, hw⟩ := boundary_closure_nonempty (cone F r) y 0 true
    have hvw : v = w := eq_of_coneCoord_eq (by
      rw [coneCoord_of_mem_boundary_zero_true hx hv, coneCoord_of_mem_boundary_zero_true hy hw, h])
    exact hvw ▸ hw
  exact le_antisymm (key hx hy h) (key hy hx h.symm)

theorem boundary_closure_top_zero_true_cone_one (B : Atom) :
    ((cone B 1).ogp.boundary (.Iic (cone B 1).top) 0 true : Set (cone B 1).ogp) =
      {conePoint B 1 0 default} := by
  have hS : (coneCoord B 1 (cone B 1).top).2.Nonempty := by
    rw [coneCoord_top]
    exact Finset.univ_nonempty
  have key : ∀ v ∈ (cone B 1).ogp.boundary (.Iic (cone B 1).top) 0 true,
      v = conePoint B 1 0 default := fun v hv => eq_of_coneCoord_eq (by
    rw [coneCoord_conePoint, coneCoord_of_mem_boundary_zero_true hS hv]
    exact Prod.ext rfl (Finset.singleton_inj.2 (Subsingleton.elim _ _)))
  obtain ⟨v, hv⟩ := boundary_closure_nonempty (cone B 1) (cone B 1).top 0 true
  exact Set.eq_singleton_iff_unique_mem.2 ⟨key v hv ▸ hv, key⟩

theorem nonempty_iso_of_iso_cone_one {X Y : Atom} (e : cone X 1 ≅ cone Y 1) :
    Nonempty (X ≅ Y) := by
  set cX := conePoint X 1 0 default
  set cY := conePoint Y 1 0 default
  have htop : e.hom (cone X 1).top = (cone Y 1).top :=
    (isCollapseHom_of_iso e).apply_top
  have hc : e.hom cX = cY := by
    have h := (Atom.isMap e.hom).image_boundary (cone X 1).top 0 true
    rw [htop, boundary_closure_top_zero_true_cone_one, boundary_closure_top_zero_true_cone_one,
      Set.image_singleton] at h
    exact Set.singleton_eq_singleton_iff.1 h
  have hc' : e.inv cY = cX := by rw [← hc, Iso.hom_inv_id_apply]
  have hbase : ∀ b, ∃ b', coneIncl Y 1 b' = (coneIncl X 1 ≫ e.hom) b := by
    intro b
    set y := (coneIncl X 1 ≫ e.hom) b
    have h0 : (coneCoord Y 1 y).2 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
      have hle : cY ≤ y := by
        rw [le_iff_coneCoord, coneCoord_conePoint]
        exact ⟨bot_le, Finset.singleton_subset_iff.2 (Subsingleton.elim i 0 ▸ hi)⟩
      have hy : e.inv y = coneIncl X 1 b := Iso.hom_inv_id_apply e _
      have := (Atom.isMap e.inv).monotone hle
      rw [hc', hy, le_iff_coneCoord, coneCoord_conePoint, coneCoord_coneIncl] at this
      simpa using this.2
    exact exists_coneIncl_eq_of_coneCoord_snd_eq_empty h0
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_isInclusionHom _ (isInclusionHom_coneIncl Y 1) _ hbase
  have hinj : IsInclusionHom φ := fun a b h => by
    have h' := congrArg (coneIncl Y 1) h
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hφ] at h'
    exact isInclusionHom_coneIncl X 1 (isInclusionHom_of_mono e.hom h')
  have hd : X.dimension = Y.dimension := by
    simpa [dimension_cone] using Atom.dimension_eq_of_iso e
  have := isIso_of_isInclusionHom_of_dimension_eq φ hinj hd
  exact ⟨asIso φ⟩

end Atoms.Shape
