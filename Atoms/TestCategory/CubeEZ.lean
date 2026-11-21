import Atoms.Homotopical.Cylinder.Segment
import Atoms.Homotopical.EilenbergZilber.Basic
import Atoms.TestCategory.CubeTest

open CategoryTheory Limits Atoms.Homotopical

namespace Atoms.TestCategory

universe w u

namespace CubeCoord

theorem IsOrdered.eq_of_eq_proj {m n : ℕ} {f : Fin n → CubeCoord m} (hf : IsOrdered f)
    {j₁ j₂ : Fin n} {i : Fin m} (h₁ : f j₁ = proj i) (h₂ : f j₂ = proj i) : j₁ = j₂ := by
  rcases lt_trichotomy j₁ j₂ with h | h | h
  · exact absurd (hf h h₁ h₂) (lt_irrefl i)
  · exact h
  · exact absurd (hf h h₂ h₁) (lt_irrefl i)

theorem IsOrdered.insertNth_const {m n : ℕ} {f : Fin n → CubeCoord m} (hf : IsOrdered f)
    (i : Fin (n + 1)) (b : Bool) : IsOrdered (Fin.insertNth i (const b) f) := by
  intro j₁ j₂ i₁ i₂ hj h₁ h₂
  obtain rfl | ⟨k₁, rfl⟩ := i.eq_self_or_eq_succAbove j₁
  · simp at h₁
  obtain rfl | ⟨k₂, rfl⟩ := i.eq_self_or_eq_succAbove j₂
  · simp at h₂
  rw [Fin.insertNth_apply_succAbove] at h₁ h₂
  exact hf (Fin.succAbove_lt_succAbove_iff.1 hj) h₁ h₂

theorem isOrdered_proj_comp {m n : ℕ} {φ : Fin n → Fin m} (hφ : StrictMono φ) :
    IsOrdered fun j => proj (φ j) :=
  fun _ _ _ _ hj h₁ h₂ => by
    cases h₁
    cases h₂
    exact hφ hj

theorem isOrdered_const {m n : ℕ} (b : Fin n → Bool) :
    IsOrdered fun j => (const (b j) : CubeCoord m) :=
  fun _ _ _ _ _ h => by cases h

end CubeCoord

namespace Cube

abbrev of (n : ℕ) : Cube.{u} :=
  ULift.up n

def δ {n : ℕ} (i : Fin (n + 1)) (ε : Bool) :
    of.{u} n ⟶ of (n + 1) :=
  ⟨Fin.insertNth i (.const ε) .proj, (CubeCoord.isOrdered_proj n).insertNth_const i ε⟩

@[simp]
theorem δ_coord_self {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : (δ.{u} i ε).coord i = .const ε :=
  Fin.insertNth_apply_same (α := fun _ => CubeCoord n) _ _ _

@[simp]
theorem δ_coord_succAbove {n : ℕ} (i : Fin (n + 1)) (ε : Bool) (j : Fin n) :
    (δ.{u} i ε).coord (i.succAbove j) = .proj j :=
  Fin.insertNth_apply_succAbove (α := fun _ => CubeCoord n) _ _ _ _

@[simp]
theorem toFun_δ {n : ℕ} (i : Fin (n + 1)) (ε : Bool) (x : Fin n → Bool) :
    toFun (δ.{u} i ε) x = Fin.insertNth i ε x := by
  funext j
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j <;> simp

def σ {n : ℕ} (i : Fin (n + 1)) : of.{u} (n + 1) ⟶ of n :=
  ⟨fun j => .proj (i.succAbove j), CubeCoord.isOrdered_proj_comp (Fin.strictMono_succAbove i)⟩

@[simp]
theorem σ_coord {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : (σ.{u} i).coord j = .proj (i.succAbove j) :=
  rfl

@[simp]
theorem toFun_σ {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → Bool) :
    toFun (σ.{u} i) x = Fin.removeNth i x :=
  rfl

@[reassoc (attr := simp)]
theorem δ_comp_σ {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : δ.{u} i ε ≫ σ i = 𝟙 _ :=
  toFun_injective (by rw [toFun_comp]; funext x; simp)

instance {n : ℕ} (i : Fin (n + 1)) : IsSplitEpi (σ.{u} i) :=
  IsSplitEpi.mk' ⟨δ i false, δ_comp_σ i false⟩

private theorem succAbove_succAbove_of_lt {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) (t : Fin n) :
    j.succAbove ((i.castPred (Fin.ne_last_of_lt hij)).succAbove t) =
      i.succAbove ((j.pred (Fin.ne_zero_of_lt hij)).succAbove t) := by
  rw [Fin.lt_def] at hij
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.coe_castPred, Fin.val_pred,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

@[reassoc]
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) (ε η : Bool) :
    δ.{u} (i.castPred (Fin.ne_last_of_lt hij)) ε ≫ δ j η =
      δ (j.pred (Fin.ne_zero_of_lt hij)) η ≫ δ i ε := by
  ext k
  obtain rfl | ⟨l, rfl⟩ := j.eq_self_or_eq_succAbove k
  · have h := δ_coord_succAbove.{u} i ε (k.pred (Fin.ne_zero_of_lt hij))
    rw [Fin.succAbove_pred_of_lt _ _ hij] at h
    simp [h]
  obtain rfl | ⟨t, rfl⟩ := (i.castPred (Fin.ne_last_of_lt hij)).eq_self_or_eq_succAbove l
  · simp only [comp_coord, δ_coord_succAbove, CubeCoord.proj_subst, δ_coord_self]
    rw [Fin.succAbove_castPred_of_lt _ _ hij]
    simp
  · simp only [comp_coord, δ_coord_succAbove, CubeCoord.proj_subst]
    rw [succAbove_succAbove_of_lt hij]
    simp

@[reassoc]
theorem δ_comp_σ_of_lt {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) (ε : Bool) :
    δ.{u} i ε ≫ σ j =
      σ (j.pred (Fin.ne_zero_of_lt hij)) ≫ δ (i.castPred (Fin.ne_last_of_lt hij)) ε := by
  ext k
  obtain rfl | ⟨t, rfl⟩ := (i.castPred (Fin.ne_last_of_lt hij)).eq_self_or_eq_succAbove k
  · simp only [comp_coord, σ_coord, CubeCoord.proj_subst]
    rw [Fin.succAbove_castPred_of_lt _ _ hij]
    simp
  · simp only [comp_coord, σ_coord, CubeCoord.proj_subst]
    rw [succAbove_succAbove_of_lt hij]
    simp

theorem face_eq_δ (ε : Bool) (n : ℕ) : face.{u} ε (of n) = δ 0 ε := by
  ext j
  induction j using Fin.cases with
  | zero => simp
  | succ j => exact (δ_coord_succAbove.{u} 0 ε j).symm

theorem degeneracy_eq_σ (n : ℕ) : degeneracy.{u} (of n) = σ 0 := by
  ext j
  simp

def point {m : Cube.{u}} (x : Fin m.down → Bool) : of.{u} 0 ⟶ m :=
  ⟨fun j => .const (x j), CubeCoord.isOrdered_const x⟩

@[simp]
theorem toFun_point {m : Cube.{u}} (x : Fin m.down → Bool) (y : Fin 0 → Bool) :
    toFun (point x) y = x :=
  rfl

theorem mono_iff_injective {m n : Cube.{u}} (f : m ⟶ n) :
    Mono f ↔ Function.Injective (Cube.toFun f) := by
  refine ⟨fun _ x x' h => ?_, fun hf => ⟨fun g h hgh => toFun_injective (hf.comp_left ?_)⟩⟩
  · have hx : point x ≫ f = point x' ≫ f :=
      toFun_injective (funext fun y => by simpa [toFun_comp] using h)
    exact congrFun (congrArg toFun ((cancel_mono f).1 hx)) Fin.elim0
  · beta_reduce
    rw [← toFun_comp, ← toFun_comp, hgh]

theorem exists_coord_eq_proj_of_surjective {m n : Cube.{u}} {f : m ⟶ n}
    (hf : Function.Surjective (toFun f)) (j : Fin n.down) : ∃ i, f.coord j = .proj i := by
  cases hj : f.coord j with
  | proj i => exact ⟨i, rfl⟩
  | const b =>
    obtain ⟨x, hx⟩ := hf fun _ => !b
    have := congrFun hx j
    simp [hj] at this

private theorem exists_section {m n : Cube.{u}} (f : m ⟶ n)
    (hf : ∀ j, ∃ i, f.coord j = .proj i) :
    ∃ s : n ⟶ m, s ≫ f = 𝟙 n ∧ ∀ i j, s.coord i = .proj j → f.coord j = .proj i := by
  classical
  let c : Fin m.down → CubeCoord n.down := fun i =>
    if h : ∃ j, f.coord j = .proj i then .proj h.choose else .const false
  have hc : ∀ i j, c i = .proj j → f.coord j = .proj i := fun i j h => by
    simp only [c] at h
    split_ifs at h with hi
    cases h
    exact hi.choose_spec
  refine ⟨⟨c, fun i₁ i₂ j₁ j₂ hi h₁ h₂ => ?_⟩, hom_ext fun j => ?_, hc⟩
  · replace h₁ := hc _ _ h₁
    replace h₂ := hc _ _ h₂
    refine lt_of_not_ge fun hj => ?_
    rcases hj.lt_or_eq with hj | rfl
    · exact lt_asymm hi (f.ordered hj h₂ h₁)
    · exact hi.ne (CubeCoord.proj.inj (h₁.symm.trans h₂))
  · obtain ⟨i, hi⟩ := hf j
    have h : ∃ j, f.coord j = .proj i := ⟨j, hi⟩
    have hci : c i = .proj j := by
      simp only [c, dif_pos h]
      rw [f.ordered.eq_of_eq_proj h.choose_spec hi]
    rw [comp_coord, hi, CubeCoord.proj_subst]
    exact hci

theorem isSplitEpi_iff_surjective {m n : Cube.{u}} (f : m ⟶ n) :
    IsSplitEpi f ↔ Function.Surjective (Cube.toFun f) := by
  refine ⟨fun _ y => ⟨toFun (section_ f) y, ?_⟩, fun hf => ?_⟩
  · rw [← Function.comp_apply (f := toFun f), ← toFun_comp, IsSplitEpi.id, toFun_id, id]
  · obtain ⟨s, hs, -⟩ := exists_section f (exists_coord_eq_proj_of_surjective hf)
    exact IsSplitEpi.mk' ⟨s, hs⟩

instance : HasTrivialAutomorphisms Cube.{u} where
  subsingleton_aut m := ⟨fun e₁ e₂ => by
    suffices h : ∀ e : m ≅ m, e.hom = 𝟙 m by
      ext
      rw [h, h]
    intro e
    choose π hπ using exists_coord_eq_proj_of_surjective
      ((isSplitEpi_iff_surjective e.hom).1 inferInstance)
    have hπm : StrictMono π := fun j₁ j₂ hj => e.hom.ordered hj (hπ j₁) (hπ j₂)
    have hid : π = id := le_antisymm hπm.le_id hπm.id_le
    exact hom_ext fun j => by rw [hπ, hid, id_coord, id]⟩

private theorem down_le_of_mono {m n : Cube.{u}} (f : m ⟶ n) [Mono f] : m.down ≤ n.down := by
  have := Fintype.card_le_of_injective _ ((mono_iff_injective f).1 inferInstance)
  exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).1 (by simpa using this)

private theorem isIso_of_mono_of_down_eq {m n : Cube.{u}} (f : m ⟶ n) [Mono f]
    (h : m.down = n.down) : IsIso f := by
  have hf := (mono_iff_injective f).1 inferInstance
  have := (isSplitEpi_iff_surjective f).2
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨hf, by simp [h]⟩).2
  exact isIso_of_mono_of_isSplitEpi f

private theorem injective_toFun_of_forall {m n : Cube.{u}} (f : m ⟶ n)
    (h : ∀ i, ∃ j, f.coord j = .proj i) : Function.Injective (toFun f) :=
  fun x x' hx => funext fun i => by
    obtain ⟨j, hj⟩ := h i
    simpa [hj] using congrFun hx j

private theorem exists_σ_comp_eq {m : ℕ} {n : Cube.{u}} (i : Fin (m + 1))
    (f : of.{u} (m + 1) ⟶ n) (hf : ∀ j, f.coord j ≠ .proj i) :
    ∃ g : of.{u} m ⟶ n, σ i ≫ g = f := by
  have h : ∀ j, ∃ c : CubeCoord m, f.coord j = c.subst (σ.{u} i).coord := fun j => by
    cases hj : f.coord j with
    | const b => exact ⟨.const b, rfl⟩
    | proj k =>
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq fun h => hf j (hj.trans (congrArg _ h))
      exact ⟨.proj l, rfl⟩
  choose g hg using h
  refine ⟨⟨g, fun j₁ j₂ k₁ k₂ hj h₁ h₂ => ?_⟩, hom_ext fun j => (hg j).symm⟩
  have := f.ordered hj ((hg j₁).trans (by rw [h₁]; rfl)) ((hg j₂).trans (by rw [h₂]; rfl))
  exact Fin.succAbove_lt_succAbove_iff.1 this

private theorem exists_factorization (m : ℕ) {n : Cube.{u}}
    (f : of.{u} m ⟶ n) :
    ∃ (c : Cube.{u}) (p : of m ⟶ c) (ι : c ⟶ n), IsSplitEpi p ∧ Mono ι ∧ p ≫ ι = f := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_cases h : ∀ i, ∃ j, f.coord j = .proj i
  · exact ⟨_, 𝟙 _, f, inferInstance, (mono_iff_injective f).2 (injective_toFun_of_forall f h),
      Category.id_comp f⟩
  simp only [not_forall, not_exists] at h
  obtain ⟨i, hi⟩ := h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero i.pos.ne'
  obtain ⟨g, rfl⟩ := exists_σ_comp_eq i f hi
  obtain ⟨c, p, ι, hp, hι, rfl⟩ := ih k k.lt_succ_self g
  exact ⟨c, σ i ≫ p, ι, inferInstance, hι, Category.assoc _ _ _⟩

private theorem eq_of_forall_section_iff {m n : Cube.{u}} (p q : m ⟶ n) [IsSplitEpi p]
    (h : ∀ s : n ⟶ m, s ≫ p = 𝟙 n ↔ s ≫ q = 𝟙 n) : p = q := by
  obtain ⟨s, hs, hsp⟩ := exists_section p
    (exists_coord_eq_proj_of_surjective ((isSplitEpi_iff_surjective p).1 inferInstance))
  refine hom_ext fun j => ?_
  have hj := congrArg (fun g => Hom.coord g j) ((h s).1 hs)
  simp only [comp_coord, id_coord] at hj
  obtain ⟨k, hk, hsk⟩ := CubeCoord.exists_of_subst_eq_proj hj
  rw [hk, hsp k j hsk]

instance ezCategory : EZCategory Cube.{u} :=
  EZCategory.ofCollapseInclusion (fun n => n.down) (MorphismProperty.splitEpimorphisms _)
    (MorphismProperty.monomorphisms _) le_rfl le_rfl
    (fun _ _ i (_ : Mono i) => down_le_of_mono i)
    (fun _ _ i (_ : Mono i) h => isIso_of_mono_of_down_eq i h)
    (fun _ _ f => exists_factorization _ f)
    (fun _ _ p q (_ : IsSplitEpi p) _ h => eq_of_forall_section_iff p q h)

@[simp]
theorem deg_eq (n : Cube.{u}) : EZCategory.deg n = n.down :=
  rfl

theorem comp_δ_false_ne {m : Cube.{u}} {n : ℕ} (i : Fin (n + 1)) (a b : m ⟶ of n) :
    a ≫ δ i false ≠ b ≫ δ i true := fun h => by
  have := congrArg (fun g => Hom.coord g i) h
  simp at this

theorem isPullback_uliftYoneda_δ {n : ℕ} (i : Fin (n + 1)) :
    IsPullback (initial.to (uliftYoneda.{w}.obj (of.{u} n)))
      (initial.to (uliftYoneda.{w}.obj (of.{u} n)))
      (uliftYoneda.{w}.map (δ.{u} i false)) (uliftYoneda.{w}.map (δ.{u} i true)) :=
  IsPullback.of_forall_isPullback_app fun a ↦ (Types.isPullback_iff _ _ _ _).2
    ⟨ConcreteCategory.hom_ext _ _ fun x ↦ (FunctorToTypes.isEmpty_initial_obj a).elim x,
      fun x _ _ ↦ (FunctorToTypes.isEmpty_initial_obj a).elim x,
      fun x₂ x₃ he ↦ (comp_δ_false_ne i x₂.down x₃.down (congrArg ULift.down he)).elim⟩

theorem isPullback_map_δ_δ {D : Type*} [Category D] (F : Cube.{u} ⥤ D) {n : ℕ}
    {i j : Fin (n + 2)} (hij : i < j) (ε η : Bool) :
    IsPullback (F.map (δ (i.castPred (Fin.ne_last_of_lt hij)) ε))
      (F.map (δ (j.pred (Fin.ne_zero_of_lt hij)) η)) (F.map (δ j η)) (F.map (δ i ε)) :=
  IsPullback.of_retractions (by rw [← F.map_comp, ← F.map_comp, δ_comp_δ hij])
    (r := F.map (σ (j.pred (Fin.ne_zero_of_lt hij)))) (q := F.map (σ i)) (p := F.map (σ j))
    (by rw [← F.map_comp, δ_comp_σ, F.map_id]) (by rw [← F.map_comp, δ_comp_σ, F.map_id])
    (by rw [← F.map_comp, δ_comp_σ, F.map_id])
    (by rw [← F.map_comp, ← F.map_comp, δ_comp_σ_of_lt hij])

end Cube

end Atoms.TestCategory
