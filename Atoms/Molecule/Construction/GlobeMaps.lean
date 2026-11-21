import Atoms.Molecule.Construction.GlobeComap
import Atoms.Molecule.Construction.SimplexMaps

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

def globeCollapse : (n k : ℕ) → k ≤ n → globe.{u} n → globe.{u} k
  | _, 0, _ => fun _ => ⊤
  | 0, k + 1, h => absurd h (Nat.not_succ_le_zero k)
  | n + 1, k + 1, h => suspMap (globeCollapse n k (Nat.le_of_succ_le_succ h))

@[simp] theorem globeCollapse_zero (n : ℕ) (h : 0 ≤ n) (x : globe.{u} n) :
    globeCollapse n 0 h x = ⊤ :=
  rfl

theorem globeCollapse_succ (n k : ℕ) (h : k + 1 ≤ n + 1) :
    globeCollapse.{u} (n + 1) (k + 1) h = suspMap (globeCollapse n k (Nat.le_of_succ_le_succ h)) :=
  rfl

theorem isMap_globeCollapse {n k : ℕ} (h : k ≤ n) : IsMap (globeCollapse.{u} n k h) := by
  induction k generalizing n with
  | zero => exact isMap_constPoint (isRDC_globe n)
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact isMap_suspMap (isRDC_globe n) (ih _)

theorem surjective_globeCollapse {n k : ℕ} (h : k ≤ n) :
    Function.Surjective (globeCollapse.{u} n k h) := by
  induction k generalizing n with
  | zero => exact fun y => ⟨⊤, Subsingleton.elim (α := PUnit) _ _⟩
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact surjective_suspMap (ih _)

def globeIncl : (k n : ℕ) → k ≤ n → Bool → (globe.{u} k ⟶ globe.{u} n)
  | 0, 0, _, _ => 𝟙 _
  | 0, n + 1, _, α => suspension.poleIncl (globe n) α
  | k + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero k)
  | k + 1, n + 1, h, α => suspension.map (globeIncl k n (Nat.le_of_succ_le_succ h) α)

@[simp] theorem globeIncl_zero_succ (n : ℕ) (h : 0 ≤ n + 1) (α : Bool) (x : globe.{u} 0) :
    globeIncl 0 (n + 1) h α x = pole α :=
  rfl

@[simp] theorem globeIncl_succ_succ (k n : ℕ) (h : k + 1 ≤ n + 1) (α : Bool)
    (x : globe.{u} (k + 1)) :
    globeIncl (k + 1) (n + 1) h α x = suspMap (globeIncl k n (Nat.le_of_succ_le_succ h) α) x :=
  rfl

instance (k n : ℕ) (h : k ≤ n) (α : Bool) : IsInclusion (globeIncl.{u} k n h α) := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => exact IsInclusion.id _
    | succ n => exact inferInstanceAs (IsInclusion (suspension.poleIncl (globe n) α))
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := ih n (Nat.le_of_succ_le_succ h)
    exact inferInstanceAs (IsInclusion (suspension.map (globeIncl k n _ α)))

theorem globeIncl_self (n : ℕ) (α : Bool) : globeIncl.{u} n n le_rfl α = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    rw [globeIncl_succ_succ, ih, ConcreteCategory.id_apply]
    cases x <;> rfl

theorem globeIncl_top_eq_globeFace : (n k : ℕ) → (hk : k < n) → (α : Bool) →
    globeIncl.{u} k n hk.le α ⊤ = globeFace n k hk α
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _ => rfl
  | n + 1, k + 1, h, α => by
    rw [globeIncl_succ_succ, globeFace_succ, ← globeIncl_top_eq_globeFace n k _ α]
    rfl

theorem grade_le_globe {n : ℕ} (x : globe.{u} n) : grade ℕ x ≤ n :=
  (grade_mono (𝕆 := ℕ) (le_top (a := x))).trans (grade_top_globe n).le

private theorem exists_eq_globeIncl_top_of_grade_eq {n j : ℕ} (x : globe.{u} n) (h : j ≤ n)
    (hj : grade ℕ x = j) : ∃ α, x = globeIncl j n h α ⊤ := by
  rcases eq_top_or_exists_eq_globeFace n x with rfl | ⟨k, hk, α, rfl⟩
  · obtain rfl : j = n := hj.symm.trans (grade_top_globe n)
    exact ⟨false, by rw [globeIncl_self, ConcreteCategory.id_apply]⟩
  · obtain rfl : j = k := hj.symm.trans (grade_globeFace n k hk α)
    exact ⟨α, (globeIncl_top_eq_globeFace n j hk α).symm⟩

theorem exists_eq_globeIncl_top {n : ℕ} (x : globe.{u} n) :
    ∃ α, x = globeIncl (grade ℕ x) n (grade_le_globe x) α ⊤ :=
  exists_eq_globeIncl_top_of_grade_eq x _ rfl

theorem boundary_globe_eq_Iic_globeIncl {n k : ℕ} (hk : k ≤ n) (α : Bool) :
    (globe.{u} n).boundary ⊤ k α = LowerSet.Iic (globeIncl k n hk α ⊤) := by
  rcases hk.lt_or_eq with hk | rfl
  · rw [boundary_globe n k hk α, globeIncl_top_eq_globeFace n k hk α]
  · rw [boundary_eq_self (by rw [LowerSet.krullDim_top, krullDim_globe]) α, globeIncl_self,
      ConcreteCategory.id_apply]
    exact LowerSet.Iic_top.symm

private theorem apply_top_of_surjective {n k : ℕ} {p : globe.{u} n → globe.{u} k} (hp : IsMap p)
    (hs : Function.Surjective p) : p ⊤ = ⊤ := by
  obtain ⟨y, hy⟩ := hs ⊤
  exact top_le_iff.1 (hy ▸ hp.monotone le_top)

theorem le_of_isMap_of_surjective {n k : ℕ} {p : globe.{u} n → globe.{u} k} (hp : IsMap p)
    (hs : Function.Surjective p) : k ≤ n := by
  have h := hp.grade_le ⊤
  rwa [apply_top_of_surjective hp hs, grade_top_globe, grade_top_globe] at h

private theorem Iic_apply_eq_boundary {n k : ℕ} {p : globe.{u} n → globe.{u} k} (hp : IsMap p)
    (hs : Function.Surjective p) {x : globe.{u} n} {α : Bool}
    (hx : x = globeIncl (grade ℕ x) n (grade_le_globe x) α ⊤) :
    LowerSet.Iic (p x) = (globe.{u} k).boundary ⊤ (grade ℕ x) α := by
  have hb := boundary_globe_eq_Iic_globeIncl (grade_le_globe x) α
  rw [← hx] at hb
  have hi := hp.image_boundary ⊤ (grade ℕ x) α
  rw [LowerSet.Iic_top, hb, apply_top_of_surjective hp hs, LowerSet.Iic_top] at hi
  exact SetLike.coe_injective (by rw [LowerSet.coe_Iic, ← hp.image_Iic, ← LowerSet.coe_Iic, hi])

private theorem eq_of_surjective {n k : ℕ} {p q : globe.{u} n → globe.{u} k} (hp : IsMap p)
    (hps : Function.Surjective p) (hq : IsMap q) (hqs : Function.Surjective q) : p = q :=
  funext fun x => by
    obtain ⟨α, hx⟩ := exists_eq_globeIncl_top x
    exact LowerSet.Iic_injective ((Iic_apply_eq_boundary hp hps hx).trans
      (Iic_apply_eq_boundary hq hqs hx).symm)

theorem eq_globeCollapse {n k : ℕ} (h : k ≤ n) {p : globe.{u} n → globe.{u} k} (hp : IsMap p)
    (hs : Function.Surjective p) : p = globeCollapse n k h :=
  eq_of_surjective hp hs (isMap_globeCollapse h) (surjective_globeCollapse h)

theorem IsMap.grade_apply_top_le_globe {n m : ℕ} {p : globe.{u} n → globe.{u} m}
    (hp : IsMap p) : grade ℕ (p ⊤) ≤ n :=
  (hp.grade_le ⊤).trans (grade_top_globe n).le

theorem IsMap.existsUnique_globe_factor {n m : ℕ} {p : globe.{u} n → globe.{u} m}
    (hp : IsMap p) :
    ∃! ι : globe.{u} (grade ℕ (p ⊤)) ⟶ globe.{u} m, IsInclusion ι ∧
      p = ⇑ι ∘ globeCollapse n (grade ℕ (p ⊤)) hp.grade_apply_top_le_globe := by
  obtain ⟨α, hα⟩ := exists_eq_globeIncl_top (p ⊤)
  set ι := globeIncl (grade ℕ (p ⊤)) m (grade_le_globe (p ⊤)) α
  have hr (x : globe.{u} n) : ∃ y, ι y = p x := by
    have hx : p x ∈ map ι (LowerSet.Iic ⊤) := by
      rw [map_Iic, LowerSet.mem_Iic_iff, ← hα]
      exact hp.monotone le_top
    obtain ⟨y, -, hy⟩ := hx
    exact ⟨y, hy⟩
  choose q hq using hr
  have hpq : p = ⇑ι ∘ q := funext fun x => (hq x).symm
  have hqm : IsMap q := IsMap.of_comp ι (hpq ▸ hp)
  have hqs : Function.Surjective q := fun y => by
    have hy : ι y ≤ p ⊤ := ((IsInclusion.le_iff ι).2 le_top).trans_eq hα.symm
    obtain ⟨x, -, hx⟩ := hp.fibration hy
    exact ⟨x, IsInclusion.injective ((hq x).trans hx)⟩
  have hqτ := eq_globeCollapse hp.grade_apply_top_le_globe hqm hqs
  rw [hqτ] at hpq
  refine ⟨ι, ⟨inferInstance, hpq⟩, fun ι' hι' => ConcreteCategory.hom_ext _ _ fun y => ?_⟩
  obtain ⟨x, rfl⟩ := surjective_globeCollapse hp.grade_apply_top_le_globe y
  exact (congrFun hι'.2 x).symm.trans (congrFun hpq x)

end Atoms.Molecule.OGP
