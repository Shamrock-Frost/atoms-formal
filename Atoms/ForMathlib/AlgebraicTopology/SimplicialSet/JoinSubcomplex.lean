import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

open CategoryTheory Limits Simplicial MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory.DayConvolution

universe u

namespace AugmentedSimplexCategory

private lemma mem_range_toFun_eqToHom_comp_tensorHom_iff_of_lt
    {n a b x y : AugmentedSimplexCategory} (h : a ⊗ b = n) (f : a ⟶ x) (g : b ⟶ y)
    (v : Fin (card (x ⊗ y))) (hv : v.val < card x) :
    v ∈ Set.range (toFun (eqToHom h.symm ≫ (f ⊗ₘ g))) ↔
      (⟨v.val, hv⟩ : Fin (card x)) ∈ Set.range (toFun f) := by
  have hn : card n = card a + card b := h ▸ card_tensorObj a b
  constructor
  · rintro ⟨w, hw⟩
    rw [toFun_comp_apply] at hw
    by_cases hlt : (toFun (eqToHom h.symm) w).val < card a
    · refine ⟨⟨_, hlt⟩, Fin.ext ?_⟩
      rw [← val_toFun_tensorHom_of_lt f g _ hlt, hw]
    · have := val_toFun_tensorHom_of_le f g _ (not_lt.1 hlt)
      rw [hw] at this
      omega
  · rintro ⟨w, hw⟩
    have hw₀ := w.isLt
    refine ⟨⟨w.val, by omega⟩, Fin.ext ?_⟩
    have hw' : (toFun (eqToHom h.symm) ⟨w.val, by omega⟩).val < card a := by
      rw [val_toFun_eqToHom]
      exact w.isLt
    rw [toFun_comp_apply, val_toFun_tensorHom_of_lt f g _ hw', ← congrArg Fin.val hw]
    exact congrArg (fun w ↦ (toFun f w).val) (Fin.ext (val_toFun_eqToHom _ _))

private lemma mem_range_toFun_eqToHom_comp_tensorHom_iff_of_le
    {n a b x y : AugmentedSimplexCategory} (h : a ⊗ b = n) (f : a ⟶ x) (g : b ⟶ y)
    (v : Fin (card (x ⊗ y))) (hv : card x ≤ v.val) :
    v ∈ Set.range (toFun (eqToHom h.symm ≫ (f ⊗ₘ g))) ↔
      (⟨v.val - card x, by have := card_tensorObj x y; omega⟩ : Fin (card y)) ∈
        Set.range (toFun g) := by
  have hn : card n = card a + card b := h ▸ card_tensorObj a b
  constructor
  · rintro ⟨w, hw⟩
    rw [toFun_comp_apply] at hw
    have hw₀ := (toFun (eqToHom h.symm) w).isLt
    have hab := card_tensorObj a b
    by_cases hlt : (toFun (eqToHom h.symm) w).val < card a
    · have h₁ := val_toFun_tensorHom_of_lt f g _ hlt
      have h₂ := (toFun f ⟨_, hlt⟩).isLt
      rw [hw] at h₁
      omega
    · refine ⟨⟨(toFun (eqToHom h.symm) w).val - card a, by omega⟩, Fin.ext ?_⟩
      have := val_toFun_tensorHom_of_le f g _ (not_lt.1 hlt)
      rw [hw] at this
      dsimp only
      omega
  · rintro ⟨w, hw⟩
    have hw₀ := w.isLt
    have hw' : card a ≤ (toFun (eqToHom h.symm) ⟨card a + w.val, by omega⟩).val := by
      rw [val_toFun_eqToHom]
      exact Nat.le_add_right _ _
    have e : ∀ w' : Fin (card b), w'.val = w.val → (toFun g w').val = (toFun g w).val :=
      fun w' hw'' ↦ by rw [Fin.ext hw'']
    refine ⟨⟨card a + w.val, by omega⟩, Fin.ext ?_⟩
    rw [toFun_comp_apply, val_toFun_tensorHom_of_le f g _ hw', e _ (by
      simp only [val_toFun_eqToHom]
      omega), hw]
    dsimp only
    omega

end AugmentedSimplexCategory

namespace SSet

noncomputable def joinMk {X Y : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)) :
    (join X Y).obj n :=
  (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y).map (eqToHom h.symm).op
    ((DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y)).app
      (op a, op b) ((x, y) : (trivialAugmentation.obj X).obj (op a) ×
        (trivialAugmentation.obj Y).obj (op b)))

theorem exists_joinMk {X Y : SSet.{u}} {n : SimplexCategoryᵒᵖ} (t : (join X Y).obj n) :
    ∃ (a b : AugmentedSimplexCategory) (h : a ⊗ b = .of n.unop)
      (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)),
      joinMk h x y = t := by
  obtain ⟨⟨⟨⟨a, b⟩, h⟩, x, y⟩, rfl⟩ :=
    (AugmentedSimplexCategory.bijective_map_unit_app _ _ (.of n.unop)).2 t
  exact ⟨a, b, h, x, y, rfl⟩

theorem eq_and_eq_and_heq_of_joinMk_eq {X Y : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    {a b a' b' : AugmentedSimplexCategory} {h : a ⊗ b = .of n.unop} {h' : a' ⊗ b' = .of n.unop}
    {x : (trivialAugmentation.obj X).obj (op a)} {y : (trivialAugmentation.obj Y).obj (op b)}
    {x' : (trivialAugmentation.obj X).obj (op a')} {y' : (trivialAugmentation.obj Y).obj (op b')}
    (he : joinMk h x y = joinMk h' x' y') : a = a' ∧ b = b' ∧ x ≍ x' ∧ y ≍ y' := by
  have := (AugmentedSimplexCategory.bijective_map_unit_app _ _ (.of n.unop)).1
    (a₁ := ⟨⟨(a, b), h⟩, x, y⟩) (a₂ := ⟨⟨(a', b'), h'⟩, x', y'⟩) he
  obtain ⟨hs, hxy⟩ := Sigma.mk.inj_iff.1 this
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (congrArg Subtype.val hs)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hxy)
  exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem joinMap_app_joinMk {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    {n : SimplexCategoryᵒᵖ} {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)) :
    (joinMap f g).app n (joinMk h x y) =
      joinMk h ((trivialAugmentation.map f).app _ x) ((trivialAugmentation.map g).app _ y) := by
  refine (NatTrans.naturality_apply (DayConvolution.map (trivialAugmentation.map f)
    (trivialAugmentation.map g)) (eqToHom h.symm).op _).trans ?_
  exact congrArg _ (ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (trivialAugmentation.map f) (trivialAugmentation.map g) (op a) (op b))
      ((x, y) : (trivialAugmentation.obj X).obj (op a) × (trivialAugmentation.obj Y).obj (op b)))

private lemma trivialAugmentation_map_id_app (X : SSet.{u}) (c : AugmentedSimplexCategoryᵒᵖ)
    (x : (trivialAugmentation.obj X).obj c) : (trivialAugmentation.map (𝟙 X)).app c x = x := by
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma joinMk_mem_range_joinMap_iff {X X' Y Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y)
    {n : SimplexCategoryᵒᵖ} {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)) :
    joinMk h x y ∈ Set.range ((joinMap f g).app n) ↔
      x ∈ Set.range ((trivialAugmentation.map f).app (op a)) ∧
        y ∈ Set.range ((trivialAugmentation.map g).app (op b)) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a', b', h', x', y', rfl⟩ := exists_joinMk t
    rw [joinMap_app_joinMk] at ht
    obtain ⟨rfl, rfl, hx, hy⟩ := eq_and_eq_and_heq_of_joinMk_eq ht
    exact ⟨⟨x', eq_of_heq hx⟩, ⟨y', eq_of_heq hy⟩⟩
  · rintro ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩
    exact ⟨joinMk h x' y', joinMap_app_joinMk f g h x' y'⟩

theorem isPullback_joinMap {K L U V : SSet.{u}} (i : K ⟶ L) (j : U ⟶ V) [Mono i] :
    IsPullback (joinMap (𝟙 K) j) (joinMap i (𝟙 U)) (joinMap i (𝟙 V)) (joinMap (𝟙 L) j) := by
  refine IsPullback.of_forall_isPullback_app fun n ↦
    (Types.isPullback_iff _ _ _ _).2 ⟨?_, fun _ _ h ↦ ?_, fun p q hpq ↦ ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, joinMap_comp_joinMap, joinMap_comp_joinMap,
      Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
  · exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (mono_joinMap i (𝟙 U)) n)
      h.2
  · obtain ⟨a, b, h, x, v, rfl⟩ := exists_joinMk p
    obtain ⟨a', b', h', l, u, rfl⟩ := exists_joinMk q
    rw [joinMap_app_joinMk, joinMap_app_joinMk] at hpq
    obtain ⟨rfl, rfl, hx, hy⟩ := eq_and_eq_and_heq_of_joinMk_eq hpq
    refine ⟨joinMk h x u, ?_, ?_⟩
    · rw [joinMap_app_joinMk, trivialAugmentation_map_id_app, ← eq_of_heq hy,
        trivialAugmentation_map_id_app]
    · rw [joinMap_app_joinMk, trivialAugmentation_map_id_app, eq_of_heq hx,
        trivialAugmentation_map_id_app]

private lemma mem_range_trivialAugmentation_map_app_star {X X' : SSet.{u}} (f : X ⟶ X')
    (x : (trivialAugmentation.obj X').obj (op .star)) :
    x ∈ Set.range ((trivialAugmentation.map f).app (op .star)) :=
  ⟨default, Subsingleton.elim _ _⟩

private lemma range_trivialAugmentation_map_ι_app_of {X : SSet.{u}} (A : X.Subcomplex)
    (k : SimplexCategory) :
    Set.range ((trivialAugmentation.map A.ι).app (op (.of k))) = A.obj (op k) :=
  congrArg (fun S : X.Subcomplex ↦ S.obj (op k)) (Subfunctor.range_ι A)

namespace Subcomplex

noncomputable def join {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    (SSet.join X Y).Subcomplex :=
  Subcomplex.range (joinMap A.ι B.ι)

private lemma joinMk_mem_join_obj_iff {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    {n : SimplexCategoryᵒᵖ} {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)) :
    joinMk h x y ∈ (A.join B).obj n ↔
      x ∈ Set.range ((trivialAugmentation.map A.ι).app (op a)) ∧
        y ∈ Set.range ((trivialAugmentation.map B.ι).app (op b)) :=
  joinMk_mem_range_joinMap_iff A.ι B.ι h x y

private lemma range_trivialAugmentation_map_ι_app_mono {X : SSet.{u}} {A A' : X.Subcomplex}
    (hA : A ≤ A') (c : AugmentedSimplexCategory) :
    Set.range ((trivialAugmentation.map A.ι).app (op c)) ⊆
      Set.range ((trivialAugmentation.map A'.ι).app (op c)) := by
  cases c with
  | star => exact fun x _ ↦ mem_range_trivialAugmentation_map_app_star _ x
  | of k =>
    rw [range_trivialAugmentation_map_ι_app_of, range_trivialAugmentation_map_ι_app_of]
    exact hA _

private lemma range_trivialAugmentation_map_ι_app_inf {X : SSet.{u}} (A A' : X.Subcomplex)
    (c : AugmentedSimplexCategory) :
    Set.range ((trivialAugmentation.map (A ⊓ A').ι).app (op c)) =
      Set.range ((trivialAugmentation.map A.ι).app (op c)) ∩
        Set.range ((trivialAugmentation.map A'.ι).app (op c)) := by
  cases c with
  | star =>
    exact Set.ext fun x ↦ iff_of_true (mem_range_trivialAugmentation_map_app_star _ x)
      ⟨mem_range_trivialAugmentation_map_app_star _ x,
        mem_range_trivialAugmentation_map_app_star _ x⟩
  | of k =>
    rw [range_trivialAugmentation_map_ι_app_of, range_trivialAugmentation_map_ι_app_of,
      range_trivialAugmentation_map_ι_app_of]
    rfl

theorem join_mono {X Y : SSet.{u}} {A A' : X.Subcomplex} {B B' : Y.Subcomplex} (hA : A ≤ A')
    (hB : B ≤ B') : A.join B ≤ A'.join B' := by
  intro n t ht
  obtain ⟨a, b, h, x, y, rfl⟩ := exists_joinMk t
  rw [joinMk_mem_join_obj_iff] at ht ⊢
  exact ⟨range_trivialAugmentation_map_ι_app_mono hA a ht.1,
    range_trivialAugmentation_map_ι_app_mono hB b ht.2⟩

theorem join_inf_join {X Y : SSet.{u}} (A A' : X.Subcomplex) (B B' : Y.Subcomplex) :
    A.join B ⊓ A'.join B' = (A ⊓ A').join (B ⊓ B') := by
  ext n t
  obtain ⟨a, b, h, x, y, rfl⟩ := exists_joinMk t
  rw [Subfunctor.min_obj, Set.mem_inter_iff, joinMk_mem_join_obj_iff, joinMk_mem_join_obj_iff,
    joinMk_mem_join_obj_iff, range_trivialAugmentation_map_ι_app_inf,
    range_trivialAugmentation_map_ι_app_inf, Set.mem_inter_iff, Set.mem_inter_iff]
  tauto

end Subcomplex

section stdSimplex

open AugmentedSimplexCategory

private lemma stdSimplexJoinIso_hom_app_joinMk (m n : ℕ) {k : SimplexCategoryᵒᵖ}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of k.unop)
    (x : (trivialAugmentation.obj Δ[m]).obj (op a))
    (y : (trivialAugmentation.obj Δ[n]).obj (op b)) :
    (stdSimplexJoinIso.{u} m n).hom.app k (joinMk h x y) =
      ULift.up (eqToHom h.symm ≫ (stdSimplexToHom _ _ x ⊗ₘ stdSimplexToHom _ _ y)) := by
  refine (NatTrans.naturality_apply ((DayConvolution.homEquiv _ _ _).symm
    (stdSimplexJoinFamily.{u} m n)) (eqToHom h.symm).op _).trans
    ((congrArg _ (DayConvolution.homEquiv_symm_app_unit_app _ _ _
      (stdSimplexJoinFamily.{u} m n) _ _ x y)).trans ?_)
  rfl

private lemma mem_boundary_obj_iff {N : ℕ} {k : SimplexCategoryᵒᵖ} (s : (Δ[N] : SSet.{u}).obj k) :
    s ∈ (∂Δ[N]).obj k ↔ ∃ i, i ∉ Set.range (stdSimplex.asOrderHom s) :=
  not_forall

private lemma mem_horn_obj_iff {N : ℕ} (j : Fin (N + 1)) {k : SimplexCategoryᵒᵖ}
    (s : (Δ[N] : SSet.{u}).obj k) :
    s ∈ (Λ[N, j]).obj k ↔ ∃ i, i ≠ j ∧ i ∉ Set.range (stdSimplex.asOrderHom s) := by
  rw [mem_horn_iff, Ne, Set.eq_univ_iff_forall]
  simp only [Set.mem_union, Set.mem_singleton_iff, not_forall, not_or]
  exact exists_congr fun _ ↦ and_comm

private lemma mem_top_obj_iff {N : ℕ} {k : SimplexCategoryᵒᵖ} (s : (Δ[N] : SSet.{u}).obj k) :
    s ∈ (⊤ : (Δ[N] : SSet.{u}).Subcomplex).obj k ↔ True :=
  iff_of_true (Set.mem_univ s) trivial

private lemma mem_range_trivialAugmentation_map_ι_app_iff {N : ℕ}
    (C : (Δ[N] : SSet.{u}).Subcomplex) (P : Set (Fin (N + 1)) → Prop)
    (hC : ∀ (k : SimplexCategoryᵒᵖ) (s : (Δ[N] : SSet.{u}).obj k),
      s ∈ C.obj k ↔ P (Set.range (stdSimplex.asOrderHom s))) (hP : P ∅)
    {a : AugmentedSimplexCategory} (x : (trivialAugmentation.obj Δ[N]).obj (op a)) :
    x ∈ Set.range ((trivialAugmentation.map C.ι).app (op a)) ↔
      P (Set.range (toFun (stdSimplexToHom ⦋N⦌ a x))) := by
  cases a with
  | star =>
    have : Set.range (toFun (stdSimplexToHom ⦋N⦌ .star x)) = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨i, _⟩ ↦ i.elim0
    exact iff_of_true (mem_range_trivialAugmentation_map_app_star _ x) ((congrArg P this).mpr hP)
  | of k =>
    rw [range_trivialAugmentation_map_ι_app_of]
    exact hC (op k) x

private lemma joinMk_mem_preimage_obj_iff {m n : ℕ} (C : (Δ[m + n + 1] : SSet.{u}).Subcomplex)
    (Q : Set (Fin (m + n + 1 + 1)) → Prop)
    (hC : ∀ (k : SimplexCategoryᵒᵖ) (s : (Δ[m + n + 1] : SSet.{u}).obj k),
      s ∈ C.obj k ↔ Q (Set.range (stdSimplex.asOrderHom s)))
    {k : SimplexCategoryᵒᵖ} {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of k.unop)
    (x : (trivialAugmentation.obj Δ[m]).obj (op a))
    (y : (trivialAugmentation.obj Δ[n]).obj (op b)) :
    joinMk h x y ∈ (C.preimage (stdSimplexJoinIso m n).hom).obj k ↔
      Q (Set.range
        (toFun (eqToHom h.symm ≫ (stdSimplexToHom _ a x ⊗ₘ stdSimplexToHom _ b y)))) := by
  rw [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplexJoinIso_hom_app_joinMk]
  exact hC k _

private lemma exists_notMem_range_toFun_iff {m n : ℕ} {k : SimplexCategory}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of k) (f : a ⟶ .of ⦋m⦌) (g : b ⟶ .of ⦋n⦌)
    (p : Fin (m + n + 1 + 1) → Prop) :
    (∃ v : Fin (m + n + 1 + 1), p v ∧ v ∉ Set.range (toFun (eqToHom h.symm ≫ (f ⊗ₘ g)))) ↔
      (∃ i : Fin (m + 1), p (Fin.castLE (m := m + n + 1 + 1) (by omega) i) ∧
        i ∉ Set.range (toFun f)) ∨
        (∃ j : Fin (n + 1), p (⟨m + 1 + j, by omega⟩ : Fin (m + n + 1 + 1)) ∧
          j ∉ Set.range (toFun g)) := by
  constructor
  · rintro ⟨v, hp, hv⟩
    by_cases hlt : v.val < m + 1
    · have e : Fin.castLE (by omega) (⟨v.val, hlt⟩ : Fin (m + 1)) = v := Fin.ext rfl
      exact Or.inl ⟨⟨v.val, hlt⟩, by rwa [e],
        (mem_range_toFun_eqToHom_comp_tensorHom_iff_of_lt h f g v hlt).not.1 hv⟩
    · have e : (⟨m + 1 + (v.val - (m + 1)), by omega⟩ : Fin (m + n + 1 + 1)) = v :=
        Fin.ext (by
          dsimp only
          omega)
      exact Or.inr ⟨⟨v.val - (m + 1), by omega⟩, by rwa [e],
        (mem_range_toFun_eqToHom_comp_tensorHom_iff_of_le h f g v (not_lt.1 hlt)).not.1 hv⟩
  · rintro (⟨i, hp, hi⟩ | ⟨j, hp, hj⟩)
    · exact ⟨_, hp, (mem_range_toFun_eqToHom_comp_tensorHom_iff_of_lt h f g
        (Fin.castLE (m := m + n + 1 + 1) (by omega) i) i.isLt).not.2 hi⟩
    · refine ⟨_, hp, fun hm ↦ hj ?_⟩
      obtain ⟨w, hw⟩ := (mem_range_toFun_eqToHom_comp_tensorHom_iff_of_le h f g
        (⟨m + 1 + j, by omega⟩ : Fin (m + n + 1 + 1)) (Nat.le_add_right _ _)).1 hm
      exact ⟨w, hw.trans (Fin.ext (Nat.add_sub_cancel_left _ _))⟩

end stdSimplex

theorem range_joinMap_le {X Y X' Y' Z W : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ W} {f' : X' ⟶ Z}
    {g' : Y' ⟶ W} (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g) :
    Subcomplex.range (joinMap f g) ≤ Subcomplex.range (joinMap f' g') := by
  have e : joinMap (a ≫ f') (b ≫ g') = joinMap a b ≫ joinMap f' g' :=
    joinFunctor.map_comp (X := (X, Y)) (Y := (X', Y')) (Z := (Z, W)) (a, b) (f', g')
  rw [← ha, ← hb, e]
  exact Subfunctor.range_comp_le _ _

theorem boundary_join_sup_join_boundary (m n : ℕ) :
    (∂Δ[m]).join ⊤ ⊔ (⊤ : (Δ[m] : SSet.{u}).Subcomplex).join ∂Δ[n] =
      (∂Δ[m + n + 1]).preimage (stdSimplexJoinIso.{u} m n).hom := by
  ext k t
  obtain ⟨a, b, h, x, y, rfl⟩ := exists_joinMk t
  rw [Subfunctor.max_obj, Set.mem_union, Subcomplex.joinMk_mem_join_obj_iff,
    Subcomplex.joinMk_mem_join_obj_iff,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ i, i ∉ R)
      (fun _ ↦ mem_boundary_obj_iff) ⟨0, Set.notMem_empty _⟩ x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ i, i ∉ R)
      (fun _ ↦ mem_boundary_obj_iff) ⟨0, Set.notMem_empty _⟩ y,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial y,
    joinMk_mem_preimage_obj_iff _ (fun R ↦ ∃ i, i ∉ R) (fun _ ↦ mem_boundary_obj_iff)]
  have := exists_notMem_range_toFun_iff h (stdSimplexToHom _ a x) (stdSimplexToHom _ b y)
    (fun _ ↦ True)
  simp only [true_and, and_true] at this ⊢
  exact this.symm

theorem horn_join_sup_join_boundary (m n : ℕ) (k : Fin (m + 2)) :
    (Λ[m + 1, k]).join ⊤ ⊔ (⊤ : (Δ[m + 1] : SSet.{u}).Subcomplex).join ∂Δ[n] =
      (Λ[m + 1 + n + 1, k.castLE (by omega)]).preimage (stdSimplexJoinIso.{u} (m + 1) n).hom := by
  ext l t
  obtain ⟨a, b, h, x, y, rfl⟩ := exists_joinMk t
  obtain ⟨i₀, hi₀⟩ := exists_ne k
  rw [Subfunctor.max_obj, Set.mem_union, Subcomplex.joinMk_mem_join_obj_iff,
    Subcomplex.joinMk_mem_join_obj_iff,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ i, i ≠ k ∧ i ∉ R)
      (fun _ ↦ mem_horn_obj_iff k) ⟨i₀, hi₀, Set.notMem_empty _⟩ x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ i, i ∉ R)
      (fun _ ↦ mem_boundary_obj_iff) ⟨0, Set.notMem_empty _⟩ y,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial y,
    joinMk_mem_preimage_obj_iff _ (fun R ↦ ∃ i, i ≠ k.castLE (by omega) ∧ i ∉ R)
      (fun _ ↦ mem_horn_obj_iff _)]
  refine Iff.trans ?_ (exists_notMem_range_toFun_iff h _ _
    (fun v ↦ v ≠ k.castLE (by omega))).symm
  simp only [and_true, true_and]
  constructor
  · rintro (⟨i, hik, hi⟩ | ⟨j, hj⟩)
    · exact Or.inl ⟨i, fun e ↦ hik (Fin.castLE_injective _ e), hi⟩
    · refine Or.inr ⟨j, fun e ↦ ?_, hj⟩
      have he := congrArg Fin.val e
      have := k.isLt
      simp only [Fin.val_castLE] at he
      omega
  · rintro (⟨i, hik, hi⟩ | ⟨j, -, hj⟩)
    · exact Or.inl ⟨i, fun e ↦ hik (congrArg _ e), hi⟩
    · exact Or.inr ⟨j, hj⟩

theorem boundary_join_sup_join_horn (m n : ℕ) (k : Fin (n + 2)) :
    (∂Δ[m]).join ⊤ ⊔ (⊤ : (Δ[m] : SSet.{u}).Subcomplex).join Λ[n + 1, k] =
      (Λ[m + (n + 1) + 1, ⟨m + 1 + k, by omega⟩]).preimage
        (stdSimplexJoinIso.{u} m (n + 1)).hom := by
  ext l t
  obtain ⟨a, b, h, x, y, rfl⟩ := exists_joinMk t
  obtain ⟨j₀, hj₀⟩ := exists_ne k
  rw [Subfunctor.max_obj, Set.mem_union, Subcomplex.joinMk_mem_join_obj_iff,
    Subcomplex.joinMk_mem_join_obj_iff,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ i, i ∉ R)
      (fun _ ↦ mem_boundary_obj_iff) ⟨0, Set.notMem_empty _⟩ x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun R ↦ ∃ j, j ≠ k ∧ j ∉ R)
      (fun _ ↦ mem_horn_obj_iff k) ⟨j₀, hj₀, Set.notMem_empty _⟩ y,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial x,
    mem_range_trivialAugmentation_map_ι_app_iff _ (fun _ ↦ True) (fun _ ↦ mem_top_obj_iff)
      trivial y,
    joinMk_mem_preimage_obj_iff _ (fun R ↦ ∃ i, i ≠ ⟨m + 1 + k, by omega⟩ ∧ i ∉ R)
      (fun _ ↦ mem_horn_obj_iff _)]
  refine Iff.trans ?_ (exists_notMem_range_toFun_iff h _ _
    (fun v ↦ v ≠ ⟨m + 1 + k, by omega⟩)).symm
  simp only [and_true, true_and]
  constructor
  · rintro (⟨i, hi⟩ | ⟨j, hjk, hj⟩)
    · refine Or.inl ⟨i, fun e ↦ ?_, hi⟩
      have he := congrArg Fin.val e
      have := i.isLt
      simp only [Fin.val_castLE] at he
      omega
    · refine Or.inr ⟨j, fun e ↦ hjk (Fin.ext ?_), hj⟩
      have := congrArg Fin.val e
      dsimp only at this
      omega
  · rintro (⟨i, -, hi⟩ | ⟨j, hjk, hj⟩)
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨j, fun e ↦ hjk (by rw [e]), hj⟩

end SSet
