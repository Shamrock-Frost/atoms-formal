import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Subfunctor.Image

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

def IsBounded (α : Cardinal.{v}) (X : Aᵒᵖ ⥤ Type v) : Prop :=
  ∀ a : Aᵒᵖ, Cardinal.mk (X.obj a) ≤ α

theorem mk_sigma_le_of_le {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {ι : Type v}
    {f : ι → Type v} (hι : Cardinal.mk ι ≤ α) (hf : ∀ i, Cardinal.mk (f i) ≤ α) :
    Cardinal.mk (Σ i, f i) ≤ α := by
  rw [Cardinal.mk_sigma]
  exact (Cardinal.sum_le_mk_mul_iSup _).trans (Cardinal.mul_le_of_le hα hι (ciSup_le' hf))

theorem mk_arrow_le {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {K : Type v}
    [Category.{v} K] (hK : Cardinal.mk K ≤ α) (hH : ∀ x y : K, Cardinal.mk (x ⟶ y) ≤ α) :
    Cardinal.mk (Arrow K) ≤ α := by
  rw [Cardinal.mk_congr (Arrow.equivSigma K)]
  exact mk_sigma_le_of_le hα hK fun x => mk_sigma_le_of_le hα hK fun y => hH x y

theorem mk_opposite (K : Type v) : Cardinal.mk Kᵒᵖ = Cardinal.mk K :=
  Cardinal.mk_congr (equivToOpposite (α := K)).symm

theorem mk_arrow_op_le {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {K : Type v}
    [Category.{v} K] (hK : Cardinal.mk K ≤ α) (hH : ∀ x y : K, Cardinal.mk (x ⟶ y) ≤ α) :
    Cardinal.mk (Arrow Kᵒᵖ) ≤ α := by
  refine mk_arrow_le hα ?_ fun x y => ?_
  · rwa [mk_opposite]
  · rw [Cardinal.mk_congr (opEquiv _ _)]
    exact hH _ _

theorem IsBounded.of_mono {α : Cardinal.{v}} {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) [Mono f]
    (hY : IsBounded α Y) : IsBounded α X := fun a =>
  (Cardinal.mk_le_of_injective ((mono_iff_injective (f.app a)).1
    (NatTrans.mono_iff_mono_app f |>.1 inferInstance a))).trans (hY a)

theorem isBounded_yoneda {α : Cardinal.{v}} (hA : ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ α)
    (a : A) : IsBounded α (yoneda.obj a) := fun b => hA b.unop a

theorem isBounded_range {β : Cardinal.{v}} {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y)
    (hX : IsBounded β X) : IsBounded β (Subfunctor.range f).toFunctor := fun a =>
  Cardinal.mk_range_le.trans (hX a)

theorem IsBounded.mono {α β : Cardinal.{v}} (h : α ≤ β) {X : Aᵒᵖ ⥤ Type v}
    (hX : IsBounded α X) : IsBounded β X := fun a =>
  (hX a).trans h

theorem exists_isBounded_forall {ι : Type v} (X : ι → Aᵒᵖ ⥤ Type v) :
    ∃ α : Cardinal.{v}, ∀ i, IsBounded α (X i) :=
  ⟨⨆ p : ι × Aᵒᵖ, Cardinal.mk ((X p.1).obj p.2), fun i a =>
    le_ciSup (f := fun p : ι × Aᵒᵖ => Cardinal.mk ((X p.1).obj p.2)) Cardinal.bddAbove_of_small
      (i, a)⟩

variable (A) in
theorem exists_cardinal_bound_category :
    ∃ c : Cardinal.{v}, ∀ γ : Cardinal.{v}, c ≤ γ →
      Cardinal.mk A ≤ γ ∧ ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ γ := by
  refine ⟨max (Cardinal.mk A) (⨆ p : A × A, Cardinal.mk (p.1 ⟶ p.2)),
    fun γ hγ => ⟨(le_max_left _ _).trans hγ, fun a b => ?_⟩⟩
  exact (le_ciSup (f := fun p : A × A => Cardinal.mk (p.1 ⟶ p.2)) Cardinal.bddAbove_of_small
    (a, b)).trans ((le_max_right _ _).trans hγ)

variable (A) in
theorem exists_two_pow_bound (c : Cardinal.{v}) :
    ∃ α₀ : Cardinal.{v}, c ≤ α₀ ∧ Cardinal.aleph0 ≤ α₀ ∧ ∀ α : Cardinal.{v}, α₀ ≤ α →
      Cardinal.aleph0 ≤ 2 ^ α ∧ Cardinal.mk A ≤ 2 ^ α ∧
        ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ 2 ^ α := by
  obtain ⟨c₀, hc₀⟩ := exists_cardinal_bound_category A
  refine ⟨max (max c Cardinal.aleph0) c₀, (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), fun α hα => ?_⟩
  have hαβ : α ≤ 2 ^ α := (Cardinal.cantor α).le
  exact ⟨(((le_max_right _ _).trans (le_max_left _ _)).trans hα).trans hαβ,
    hc₀ _ ((le_max_right _ _).trans hα |>.trans hαβ)⟩

theorem isBounded_colimit {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {J : Type v}
    [SmallCategory J] (hJ : Cardinal.mk J ≤ α) (F : J ⥤ Aᵒᵖ ⥤ Type v)
    (hF : ∀ j, IsBounded α (F.obj j)) : IsBounded α (colimit F) := by
  intro a
  let hc := isColimitOfPreserves ((evaluation Aᵒᵖ (Type v)).obj a) (colimit.isColimit F)
  have hsurj : Function.Surjective
      (fun p : Σ j, (F.obj j).obj a => (colimit.ι F p.1).app a p.2) := by
    intro x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ hc x
    exact ⟨⟨j, y⟩, rfl⟩
  exact (Cardinal.mk_le_of_surjective hsurj).trans (mk_sigma_le_of_le hα hJ fun j => hF j a)

theorem isBounded_iSup {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {X : Aᵒᵖ ⥤ Type v}
    {ι : Type v} (hι : Cardinal.mk ι ≤ α) (S : ι → Subfunctor X)
    (hS : ∀ i, IsBounded α (S i).toFunctor) : IsBounded α (⨆ i, S i).toFunctor := by
  intro a
  change Cardinal.mk ((⨆ i, S i).obj a) ≤ α
  rw [Subfunctor.iSup_obj]
  exact (Cardinal.mk_iUnion_le _).trans
    (Cardinal.mul_le_of_le hα hι (ciSup_le' fun i => hS i a))

theorem isBounded_sup {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α) {X : Aᵒᵖ ⥤ Type v}
    {S T : Subfunctor X} (hS : IsBounded α S.toFunctor) (hT : IsBounded α T.toFunctor) :
    IsBounded α (S ⊔ T).toFunctor := fun a => by
  change Cardinal.mk ↥(S.obj a ∪ T.obj a) ≤ α
  exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hα (hS a) (hT a))

theorem iSup_boundedSubfunctor_eq_top {α : Cardinal.{v}}
    (hA : ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ α) (X : Aᵒᵖ ⥤ Type v) :
    ⨆ S : {S : Subfunctor X // IsBounded α S.toFunctor}, S.1 = ⊤ := by
  refine eq_top_iff.2 fun a x _ => ?_
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨⟨Subfunctor.range (yonedaEquiv.symm x : yoneda.obj (unop a) ⟶ X),
    isBounded_range _ (isBounded_yoneda hA _)⟩, ⟨𝟙 _, ?_⟩⟩
  exact (yonedaEquiv_apply _).symm.trans (yonedaEquiv.apply_symm_apply x)

theorem isCardinalFiltered_boundedSubfunctor {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α)
    (X : Aᵒᵖ ⥤ Type v) [Fact (Order.succ α).IsRegular] :
    IsCardinalFiltered {S : Subfunctor X // IsBounded α S.toFunctor} (Order.succ α) := by
  refine isCardinalFiltered_preorder _ _ fun K s hK => ?_
  refine ⟨⟨⨆ k, (s k).1, isBounded_iSup hα (Order.lt_succ_iff.1 hK) _ fun k => (s k).2⟩,
    fun k => ?_⟩
  exact le_iSup (fun k => (s k).1) k

structure CarrierPresheaf (A : Type v) [SmallCategory A] (T : Type v) where
  obj : Aᵒᵖ → Set T
  map : ∀ {a b : Aᵒᵖ}, (a ⟶ b) → obj a → obj b
  map_id : ∀ (a : Aᵒᵖ) (x : obj a), map (𝟙 a) x = x
  map_comp : ∀ {a b c : Aᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (x : obj a),
    map (f ≫ g) x = map g (map f x)

namespace CarrierPresheaf

variable {T : Type v}

@[simps]
def toFunctor (d : CarrierPresheaf A T) : Aᵒᵖ ⥤ Type v where
  obj a := d.obj a
  map f := ↾(d.map f)
  map_id a := by
    ext x
    simp [d.map_id]
  map_comp f g := by
    ext x
    simp [d.map_comp]

theorem isBounded_toFunctor {α : Cardinal.{v}} (hT : Cardinal.mk T ≤ α)
    (d : CarrierPresheaf A T) : IsBounded α d.toFunctor := fun _ =>
  (Cardinal.mk_subtype_le _).trans hT

noncomputable def ofInjective (X : Aᵒᵖ ⥤ Type v) (e : ∀ a, X.obj a → T)
    (he : ∀ a, Function.Injective (e a)) : CarrierPresheaf A T where
  obj a := Set.range (e a)
  map {a b} f y := ⟨e b (X.map f ((Equiv.ofInjective _ (he a)).symm y)), Set.mem_range_self _⟩
  map_id a y := by
    apply Subtype.ext
    simp [Equiv.apply_ofInjective_symm]
  map_comp f g y := by
    apply Subtype.ext
    simp

noncomputable def isoOfInjective (X : Aᵒᵖ ⥤ Type v) (e : ∀ a, X.obj a → T)
    (he : ∀ a, Function.Injective (e a)) : X ≅ (ofInjective X e he).toFunctor :=
  NatIso.ofComponents (fun a => (Equiv.ofInjective _ (he a)).toIso) fun {a b} f => by
    ext x
    apply Subtype.ext
    change e b (X.map f x) =
      e b (X.map f ((Equiv.ofInjective _ (he a)).symm (Equiv.ofInjective _ (he a) x)))
    rw [Equiv.symm_apply_apply]

end CarrierPresheaf

theorem exists_boundedRepresentatives (α : Cardinal.{v}) :
    ∃ (ι : Type v) (R : ι → Aᵒᵖ ⥤ Type v), (∀ i, IsBounded α (R i)) ∧
      ∀ X : Aᵒᵖ ⥤ Type v, IsBounded α X → ∃ i, Nonempty (X ≅ R i) := by
  refine ⟨CarrierPresheaf A α.out, CarrierPresheaf.toFunctor,
    CarrierPresheaf.isBounded_toFunctor (Cardinal.mk_out α).le, fun X hX => ?_⟩
  have he : ∀ a, Nonempty (X.obj a ↪ α.out) := fun a => by
    rw [← Cardinal.le_def, Cardinal.mk_out]
    exact hX a
  let e := fun a => (he a).some
  exact ⟨_, ⟨CarrierPresheaf.isoOfInjective X (fun a => e a) fun a => (e a).injective⟩⟩

theorem mk_arrow_elements_op_le {α : Cardinal.{v}} (hα : Cardinal.aleph0 ≤ α)
    (hA : ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ α) (hAo : Cardinal.mk A ≤ α)
    {X : Aᵒᵖ ⥤ Type v} (hX : IsBounded α X) : Cardinal.mk (Arrow X.Elementsᵒᵖ) ≤ α := by
  refine mk_arrow_op_le hα ?_ fun x y => ?_
  · refine mk_sigma_le_of_le (f := fun a : Aᵒᵖ => X.obj a) hα ?_ hX
    rwa [mk_opposite]
  · refine (Cardinal.mk_subtype_le (α := x.1 ⟶ y.1) _).trans ?_
    rw [Cardinal.mk_congr (opEquiv _ _)]
    exact hA _ _

theorem isCardinalPresentable_of_isBounded {α κ : Cardinal.{v}} [Fact κ.IsRegular]
    (hακ : α < κ) (hα : Cardinal.aleph0 ≤ α) (hA : ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ α)
    (hAo : Cardinal.mk A ≤ α) {X : Aᵒᵖ ⥤ Type v} (hX : IsBounded α X) :
    IsCardinalPresentable X κ := by
  have : ∀ k, IsCardinalPresentable ((Presheaf.functorToRepresentables.{0} X).obj k) κ :=
    fun k => by (try simp only [Presheaf.functorToRepresentables_obj]); infer_instance
  exact isCardinalPresentable_of_isColimit _ (Presheaf.colimitOfRepresentable.{0} X) κ
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).2
      ((mk_arrow_elements_op_le hα hA hAo hX).trans_lt hακ))

end Atoms.Homotopical
