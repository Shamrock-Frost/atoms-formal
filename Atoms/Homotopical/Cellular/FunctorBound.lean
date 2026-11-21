import Atoms.Homotopical.Cellular.BoundedEmbedding

open CategoryTheory Limits Opposite MorphismProperty

namespace Atoms.Homotopical

universe v u

section Counting

variable {A : Type v} [SmallCategory A]

theorem mk_boundedSubfunctor_le {γ δ : Cardinal.{v}} (hγ : Cardinal.aleph0 ≤ γ)
    (hδ : Cardinal.aleph0 ≤ δ) (hAγ : Cardinal.mk A ≤ γ) (hAδ : Cardinal.mk A ≤ δ)
    {X : Aᵒᵖ ⥤ Type v} (hX : IsBounded δ X) :
    Cardinal.mk {S : Subfunctor X // IsBounded γ S.toFunctor} ≤ δ ^ γ := by
  let f : {S : Subfunctor X // IsBounded γ S.toFunctor} →
      {t : Set (Σ a, X.obj a) // Cardinal.mk t ≤ γ} := fun S =>
    ⟨{p | p.2 ∈ S.1.obj p.1}, by
      refine le_trans ?_ (mk_sigma_le_of_le (f := fun a => S.1.obj a) hγ
        ((mk_opposite A).trans_le hAγ) S.2)
      refine Cardinal.mk_le_of_injective
        (f := fun p : {p : Σ a, X.obj a | p.2 ∈ S.1.obj p.1} => ⟨p.1.1, p.1.2, p.2⟩) ?_
      rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Subtype.mk.injEq] at h
      subst h
      rfl⟩
  have hf : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    ext a x
    have h' := congrArg (fun t => (⟨a, x⟩ : Σ a, X.obj a) ∈ t.1) h
    exact Iff.of_eq h'
  refine (Cardinal.mk_le_of_injective hf).trans ((Cardinal.mk_bounded_set_le _ _).trans ?_)
  refine Cardinal.power_le_power_right (max_le ?_ hδ)
  exact mk_sigma_le_of_le (f := fun a => X.obj a) hδ ((mk_opposite A).trans_le hAδ) hX

end Counting

namespace BoundedEmbedding

variable {C : Type u} [Category.{v} C] {B : Type v} [SmallCategory B] (E : BoundedEmbedding C B)
  {X : C}

theorem exists_isBounded_le_range_map_subι {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) {β : Cardinal.{v}} (hβ : Cardinal.aleph0 ≤ β)
    (hB : ∀ a b : B, Cardinal.mk (a ⟶ b) ≤ β) (hB'o : Cardinal.mk B' ≤ β)
    [PreservesColimitsOfShape
      {S : Subfunctor (E.ι.obj X) // Atoms.Homotopical.IsBounded β S.toFunctor} F]
    (R : Subfunctor (F.obj X)) (hR : Atoms.Homotopical.IsBounded β R.toFunctor) :
    ∃ T : Subfunctor (E.ι.obj X), Atoms.Homotopical.IsBounded β T.toFunctor ∧
      R ≤ Subfunctor.range (F.map (E.subι T)) := by
  let P := {S : Subfunctor (E.ι.obj X) // Atoms.Homotopical.IsBounded β S.toFunctor}
  have : Fact (Order.succ β).IsRegular := ⟨Cardinal.isRegular_succ hβ⟩
  have := isCardinalFiltered_boundedSubfunctor hβ (E.ι.obj X)
  have := isFiltered_of_isCardinalFiltered P (Order.succ β)
  let G : P ⥤ Subfunctor (E.ι.obj X) := (Subtype.mono_coe _).functor
  have hlub : IsLUB (Set.range G.obj) ⊤ := E.isLUB_boundedSubfunctor hB X
  have hcov : ∀ (b : B'ᵒᵖ) (y : (F.obj X).obj b), ∃ p : P,
      y ∈ (Subfunctor.range (F.map (E.subι p.1))).obj b := by
    intro b y
    obtain ⟨p, y', hy'⟩ := E.exists_map_homOfLe_app_eq F G hlub
      ((F.map (inv (E.subι (⊤ : Subfunctor (E.ι.obj X))))).app b y)
    refine ⟨p, y', ?_⟩
    change (F.map (E.subι (G.obj p))).app b y' = y
    rw [← homOfLe_subι E (hlub.1 ⟨p, rfl⟩), F.map_comp, NatTrans.comp_app_apply, hy',
      ← NatTrans.comp_app_apply, ← F.map_comp, IsIso.inv_hom_id, F.map_id]
    rfl
  choose p hp using hcov
  refine ⟨⨆ q : Σ b : B'ᵒᵖ, R.obj b, (p q.1 q.2.1).1,
    isBounded_iSup hβ (mk_sigma_le_of_le hβ ((mk_opposite B').trans_le hB'o) hR) _
      fun q => (p q.1 q.2.1).2, ?_⟩
  intro b y hy
  obtain ⟨y', hy'⟩ := hp b y
  refine ⟨(F.map (E.homOfLe (le_iSup (fun q : Σ b : B'ᵒᵖ, R.obj b => (p q.1 q.2.1).1)
    ⟨b, y, hy⟩))).app b y', ?_⟩
  rw [← NatTrans.comp_app_apply, ← F.map_comp, homOfLe_subι]
  exact hy'

theorem exists_isBounded_le_inf_range_map_subι {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) {β : Cardinal.{v}} (hβ : Cardinal.aleph0 ≤ β)
    (hB : ∀ a b : B, Cardinal.mk (a ⟶ b) ≤ β) (hB'o : Cardinal.mk B' ≤ β)
    (X₀ : Subfunctor (E.ι.obj X)) [Mono (F.map (E.subι X₀))]
    [PreservesColimitsOfShape
      {S : Subfunctor (E.ι.obj (E.sub X₀)) // Atoms.Homotopical.IsBounded β S.toFunctor} F]
    (R : Subfunctor (F.obj X)) (hR : Atoms.Homotopical.IsBounded β R.toFunctor) :
    ∃ T : Subfunctor (E.ι.obj X), T ≤ X₀ ∧ Atoms.Homotopical.IsBounded β T.toFunctor ∧
      Subfunctor.range (F.map (E.subι X₀)) ⊓ R ≤ Subfunctor.range (F.map (E.subι T)) := by
  have hinj : ∀ b, Function.Injective ((F.map (E.subι X₀)).app b) := fun b =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance b)
  obtain ⟨T₀, hT₀, hRT₀⟩ := E.exists_isBounded_le_range_map_subι F hβ hB hB'o
    (R.preimage (F.map (E.subι X₀))) fun b =>
      (Cardinal.mk_le_of_injective (f := fun x : (R.preimage (F.map (E.subι X₀))).obj b =>
        (⟨(F.map (E.subι X₀)).app b x.1, x.2⟩ : R.obj b))
        fun x y hxy => Subtype.ext (hinj b (congrArg Subtype.val hxy))).trans (hR b)
  let m := E.subι T₀ ≫ E.subι X₀
  have e : E.ι.map m = E.ι.map (E.subι T₀) ≫ E.ι.map (E.subι X₀) := E.ι.map_comp _ _
  have : Mono (E.ι.map m) := by
    rw [e]
    infer_instance
  refine ⟨Subfunctor.range (E.ι.map m), ?_, isBounded_range _ ((E.isBounded_sub_iff β T₀).2 hT₀),
    ?_⟩
  · rw [e]
    exact (Subfunctor.range_comp_le _ _).trans (E.range_map_subι X₀).le
  · rintro b _ ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨y, rfl⟩ := hRT₀ b hx
    refine ⟨(F.map (E.isoSubRange m).hom).app b y, ?_⟩
    rw [← NatTrans.comp_app_apply, ← F.map_comp, isoSubRange_hom_subι, F.map_comp,
      NatTrans.comp_app_apply]

theorem exists_isBounded_obj_of_isBounded {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) (γ : Cardinal.{v}) :
    ∃ c : Cardinal.{v}, ∀ X : C, E.IsBounded γ X → Atoms.Homotopical.IsBounded c (F.obj X) := by
  obtain ⟨ι, R, -, hR⟩ := E.exists_boundedRepresentatives γ
  refine ⟨⨆ p : ι × B'ᵒᵖ, Cardinal.mk ((F.obj (R p.1)).obj p.2), fun X hX => ?_⟩
  obtain ⟨i, ⟨e⟩⟩ := hR X hX
  refine IsBounded.of_mono (F.mapIso e.symm).inv fun a => ?_
  exact le_ciSup Cardinal.bddAbove_of_small (i, a)

theorem isBounded_obj_of_boundedSubfunctor {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) (κ : Cardinal.{v}) [Fact κ.IsRegular] [F.IsCardinalAccessible κ]
    {γ β : Cardinal.{v}} (hγ : Cardinal.aleph0 ≤ γ) (hκ : κ ≤ Order.succ γ)
    (hB : ∀ a b : B, Cardinal.mk (a ⟶ b) ≤ γ) (hβ : Cardinal.aleph0 ≤ β) (X : C)
    (hP : Cardinal.mk {S : Subfunctor (E.ι.obj X) // Atoms.Homotopical.IsBounded γ S.toFunctor}
      ≤ β)
    (hG : ∀ S : {S : Subfunctor (E.ι.obj X) // Atoms.Homotopical.IsBounded γ S.toFunctor},
      Atoms.Homotopical.IsBounded β (F.obj (E.sub S.1))) :
    Atoms.Homotopical.IsBounded β (F.obj X) := by
  let P := {S : Subfunctor (E.ι.obj X) // Atoms.Homotopical.IsBounded γ S.toFunctor}
  have : Fact (Order.succ γ).IsRegular := ⟨Cardinal.isRegular_succ hγ⟩
  have := isCardinalFiltered_boundedSubfunctor hγ (E.ι.obj X)
  have := isFiltered_of_isCardinalFiltered P (Order.succ γ)
  have : IsCardinalFiltered P κ := IsCardinalFiltered.of_le _ hκ
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ P
  let G : P ⥤ Subfunctor (E.ι.obj X) := (Subtype.mono_coe _).functor
  let hc := isColimitOfPreserves F (E.isColimitSubFunctorCocone G (E.isLUB_boundedSubfunctor hB X))
  let e : colimit ((G ⋙ E.subFunctor X) ⋙ F) ≅ F.obj X :=
    (colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      F.mapIso (@asIso _ _ _ _ (E.subι (⊤ : Subfunctor (E.ι.obj X))) (E.isIso_subι_top))
  exact (isBounded_colimit hβ hP _ fun S => hG S).of_mono e.inv

theorem exists_isBounded_pow_of_isCardinalAccessible {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) (κ : Cardinal.{v}) [Fact κ.IsRegular] [F.IsCardinalAccessible κ] :
    ∃ γ : Cardinal.{v}, Cardinal.aleph0 ≤ γ ∧
      ∀ δ : Cardinal.{v}, γ ≤ δ → ∀ X : C, E.IsBounded δ X →
        Atoms.Homotopical.IsBounded (δ ^ γ) (F.obj X) := by
  obtain ⟨c₀, hc₀⟩ := exists_cardinal_bound_category B
  let γ₁ := max (max Cardinal.aleph0 κ) c₀
  have hγ₁ : Cardinal.aleph0 ≤ γ₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hκ : κ ≤ Order.succ γ₁ :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (Order.le_succ _)
  obtain ⟨hBo, hB⟩ := hc₀ γ₁ (le_max_right _ _)
  obtain ⟨c, hc⟩ := E.exists_isBounded_obj_of_isBounded F γ₁
  refine ⟨max γ₁ c, hγ₁.trans (le_max_left _ _), fun δ hδγ X hX => ?_⟩
  have hδ : Cardinal.aleph0 ≤ δ := hγ₁.trans ((le_max_left _ _).trans hδγ)
  have hδ0 : δ ≠ 0 := (Cardinal.aleph0_pos.trans_le hδ).ne'
  have hδpow : δ ≤ δ ^ max γ₁ c :=
    Cardinal.self_le_power δ (Cardinal.one_le_aleph0.trans (hγ₁.trans (le_max_left _ _)))
  refine E.isBounded_obj_of_boundedSubfunctor F κ hγ₁ hκ hB (hδ.trans hδpow) X ?_ ?_
  · exact (mk_boundedSubfunctor_le hγ₁ hδ hBo (hBo.trans ((le_max_left _ _).trans hδγ))
      hX).trans (Cardinal.power_le_power_left hδ0 (le_max_left _ _))
  · intro S a
    exact (hc _ ((E.isBounded_sub_iff γ₁ S.1).2 S.2) a).trans
      (((le_max_right _ _).trans hδγ).trans hδpow)

theorem exists_isBounded_two_pow_of_isCardinalAccessible {B' : Type v} [SmallCategory B']
    (F : C ⥤ B'ᵒᵖ ⥤ Type v) (κ : Cardinal.{v}) [Fact κ.IsRegular] [F.IsCardinalAccessible κ] :
    ∃ γ : Cardinal.{v}, Cardinal.aleph0 ≤ γ ∧
      ∀ α : Cardinal.{v}, γ ≤ α → ∀ X : C, E.IsBounded (2 ^ α) X →
        Atoms.Homotopical.IsBounded (2 ^ α) (F.obj X) := by
  obtain ⟨γ, hγ, hF⟩ := E.exists_isBounded_pow_of_isCardinalAccessible F κ
  refine ⟨γ, hγ, fun α hα X hX => ?_⟩
  have h := hF (2 ^ α) (hα.trans (Cardinal.cantor α).le) X hX
  rwa [← Cardinal.power_mul,
    Cardinal.mul_eq_left (hγ.trans hα) hα (Cardinal.aleph0_pos.trans_le hγ).ne'] at h

end BoundedEmbedding

section Presheaves

variable {A : Type v} [SmallCategory A]

theorem exists_isBounded_pow_of_isCardinalAccessible (G : (Aᵒᵖ ⥤ Type v) ⥤ Aᵒᵖ ⥤ Type v)
    (κ : Cardinal.{v}) [Fact κ.IsRegular] [G.IsCardinalAccessible κ] :
    ∃ γ : Cardinal.{v}, Cardinal.aleph0 ≤ γ ∧
      ∀ δ : Cardinal.{v}, γ ≤ δ → ∀ X : Aᵒᵖ ⥤ Type v, IsBounded δ X →
        IsBounded (δ ^ γ) (G.obj X) :=
  (BoundedEmbedding.id A).exists_isBounded_pow_of_isCardinalAccessible G κ

theorem exists_isBounded_two_pow_of_isCardinalAccessible
    (G : (Aᵒᵖ ⥤ Type v) ⥤ Aᵒᵖ ⥤ Type v) (κ : Cardinal.{v}) [Fact κ.IsRegular]
    [G.IsCardinalAccessible κ] :
    ∃ γ : Cardinal.{v}, Cardinal.aleph0 ≤ γ ∧
      ∀ α : Cardinal.{v}, γ ≤ α → ∀ X : Aᵒᵖ ⥤ Type v, IsBounded (2 ^ α) X →
        IsBounded (2 ^ α) (G.obj X) :=
  (BoundedEmbedding.id A).exists_isBounded_two_pow_of_isCardinalAccessible G κ

variable {B : Type v} [SmallCategory B]

theorem mk_costructuredArrow_yoneda_le {β : Cardinal.{v}} (hβ : Cardinal.aleph0 ≤ β)
    (hAo : Cardinal.mk A ≤ β) {X : Aᵒᵖ ⥤ Type v} (hX : IsBounded β X) :
    Cardinal.mk (CostructuredArrow yoneda X) ≤ β := by
  refine (Cardinal.mk_le_of_surjective
    (f := fun p : Σ a : A, X.obj (op a) => CostructuredArrow.mk (yonedaEquiv.symm p.2))
    fun j => ⟨⟨j.left, yonedaEquiv j.hom⟩, ?_⟩).trans
      (mk_sigma_le_of_le hβ hAo fun a => hX (op a))
  dsimp only
  rw [Equiv.symm_apply_apply]
  exact (CostructuredArrow.eq_mk j).symm

theorem exists_isBounded_obj_of_preservesColimits (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    [PreservesColimitsOfSize.{v, v} F] :
    ∃ c : Cardinal.{v}, Cardinal.aleph0 ≤ c ∧ ∀ β : Cardinal.{v}, c ≤ β →
      ∀ X : Aᵒᵖ ⥤ Type v, IsBounded β X → IsBounded β (F.obj X) := by
  let s := ⨆ p : A × Bᵒᵖ, Cardinal.mk ((F.obj (yoneda.obj p.1)).obj p.2)
  refine ⟨max Cardinal.aleph0 (max (Cardinal.mk A) s), le_max_left _ _, fun β hcβ X hX => ?_⟩
  have hβ : Cardinal.aleph0 ≤ β := (le_max_left _ _).trans hcβ
  have hAo : Cardinal.mk A ≤ β := ((le_max_left _ _).trans (le_max_right _ _)).trans hcβ
  have hs : s ≤ β := ((le_max_right _ _).trans (le_max_right _ _)).trans hcβ
  let hc := isColimitOfPreserves F (Presheaf.isColimitTautologicalCocone X)
  let e : colimit ((CostructuredArrow.proj yoneda X ⋙ yoneda) ⋙ F) ≅ F.obj X :=
    (colimit.isColimit _).coconePointUniqueUpToIso hc
  refine (isBounded_colimit hβ (mk_costructuredArrow_yoneda_le hβ hAo hX) _
    fun j b => ?_).of_mono e.inv
  exact (le_ciSup (f := fun p : A × Bᵒᵖ => Cardinal.mk ((F.obj (yoneda.obj p.1)).obj p.2))
    Cardinal.bddAbove_of_small (j.left, b)).trans hs

theorem exists_isBounded_le_range_map_ι (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    {β : Cardinal.{v}} (hβ : Cardinal.aleph0 ≤ β) (hA : ∀ a b : A, Cardinal.mk (a ⟶ b) ≤ β)
    (hBo : Cardinal.mk B ≤ β) {X : Aᵒᵖ ⥤ Type v}
    [PreservesColimitsOfShape {S : Subfunctor X // IsBounded β S.toFunctor} F]
    (R : Subfunctor (F.obj X)) (hR : IsBounded β R.toFunctor) :
    ∃ T : Subfunctor X, IsBounded β T.toFunctor ∧ R ≤ Subfunctor.range (F.map T.ι) := by
  have : PreservesColimitsOfShape
      {S : Subfunctor ((BoundedEmbedding.id A).ι.obj X) // IsBounded β S.toFunctor} F := ‹_›
  obtain ⟨T, hT, hRT⟩ := (BoundedEmbedding.id A).exists_isBounded_le_range_map_subι F hβ hA hBo
    R hR
  exact ⟨T, hT, hRT.trans_eq
    (congrArg (fun f => Subfunctor.range (F.map f)) (BoundedEmbedding.id_subι (Y := X) T))⟩

theorem range_map_ι_inf_of_preservesColimits (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    [PreservesColimitsOfSize.{v, v} F]
    (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f))
    {X : Aᵒᵖ ⥤ Type v} (J K : Subfunctor X) :
    Subfunctor.range (F.map (J ⊓ K).ι) =
      Subfunctor.range (F.map J.ι) ⊓ Subfunctor.range (F.map K.ι) := by
  refine le_antisymm (le_inf (Subfunctor.range_map_ι_le_of_le F inf_le_left)
    (Subfunctor.range_map_ι_le_of_le F inf_le_right)) ?_
  rintro b z ⟨⟨y₁, h₁⟩, ⟨y₂, h₂⟩⟩
  have : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  have hinj : ∀ {S T : Subfunctor X} (h : S ≤ T),
      Function.Injective ((F.map (Subfunctor.homOfLe h)).app b) := fun h =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (hF _ inferInstance) b)
  have hsq : Lattice.BicartSq (J ⊓ K) J K (J ⊔ K) := ⟨rfl, rfl⟩
  have hP := Types.isPullback_of_isPushout
    (((Subfunctor.isPushout_of_bicartSq hsq).map F).map ((evaluation Bᵒᵖ (Type v)).obj b))
    (hinj inf_le_left)
  have hJK : Function.Injective ((F.map (J ⊔ K).ι).app b) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (hF _ inferInstance) b)
  have e : ∀ {S T : Subfunctor X} (h : S ≤ T) (y : (F.obj S.toFunctor).obj b),
      (F.map T.ι).app b ((F.map (Subfunctor.homOfLe h)).app b y) = (F.map S.ι).app b y :=
    fun h y => by
      rw [← NatTrans.comp_app_apply, ← F.map_comp, Subfunctor.homOfLe_ι]
  obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback hP y₁ y₂
    (hJK ((e le_sup_left y₁).trans (h₁.trans h₂.symm) |>.trans (e le_sup_right y₂).symm))
  exact ⟨x, (e inf_le_left x).symm.trans ((congrArg _ hx).trans h₁)⟩

end Presheaves

end Atoms.Homotopical
