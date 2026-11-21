import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantReplacement
import Atoms.Homotopical.Cellular.FunctorBound

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A B : Type v} [SmallCategory A] [SmallCategory B]

theorem exists_isBounded_le_of_step (κ : Cardinal.{v}) [Fact κ.IsRegular] {β : Cardinal.{v}}
    (hβ : Cardinal.aleph0 ≤ β) (hκβ : κ ≤ β) {X : Aᵒᵖ ⥤ Type v}
    (P : Subfunctor X → Subfunctor X → Prop)
    (hP : ∀ ⦃K K' K'' : Subfunctor X⦄, K' ≤ K'' → P K K' → P K K'')
    (hPc : ∀ Kc : κ.ord.ToType → Subfunctor X, Monotone Kc →
      (∀ γ, P (Kc γ) (⨆ γ, Kc γ)) → P (⨆ γ, Kc γ) (⨆ γ, Kc γ))
    (hstep : ∀ K : Subfunctor X, IsBounded β K.toFunctor → ∃ K' : Subfunctor X,
      IsBounded β K'.toFunctor ∧ K ≤ K' ∧ P K K')
    (J : Subfunctor X) (hJ : IsBounded β J.toFunctor) :
    ∃ K : Subfunctor X, J ≤ K ∧ IsBounded β K.toFunctor ∧ P K K := by
  classical
  have hstep' : ∀ K : Subfunctor X, ∃ K' : Subfunctor X, K ≤ K' ∧
      (IsBounded β K.toFunctor → IsBounded β K'.toFunctor ∧ P K K') := by
    intro K
    by_cases hK : IsBounded β K.toFunctor
    · obtain ⟨K', h₁, h₂, h₃⟩ := hstep K hK
      exact ⟨K', h₂, fun _ => ⟨h₁, h₃⟩⟩
    · exact ⟨K, le_rfl, fun h => absurd h hK⟩
  choose g hg_le hg using hstep'
  let ι := κ.ord.ToType
  have : NoMaxOrder ι := Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le
  have := isFiltered_of_isCardinalFiltered ι κ
  have hι : Cardinal.mk ι ≤ β := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact hκβ
  let Kc : ι → Subfunctor X := WellFoundedLT.fix (motive := fun _ => Subfunctor X)
    fun γ rec => J ⊔ ⨆ δ : {δ : ι // δ < γ}, g (rec δ.1 δ.2)
  have hK_eq : ∀ γ, Kc γ = J ⊔ ⨆ δ : {δ : ι // δ < γ}, g (Kc δ.1) := fun γ =>
    WellFoundedLT.fix_eq _ γ
  have hbdd : ∀ γ, IsBounded β (Kc γ).toFunctor := fun γ =>
    WellFoundedLT.induction (motive := fun γ => IsBounded β (Kc γ).toFunctor) γ fun γ ih => by
      rw [hK_eq]
      exact isBounded_sup hβ hJ (isBounded_iSup hβ ((Cardinal.mk_subtype_le _).trans hι) _
        fun δ => (hg _ (ih δ.1 δ.2)).1)
  have hstepK : ∀ δ γ : ι, δ < γ → g (Kc δ) ≤ Kc γ := fun δ γ hδ => by
    rw [hK_eq γ]
    exact le_sup_of_le_right (le_iSup (fun δ' : {δ' : ι // δ' < γ} => g (Kc δ'.1)) ⟨δ, hδ⟩)
  have hmono : Monotone Kc := fun δ γ hδ =>
    hδ.eq_or_lt.elim (fun e => e ▸ le_rfl) fun hlt => (hg_le _).trans (hstepK _ _ hlt)
  obtain ⟨γ₀⟩ := IsFiltered.nonempty (C := ι)
  refine ⟨⨆ γ, Kc γ, ?_, isBounded_iSup hβ hι Kc hbdd, hPc Kc hmono fun γ => ?_⟩
  · refine le_trans ?_ (le_iSup Kc γ₀)
    rw [hK_eq]
    exact le_sup_left
  · obtain ⟨γ', hγ'⟩ := exists_gt γ
    exact hP ((hstepK _ _ hγ').trans (le_iSup Kc γ')) (hg _ (hbdd γ)).2

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  [HasCellularModel C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
  [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] [HasBinaryProducts C]
  [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}]
  {B : Type v} [SmallCategory B] (E : BoundedEmbedding C B)
  (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) [S.IsSmall.{v}]

theorem trivialCofibrations_homOfLe_inf_of_range_le
    (hS : S ≤ MorphismProperty.monomorphisms C) {X D : C} (i : X ⟶ D)
    (hi : 𝕀.trivialCofibrations S i) (d : 𝕀.DeformationRetract ((𝕀.fibrantReplacement S).map i))
    (K : Subfunctor (E.ι.obj D))
    (hK : Subfunctor.range (E.ι.map (𝕀.I.map ((𝕀.fibrantReplacement S).map (E.subι K)) ≫
        d.homotopy)) ≤ Subfunctor.range (E.ι.map ((𝕀.fibrantReplacement S).map (E.subι K))))
    (hKi : Subfunctor.range (E.ι.map ((𝕀.fibrantReplacement S).map
          (E.subι (Subfunctor.range (E.ι.map i))))) ⊓
        Subfunctor.range (E.ι.map ((𝕀.fibrantReplacement S).map (E.subι K))) ≤
      Subfunctor.range (E.ι.map ((𝕀.fibrantReplacement S).map
        (E.subι (Subfunctor.range (E.ι.map i) ⊓ K))))) :
    (𝕀.trivialCofibrations S)
      (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ K ≤ K)) := by
  have : Mono i := hi.1
  let L := 𝕀.fibrantReplacement S
  let M := Subfunctor.range (E.ι.map i) ⊓ K
  let u : E.sub M ⟶ E.sub K := E.homOfLe inf_le_right
  have hu₀ : u ≫ E.subι K = E.subι M := E.homOfLe_subι _
  have := 𝕀.mono_fibrantReplacement_map S hS (E.subι K)
  have := 𝕀.mono_fibrantReplacement_map S hS (E.subι M)
  have := 𝕀.mono_fibrantReplacement_map S hS (E.isoSubRange i).hom
  have hu : L.map u ≫ L.map (E.subι K) = L.map (E.subι M) := by
    rw [← Functor.map_comp, hu₀]
  obtain ⟨c, hc⟩ := E.exists_comp_eq_of_range_le i (E.subι M) (by
    rw [E.range_map_subι]
    exact inf_le_left)
  have hmM : L.map (E.subι M) = L.map c ≫ L.map i := by
    rw [← Functor.map_comp, hc]
  obtain ⟨h', hh'⟩ := E.exists_comp_eq_of_range_le _ _ hK
  have e₁ : L.map (E.subι K) ≫ d.retraction ≫ L.map i =
      (𝕀.endpoint true).app _ ≫ h' ≫ L.map (E.subι K) := by
    rw [hh', ← d.endpoint_true_comp_homotopy, 𝕀.endpoint_naturality_assoc]
  have ei : L.map (E.subι K) ≫ d.retraction ≫ L.map i =
      (L.map (E.subι K) ≫ d.retraction ≫ L.map (E.isoSubRange i).hom) ≫
        L.map (E.subι (Subfunctor.range (E.ι.map i))) := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp,
      BoundedEmbedding.isoSubRange_hom_subι]
  obtain ⟨r', hr'⟩ := E.exists_comp_eq_of_range_le (L.map (E.subι M))
    (L.map (E.subι K) ≫ d.retraction ≫ L.map i) (by
      refine le_trans (le_inf ?_ ?_) hKi
      · rw [ei, E.ι.map_comp]
        exact Subfunctor.range_comp_le _ _
      · rw [e₁, E.ι.map_comp, E.ι.map_comp]
        exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_comp_le _ _))
  have hIu : 𝕀.I.map (L.map u) ≫ 𝕀.I.map (L.map (E.subι K)) =
      𝕀.I.map (L.map c) ≫ 𝕀.I.map (L.map i) := by
    rw [← Functor.map_comp, hu, hmM, Functor.map_comp]
  refine 𝕀.trivialCofibrations_of_deformation_retract_fibrantReplacement_map S hS u
    ⟨r', h', ?_, ?_, ?_, ?_⟩
  · rw [← cancel_mono (L.map (E.subι M)), Category.assoc, hr', reassoc_of% hu, hmM,
      Category.assoc, reassoc_of% d.comp_retraction, Category.id_comp]
  · rw [← cancel_mono (L.map (E.subι K)), Category.assoc, hh', 𝕀.endpoint_naturality_assoc,
      d.endpoint_false_comp_homotopy]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [← cancel_mono (L.map (E.subι K)), Category.assoc, Category.assoc, hu, hr', e₁]
  · rw [← cancel_mono (L.map (E.subι K)), Category.assoc, Category.assoc, hh',
      reassoc_of% hIu, d.map_comp_homotopy, ← reassoc_of% hIu, (𝕀.contraction).naturality]
    rfl

theorem exists_bounded_enlargement_of_embedding (hS : S ≤ MorphismProperty.monomorphisms C) :
    ∃ α₀ : Cardinal.{v}, Cardinal.aleph0 ≤ α₀ ∧ ∀ α : Cardinal.{v}, α₀ ≤ α →
      ∀ {X D : C} (i : X ⟶ D), 𝕀.trivialCofibrations S i →
        ∀ J : Subfunctor (E.ι.obj D), IsBounded (2 ^ α) J.toFunctor →
          ∃ K : Subfunctor (E.ι.obj D), J ≤ K ∧ IsBounded (2 ^ α) K.toFunctor ∧
            (𝕀.trivialCofibrations S)
              (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ K ≤ K)) := by
  obtain ⟨κR, _, _⟩ := 𝕀.exists_isCardinalAccessible_fibrantReplacement S
  obtain ⟨κι, _, _⟩ := Functor.IsAccessible.exists_cardinal (F := E.ι)
  let κ := κR ⊔ κι
  have : Fact κ.IsRegular := ⟨iteInduction (fun _ ↦ Fact.out) (fun _ ↦ Fact.out)⟩
  have := Functor.isCardinalAccessible_of_le (𝕀.fibrantReplacement S) (le_sup_left : κR ≤ κ)
  have := Functor.isCardinalAccessible_of_le E.ι (le_sup_right : κι ≤ κ)
  let F₁ := 𝕀.fibrantReplacement S ⋙ E.ι
  let F₂ := 𝕀.fibrantReplacement S ⋙ 𝕀.I ⋙ E.ι
  obtain ⟨γ, hγ, hG⟩ := E.exists_isBounded_two_pow_of_isCardinalAccessible F₂ κ
  obtain ⟨γ', -, hR⟩ := E.exists_isBounded_two_pow_of_isCardinalAccessible F₁ κ
  obtain ⟨α₀, hle, hα₀, hα₀α⟩ := exists_two_pow_bound B (max (max γ γ') κ)
  refine ⟨α₀, hα₀, fun α hα X D i hi J hJ => ?_⟩
  have hαβ : α ≤ 2 ^ α := (Cardinal.cantor α).le
  have hmax : max (max γ γ') κ ≤ α := hle.trans hα
  have hγα : γ ≤ α := (le_max_left _ _).trans ((le_max_left _ _).trans hmax)
  have hγ'α : γ' ≤ α := (le_max_right _ _).trans ((le_max_left _ _).trans hmax)
  have hκβ : κ ≤ 2 ^ α := ((le_max_right _ _).trans hmax).trans hαβ
  obtain ⟨hβ, hBo, hB⟩ := hα₀α α hα
  have : Mono i := hi.1
  obtain ⟨d⟩ := 𝕀.exists_deformation_retract_fibrantReplacement_map S hS i hi
  have hpres : ∀ Y : C, PreservesColimitsOfShape
      {T : Subfunctor (E.ι.obj Y) // IsBounded (2 ^ α) T.toFunctor} F₁ := fun Y => by
    have : Fact (Order.succ ((2 : Cardinal.{v}) ^ α)).IsRegular := ⟨Cardinal.isRegular_succ hβ⟩
    have := isCardinalFiltered_boundedSubfunctor hβ (E.ι.obj Y)
    have : IsCardinalFiltered {T : Subfunctor (E.ι.obj Y) // IsBounded (2 ^ α) T.toFunctor} κ :=
      IsCardinalFiltered.of_le _ (hκβ.trans (Order.le_succ _))
    exact F₁.preservesColimitsOfShape_of_isCardinalAccessible κ _
  have := hpres D
  have := hpres (E.sub (Subfunctor.range (E.ι.map i)))
  have := 𝕀.mono_fibrantReplacement_map S hS (E.subι (Subfunctor.range (E.ι.map i)))
  have : Mono (F₁.map (E.subι (Subfunctor.range (E.ι.map i)))) :=
    inferInstanceAs (Mono (E.ι.map ((𝕀.fibrantReplacement S).map _)))
  let P : Subfunctor (E.ι.obj D) → Subfunctor (E.ι.obj D) → Prop := fun K K' =>
    Subfunctor.range (F₂.map (E.subι K) ≫ E.ι.map d.homotopy) ≤
        Subfunctor.range (F₁.map (E.subι K')) ∧
      Subfunctor.range (F₁.map (E.subι (Subfunctor.range (E.ι.map i)))) ⊓
          Subfunctor.range (F₁.map (E.subι K)) ≤
        Subfunctor.range (F₁.map (E.subι (Subfunctor.range (E.ι.map i) ⊓ K')))
  have hP : ∀ ⦃K K' K'' : Subfunctor (E.ι.obj D)⦄, K' ≤ K'' → P K K' → P K K'' :=
    fun _ _ _ h hK =>
      ⟨hK.1.trans (E.range_map_subι_le_of_le F₁ h),
        hK.2.trans (E.range_map_subι_le_of_le F₁ (inf_le_inf_left _ h))⟩
  have hPc : ∀ Kc : κ.ord.ToType → Subfunctor (E.ι.obj D), Monotone Kc →
      (∀ γ, P (Kc γ) (⨆ γ, Kc γ)) → P (⨆ γ, Kc γ) (⨆ γ, Kc γ) := by
    intro Kc hKc hK
    have := isFiltered_of_isCardinalFiltered κ.ord.ToType κ
    have := F₁.preservesColimitsOfShape_of_isCardinalAccessible κ κ.ord.ToType
    have := F₂.preservesColimitsOfShape_of_isCardinalAccessible κ κ.ord.ToType
    refine ⟨E.range_map_subι_comp_le_of_isLUB F₂ hKc.functor isLUB_iSup _ _
      fun γ => (hK γ).1, ?_⟩
    have h₁ : Subfunctor.range (F₁.map (E.subι (⨆ γ, Kc γ)) ≫ 𝟙 _) ≤
        ⨆ γ, Subfunctor.range (F₁.map (E.subι (Kc γ))) :=
      E.range_map_subι_comp_le_of_isLUB F₁ hKc.functor isLUB_iSup _ _ fun γ => by
        rw [Category.comp_id]
        exact le_iSup (fun γ => Subfunctor.range (F₁.map (E.subι (Kc γ)))) γ
    rw [Category.comp_id] at h₁
    rintro b m ⟨hm₁, hm₂⟩
    have hm := h₁ b hm₂
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hm
    obtain ⟨γ, hγ⟩ := hm
    exact (hK γ).2 b ⟨hm₁, hγ⟩
  have hstep : ∀ K : Subfunctor (E.ι.obj D), IsBounded (2 ^ α) K.toFunctor →
      ∃ K' : Subfunctor (E.ι.obj D),
        IsBounded (2 ^ α) K'.toFunctor ∧ K ≤ K' ∧ P K K' := by
    intro K hK
    have hK' : E.IsBounded (2 ^ α) (E.sub K) := (E.isBounded_sub_iff _ K).2 hK
    have hR₁ : IsBounded (2 ^ α)
        (Subfunctor.range (F₂.map (E.subι K) ≫ E.ι.map d.homotopy)).toFunctor :=
      fun a => Cardinal.mk_range_le.trans (hG α hγα _ hK' a)
    obtain ⟨T, hT, hRT⟩ := E.exists_isBounded_le_range_map_subι F₁ hβ hB hBo _ hR₁
    obtain ⟨W, hWX, hW, hRW⟩ := E.exists_isBounded_le_inf_range_map_subι F₁ hβ hB hBo
      (Subfunctor.range (E.ι.map i)) _ (isBounded_range _ (hR α hγ'α _ hK'))
    exact ⟨K ⊔ T ⊔ W, isBounded_sup hβ (isBounded_sup hβ hK hT) hW,
      le_sup_left.trans le_sup_left,
      hRT.trans (E.range_map_subι_le_of_le F₁ (le_sup_right.trans le_sup_left)),
      hRW.trans (E.range_map_subι_le_of_le F₁ (le_inf hWX le_sup_right))⟩
  obtain ⟨K, hJK, hKb, hK₁, hK₂⟩ := exists_isBounded_le_of_step κ hβ hκβ P hP hPc hstep J hJ
  refine ⟨K, hJK, hKb, 𝕀.trivialCofibrations_homOfLe_inf_of_range_le E S hS i hi d
    K ?_ hK₂⟩
  rw [E.ι.map_comp]
  exact hK₁

section Presheaves

variable {A : Type v} [SmallCategory A] (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
  (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) [S.IsSmall.{v}]

theorem exists_bounded_enlargement
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    ∃ α₀ : Cardinal.{v}, Cardinal.aleph0 ≤ α₀ ∧ ∀ α : Cardinal.{v}, α₀ ≤ α →
      ∀ {C D : Aᵒᵖ ⥤ Type v} (i : C ⟶ D),
        𝕀.trivialCofibrations S i →
        ∀ J : Subfunctor D, IsBounded (2 ^ α) J.toFunctor →
          ∃ K : Subfunctor D, J ≤ K ∧ IsBounded (2 ^ α) K.toFunctor ∧
            (𝕀.trivialCofibrations S)
              (Subfunctor.homOfLe (inf_le_right : Subfunctor.range i ⊓ K ≤ K)) := by
  obtain ⟨α₀, hα₀, h⟩ := 𝕀.exists_bounded_enlargement_of_embedding (BoundedEmbedding.id A) S hS
  refine ⟨α₀, hα₀, @fun α hα C D i hi J hJ => ?_⟩
  obtain ⟨K, hJK, hK, hKi⟩ := h α hα i hi J hJ
  exact ⟨K, hJK, hK, (congrArg (fun f => 𝕀.trivialCofibrations S f)
    (BoundedEmbedding.id_homOfLe (Y := D) (inf_le_right : Subfunctor.range i ⊓ K ≤ K))).mp hKi⟩

end Presheaves

end HomotopicalAlgebra.ExactCylinder
