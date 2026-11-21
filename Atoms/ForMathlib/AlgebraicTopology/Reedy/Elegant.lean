import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.AlgebraicTopology.Reedy.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Pushouts

open CategoryTheory Limits Opposite

universe w w' v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

theorem exists_map_eq_of_isPushout_yoneda {c d₁ d₂ e : C} {σ₁ : c ⟶ d₁} {σ₂ : c ⟶ d₂}
    {τ₁ : d₁ ⟶ e} {τ₂ : d₂ ⟶ e}
    (sq : IsPushout (yoneda.map σ₁) (yoneda.map σ₂) (yoneda.map τ₁) (yoneda.map τ₂))
    (X : Cᵒᵖ ⥤ Type w) {y₁ : X.obj (op d₁)} {y₂ : X.obj (op d₂)}
    (h : X.map σ₁.op y₁ = X.map σ₂.op y₂) :
    ∃ z : X.obj (op e), X.map τ₁.op z = y₁ ∧ X.map τ₂.op z = y₂ := by
  let X' : Cᵒᵖ ⥤ Type (max w v) := X ⋙ uliftFunctor.{v}
  have sq' : IsPushout (uliftYoneda.{w}.map σ₁) (uliftYoneda.{w}.map σ₂)
      (uliftYoneda.{w}.map τ₁) (uliftYoneda.{w}.map τ₂) :=
    IsPushout.map ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{w}) sq
  have hw : uliftYoneda.map σ₁ ≫ (uliftYonedaEquiv (F := X')).symm ⟨y₁⟩ =
      uliftYoneda.map σ₂ ≫ (uliftYonedaEquiv (F := X')).symm ⟨y₂⟩ := by
    have e₁ := uliftYonedaEquiv_symm_map (F := X') σ₁.op ⟨y₁⟩
    have e₂ := uliftYonedaEquiv_symm_map (F := X') σ₂.op ⟨y₂⟩
    rw [Quiver.Hom.unop_op] at e₁ e₂
    rw [← e₁, ← e₂]
    exact congrArg _ (congrArg ULift.up h)
  refine ⟨(uliftYonedaEquiv (sq'.desc _ _ hw)).down, ?_, ?_⟩
  · have := uliftYonedaEquiv_naturality (sq'.desc _ _ hw) τ₁.op
    rw [Quiver.Hom.unop_op, IsPushout.inl_desc] at this
    exact congrArg ULift.down (this.trans (Equiv.apply_symm_apply _ _))
  · have := uliftYonedaEquiv_naturality (sq'.desc _ _ hw) τ₂.op
    rw [Quiver.Hom.unop_op, IsPushout.inr_desc] at this
    exact congrArg ULift.down (this.trans (Equiv.apply_symm_apply _ _))

namespace MorphismProperty

variable (W : MorphismProperty C)

def IsDegenerate (X : Cᵒᵖ ⥤ Type w) {c : C} (x : X.obj (Opposite.op c)) : Prop :=
  ∃ (d : C) (σ : c ⟶ d) (_ : W σ) (_ : ¬ identities C σ) (y : X.obj (Opposite.op d)),
    X.map σ.op y = x

def IsElegant : Prop :=
  ∀ (X : Cᵒᵖ ⥤ Type w) (c : C), Function.Bijective
    (fun p : Σ d : C, {σ : c ⟶ d // W σ} ×
        {y : X.obj (Opposite.op d) // ¬ W.IsDegenerate X y} =>
      X.map p.2.1.1.op p.2.2.1)

def HasStrongPushouts : Prop :=
  ∀ ⦃c d₁ d₂ : C⦄ (σ₁ : c ⟶ d₁) (σ₂ : c ⟶ d₂), W σ₁ → W σ₂ →
    ∃ (e : C) (τ₁ : d₁ ⟶ e) (τ₂ : d₂ ⟶ e), W τ₁ ∧ W τ₂ ∧
      IsPushout (yoneda.map σ₁) (yoneda.map σ₂) (yoneda.map τ₁) (yoneda.map τ₂)

structure IsEZReedy : Prop where
  isSplitEpi ⦃c d : C⦄ (σ : c ⟶ d) : W σ → IsSplitEpi σ
  eq_of_sections ⦃c d : C⦄ (σ σ' : c ⟶ d) : W σ → W σ' →
    (∀ δ : d ⟶ c, δ ≫ σ = 𝟙 d ↔ δ ≫ σ' = 𝟙 d) → σ = σ'

variable {W}

theorem identities_of_not_isDegenerate {X : Cᵒᵖ ⥤ Type w} {c d : C} {σ : c ⟶ d} (hσ : W σ)
    {x : X.obj (Opposite.op c)} (hx : ¬ W.IsDegenerate X x) {y : X.obj (Opposite.op d)}
    (h : X.map σ.op y = x) :
    identities C σ :=
  by_contra fun hσ' ↦ hx ⟨d, σ, hσ, hσ', y, h⟩

theorem IsDegenerate.app {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) {c : C} {x : X.obj (Opposite.op c)}
    (hx : W.IsDegenerate X x) : W.IsDegenerate Y (f.app _ x) := by
  obtain ⟨d, σ, hσ, hσ', y, rfl⟩ := hx
  exact ⟨d, σ, hσ, hσ', f.app _ y, (NatTrans.naturality_apply f σ.op y).symm⟩

theorem isDegenerate_comp_uliftFunctor_iff {X : Cᵒᵖ ⥤ Type w} {c : C}
    (x : X.obj (Opposite.op c)) :
    W.IsDegenerate (X ⋙ uliftFunctor.{w'}) (ULift.up x) ↔ W.IsDegenerate X x :=
  ⟨fun ⟨d, σ, hσ, hσ', y, h⟩ ↦ ⟨d, σ, hσ, hσ', y.down, congrArg ULift.down h⟩,
    fun ⟨d, σ, hσ, hσ', y, h⟩ ↦ ⟨d, σ, hσ, hσ', ULift.up y, congrArg ULift.up h⟩⟩

theorem isElegant_of_isElegant_max (h : W.IsElegant.{max w w'}) : W.IsElegant.{w} := by
  intro X c
  have hX := h (X ⋙ uliftFunctor.{w'}) c
  refine ⟨?_, fun x ↦ ?_⟩
  · rintro ⟨d₁, σ₁, ⟨y₁, hy₁⟩⟩ ⟨d₂, σ₂, ⟨y₂, hy₂⟩⟩ hxy
    have := @hX.1
      ⟨d₁, σ₁, ⟨ULift.up y₁, (isDegenerate_comp_uliftFunctor_iff y₁).not.2 hy₁⟩⟩
      ⟨d₂, σ₂, ⟨ULift.up y₂, (isDegenerate_comp_uliftFunctor_iff y₂).not.2 hy₂⟩⟩
      (congrArg ULift.up hxy)
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 this
    simp only [heq_eq_eq, Prod.mk.injEq] at hh
    obtain ⟨rfl, hy⟩ := hh
    obtain rfl : y₁ = y₂ := congrArg ULift.down (congrArg Subtype.val hy)
    rfl
  · obtain ⟨⟨d, σ, ⟨y, hy⟩⟩, hxy⟩ := hX.2 (ULift.up x)
    exact ⟨⟨d, σ, ⟨y.down, (isDegenerate_comp_uliftFunctor_iff y.down).not.1 hy⟩⟩,
      congrArg ULift.down hxy⟩

end MorphismProperty

end CategoryTheory

namespace HomotopicalAlgebra.ReedyStructure

open MorphismProperty

variable {C : Type u} [Category.{v} C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

include r in
theorem eq_id_of_prop₂ {c : C} {f : c ⟶ c} (hf : W₂ f) : f = 𝟙 c := by
  obtain ⟨⟩ := r.identities_of_prop₂_of_eq hf rfl
  rfl

include r in
theorem prop₂_of_not_isDegenerate {X : Cᵒᵖ ⥤ Type w} {d₁ d₂ : C} {g : d₁ ⟶ d₂}
    {y : X.obj (op d₂)} (hy : ¬ W₁.IsDegenerate X (X.map g.op y)) : W₂ g := by
  obtain ⟨e, ρ, μ, hρ, hμ, rfl, -⟩ := r.exists_fac g
  rw [op_comp, Functor.map_comp_apply] at hy
  obtain ⟨⟩ := identities_of_not_isDegenerate hρ hy rfl
  simpa using hμ

include r in
theorem exists_not_isDegenerate (X : Cᵒᵖ ⥤ Type w) {c : C} (x : X.obj (Opposite.op c)) :
    ∃ (d : C) (σ : c ⟶ d) (_ : W₁ σ) (y : X.obj (Opposite.op d)),
      ¬ W₁.IsDegenerate X y ∧ X.map σ.op y = x := by
  induction hc : r.deg c using WellFoundedLT.induction generalizing c with
  | ind n ih =>
    by_cases hx : W₁.IsDegenerate X x
    · obtain ⟨d, σ, hσ, hσ', y, rfl⟩ := hx
      obtain ⟨e, τ, hτ, z, hz, rfl⟩ := ih _ (hc ▸ r.lt₁ σ hσ hσ') y rfl
      exact ⟨e, σ ≫ τ, W₁.comp_mem _ _ hσ hτ, z, hz, by simp⟩
    · exact ⟨c, 𝟙 c, W₁.id_mem c, x, hx, by simp⟩

include r in
private theorem surjective_restrict (X : Cᵒᵖ ⥤ Type w) (c : C) : Function.Surjective
    (fun p : Σ d : C, {σ : c ⟶ d // W₁ σ} ×
        {y : X.obj (Opposite.op d) // ¬ W₁.IsDegenerate X y} =>
      X.map p.2.1.1.op p.2.2.1) := fun x ↦ by
  obtain ⟨d, σ, hσ, y, hy, rfl⟩ := r.exists_not_isDegenerate X x
  exact ⟨⟨d, ⟨σ, hσ⟩, ⟨y, hy⟩⟩, rfl⟩

include r in
theorem isIdempotentComplete : IsIdempotentComplete C := by
  refine ⟨fun c ε hε ↦ ?_⟩
  obtain ⟨d, ρ, σ, hρ, hσ, rfl, -⟩ := r.exists_fac ε
  obtain ⟨d', ρ', σ', hρ', hσ', hfac, -⟩ := r.exists_fac (σ ≫ ρ)
  obtain rfl : d = d' := r.unique_obj (.mk d ρ σ rfl hρ hσ)
    (.mk d' (ρ ≫ ρ') (σ' ≫ σ) (by simpa [reassoc_of% hfac] using hε)
      (W₁.comp_mem _ _ hρ hρ') (W₂.comp_mem _ _ hσ' hσ))
  obtain ⟨⟩ := r.identities_of_prop₁_of_eq hρ' rfl
  obtain rfl := r.eq_id_of_prop₂ hσ'
  exact ⟨d, σ, ρ, by simpa using hfac.symm, rfl⟩

include r in
theorem isSplitEpi_of_hasStrongPushouts (h : W₁.HasStrongPushouts) {c d : C} (σ : c ⟶ d)
    (hσ : W₁ σ) : IsSplitEpi σ := by
  obtain ⟨e, τ₁, τ₂, hτ₁, -, sq⟩ := h σ σ hσ hσ
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : e ⟶ d, τ₁ ≫ γ = 𝟙 d ∧ τ₂ ≫ γ = 𝟙 d :=
    ⟨yoneda.preimage (sq.desc (𝟙 _) (𝟙 _) rfl), yoneda.map_injective (by simp),
      yoneda.map_injective (by simp)⟩
  have hde : r.deg d = r.deg e :=
    le_antisymm (by simpa [hγ₁] using r.degHom_le τ₁ γ) (r.le₁ τ₁ hτ₁)
  obtain ⟨⟩ := r.identities_of_prop₁_of_eq hτ₁ hde
  obtain rfl : γ = 𝟙 _ := by simpa using hγ₁
  obtain rfl : τ₂ = 𝟙 _ := by simpa using hγ₂
  refine isSplitEpi_of_epi_yoneda_map σ ⟨fun a b hab ↦ ?_⟩
  simpa using (sq.inl_desc a b hab).symm.trans (sq.inr_desc a b hab)

include r in
theorem isElegant_of_hasStrongPushouts (h : W₁.HasStrongPushouts) : W₁.IsElegant.{w} := by
  refine fun X c ↦ ⟨?_, r.surjective_restrict X c⟩
  rintro ⟨d₁, ⟨σ₁, hσ₁⟩, ⟨y₁, hy₁⟩⟩ ⟨d₂, ⟨σ₂, hσ₂⟩, ⟨y₂, hy₂⟩⟩
    (hxy : X.map σ₁.op y₁ = X.map σ₂.op y₂)
  obtain ⟨e, τ₁, τ₂, hτ₁, hτ₂, sq⟩ := h σ₁ σ₂ hσ₁ hσ₂
  have hσ : σ₁ ≫ τ₁ = σ₂ ≫ τ₂ := yoneda.map_injective (by simpa using sq.w)
  obtain ⟨z, hz₁, hz₂⟩ := exists_map_eq_of_isPushout_yoneda sq X hxy
  obtain ⟨⟩ := identities_of_not_isDegenerate hτ₁ hy₁ hz₁
  obtain ⟨⟩ := identities_of_not_isDegenerate hτ₂ hy₂ hz₂
  simp only [op_id, Functor.map_id_apply, Category.comp_id] at hz₁ hz₂ hσ
  subst hz₁ hz₂ hσ
  rfl

include r in
theorem hasStrongPushouts_of_isElegant (h : W₁.IsElegant.{v}) : W₁.HasStrongPushouts := by
  intro c d₁ d₂ σ₁ σ₂ hσ₁ hσ₂
  let P := pushout (yoneda.map σ₁) (yoneda.map σ₂)
  have sq : IsPushout (yoneda.map σ₁) (yoneda.map σ₂) (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  obtain ⟨⟨e₁, ⟨τ₁, hτ₁⟩, ⟨z₁, hz₁⟩⟩, h₁⟩ :=
    (h P d₁).2 (yonedaEquiv (pushout.inl (yoneda.map σ₁) (yoneda.map σ₂)))
  obtain ⟨⟨e₂, ⟨τ₂, hτ₂⟩, ⟨z₂, hz₂⟩⟩, h₂⟩ :=
    (h P d₂).2 (yonedaEquiv (pushout.inr (yoneda.map σ₁) (yoneda.map σ₂)))
  dsimp only at h₁ h₂
  have key := (h P c).1 (a₁ := ⟨e₁, ⟨σ₁ ≫ τ₁, W₁.comp_mem _ _ hσ₁ hτ₁⟩, ⟨z₁, hz₁⟩⟩)
    (a₂ := ⟨e₂, ⟨σ₂ ≫ τ₂, W₁.comp_mem _ _ hσ₂ hτ₂⟩, ⟨z₂, hz₂⟩⟩) (by
      dsimp only
      rw [op_comp, Functor.map_comp_apply, h₁, op_comp, Functor.map_comp_apply, h₂,
        yonedaEquiv_naturality, yonedaEquiv_naturality, pushout.condition])
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 key
  simp only [heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq] at hh
  obtain ⟨hσ, rfl⟩ := hh
  let f : P ⟶ yoneda.obj e₁ := sq.desc (yoneda.map τ₁) (yoneda.map τ₂) (by
    rw [← Functor.map_comp, ← Functor.map_comp, hσ])
  have hτ : ∀ {d : C} (τ : d ⟶ e₁) (g : yoneda.obj d ⟶ P), P.map τ.op z₁ = yonedaEquiv g →
      yoneda.map τ ≫ yonedaEquiv.symm z₁ = g := fun τ g hg ↦ by
    rw [yonedaEquiv_symm_naturality_left, hg, Equiv.symm_apply_apply]
  have hfz : f ≫ yonedaEquiv.symm z₁ = 𝟙 P := sq.hom_ext
    (by rw [sq.inl_desc_assoc, Category.comp_id, hτ τ₁ _ h₁])
    (by rw [sq.inr_desc_assoc, Category.comp_id, hτ τ₂ _ h₂])
  let ε : e₁ ⟶ e₁ := yoneda.preimage (yonedaEquiv.symm z₁ ≫ f)
  have hε : P.map ε.op z₁ = z₁ := by
    have := yonedaEquiv_naturality (yonedaEquiv.symm z₁) ε
    rw [Equiv.apply_symm_apply] at this
    rw [this, Functor.map_preimage, Category.assoc, hfz, Category.comp_id,
      Equiv.apply_symm_apply]
  have hzf : yonedaEquiv.symm z₁ ≫ f = 𝟙 _ := by
    have hε₂ : yoneda.preimage (yonedaEquiv.symm z₁ ≫ f) = 𝟙 e₁ :=
      r.eq_id_of_prop₂ (r.prop₂_of_not_isDegenerate (g := ε) (y := z₁) (by rwa [hε]))
    rw [← yoneda.map_preimage (yonedaEquiv.symm z₁ ≫ f), hε₂, CategoryTheory.Functor.map_id]
  refine ⟨e₁, τ₁, τ₂, hτ₁, hτ₂, sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ⟨f, yonedaEquiv.symm z₁, hfz, hzf⟩ (by simp) (by simp) (by simp [f]) (by simp [f])⟩

include r in
theorem isElegant_iff_hasStrongPushouts : W₁.IsElegant.{v} ↔ W₁.HasStrongPushouts :=
  ⟨r.hasStrongPushouts_of_isElegant, r.isElegant_of_hasStrongPushouts⟩

include r in
theorem isElegant_iff_isElegant : W₁.IsElegant.{max w v} ↔ W₁.IsElegant.{v} :=
  ⟨isElegant_of_isElegant_max.{v, w},
    fun h ↦ r.isElegant_of_hasStrongPushouts (r.hasStrongPushouts_of_isElegant h)⟩

include r in
theorem isDegenerate_app_iff_of_mono (h : W₁.HasStrongPushouts) {X Y : Cᵒᵖ ⥤ Type w}
    (f : X ⟶ Y) [Mono f] {c : C} (x : X.obj (Opposite.op c)) :
    W₁.IsDegenerate Y (f.app _ x) ↔ W₁.IsDegenerate X x := by
  refine ⟨fun ⟨d, σ, hσ, hσ', y, hy⟩ ↦ ?_, IsDegenerate.app f⟩
  have := r.isSplitEpi_of_hasStrongPushouts h σ hσ
  refine ⟨d, σ, hσ, hσ', X.map (section_ σ).op x, ?_⟩
  have hf : Function.Injective (f.app (Opposite.op c)) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance _)
  refine hf ?_
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ← hy, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]

include r in
theorem isElegant_of_isEZReedy (h : W₁.IsEZReedy) : W₁.IsElegant.{w} := by
  refine fun X c ↦ ⟨?_, r.surjective_restrict X c⟩
  rintro ⟨d₁, ⟨σ₁, hσ₁⟩, ⟨y₁, hy₁⟩⟩ ⟨d₂, ⟨σ₂, hσ₂⟩, ⟨y₂, hy₂⟩⟩
    (hxy : X.map σ₁.op y₁ = X.map σ₂.op y₂)
  have key : ∀ {d d' : C} (σ : c ⟶ d) (σ' : c ⟶ d') (y : X.obj (op d)) (y' : X.obj (op d')),
      ¬ W₁.IsDegenerate X y → X.map σ.op y = X.map σ'.op y' → ∀ δ : d ⟶ c, δ ≫ σ = 𝟙 d →
        W₂ (δ ≫ σ') ∧ X.map (δ ≫ σ').op y' = y := by
    intro d d' σ σ' y y' hy hσy δ hδ
    have hy' : X.map (δ ≫ σ').op y' = y := by
      rw [op_comp, Functor.map_comp_apply, ← hσy, ← Functor.map_comp_apply, ← op_comp, hδ,
        op_id, Functor.map_id_apply]
    exact ⟨r.prop₂_of_not_isDegenerate (hy' ▸ hy), hy'⟩
  have := h.isSplitEpi σ₁ hσ₁
  have := h.isSplitEpi σ₂ hσ₂
  have hd : r.deg d₁ = r.deg d₂ := le_antisymm
    (r.le₂ _ (key σ₁ σ₂ y₁ y₂ hy₁ hxy _ (IsSplitEpi.id σ₁)).1)
    (r.le₂ _ (key σ₂ σ₁ y₂ y₁ hy₂ hxy.symm _ (IsSplitEpi.id σ₂)).1)
  obtain ⟨hg, hgy⟩ := key σ₁ σ₂ y₁ y₂ hy₁ hxy _ (IsSplitEpi.id σ₁)
  generalize section_ σ₁ ≫ σ₂ = g at hg hgy
  obtain ⟨⟩ := r.identities_of_prop₂_of_eq hg hd
  simp only [op_id, Functor.map_id_apply] at hgy
  subst hgy
  obtain rfl := h.eq_of_sections σ₁ σ₂ hσ₁ hσ₂ fun δ ↦
    ⟨fun hδ ↦ r.eq_id_of_prop₂ (key σ₁ σ₂ y₂ y₂ hy₁ hxy δ hδ).1,
      fun hδ ↦ r.eq_id_of_prop₂ (key σ₂ σ₁ y₂ y₂ hy₂ hxy.symm δ hδ).1⟩
  rfl

end HomotopicalAlgebra.ReedyStructure
