import Atoms.Homotopical.EilenbergZilber.RigidCellularModel
import Atoms.Homotopical.Cellular.Model
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Atoms.ForMathlib.CategoryTheory.Presentable.Presheaf
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Sites.Sieves

open CategoryTheory Limits MorphismProperty Opposite HomotopicalAlgebra

namespace Atoms.Homotopical.EZCategory

universe w v u

section SplitEpi

variable {A : Type v} [SmallCategory A] [EZCategory A]

theorem eq_of_isSplitEpi_of_sections {a b : A} (p q : a ⟶ b) [IsSplitEpi p] [IsSplitEpi q]
    (h : ∀ s : b ⟶ a, s ≫ p = 𝟙 b ↔ s ≫ q = 𝟙 b) : p = q := by
  obtain ⟨d, u, v, sq⟩ := exists_absolutePushout p q inferInstance inferInstance
  have huv : u = v := by
    have hs := (h (section_ p)).1 (IsSplitEpi.id p)
    rw [← Category.id_comp u, ← IsSplitEpi.id p, Category.assoc, sq.w, ← Category.assoc, hs,
      Category.id_comp]
  have : IsSplitEpi v := isSplitEpi_of_isAbsolutePushout sq inferInstance
  let Ω : Aᵒᵖ ⥤ Type v :=
    { obj c := Sieve c.unop
      map f := ↾fun τ ↦ τ.pullback f.unop
      map_id c := by
        ext τ d f
        simp
      map_comp f g := by
        ext τ d h
        simp }
  let τ : Sieve b :=
    { arrows c f := ¬IsSplitEpi f
      downward_closed {c c'} f hf g hg := hf (@isSplitEpi_of_comp _ _ _ _ _ g f hg) }
  have hτ : ∀ {c : A} (f : c ⟶ b), τ f ↔ ¬IsSplitEpi f := fun _ ↦ Iff.rfl
  have hsplit : ∀ {c : A} (f : c ⟶ a), IsSplitEpi (f ≫ p) ↔ IsSplitEpi (f ≫ q) := by
    have key : ∀ {c : A} (f : c ⟶ a) (p q : a ⟶ b),
        (∀ s : b ⟶ a, s ≫ p = 𝟙 b → s ≫ q = 𝟙 b) → IsSplitEpi (f ≫ p) → IsSplitEpi (f ≫ q) :=
      fun f p q h hf ↦ IsSplitEpi.mk' ⟨section_ (f ≫ p), by
        rw [← Category.assoc, h _ (by rw [Category.assoc, IsSplitEpi.id])]⟩
    intro c f
    exact ⟨key f p q fun s ↦ (h s).1, key f q p fun s ↦ (h s).2⟩
  have hpull : ∀ {c : A} (f : c ⟶ b), Ω.map f.op τ = τ.pullback f := fun _ ↦ rfl
  have hw : yoneda.map p ≫ (yonedaEquiv (F := Ω)).symm τ =
      yoneda.map q ≫ (yonedaEquiv (F := Ω)).symm τ := by
    rw [← Quiver.Hom.unop_op p, ← Quiver.Hom.unop_op q, ← yonedaEquiv_symm_map,
      ← yonedaEquiv_symm_map, hpull, hpull]
    congr 1
    ext c f
    rw [Sieve.pullback_apply, Sieve.pullback_apply, hτ, hτ]
    exact not_congr (hsplit f)
  have hfix : τ.pullback (v ≫ section_ v) = τ := by
    rw [← hpull]
    apply yonedaEquiv.symm.injective
    rw [yonedaEquiv_symm_map, ← sq.inr_desc _ _ hw, Quiver.Hom.unop_op,
      ← Category.assoc, ← Functor.map_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]
  have hid : IsSplitEpi (v ≫ section_ v) := by
    by_contra hn
    have := congrArg (fun σ : Sieve b ↦ σ (𝟙 b)) hfix
    simp only [Sieve.pullback_apply, Category.id_comp, hτ, eq_iff_iff] at this
    exact this.1 hn (IsSplitEpi.mk' ⟨𝟙 b, Category.id_comp _⟩)
  have he : v ≫ section_ v = 𝟙 b := by
    have e : (v ≫ section_ v) ≫ (v ≫ section_ v) = v ≫ section_ v := by
      rw [Category.assoc, ← Category.assoc (section_ v), IsSplitEpi.id, Category.id_comp]
    rw [← Category.id_comp (v ≫ section_ v), ← IsSplitEpi.id (v ≫ section_ v),
      Category.assoc, e]
  have : IsIso v := ⟨section_ v, he, IsSplitEpi.id v⟩
  rw [← cancel_mono v, ← huv, sq.w, huv]

end SplitEpi

section Sections

variable {A : Type v} [SmallCategory A] {X : Aᵒᵖ ⥤ Type (max w v)}

theorem boundary_comp_eq_iff {a : A} (x y : X.obj (op a)) :
    (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x =
        (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y ↔
      ∀ ⦃b : A⦄ (f : b ⟶ a), ¬IsSplitEpi f → X.map f.op x = X.map f.op y := by
  constructor
  · intro h b f hf
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op b)) ⟨⟨f⟩, hf⟩
  · intro h
    ext b ⟨⟨f⟩, hf⟩
    exact h f hf

theorem range_boundary_comp_le_iff {a : A} (x : X.obj (op a)) (T : Subfunctor X) :
    Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x) ≤ T ↔
      ∀ ⦃b : A⦄ (f : b ⟶ a), ¬IsSplitEpi f → X.map f.op x ∈ T.obj (op b) := by
  constructor
  · intro h b f hf
    exact h (op b) ⟨⟨⟨f⟩, hf⟩, rfl⟩
  · rintro h b _ ⟨⟨⟨f⟩, hf⟩, rfl⟩
    exact h f hf

theorem exists_of_not_isNondegenerate [EZCategory A] {a : A} {x : X.obj (op a)}
    (hx : ¬IsNondegenerate X x) :
    ∃ (b : A) (p : a ⟶ b) (y : X.obj (op b)),
      IsSplitEpi p ∧ ¬IsIso p ∧ IsNondegenerate X y ∧ X.map p.op y = x := by
  simp only [IsNondegenerate, not_forall] at hx
  obtain ⟨b, p, hp, ⟨z, hz⟩, hnp⟩ := hx
  obtain ⟨c, q, y, hq, hy, hyz⟩ := exists_isNondegenerate X b z
  refine ⟨c, p ≫ q, y, ?_, fun hi ↦ hnp ?_, hy, ?_⟩
  · have := hp
    have := hq
    infer_instance
  · have := hp
    have : Mono p := mono_of_mono p q
    exact isIso_of_mono_of_isSplitEpi p
  · rw [op_comp, Functor.map_comp_apply, hyz, hz]

theorem mem_of_not_isNondegenerate [EZCategory A] {a : A} {x : X.obj (op a)}
    (hx : ¬IsNondegenerate X x) {T : Subfunctor X}
    (hT : Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x) ≤ T) :
    x ∈ T.obj (op a) := by
  obtain ⟨b, p, y, hp, hnp, -, rfl⟩ := exists_of_not_isNondegenerate hx
  have hs : ¬IsSplitEpi (section_ p) := fun h ↦ hnp ⟨section_ p,
    (cancel_epi (section_ p)).1 (by rw [← Category.assoc, IsSplitEpi.id, Category.id_comp,
      Category.comp_id]), IsSplitEpi.id p⟩
  have h := (range_boundary_comp_le_iff _ T).1 hT (section_ p) hs
  rw [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h
  exact T.map p.op h

theorem exists_factorization_of_not_isSplitEpi [EZCategory A] {a b : A} (f : b ⟶ a)
    (hf : ¬IsSplitEpi f) :
    ∃ (c : A) (π : b ⟶ c) (i : c ⟶ a),
      IsSplitEpi π ∧ Mono i ∧ ¬IsIso i ∧ deg c < deg a ∧ π ≫ i = f := by
  obtain ⟨c, π, i, hπ, hi, rfl⟩ := exists_factorization f
  have hni : ¬IsIso i := fun h ↦ hf (by have := hπ; infer_instance)
  exact ⟨c, π, i, hπ, hi, hni, lt_of_le_of_ne (deg_le_of_mono i hi)
    fun he ↦ hni (isIso_of_mono_of_deg_eq i hi he), rfl⟩

theorem boundary_comp_eq_of_forall_mono [EZCategory A] {a : A} {x y : X.obj (op a)}
    (h : ∀ ⦃c : A⦄ (i : c ⟶ a), Mono i → ¬IsIso i → X.map i.op x = X.map i.op y) :
    (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x =
      (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y := by
  refine (boundary_comp_eq_iff x y).2 fun b f hf ↦ ?_
  obtain ⟨c, π, i, -, hi, hni, -, rfl⟩ := exists_factorization_of_not_isSplitEpi f hf
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h i hi hni]

private theorem mono_of_map_eq_of_isNondegenerate [EZCategory A] {b c : A} (m : b ⟶ c)
    {y : X.obj (op b)} {z : X.obj (op c)} (hy : IsNondegenerate X y) (h : X.map m.op z = y) :
    Mono m := by
  obtain ⟨d, π, i, hπ, hi, rfl⟩ := exists_factorization m
  have : IsIso π := hy π hπ ⟨X.map i.op z, by rw [← Functor.map_comp_apply, ← op_comp, h]⟩
  exact mono_comp π i

variable [EZCategory A] [HasTrivialAutomorphisms A]

theorem eq_of_not_isNondegenerate_of_boundary_eq {a : A} {x y : X.obj (op a)}
    (hx : ¬IsNondegenerate X x) (hy : ¬IsNondegenerate X y)
    (h : (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x =
      (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y) :
    x = y := by
  obtain ⟨b₀, p₀, y₀, hp₀, hnp₀, hy₀, rfl⟩ := exists_of_not_isNondegenerate hx
  obtain ⟨b₁, p₁, y₁, hp₁, hnp₁, hy₁, rfl⟩ := exists_of_not_isNondegenerate hy
  have hbd := (boundary_comp_eq_iff _ _).1 h
  have hsec : ∀ {b₀ b₁ : A} (p₀ : a ⟶ b₀) (p₁ : a ⟶ b₁) (y₀ : X.obj (op b₀))
      (y₁ : X.obj (op b₁)), ¬IsIso p₀ → IsNondegenerate X y₀ →
      (∀ ⦃b : A⦄ (f : b ⟶ a), ¬IsSplitEpi f →
        X.map f.op (X.map p₀.op y₀) = X.map f.op (X.map p₁.op y₁)) →
      ∀ s : b₀ ⟶ a, s ≫ p₀ = 𝟙 b₀ → X.map (s ≫ p₁).op y₁ = y₀ := by
    intro b₀ b₁ p₀ p₁ y₀ y₁ hnp₀ _ hbd s hs
    have hns : ¬IsSplitEpi s := fun h ↦ hnp₀ ⟨s, (cancel_epi s).1 (by
      rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]), hs⟩
    have := hbd s hns
    rw [← Functor.map_comp_apply, ← op_comp, hs, op_id, Functor.map_id_apply,
      ← Functor.map_comp_apply, ← op_comp] at this
    exact this.symm
  have h₀ := hsec p₀ p₁ y₀ y₁ hnp₀ hy₀ hbd
  have h₁ := hsec p₁ p₀ y₁ y₀ hnp₁ hy₁ fun b f hf ↦ (hbd f hf).symm
  have hdeg : deg b₀ = deg b₁ := le_antisymm
    (deg_le_of_mono _ (mono_of_map_eq_of_isNondegenerate _ hy₀ (h₀ _ (IsSplitEpi.id p₀))))
    (deg_le_of_mono _ (mono_of_map_eq_of_isNondegenerate _ hy₁ (h₁ _ (IsSplitEpi.id p₁))))
  have hiso : ∀ s : b₀ ⟶ a, s ≫ p₀ = 𝟙 b₀ → IsIso (s ≫ p₁) := fun s hs ↦
    isIso_of_mono_of_deg_eq _ (mono_of_map_eq_of_isNondegenerate _ hy₀ (h₀ s hs)) hdeg
  have hiso' : ∀ t : b₁ ⟶ a, t ≫ p₁ = 𝟙 b₁ → IsIso (t ≫ p₀) := fun t ht ↦
    isIso_of_mono_of_deg_eq _ (mono_of_map_eq_of_isNondegenerate _ hy₁ (h₁ t ht)) hdeg.symm
  have := hiso _ (IsSplitEpi.id p₀)
  let θ : b₀ ≅ b₁ := asIso (section_ p₀ ≫ p₁)
  have hθ : ∀ s : b₀ ⟶ a, s ≫ p₀ = 𝟙 b₀ → s ≫ p₁ = θ.hom := fun s hs ↦ by
    have := hiso s hs
    exact congrArg Iso.hom (Subsingleton.elim (asIso (s ≫ p₁)) θ)
  have hθ' : ∀ t : b₁ ⟶ a, t ≫ p₁ = 𝟙 b₁ → t ≫ p₀ = θ.inv := fun t ht ↦ by
    have := hiso' t ht
    exact congrArg Iso.hom (Subsingleton.elim (asIso (t ≫ p₀)) θ.symm)
  have hp : p₀ ≫ θ.hom = p₁ := by
    refine eq_of_isSplitEpi_of_sections _ _ fun t ↦ ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩
    · have ht' : (θ.hom ≫ t) ≫ p₀ = 𝟙 b₀ := by
        simp only [← cancel_mono θ.hom, Category.assoc, ht, Category.id_comp, Category.comp_id]
      rw [← cancel_epi θ.hom, ← Category.assoc, hθ _ ht', Category.comp_id]
    · rw [← Category.assoc, hθ' t ht, Iso.inv_hom_id]
  rw [← hp, op_comp, Functor.map_comp_apply, ← hθ _ (IsSplitEpi.id p₀), h₀ _ (IsSplitEpi.id p₀)]

end Sections

section Box

variable {C : Type*} [Category C] [HasBinaryCoproducts C] [HasPushouts C]

theorem ExactCylinder.exists_lift_endpointBox (𝕀 : ExactCylinder.{w} C)
    (S : MorphismProperty C) {X Y : C} {p : X ⟶ Y} (hp : 𝕀.naiveFibrations S p) (ε : Bool)
    {K L : C} (i : K ⟶ L) [Mono i] (a : 𝕀.I.obj K ⟶ X) (b : L ⟶ X) (c : 𝕀.I.obj L ⟶ Y)
    (hab : (𝕀.endpoint ε).app K ≫ a = i ≫ b) (ha : a ≫ p = 𝕀.I.map i ≫ c)
    (hb : b ≫ p = (𝕀.endpoint ε).app L ≫ c) :
    ∃ H : 𝕀.I.obj L ⟶ X, 𝕀.I.map i ≫ H = a ∧ (𝕀.endpoint ε).app L ≫ H = b ∧ H ≫ p = c := by
  have sq : CommSq (pushout.desc a b hab) (𝕀.endpointBox ε i) p c := ⟨pushout.hom_ext
    (by rw [pushout.inl_desc_assoc, ha]; exact (𝕀.inl_endpointBox_assoc _ i c).symm)
    (by rw [pushout.inr_desc_assoc, hb]; exact (𝕀.inr_endpointBox_assoc _ i c).symm)⟩
  obtain ⟨⟨⟨H, hl, hr⟩⟩⟩ :=
    (hp _ ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε i inferInstance)).sq_hasLift sq
  exact ⟨H, 𝕀.map_comp_eq_of_endpointBox_comp_eq ε i hl,
    𝕀.endpoint_comp_eq_of_endpointBox_comp_eq ε i hl, hr⟩

theorem ExactCylinder.exists_homotopy_of_eq_on_endpointBox [HasEffectiveUnions C]
    (𝕀 : ExactCylinder.{w} C) (S : MorphismProperty C) {X Y : C} {p : X ⟶ Y}
    (hp : 𝕀.naiveFibrations S p) (ε : Bool)
    {K L : C} (i : K ⟶ L) [Mono i] (h k : 𝕀.I.obj L ⟶ X)
    (hbd : 𝕀.I.map i ≫ h = 𝕀.I.map i ≫ k)
    (hend : (𝕀.endpoint (!ε)).app L ≫ h = (𝕀.endpoint (!ε)).app L ≫ k)
    (hpk : h ≫ p = k ≫ p) :
    ∃ H : 𝕀.I.obj L ⟶ X, (𝕀.endpoint false).app L ≫ H = (𝕀.endpoint ε).app L ≫ h ∧
      (𝕀.endpoint true).app L ≫ H = (𝕀.endpoint ε).app L ≫ k ∧
      𝕀.I.map i ≫ H = 𝕀.contraction.app K ≫ i ≫ (𝕀.endpoint ε).app L ≫ h ∧
      H ≫ p = 𝕀.contraction.app L ≫ ((𝕀.endpoint ε).app L ≫ h) ≫ p := by
  have hj : Mono (𝕀.endpointBox (!ε) i) := 𝕀.mono_endpointBox (!ε) i inferInstance
  have hJ : 𝕀.anodyne S (𝕀.bothBox (𝕀.endpointBox (!ε) i)) :=
    (𝕀.isAnodyneClass_anodyne S).bothBox_mem _ hj
      ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem (!ε) i inferInstance)
  have hjhk : 𝕀.endpointBox (!ε) i ≫ h = 𝕀.endpointBox (!ε) i ≫ k := by
    refine pushout.hom_ext ?_ ?_
    · exact (𝕀.inl_endpointBox_assoc _ i h).trans (hbd.trans (𝕀.inl_endpointBox_assoc _ i k).symm)
    · exact (𝕀.inr_endpointBox_assoc _ i h).trans
        (hend.trans (𝕀.inr_endpointBox_assoc _ i k).symm)
  have hc : 𝕀.endpoints (𝕀.endpointBoxSource (!ε) i) ≫
      𝕀.contraction.app (𝕀.endpointBoxSource (!ε) i) ≫ 𝕀.endpointBox (!ε) i ≫ h =
      coprod.map (𝕀.endpointBox (!ε) i) (𝕀.endpointBox (!ε) i) ≫ coprod.desc h k :=
    coprod.hom_ext
      (by rw [𝕀.inl_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc,
        coprod.inl_map_assoc, coprod.inl_desc])
      (by rw [𝕀.inr_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc,
        coprod.inr_map_assoc, coprod.inr_desc, hjhk])
  have sq : CommSq (pushout.desc _ _ hc) (𝕀.bothBox (𝕀.endpointBox (!ε) i)) p
      (𝕀.contraction.app (𝕀.I.obj L) ≫ h ≫ p) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_bothBox_assoc, 𝕀.map_contraction_app_assoc,
        Category.assoc, Category.assoc]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_bothBox_assoc]
      refine coprod.hom_ext ?_ ?_
      · rw [𝕀.inl_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc, coprod.inl_desc_assoc]
      · rw [𝕀.inr_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc, coprod.inr_desc_assoc,
          hpk]⟩
  obtain ⟨⟨⟨F, hFl, hFr⟩⟩⟩ := (hp _ hJ).sq_hasLift sq
  have hF₁ : 𝕀.I.map (𝕀.endpointBox (!ε) i) ≫ F =
      𝕀.contraction.app (𝕀.endpointBoxSource (!ε) i) ≫ 𝕀.endpointBox (!ε) i ≫ h :=
    𝕀.map_comp_eq_of_bothBox_comp_eq _ hFl
  have hF₂ : 𝕀.endpoints (𝕀.I.obj L) ≫ F = coprod.desc h k :=
    𝕀.endpoints_comp_eq_of_bothBox_comp_eq _ hFl
  have hFh : (𝕀.endpoint false).app (𝕀.I.obj L) ≫ F = h := by
    rw [← 𝕀.inl_endpoints, Category.assoc, hF₂, coprod.inl_desc]
  have hFk : (𝕀.endpoint true).app (𝕀.I.obj L) ≫ F = k := by
    rw [← 𝕀.inr_endpoints, Category.assoc, hF₂, coprod.inr_desc]
  have hF₃ : 𝕀.I.map (𝕀.I.map i) ≫ F = 𝕀.contraction.app (𝕀.I.obj K) ≫ 𝕀.I.map i ≫ h :=
    calc 𝕀.I.map (𝕀.I.map i) ≫ F
        = 𝕀.I.map ((pushout.inl _ _ : _ ⟶ 𝕀.endpointBoxSource (!ε) i) ≫
            𝕀.endpointBox (!ε) i) ≫ F := by rw [𝕀.inl_endpointBox]
      _ = 𝕀.I.map (pushout.inl _ _ : _ ⟶ 𝕀.endpointBoxSource (!ε) i) ≫
            𝕀.I.map (𝕀.endpointBox (!ε) i) ≫ F :=
        Functor.map_comp_assoc _ _ _ _
      _ = 𝕀.I.map (pushout.inl _ _ : _ ⟶ 𝕀.endpointBoxSource (!ε) i) ≫
          𝕀.contraction.app (𝕀.endpointBoxSource (!ε) i) ≫
          𝕀.endpointBox (!ε) i ≫ h :=
        congrArg (𝕀.I.map (pushout.inl _ _ : _ ⟶ 𝕀.endpointBoxSource (!ε) i) ≫ ·) hF₁
      _ = 𝕀.contraction.app (𝕀.I.obj K) ≫
          (pushout.inl _ _ : _ ⟶ 𝕀.endpointBoxSource (!ε) i) ≫ 𝕀.endpointBox (!ε) i ≫ h :=
        𝕀.map_contraction_app_assoc _ _
      _ = 𝕀.contraction.app (𝕀.I.obj K) ≫ 𝕀.I.map i ≫ h :=
        congrArg _ (𝕀.inl_endpointBox_assoc _ i h)
  refine ⟨𝕀.I.map ((𝕀.endpoint ε).app L) ≫ F, ?_, ?_, ?_, ?_⟩
  · rw [𝕀.endpoint_naturality_assoc, hFh]
  · rw [𝕀.endpoint_naturality_assoc, hFk]
  · rw [← Functor.map_comp_assoc, ← 𝕀.endpoint_naturality, Functor.map_comp_assoc, hF₃,
      𝕀.map_contraction_app_assoc, 𝕀.endpoint_naturality_assoc]
  · rw [Category.assoc, hFr, 𝕀.map_contraction_app_assoc, Category.assoc]

end Box

section Composition

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]

theorem ExactCylinder.exists_homotopy_trans [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) {X Y : C}
    {p : X ⟶ Y} (hp : 𝕀.naiveFibrations S p) {K L : C} (i : K ⟶ L) [Mono i]
    (H G : 𝕀.I.obj L ⟶ X) (hG₀ : (𝕀.endpoint false).app L ≫ G = (𝕀.endpoint true).app L ≫ H)
    (hGi : 𝕀.I.map i ≫ G = 𝕀.contraction.app K ≫ i ≫ (𝕀.endpoint false).app L ≫ G)
    (hH : H ≫ p = 𝕀.contraction.app L ≫ ((𝕀.endpoint false).app L ≫ H) ≫ p)
    (hGp : G ≫ p = 𝕀.contraction.app L ≫ ((𝕀.endpoint false).app L ≫ G) ≫ p) :
    ∃ F : 𝕀.I.obj L ⟶ X, (𝕀.endpoint false).app L ≫ F = (𝕀.endpoint false).app L ≫ H ∧
      (𝕀.endpoint true).app L ≫ F = (𝕀.endpoint true).app L ≫ G ∧
      𝕀.I.map i ≫ F = 𝕀.I.map i ≫ H ∧
      F ≫ p = 𝕀.contraction.app L ≫ ((𝕀.endpoint false).app L ≫ H) ≫ p := by
  set x := (𝕀.endpoint false).app L ≫ H
  set σ := 𝕀.contraction
  obtain ⟨ψ, hψl, hψr⟩ := 𝕀.exists_map_coprod_comp L
  have sq := (IsPushout.of_hasPushout (𝕀.endpoints K) (coprod.map i i)).map 𝕀.I
  have hw : 𝕀.I.map (𝕀.endpoints K) ≫ σ.app (𝕀.I.obj K) ≫ 𝕀.I.map i ≫ H =
      𝕀.I.map (coprod.map i i) ≫ ψ ≫ coprod.desc (σ.app L ≫ x) G := by
    refine 𝕀.cylinder_coprod_hom_ext ?_ ?_
    · rw [← Functor.map_comp_assoc, 𝕀.inl_endpoints, 𝕀.map_contraction_app_assoc,
        𝕀.endpoint_naturality_assoc, ← Functor.map_comp_assoc, coprod.inl_map,
        Functor.map_comp_assoc, reassoc_of% hψl, coprod.inl_desc, 𝕀.map_contraction_app_assoc]
    · rw [← Functor.map_comp_assoc, 𝕀.inr_endpoints, 𝕀.map_contraction_app_assoc,
        𝕀.endpoint_naturality_assoc, ← Functor.map_comp_assoc, coprod.inr_map,
        Functor.map_comp_assoc, reassoc_of% hψr, coprod.inr_desc, hGi, hG₀]
  set Φ := sq.desc _ _ hw
  have hΦl : 𝕀.I.map (pushout.inl _ _) ≫ Φ = σ.app (𝕀.I.obj K) ≫ 𝕀.I.map i ≫ H := sq.inl_desc ..
  have hΦr : 𝕀.I.map (pushout.inr _ _) ≫ Φ = ψ ≫ coprod.desc (σ.app L ≫ x) G := sq.inr_desc ..
  have := 𝕀.mono_bothBox i inferInstance
  have hab : (𝕀.endpoint false).app (𝕀.bothBoxSource i) ≫ Φ = 𝕀.bothBox i ≫ H := by
    refine pushout.hom_ext (f := 𝕀.endpoints K) (g := coprod.map i i) ?_ ?_
    · rw [← 𝕀.endpoint_naturality_assoc, hΦl, 𝕀.endpoint_app_contraction_app_assoc,
        𝕀.inl_bothBox_assoc]
    · rw [← 𝕀.endpoint_naturality_assoc, hΦr, 𝕀.inr_bothBox_assoc]
      refine coprod.hom_ext ?_ ?_
      · rw [← 𝕀.endpoint_naturality_assoc, reassoc_of% hψl, coprod.inl_desc,
          𝕀.endpoint_app_contraction_app_assoc, 𝕀.inl_endpoints_assoc]
      · rw [← 𝕀.endpoint_naturality_assoc, reassoc_of% hψr, coprod.inr_desc,
          𝕀.inr_endpoints_assoc, hG₀]
  have ha : Φ ≫ p = 𝕀.I.map (𝕀.bothBox i) ≫ σ.app (𝕀.I.obj L) ≫ σ.app L ≫ x ≫ p := by
    refine sq.hom_ext ?_ ?_
    · rw [reassoc_of% hΦl, ← Functor.map_comp_assoc, 𝕀.inl_bothBox, 𝕀.map_contraction_app_assoc,
        hH]
    · rw [reassoc_of% hΦr, ← Functor.map_comp_assoc, 𝕀.inr_bothBox]
      refine 𝕀.cylinder_coprod_hom_ext ?_ ?_
      · rw [reassoc_of% hψl, coprod.inl_desc_assoc, ← Functor.map_comp_assoc, 𝕀.inl_endpoints,
          𝕀.map_contraction_app_assoc, 𝕀.endpoint_app_contraction_app_assoc, Category.assoc]
      · rw [reassoc_of% hψr, coprod.inr_desc_assoc, ← Functor.map_comp_assoc, 𝕀.inr_endpoints,
          𝕀.map_contraction_app_assoc, 𝕀.endpoint_app_contraction_app_assoc, hGp, hG₀,
          Category.assoc, hH, 𝕀.endpoint_app_contraction_app_assoc]
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := ExactCylinder.exists_lift_endpointBox 𝕀 S hp false
    (𝕀.bothBox i) Φ H (σ.app (𝕀.I.obj L) ≫ σ.app L ≫ x ≫ p) hab ha
    (by rw [𝕀.endpoint_app_contraction_app_assoc]; exact hH)
  have hF₀ : 𝕀.I.map ((𝕀.endpoint false).app L) ≫ F = σ.app L ≫ x := by
    rw [← 𝕀.inl_endpoints, ← 𝕀.inr_bothBox i, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, hF₁, hΦr, reassoc_of% hψl, coprod.inl_desc]
  have hF₁' : 𝕀.I.map ((𝕀.endpoint true).app L) ≫ F = G := by
    rw [← 𝕀.inr_endpoints, ← 𝕀.inr_bothBox i, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, hF₁, hΦr, reassoc_of% hψr, coprod.inr_desc]
  have hFi : 𝕀.I.map (𝕀.I.map i) ≫ F = σ.app (𝕀.I.obj K) ≫ 𝕀.I.map i ≫ H := by
    conv_lhs => rw [← 𝕀.inl_bothBox i]
    rw [Functor.map_comp_assoc, hF₁, hΦl]
  refine ⟨(𝕀.endpoint true).app (𝕀.I.obj L) ≫ F, ?_, ?_, ?_, ?_⟩
  · rw [← 𝕀.endpoint_naturality_assoc, hF₀]
    exact 𝕀.endpoint_app_contraction_app_assoc true x
  · rw [← 𝕀.endpoint_naturality_assoc, hF₁']
    rfl
  · rw [← 𝕀.endpoint_naturality_assoc, hFi, 𝕀.endpoint_app_contraction_app_assoc]
  · rw [Category.assoc, hF₃, 𝕀.endpoint_app_contraction_app_assoc]

end Composition

section BoundaryEquivalence

variable {A : Type v} [SmallCategory A]
  (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
  (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
  {X Y : Aᵒᵖ ⥤ Type (max w v)}

def BoundaryEquivalent (p : X ⟶ Y) {a : A} (x y : X.obj (op a)) : Prop :=
  p.app _ x = p.app _ y ∧
  (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm x =
    (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y ∧
  ∃ h : 𝕀.I.obj (uliftYoneda.{w}.obj a) ⟶ X,
    (𝕀.endpoint false).app (uliftYoneda.{w}.obj a) ≫ h = uliftYonedaEquiv.symm x ∧
    (𝕀.endpoint true).app (uliftYoneda.{w}.obj a) ≫ h = uliftYonedaEquiv.symm y ∧
    𝕀.I.map (uliftBoundary.{w} a).ι ≫ h =
      𝕀.contraction.app (uliftBoundary.{w} a).toFunctor ≫ (uliftBoundary.{w} a).ι ≫
        uliftYonedaEquiv.symm x ∧
    h ≫ p = 𝕀.contraction.app (uliftYoneda.{w}.obj a) ≫ uliftYonedaEquiv.symm x ≫ p

structure IsMinimalFibration (p : X ⟶ Y) : Prop where
  naiveFibration : 𝕀.naiveFibrations S p
  eq_of_boundaryEquivalent : ∀ ⦃a : A⦄ ⦃x y : X.obj (op a)⦄,
    BoundaryEquivalent 𝕀 p x y → x = y

variable {𝕀} {p : X ⟶ Y}

theorem boundaryEquivalent_of_homotopy {a : A} {u v : uliftYoneda.{w}.obj a ⟶ X}
    (h : 𝕀.I.obj (uliftYoneda.{w}.obj a) ⟶ X)
    (h₀ : (𝕀.endpoint false).app (uliftYoneda.{w}.obj a) ≫ h = u)
    (h₁ : (𝕀.endpoint true).app (uliftYoneda.{w}.obj a) ≫ h = v)
    (hbd : 𝕀.I.map (uliftBoundary.{w} a).ι ≫ h =
      𝕀.contraction.app (uliftBoundary.{w} a).toFunctor ≫ (uliftBoundary.{w} a).ι ≫ u)
    (hover : h ≫ p = 𝕀.contraction.app (uliftYoneda.{w}.obj a) ≫ u ≫ p) :
    BoundaryEquivalent 𝕀 p (uliftYonedaEquiv u) (uliftYonedaEquiv v) := by
  simp only [BoundaryEquivalent, Equiv.symm_apply_apply]
  have hp : u ≫ p = v ≫ p := by
    rw [← h₁, Category.assoc, hover, 𝕀.endpoint_app_contraction_app_assoc]
  refine ⟨?_, ?_, h, h₀, h₁, hbd, hover⟩
  · rw [← uliftYonedaEquiv_comp, ← uliftYonedaEquiv_comp, hp]
  · rw [← h₁, ← 𝕀.endpoint_naturality_assoc, hbd, 𝕀.endpoint_app_contraction_app_assoc]

theorem BoundaryEquivalent.refl {a : A} (x : X.obj (op a)) : BoundaryEquivalent 𝕀 p x x := by
  have := boundaryEquivalent_of_homotopy (p := p) (u := uliftYonedaEquiv.symm x)
    (v := uliftYonedaEquiv.symm x)
    (𝕀.contraction.app (uliftYoneda.{w}.obj a) ≫ uliftYonedaEquiv.symm x)
    (𝕀.endpoint_app_contraction_app_assoc false _) (𝕀.endpoint_app_contraction_app_assoc true _)
    (𝕀.map_contraction_app_assoc _ _) (Category.assoc _ _ _)
  rwa [Equiv.apply_symm_apply] at this

theorem BoundaryEquivalent.map {X' Y' : Aᵒᵖ ⥤ Type (max w v)} {p' : X' ⟶ Y'} (u : X ⟶ X')
    (v' : Y ⟶ Y') (w : u ≫ p' = p ≫ v') {a : A} {x y : X.obj (op a)}
    (hxy : BoundaryEquivalent 𝕀 p x y) :
    BoundaryEquivalent 𝕀 p' (u.app _ x) (u.app _ y) := by
  obtain ⟨-, -, h, h₀, h₁, hbd, hover⟩ := hxy
  have := boundaryEquivalent_of_homotopy (p := p') (u := uliftYonedaEquiv.symm x ≫ u)
    (v := uliftYonedaEquiv.symm y ≫ u) (h ≫ u) (by rw [← Category.assoc, h₀])
    (by rw [← Category.assoc, h₁]) (by simp only [← Category.assoc, hbd])
    (by rw [Category.assoc, w, ← Category.assoc, hover]; simp only [Category.assoc, w])
  rwa [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at this

theorem boundaryEquivalent_of_eq_on_box (hp : 𝕀.naiveFibrations S p) (ε : Bool)
    {a : A} (h k : 𝕀.I.obj (uliftYoneda.{w}.obj a) ⟶ X)
    (hbd : 𝕀.I.map (uliftBoundary.{w} a).ι ≫ h = 𝕀.I.map (uliftBoundary.{w} a).ι ≫ k)
    (hend : (𝕀.endpoint (!ε)).app (uliftYoneda.{w}.obj a) ≫ h =
      (𝕀.endpoint (!ε)).app (uliftYoneda.{w}.obj a) ≫ k)
    (hpk : h ≫ p = k ≫ p) :
    BoundaryEquivalent 𝕀 p (uliftYonedaEquiv ((𝕀.endpoint ε).app (uliftYoneda.{w}.obj a) ≫ h))
      (uliftYonedaEquiv ((𝕀.endpoint ε).app (uliftYoneda.{w}.obj a) ≫ k)) := by
  obtain ⟨H, H₀, H₁, Hbd, Hover⟩ :=
    ExactCylinder.exists_homotopy_of_eq_on_endpointBox 𝕀 S hp ε _ h k hbd hend hpk
  exact boundaryEquivalent_of_homotopy H H₀ H₁ Hbd Hover

variable (𝕀) in
theorem BoundaryEquivalent.of_boundaryEquivalent (hp : 𝕀.naiveFibrations S p) {a : A}
    {x y z : X.obj (op a)} (hxy : BoundaryEquivalent 𝕀 p x y)
    (hxz : BoundaryEquivalent 𝕀 p x z) : BoundaryEquivalent 𝕀 p y z := by
  obtain ⟨-, -, h, h₀, h₁, hbd, hover⟩ := hxy
  obtain ⟨-, -, k, k₀, k₁, kbd, kover⟩ := hxz
  have := boundaryEquivalent_of_eq_on_box S hp true h k (hbd.trans kbd.symm) (h₀.trans k₀.symm)
    (hover.trans kover.symm)
  rwa [h₁, k₁, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

theorem boundaryEquivalent_equivalence (hp : 𝕀.naiveFibrations S p) (a : A) :
    Equivalence (BoundaryEquivalent 𝕀 p (a := a)) := by
  have symm : ∀ {x y : X.obj (op a)}, BoundaryEquivalent 𝕀 p x y →
      BoundaryEquivalent 𝕀 p y x := fun hxy ↦
    BoundaryEquivalent.of_boundaryEquivalent 𝕀 S hp hxy (BoundaryEquivalent.refl _)
  exact ⟨BoundaryEquivalent.refl, symm, fun hxy hyz ↦
    BoundaryEquivalent.of_boundaryEquivalent 𝕀 S hp (symm hxy) hyz⟩

end BoundaryEquivalence

section Minimal

variable {A : Type v} [SmallCategory A]
  {𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v))}
  {S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
  {X Y : Aᵒᵖ ⥤ Type (max w v)}

theorem IsMinimalFibration.of_isPullback {X' Y' : Aᵒᵖ ⥤ Type (max w v)} {p : X ⟶ Y}
    {p' : X' ⟶ Y'} {u : X ⟶ X'} {v' : Y ⟶ Y'} (sq : IsPullback u p p' v')
    (hp' : IsMinimalFibration 𝕀 S p') : IsMinimalFibration 𝕀 S p where
  naiveFibration := MorphismProperty.of_isPullback sq hp'.naiveFibration
  eq_of_boundaryEquivalent a x y hxy := by
    have hu := hp'.eq_of_boundaryEquivalent (hxy.map u v' sq.w)
    apply uliftYonedaEquiv.symm.injective
    refine sq.hom_ext ?_ ?_
    · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, hu]
    · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, hxy.1]

theorem isIso_of_homotopic_id [EZCategory A] {p : X ⟶ Y} (hp : IsMinimalFibration 𝕀 S p)
    (f : X ⟶ X) (h : 𝕀.I.obj X ⟶ X) (h₀ : (𝕀.endpoint false).app X ≫ h = 𝟙 X)
    (h₁ : (𝕀.endpoint true).app X ≫ h = f) (hover : h ≫ p = 𝕀.contraction.app X ≫ p) :
    IsIso f := by
  have hfp : f ≫ p = p := by
    rw [← h₁, Category.assoc, hover, 𝕀.endpoint_app_contraction_app_assoc]
  have hg₀ : ∀ {Z} (g : Z ⟶ X), (𝕀.endpoint false).app Z ≫ 𝕀.I.map g ≫ h = g := fun g ↦ by
    rw [𝕀.endpoint_naturality_assoc, h₀, Category.comp_id]
  have hg₁ : ∀ {Z} (g : Z ⟶ X), (𝕀.endpoint true).app Z ≫ 𝕀.I.map g ≫ h = g ≫ f := fun g ↦ by
    rw [𝕀.endpoint_naturality_assoc, h₁]
  have hgp : ∀ {Z} (g : Z ⟶ X), 𝕀.I.map g ≫ h ≫ p = 𝕀.contraction.app Z ≫ g ≫ p := fun g ↦ by
    rw [hover, 𝕀.map_contraction_app_assoc]
  have hdeg : ∀ {a c : A} (i : c ⟶ a), Mono i → ¬IsIso i → deg c < deg a := fun i hi hni ↦
    lt_of_le_of_ne (deg_le_of_mono i hi) fun he ↦ hni (isIso_of_mono_of_deg_eq i hi he)
  have hinj : ∀ n : ℕ, ∀ {a : A}, deg a = n → ∀ x y : X.obj (op a),
      f.app _ x = f.app _ y → x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha x y hxy
    have hbd := boundary_comp_eq_of_forall_mono (x := x) (y := y) fun c i hi hni ↦
      ih _ (ha ▸ hdeg i hi hni) rfl _ _ (by
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy])
    have hxyp : uliftYonedaEquiv.symm x ≫ p = uliftYonedaEquiv.symm y ≫ p := by
      rw [← hfp, ← Category.assoc, ← Category.assoc, uliftYonedaEquiv_symm_comp x f,
        uliftYonedaEquiv_symm_comp y f, hxy]
    have := boundaryEquivalent_of_eq_on_box S hp.naiveFibration false
      (𝕀.I.map (uliftYonedaEquiv.symm x) ≫ h) (𝕀.I.map (uliftYonedaEquiv.symm y) ≫ h)
      (by rw [← Functor.map_comp_assoc, hbd, Functor.map_comp_assoc])
      (by rw [Bool.not_false, hg₁, hg₁, uliftYonedaEquiv_symm_comp x f,
        uliftYonedaEquiv_symm_comp y f, hxy])
      (by rw [Category.assoc, Category.assoc, hgp, hgp, hxyp])
    rw [hg₀, hg₀, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact hp.eq_of_boundaryEquivalent this
  have : Mono f := (NatTrans.mono_iff_mono_app f).2 fun a ↦
    (mono_iff_injective _).2 fun x y hxy ↦ hinj _ rfl x y hxy
  have hsurj : ∀ n : ℕ, ∀ {a : A}, deg a = n → ∀ y : X.obj (op a), ∃ x, f.app _ x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha y
    have hle : Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y) ≤
        Subfunctor.range f := by
      refine (range_boundary_comp_le_iff y _).2 fun b g hg ↦ ?_
      obtain ⟨c, π, i, -, hi, hni, -, rfl⟩ := exists_factorization_of_not_isSplitEpi g hg
      obtain ⟨z, hz⟩ := ih _ (ha ▸ hdeg i hi hni) rfl (X.map i.op y)
      exact ⟨X.map π.op z, by rw [NatTrans.naturality_apply, hz, op_comp, Functor.map_comp_apply]⟩
    let z := Subfunctor.lift _ hle ≫ inv (Subfunctor.toRange f)
    have hz : z ≫ f = (uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y := by
      simp only [z, Category.assoc, Subfunctor.inv_toRange_comp, Subfunctor.lift_ι]
    obtain ⟨k, hk₁, hk₂, hk₃⟩ := ExactCylinder.exists_lift_endpointBox 𝕀 S hp.naiveFibration true
      (uliftBoundary.{w} a).ι (𝕀.I.map z ≫ h) (uliftYonedaEquiv.symm y)
      (𝕀.contraction.app (uliftYoneda.{w}.obj a) ≫ uliftYonedaEquiv.symm y ≫ p)
      (by rw [hg₁, hz])
      (by rw [Category.assoc, hgp, 𝕀.map_contraction_app_assoc,
        ← (congrArg (z ≫ ·) hfp).symm.trans ((reassoc_of% hz) p)])
      (𝕀.endpoint_app_contraction_app_assoc true _).symm
    have hzk :
        (uliftBoundary.{w} a).ι ≫ (𝕀.endpoint false).app (uliftYoneda.{w}.obj a) ≫ k = z := by
      rw [← 𝕀.endpoint_naturality_assoc, hk₁, hg₀]
    have := boundaryEquivalent_of_eq_on_box S hp.naiveFibration true k
      (𝕀.I.map ((𝕀.endpoint false).app (uliftYoneda.{w}.obj a) ≫ k) ≫ h)
      (by rw [hk₁, ← Functor.map_comp_assoc, hzk])
      (hg₀ _).symm
      (by rw [hk₃, Category.assoc, hgp, Category.assoc, hk₃,
        𝕀.endpoint_app_contraction_app_assoc])
    rw [hk₂, hg₁, uliftYonedaEquiv_comp, Equiv.apply_symm_apply] at this
    exact ⟨_, (hp.eq_of_boundaryEquivalent this).symm⟩
  have : ∀ a, IsIso (f.app a) := fun a ↦ (isIso_iff_bijective _).2
    ⟨fun x y hxy ↦ hinj _ rfl x y hxy, fun y ↦ hsurj _ rfl y⟩
  exact NatIso.isIso_of_isIso_app f

end Minimal

section MinimalModel

variable {A : Type v} [SmallCategory A]
  {𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v))}
  {S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
  {X Y : Aᵒᵖ ⥤ Type (max w v)}

theorem BoundaryEquivalent.map_mono {p : X ⟶ Y} {a b : A} (m : a ⟶ b) [Mono m]
    {x y : X.obj (op b)} (hxy : BoundaryEquivalent 𝕀 p x y) :
    BoundaryEquivalent 𝕀 p (X.map m.op x) (X.map m.op y) := by
  obtain ⟨-, -, h, h₀, h₁, hbd, hover⟩ := hxy
  have hle : Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYoneda.map m) ≤
      uliftBoundary.{w} b := by
    rintro U _ ⟨⟨⟨f⟩, hf⟩, rfl⟩
    refine fun hfm ↦ hf ?_
    have : IsSplitEpi (f ≫ m) := hfm
    have : IsSplitEpi m := ⟨⟨section_ (f ≫ m) ≫ f, by rw [Category.assoc, IsSplitEpi.id]⟩⟩
    have := isIso_of_mono_of_isSplitEpi m
    have h2 : IsSplitEpi ((f ≫ m) ≫ inv m) := inferInstance
    simpa using h2
  have hm : Subfunctor.lift _ hle ≫ (uliftBoundary.{w} b).ι =
      (uliftBoundary.{w} a).ι ≫ uliftYoneda.map m := Subfunctor.lift_ι _ _
  have := boundaryEquivalent_of_homotopy (p := p) (𝕀.I.map (uliftYoneda.map m) ≫ h)
    (by rw [𝕀.endpoint_naturality_assoc, h₀]) (by rw [𝕀.endpoint_naturality_assoc, h₁])
    (by rw [← Functor.map_comp_assoc, ← hm, Functor.map_comp_assoc, hbd,
      𝕀.map_contraction_app_assoc, reassoc_of% hm])
    (by rw [Category.assoc, hover, 𝕀.map_contraction_app_assoc, Category.assoc])
  have ex := uliftYonedaEquiv_symm_map (F := X) m.op x
  have ey := uliftYonedaEquiv_symm_map (F := X) m.op y
  rw [Quiver.Hom.unop_op] at ex ey
  rwa [← ex, ← ey, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

variable (𝕀) in
def IsThin (p : X ⟶ Y) (M : Subfunctor X) : Prop :=
  ∀ ⦃a : A⦄ ⦃x y : X.obj (op a)⦄, x ∈ M.obj (op a) → y ∈ M.obj (op a) →
    BoundaryEquivalent 𝕀 p x y → x = y

variable [EZCategory A] [HasTrivialAutomorphisms A]

theorem exists_boundaryEquivalent_of_maximal {p : X ⟶ Y} (hp : 𝕀.naiveFibrations S p)
    {M : Subfunctor X} (hM : Maximal (IsThin 𝕀 p) M) {a : A} (y₀ : X.obj (op a))
    (hy₀ : Subfunctor.range ((uliftBoundary.{w} a).ι ≫ uliftYonedaEquiv.symm y₀) ≤ M) :
    ∃ y ∈ M.obj (op a), BoundaryEquivalent 𝕀 p y₀ y := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hsymm : ∀ {b : A} {u v : X.obj (op b)}, BoundaryEquivalent 𝕀 p u v →
      BoundaryEquivalent 𝕀 p v u := fun h ↦ (boundaryEquivalent_equivalence S hp _).symm h
  have hy₀M : y₀ ∉ M.obj (op a) := fun h ↦ hne _ h (BoundaryEquivalent.refl _)
  have hres : ∀ {b : A} (g : b ⟶ a) (t : a ⟶ b), t ≫ g = 𝟙 a → ∀ z : X.obj (op b),
      BoundaryEquivalent 𝕀 p (X.map g.op y₀) z → BoundaryEquivalent 𝕀 p y₀ (X.map t.op z) := by
    intro b g t ht z hz
    have : IsSplitMono t := IsSplitMono.mk' ⟨g, ht⟩
    have := hz.map_mono t
    rwa [← Functor.map_comp_apply, ← op_comp, ht, op_id, Functor.map_id_apply] at this
  have hmem : ∀ {b : A} {z : X.obj (op b)},
      z ∈ (M ⊔ Subfunctor.range (uliftYonedaEquiv.symm y₀)).obj (op b) →
        z ∈ M.obj (op b) ∨ ∃ g : b ⟶ a, IsSplitEpi g ∧ X.map g.op y₀ = z := by
    rintro b z (hz | ⟨⟨g⟩, rfl⟩)
    · exact Or.inl hz
    · by_cases hg : IsSplitEpi g
      · exact Or.inr ⟨g, hg, rfl⟩
      · exact Or.inl ((range_boundary_comp_le_iff y₀ M).1 hy₀ g hg)
  have hsec : ∀ {b : A} (g g' : b ⟶ a),
      BoundaryEquivalent 𝕀 p (X.map g.op y₀) (X.map g'.op y₀) →
        ∀ t : a ⟶ b, t ≫ g = 𝟙 a → t ≫ g' = 𝟙 a := by
    intro b g g' h t ht
    have h' := hres g t ht _ h
    rw [← Functor.map_comp_apply, ← op_comp] at h'
    have hnd : IsNondegenerate X (X.map (t ≫ g').op y₀) := by
      by_contra hd
      exact hne _ (mem_of_not_isNondegenerate hd (by rw [← h'.2.1]; exact hy₀)) h'
    have := mono_of_map_eq_of_isNondegenerate (t ≫ g') hnd rfl
    have := isIso_of_mono_of_deg_eq (t ≫ g') this rfl
    exact congrArg Iso.hom (Subsingleton.elim (asIso (t ≫ g')) (Iso.refl a))
  have hthin : IsThin 𝕀 p (M ⊔ Subfunctor.range (uliftYonedaEquiv.symm y₀)) := by
    have hnew : ∀ {b : A} (g : b ⟶ a), IsSplitEpi g → ∀ z ∈ M.obj (op b),
        ¬BoundaryEquivalent 𝕀 p (X.map g.op y₀) z := fun g hg z hz h ↦ by
      have := hg
      exact hne _ (M.map _ hz) (hres g (section_ g) (IsSplitEpi.id g) z h)
    intro b z z' hz hz' h
    rcases hmem hz with hz | ⟨g, hg, rfl⟩ <;> rcases hmem hz' with hz' | ⟨g', hg', rfl⟩
    · exact hM.1 hz hz' h
    · exact absurd (hsymm h) (hnew g' hg' z hz)
    · exact absurd h (hnew g hg z' hz')
    · have := hg
      have := hg'
      rw [eq_of_isSplitEpi_of_sections g g' fun t ↦ ⟨hsec g g' h t, hsec g' g (hsymm h) t⟩]
  exact hy₀M (hM.2 hthin le_sup_left _
    (Or.inr ⟨⟨𝟙 a⟩, Equiv.apply_symm_apply uliftYonedaEquiv y₀⟩))

theorem exists_minimalFibration_deformationRetract {p : X ⟶ Y}
    (hp : 𝕀.naiveFibrations S p) :
    ∃ (M : Subfunctor X) (r : X ⟶ M.toFunctor) (h : 𝕀.I.obj X ⟶ X),
      M.ι ≫ r = 𝟙 _ ∧
      (𝕀.endpoint false).app X ≫ h = 𝟙 X ∧
      (𝕀.endpoint true).app X ≫ h = r ≫ M.ι ∧
      𝕀.I.map M.ι ≫ h = 𝕀.contraction.app M.toFunctor ≫ M.ι ∧
      h ≫ p = 𝕀.contraction.app X ≫ p ∧
      IsMinimalFibration 𝕀 S (M.ι ≫ p) := by
  obtain ⟨M, hM⟩ := zorn_le₀ {M : Subfunctor X | IsThin 𝕀 p M} fun c hcs hc ↦
    ⟨sSup c, fun a x y hx hy hxy ↦ by
      rw [Subfunctor.sSup_obj] at hx hy
      obtain ⟨_, ⟨T, hT, rfl⟩, hxT⟩ := hx
      obtain ⟨_, ⟨T', hT', rfl⟩, hyT'⟩ := hy
      rcases hc.total hT hT' with h | h
      · exact hcs hT' (h _ hxT) hyT' hxy
      · exact hcs hT hxT (h _ hyT') hxy, fun _ ↦ le_sSup⟩
  have : PreservesColimitsOfSize.{v, max w v} 𝕀.I := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftAdjoint_of_preservesColimits 𝕀.I
  let adj := Adjunction.ofIsLeftAdjoint 𝕀.I
  set σ := 𝕀.contraction
  set Γ := 𝕀.I.rightAdjoint
  let ev : Bool → (Γ.obj X ⟶ X) := fun ε ↦ (𝕀.endpoint ε).app _ ≫ adj.counit.app X
  have hev : ∀ {K} (f : K ⟶ Γ.obj X) ε,
      f ≫ ev ε = (𝕀.endpoint ε).app K ≫ (adj.homEquiv K X).symm f := fun f ε ↦ by
    simp only [ev, Adjunction.homEquiv_counit, 𝕀.endpoint_naturality_assoc]
  let α := Γ.map p
  let β : Γ.obj X ⟶ Γ.obj Y := ev false ≫ p ≫ adj.homEquiv Y Y (σ.app Y : 𝕀.I.obj Y ⟶ Y)
  have hαβ : ∀ {K} (f : K ⟶ Γ.obj X), f ≫ α = f ≫ β ↔ (adj.homEquiv K X).symm f ≫ p =
      σ.app K ≫ ((𝕀.endpoint false).app K ≫ (adj.homEquiv K X).symm f) ≫ p := fun f ↦ by
    have e₁ : (adj.homEquiv _ Y).symm (f ≫ α) = (adj.homEquiv _ X).symm f ≫ p :=
      adj.homEquiv_naturality_right_symm _ _
    have e₂ : (adj.homEquiv _ Y).symm (f ≫ β) =
        σ.app _ ≫ ((𝕀.endpoint false).app _ ≫ (adj.homEquiv _ X).symm f) ≫ p := by
      rw [← hev, ← Category.assoc, ← Category.assoc, Category.assoc f,
        adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, 𝕀.map_contraction_app]
    rw [← (adj.homEquiv _ _).symm.injective.eq_iff, e₁, e₂]
  let E : Subfunctor (Γ.obj X) :=
    { obj := fun U ↦ {φ | α.app U φ = β.app U φ ∧ (ev true).app U φ ∈ M.obj U}
      map := fun f φ hφ ↦ ⟨by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hφ.1],
        by rw [NatTrans.naturality_apply]; exact M.map f hφ.2⟩ }
  have hE : ∀ {K} (f : K ⟶ Γ.obj X), f ≫ α = f ≫ β → Subfunctor.range (f ≫ ev true) ≤ M →
      Subfunctor.range f ≤ E := by
    rintro K f h₁ h₂ U _ ⟨z, rfl⟩
    exact ⟨ConcreteCategory.congr_hom (NatTrans.congr_app h₁ U) z, h₂ U ⟨z, rfl⟩⟩
  have hE' : ∀ {K} (f : K ⟶ E.toFunctor), (f ≫ E.ι) ≫ α = (f ≫ E.ι) ≫ β ∧
      Subfunctor.range ((f ≫ E.ι) ≫ ev true) ≤ M := fun f ↦
    ⟨by ext U z; exact (f.app U z).2.1, by rintro U _ ⟨z, rfl⟩; exact (f.app U z).2.2⟩
  have hlift : ∀ a : A, HasLiftingProperty (uliftBoundary.{w} a).ι (E.ι ≫ ev false) :=
    fun a ↦ ⟨fun {u x} sq ↦ by
    obtain ⟨hgα, hgM⟩ := hE' u
    have hg₀ : (𝕀.endpoint false).app _ ≫ (adj.homEquiv _ X).symm (u ≫ E.ι) =
        (uliftBoundary.{w} a).ι ≫ x := by
      rw [← hev, Category.assoc]
      exact sq.w
    obtain ⟨H, H₁, H₂, H₃⟩ := ExactCylinder.exists_lift_endpointBox 𝕀 S hp false
      (uliftBoundary.{w} a).ι _ x (σ.app _ ≫ x ≫ p) hg₀
      (by rw [(hαβ _).1 hgα, hg₀, 𝕀.map_contraction_app_assoc, Category.assoc])
      (𝕀.endpoint_app_contraction_app_assoc false _).symm
    obtain ⟨y, hyM, -, -, K, K₀, K₁, Kbd, Kover⟩ := exists_boundaryEquivalent_of_maximal hp hM
      (uliftYonedaEquiv ((𝕀.endpoint true).app (uliftYoneda.{w}.obj a) ≫ H)) (by
        rw [Equiv.symm_apply_apply, ← 𝕀.endpoint_naturality_assoc, H₁, ← hev]
        exact hgM)
    rw [Equiv.symm_apply_apply] at K₀ Kbd Kover
    obtain ⟨F, F₀, F₁, F₂, F₃⟩ := ExactCylinder.exists_homotopy_trans 𝕀 S hp
      (uliftBoundary.{w} a).ι H K K₀ (by rw [Kbd, K₀]) (by rw [H₃, H₂]) (by rw [Kover, K₀])
    have hF := (adj.homEquiv _ X).symm_apply_apply F
    have hℓE : Subfunctor.range (adj.homEquiv _ X F) ≤ E := hE _
      ((hαβ _).2 (by rw [hF, F₃, F₀])) (by
        rw [hev, hF, F₁, K₁]
        rintro U _ ⟨z, rfl⟩
        exact M.map _ hyM)
    refine ⟨⟨⟨Subfunctor.lift _ hℓE, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono E.ι, Category.assoc, Subfunctor.lift_ι]
      apply (adj.homEquiv _ _).symm.injective
      rw [adj.homEquiv_naturality_left_symm, hF, F₂, H₁]
    · rw [← Category.assoc, Subfunctor.lift_ι, hev, hF, F₀, H₂]⟩
  have hMlift : HasLiftingProperty M.ι (E.ι ≫ ev false) := by
    refine saturation_le _ (MorphismProperty.ofHoms fun _ : Unit ↦ E.ι ≫ ev false).llp ?_ _
      (saturation_boundaryInclusions_ι M) _ (MorphismProperty.ofHoms.mk ())
    rintro _ _ _ ⟨a⟩ _ _ _ ⟨⟩
    exact hlift a
  have hτt := (adj.homEquiv _ X).symm_apply_apply (σ.app M.toFunctor ≫ M.ι)
  have hev₀ : ∀ ε, adj.homEquiv _ X (σ.app M.toFunctor ≫ M.ι) ≫ ev ε = M.ι := fun ε ↦ by
    rw [hev, hτt, 𝕀.endpoint_app_contraction_app_assoc]
  have htE : Subfunctor.range (adj.homEquiv _ X (σ.app M.toFunctor ≫ M.ι)) ≤ E := hE _
    ((hαβ _).2 (by rw [hτt, 𝕀.endpoint_app_contraction_app_assoc, Category.assoc]))
    (by rw [hev₀]; rintro U _ ⟨z, rfl⟩; exact z.2)
  obtain ⟨⟨⟨s, hs₁, hs₂⟩⟩⟩ := hMlift.sq_hasLift
    (⟨by rw [← Category.assoc, Subfunctor.lift_ι, hev₀, Category.comp_id]⟩ :
      CommSq (Subfunctor.lift _ htE) M.ι (E.ι ≫ ev false) (𝟙 X))
  obtain ⟨hsα, hsM⟩ := hE' s
  have hr : Subfunctor.lift _ hsM ≫ M.ι = (𝕀.endpoint true).app X ≫
      (adj.homEquiv _ X).symm (s ≫ E.ι) := by rw [Subfunctor.lift_ι, hev]
  have hh : (adj.homEquiv _ X).symm (s ≫ E.ι) ≫ p = σ.app X ≫ p := by
    rw [(hαβ _).1 hsα, ← hev, Category.assoc s, hs₂]
    exact congrArg (σ.app X ≫ ·) (Category.id_comp p)
  have hhM : 𝕀.I.map M.ι ≫ (adj.homEquiv _ X).symm (s ≫ E.ι) = σ.app M.toFunctor ≫ M.ι := by
    rw [← adj.homEquiv_naturality_left_symm, ← Category.assoc, hs₁, Subfunctor.lift_ι, hτt]
  have hMr : M.ι ≫ Subfunctor.lift _ hsM = 𝟙 _ := by
    rw [← cancel_mono M.ι, Category.assoc, hr, Category.id_comp, ← 𝕀.endpoint_naturality_assoc,
      hhM, 𝕀.endpoint_app_contraction_app_assoc]
  refine ⟨M, Subfunctor.lift _ hsM, (adj.homEquiv _ X).symm (s ≫ E.ι), hMr,
    by rw [← hev, Category.assoc, hs₂], hr.symm, hhM, hh, ?_, ?_⟩
  · refine MorphismProperty.of_retract (P := 𝕀.naiveFibrations S)
      ⟨Arrow.homMk M.ι (𝟙 Y) (by simp), Arrow.homMk (Subfunctor.lift _ hsM) (𝟙 Y) ?_, ?_⟩ hp
    · simp only [Arrow.mk_hom]
      rw [← Category.assoc, hr, Category.assoc, hh, 𝕀.endpoint_app_contraction_app_assoc]
      exact (Category.comp_id p).symm
    · refine Arrow.hom_ext _ _ ?_ (by simp)
      simp only [Arrow.comp_left, Arrow.homMk_left, Arrow.id_left]
      exact hMr
  · intro a x y hxy
    exact Subtype.ext (hM.1 x.2 y.2 (hxy.map M.ι (𝟙 Y) (Category.comp_id _).symm))

theorem exists_minimalFibration_anodyne [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms _) {p : X ⟶ Y} (hp : 𝕀.naiveFibrations S p) :
    ∃ M : Subfunctor X, 𝕀.anodyne S M.ι ∧ IsMinimalFibration 𝕀 S (M.ι ≫ p) := by
  obtain ⟨M, r, h, h₁, h₂, h₃, h₄, -, hM⟩ := exists_minimalFibration_deformationRetract hp
  exact ⟨M, 𝕀.anodyne_of_deformation_retract S hS M.ι
    ⟨r, h, h₁, h₂, h₃, by rw [h₄, 𝕀.map_contraction_app]⟩, hM⟩

omit [HasTrivialAutomorphisms A] in
theorem isIso_of_homotopyEquivalence_over {X' Y' : Aᵒᵖ ⥤ Type (max w v)} {p : X ⟶ Y}
    {p' : X' ⟶ Y'} (hp : IsMinimalFibration 𝕀 S p) (hp' : IsMinimalFibration 𝕀 S p')
    (f : X ⟶ X') (g : X' ⟶ X) (h : 𝕀.I.obj X ⟶ X) (h₀ : (𝕀.endpoint false).app X ≫ h = 𝟙 X)
    (h₁ : (𝕀.endpoint true).app X ≫ h = f ≫ g) (hover : h ≫ p = 𝕀.contraction.app X ≫ p)
    (k : 𝕀.I.obj X' ⟶ X') (k₀ : (𝕀.endpoint false).app X' ≫ k = 𝟙 X')
    (k₁ : (𝕀.endpoint true).app X' ≫ k = g ≫ f) (kover : k ≫ p' = 𝕀.contraction.app X' ≫ p') :
    IsIso f := by
  have := isIso_of_homotopic_id hp _ h h₀ h₁ hover
  have := isIso_of_homotopic_id hp' _ k k₀ k₁ kover
  have : Mono f := mono_of_mono f g
  have : IsSplitEpi f := ⟨⟨inv (g ≫ f) ≫ g, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩
  exact isIso_of_mono_of_isSplitEpi f

end MinimalModel

end Atoms.Homotopical.EZCategory
