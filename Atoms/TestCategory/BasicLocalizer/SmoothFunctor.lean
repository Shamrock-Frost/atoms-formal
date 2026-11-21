import Atoms.TestCategory.Presheaf.ElementsSlice

open CategoryTheory Limits Opposite Atoms.Homotopical

namespace Atoms.TestCategory

universe u v₁ v₂ u₁ u₂ w

namespace BasicLocalizer

def SmoothFor (𝒲 : BasicLocalizer.{u}) {B' B : Cat.{u, u}} (v : B' ⟶ B) : Prop :=
  ∀ {D C C' D' : Cat.{u, u}} (q : C ⟶ B) (t : D ⟶ C)
    (q' : C' ⟶ B') (v' : C' ⟶ C) (t' : D' ⟶ C') (w : D' ⟶ D),
    IsPullback v' q' q v → IsPullback w t' t v' →
    𝒲.AsphericalFunctor t → 𝒲.AsphericalFunctor t'

end BasicLocalizer

section DiscreteFibration

variable {C C' B' B : Cat.{u, u}} {v' : C' ⟶ C} {q' : C' ⟶ B'} {q : C ⟶ B} {v : B' ⟶ B}

namespace BasicLocalizer

theorem asphericalFunctor_of_isPullback_of_isDiscreteFibration (𝒲 : BasicLocalizer.{u})
    {D D' : Cat.{u, u}} {w : D' ⟶ D} {t' : D' ⟶ C'} {t : D ⟶ C} (h : IsPullback w t' t v')
    (hv : Functor.IsDiscreteFibration v'.toFunctor) (ht : 𝒲.AsphericalFunctor t) :
    𝒲.AsphericalFunctor t' := fun c' =>
  have := Cat.isEquivalence_commaSquareFunctor_of_isDiscreteFibration h hv c'
  (𝒲.aspherical_iff_of_equivalence (Cat.commaSquareFunctor w t' t v' h.w c').asEquivalence).2
    (ht _)

theorem smoothFor_of_isDiscreteFibration (𝒲 : BasicLocalizer.{u}) (v : B' ⟶ B)
    (hv : Functor.IsDiscreteFibration v.toFunctor) : 𝒲.SmoothFor v := by
  intro D C C' D' q t q' v' t' w h₁ h₂ ht
  exact 𝒲.asphericalFunctor_of_isPullback_of_isDiscreteFibration h₂
    (Cat.isDiscreteFibration_of_isPullback h₁ hv) ht

theorem smoothFor_costructuredArrow_map {A : Type u} [SmallCategory A]
    (𝒲 : BasicLocalizer.{u}) {X Y : Aᵒᵖ ⥤ Type u} (p : X ⟶ Y) :
    𝒲.SmoothFor (CostructuredArrow.map (S := (yoneda : A ⥤ Aᵒᵖ ⥤ Type u)) p).toCatHom :=
  𝒲.smoothFor_of_isDiscreteFibration _ (isDiscreteFibration_costructuredArrow_map yoneda p)

theorem smoothFor_elements_map {A : Type u} [SmallCategory A]
    (𝒲 : BasicLocalizer.{u}) {X Y : Aᵒᵖ ⥤ Type u} (p : X ⟶ Y) :
    𝒲.SmoothFor ((elementsFunctor A).map p) :=
  𝒲.smoothFor_of_isDiscreteFibration _ (isDiscreteFibration_elements_map p)

end BasicLocalizer

end DiscreteFibration

section CommaComparison

variable {A' A B' B : Cat.{u, u}}

namespace BasicLocalizer

theorem asphericalFunctor_idSection (𝒲 : BasicLocalizer.{u}) (u : A ⟶ B) :
    𝒲.AsphericalFunctor (Comma.idSection u.toFunctor).toCatHom :=
  𝒲.asphericalFunctor_of_adjunction (v := (Comma.fst u.toFunctor (𝟭 B)).toCatHom)
    (Cat.idSectionAdjunction u)

theorem W_commaSquareFunctor_of_smooth {A' A B' B : Cat.{u, u}}
    (𝒲 : BasicLocalizer.{u}) (w : A' ⟶ A) (u' : A' ⟶ B')
    (u : A ⟶ B) (v : B' ⟶ B) (h : IsPullback w u' u v)
    (hv : 𝒲.SmoothFor v) (b : B') :
    𝒲.W (Cat.commaSquareFunctor w u' u v h.w b).toCatHom := by
  refine 𝒲.W_of_asphericalFunctor (fun x => ?_)
  have ht' := hv (Comma.snd u.toFunctor (𝟭 B)).toCatHom (Comma.idSection u.toFunctor).toCatHom
    (Comma.snd u.toFunctor v.toFunctor).toCatHom
    (Comma.mapRightToId u.toFunctor v.toFunctor).toCatHom
    (Comma.ofSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
      (congrArg Cat.Hom.toFunctor h.w)).toCatHom w (Cat.isPullback_mapRightToId u v)
    (Cat.isPullback_ofSquare h) (𝒲.asphericalFunctor_idSection u)
  exact 𝒲.aspherical_of_equivalence (Cat.commaSquareSliceEquivalence w u' u v h.w b x)
    (ht' ⟨x.left, b, x.hom⟩)

theorem commaLocallyConstant_baseChange {A' A B' B : Cat.{u, u}}
    (𝒲 : BasicLocalizer.{u}) (w : A' ⟶ A) (u' : A' ⟶ B')
    (u : A ⟶ B) (v : B' ⟶ B) (h : IsPullback w u' u v)
    (hv : 𝒲.SmoothFor v) (hu : 𝒲.CommaLocallyConstant u.toFunctor) :
    𝒲.CommaLocallyConstant u'.toFunctor := by
  intro b c f
  have hk := 𝒲.W_commaSquareFunctor_of_smooth w u' u v h hv
  have e : (CostructuredArrow.map (S := u'.toFunctor) f).toCatHom ≫
      (Cat.commaSquareFunctor w u' u v h.w c).toCatHom =
      (Cat.commaSquareFunctor w u' u v h.w b).toCatHom ≫
        (CostructuredArrow.map (S := u.toFunctor) (v.toFunctor.map f)).toCatHom :=
    congrArg Functor.toCatHom (Cat.commaSquareFunctor_comp_map w u' u v h.w f)
  have h₂ := 𝒲.W.comp_mem _ _ (hk b) (hu (v.toFunctor.map f))
  rw [← e] at h₂
  exact (𝒲.W.postcomp_iff _ _ (hk c)).1 h₂

end BasicLocalizer

end CommaComparison

section PullbackPreservation

theorem elements_isPullback {A : Type u} [SmallCategory A]
    {P X Y Z : Aᵒᵖ ⥤ Type u} (f : P ⟶ X) (g : P ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (h : IsPullback f g p q) :
    IsPullback ((elementsFunctor A).map f) ((elementsFunctor A).map g)
      ((elementsFunctor A).map p) ((elementsFunctor A).map q) := by
  have hA : ∀ a, IsPullback (f.app a) (g.app a) (p.app a) (q.app a) :=
    fun a => h.map ((evaluation Aᵒᵖ (Type u)).obj a)
  refine Cat.isPullback_of_elementwise
    (by rw [← Functor.map_comp, h.w, Functor.map_comp]) ?_ ?_ ?_ ?_
  · intro e₁ e₂ h₁ h₂
    change op ((CategoryOfElements.map f).obj e₁.unop) =
      op ((CategoryOfElements.map f).obj e₂.unop) at h₁
    change op ((CategoryOfElements.map g).obj e₁.unop) =
      op ((CategoryOfElements.map g).obj e₂.unop) at h₂
    have ha : e₁.unop.1 = e₂.unop.1 := congrArg (fun z => z.unop.1) h₁
    have k₁ := CategoryOfElements.map_eqToHom_snd (Opposite.op_injective h₁)
    have k₂ := CategoryOfElements.map_eqToHom_snd (Opposite.op_injective h₂)
    refine Opposite.unop_injective (Functor.Elements.ext _ _ ha ?_)
    refine Types.ext_of_isPullback (hA _) ?_ ?_
    · rw [NatTrans.naturality_apply]
      exact k₁
    · rw [NatTrans.naturality_apply]
      exact k₂
  · rintro (x : X.Elementsᵒᵖ) (y : Y.Elementsᵒᵖ) e
    change op ((CategoryOfElements.map p).obj x.unop) =
      op ((CategoryOfElements.map q).obj y.unop) at e
    have ha : x.unop.1 = y.unop.1 := congrArg (fun z => z.unop.1) e
    have k := CategoryOfElements.map_eqToHom_snd (Opposite.op_injective e)
    change Z.map (eqToHom ha) (p.app _ x.unop.2) = q.app _ y.unop.2 at k
    have hpq : p.app _ x.unop.2 = q.app _ (Y.map (eqToHom ha.symm) y.unop.2) := by
      rw [NatTrans.naturality_apply]
      change _ = Z.map (eqToHom ha.symm) (q.app _ y.unop.2)
      rw [← k, ← Functor.map_comp_apply, eqToHom_trans, eqToHom_refl, Functor.map_id_apply]
    obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback (hA _) _ _ hpq
    refine ⟨op (P.elementsMk x.unop.1 z), ?_, ?_⟩
    · change op (X.elementsMk x.unop.1 (f.app _ z)) = x
      rw [hz₁]
      rfl
    · change op (Y.elementsMk x.unop.1 (g.app _ z)) = y
      rw [hz₂]
      refine congrArg op (Functor.Elements.ext _ _ ha ?_)
      simp
  · intro e₁ e₂ γ₁ γ₂ h₁ h₂
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg (fun m => m.unop.val) h₁
  · rintro (e₁ : P.Elementsᵒᵖ) (e₂ : P.Elementsᵒᵖ)
      (α : op ((CategoryOfElements.map f).obj e₁.unop) ⟶
        op ((CategoryOfElements.map f).obj e₂.unop))
      (β : op ((CategoryOfElements.map g).obj e₁.unop) ⟶
        op ((CategoryOfElements.map g).obj e₂.unop)) e
    change (CategoryOfElements.map p).op.map α =
      eqToHom _ ≫ (CategoryOfElements.map q).op.map β ≫ eqToHom _ at e
    have hv : α.unop.1 = β.unop.1 := by
      have := congrArg (fun m => m.unop.val) e
      simp only [unop_comp, CategoryOfElements.comp_val] at this
      erw [CategoryOfElements.eqToHom_unop_val, CategoryOfElements.eqToHom_unop_val, eqToHom_refl,
        eqToHom_refl, Category.id_comp, Category.comp_id] at this
      exact this
    let φ : e₂.unop.1 ⟶ e₁.unop.1 := α.unop.1
    have hα : X.map φ (f.app _ e₂.unop.2) = f.app _ e₁.unop.2 := α.unop.2
    have hβ : Y.map φ (g.app _ e₂.unop.2) = g.app _ e₁.unop.2 := by
      change Y.map α.unop.1 _ = _
      rw [hv]
      exact β.unop.2
    have hγ : P.map φ e₂.unop.2 = e₁.unop.2 :=
      Types.ext_of_isPullback (hA e₁.unop.1) ((NatTrans.naturality_apply f φ _).trans hα)
        ((NatTrans.naturality_apply g φ _).trans hβ)
    refine ⟨(CategoryOfElements.homMk e₂.unop e₁.unop φ hγ).op, ?_, ?_⟩
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      rfl
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      exact hv

end PullbackPreservation

end Atoms.TestCategory
