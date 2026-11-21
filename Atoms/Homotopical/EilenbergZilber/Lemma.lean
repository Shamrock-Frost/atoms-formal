import Atoms.Homotopical.EilenbergZilber.Basic

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical.EZCategory

universe w v u

variable {A : Type u} [Category.{v} A]

theorem isSplitEpi_of_isAbsolutePushout {a b c d : A} {f : a ⟶ b} {g : a ⟶ c}
    {h : b ⟶ d} {k : c ⟶ d} (sq : IsAbsolutePushout f g h k) (hf : IsSplitEpi f) :
    IsSplitEpi k := by
  have : Epi (yoneda.map f) := inferInstance
  exact isSplitEpi_of_epi_yoneda_map k (IsPushout.epi_inr_of_epi sq)

theorem isNondegenerate_of_mono {b c : A} (i : c ⟶ b) [Mono i] :
    IsNondegenerate (yoneda.obj b) (a := c) (i : (yoneda.obj b).obj (op c)) := by
  rintro c'' r hr ⟨z, hz⟩
  have hz' : r ≫ z = i := hz
  have := hr
  refine ⟨⟨section_ r, ?_, IsSplitEpi.id r⟩⟩
  rw [← cancel_mono i, Category.assoc, ← hz', ← Category.assoc (section_ r), IsSplitEpi.id r,
    Category.id_comp, Category.id_comp]

variable [EZCategory A]

theorem exists_isNondegenerate (X : Aᵒᵖ ⥤ Type w) (a : A) (x : X.obj (op a)) :
    ∃ (b : A) (p : a ⟶ b) (y : X.obj (op b)),
      IsSplitEpi p ∧ IsNondegenerate X y ∧ X.map p.op y = x :=
  exists_isSplitEpi_isNondegenerate_of_deg (fun _ _ i hi ↦ deg_le_of_mono i hi)
    (fun _ _ i hi ↦ isIso_of_mono_of_deg_eq i hi) X x

theorem existsUnique_iso_of_isNondegenerate (X : Aᵒᵖ ⥤ Type w) {a b b' : A} (p : a ⟶ b)
    (p' : a ⟶ b') (y : X.obj (op b)) (y' : X.obj (op b')) (hp : IsSplitEpi p)
    (hy : IsNondegenerate X y) (hp' : IsSplitEpi p') (hy' : IsNondegenerate X y')
    (h : X.map p.op y = X.map p'.op y') :
    ∃! e : b ≅ b', p ≫ e.hom = p' ∧ X.map e.hom.op y' = y := by
  obtain ⟨d, τ, τ', sq⟩ := exists_absolutePushout p p' hp hp'
  let X' : Aᵒᵖ ⥤ Type (max w v) := X ⋙ uliftFunctor.{v}
  have sq' : IsPushout (uliftYoneda.{w}.map p) (uliftYoneda.{w}.map p')
      (uliftYoneda.{w}.map τ) (uliftYoneda.{w}.map τ') :=
    IsPushout.map ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{w}) sq
  have hw : uliftYoneda.map p ≫ (uliftYonedaEquiv (F := X')).symm ⟨y⟩ =
      uliftYoneda.map p' ≫ (uliftYonedaEquiv (F := X')).symm ⟨y'⟩ := by
    have e₁ := uliftYonedaEquiv_symm_map (F := X') p.op ⟨y⟩
    have e₂ := uliftYonedaEquiv_symm_map (F := X') p'.op ⟨y'⟩
    rw [Quiver.Hom.unop_op] at e₁ e₂
    rw [← e₁, ← e₂]
    exact congrArg _ (congrArg ULift.up h)
  set φ := (uliftYonedaEquiv (sq'.desc _ _ hw)).down with hφ
  have hτ : X.map τ.op φ = y := by
    have := uliftYonedaEquiv_naturality (sq'.desc _ _ hw) τ.op
    rw [Quiver.Hom.unop_op, IsPushout.inl_desc] at this
    exact congrArg ULift.down (this.trans (Equiv.apply_symm_apply _ _))
  have hτ' : X.map τ'.op φ = y' := by
    have := uliftYonedaEquiv_naturality (sq'.desc _ _ hw) τ'.op
    rw [Quiver.Hom.unop_op, IsPushout.inr_desc] at this
    exact congrArg ULift.down (this.trans (Equiv.apply_symm_apply _ _))
  have hiτ : IsIso τ :=
    hy τ (isSplitEpi_of_isAbsolutePushout sq.flip hp') ⟨φ, hτ⟩
  have hiτ' : IsIso τ' :=
    hy' τ' (isSplitEpi_of_isAbsolutePushout sq hp) ⟨φ, hτ'⟩
  have := hp
  refine ⟨asIso τ ≪≫ (asIso τ').symm, ⟨?_, ?_⟩, ?_⟩
  · simp [← Category.assoc, sq.w]
  · have key : ∀ g : b ⟶ b', g ≫ τ' = τ → X.map g.op y' = y := by
      intro g hg
      rw [← hτ', ← hτ, ← hg, op_comp, Functor.map_comp_apply]
    exact key _ (by simp)
  · rintro e ⟨he, -⟩
    ext
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
    rw [← cancel_epi p, he, ← Category.assoc, sq.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]

theorem exists_iso_of_isSplitEpi_of_mono {a b c c' : A} (p : a ⟶ c) (i : c ⟶ b) (p' : a ⟶ c')
    (i' : c' ⟶ b) (hp : IsSplitEpi p) (hi : Mono i) (hp' : IsSplitEpi p') (hi' : Mono i')
    (h : p ≫ i = p' ≫ i') : ∃ e : c ≅ c', p ≫ e.hom = p' ∧ e.hom ≫ i' = i := by
  obtain ⟨e, ⟨he, hei⟩, -⟩ := existsUnique_iso_of_isNondegenerate (yoneda.obj b) p p'
    i i' hp (isNondegenerate_of_mono i) hp' (isNondegenerate_of_mono i') h
  exact ⟨e, he, hei⟩

end Atoms.Homotopical.EZCategory
