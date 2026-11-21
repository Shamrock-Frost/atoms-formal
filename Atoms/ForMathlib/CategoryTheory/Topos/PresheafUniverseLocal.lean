import Atoms.ForMathlib.CategoryTheory.Topos.PresheafUniverse
import Mathlib.CategoryTheory.LiftingProperties.Limits
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Subfunctor.Image

universe s t u v w

namespace CategoryTheory

open Limits Opposite

section Lifting

variable {C : Type*} [Category C]

private theorem snd_iff_of_isPullback (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {X Y Z W₁ W₂ : C} {f : X ⟶ Z} {g : Y ⟶ Z} {fst₁ : W₁ ⟶ X} {snd₁ : W₁ ⟶ Y} {fst₂ : W₂ ⟶ X}
    {snd₂ : W₂ ⟶ Y} (h₁ : IsPullback fst₁ snd₁ f g) (h₂ : IsPullback fst₂ snd₂ f g) :
    P snd₁ ↔ P snd₂ :=
  P.arrow_mk_iso_iff (Arrow.isoMk (h₁.isoIsPullback _ _ h₂) (Iso.refl _) (by simp))

private theorem hasLiftingProperty_iff_forall_pullback [HasPullbacks C] {K L X Y : C} (i : K ⟶ L)
    (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ ∀ σ : L ⟶ Y, HasLiftingProperty i (pullback.snd p σ) := by
  refine ⟨fun _ σ ↦ inferInstance, fun h ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
  have := h b
  have sq' : CommSq (pullback.lift a i sq.w) i (pullback.snd p b) (𝟙 L) :=
    ⟨by rw [pullback.lift_snd, Category.comp_id]⟩
  exact ⟨⟨⟨sq'.lift ≫ pullback.fst p b, by rw [sq'.fac_left_assoc, pullback.lift_fst],
    by rw [Category.assoc, pullback.condition, sq'.fac_right_assoc, Category.id_comp]⟩⟩⟩

end Lifting

variable (A : Type v) [Category.{w} A]

def presheafUniverseSub (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1))))
    [P.IsStableUnderBaseChange] : Subfunctor (presheafUniverse.{u} A) where
  obj a := {x | P (pullback.snd (presheafUniverseTotalπ.{u} A)
    ((uliftYonedaEquiv.{max v (u + 1)} (C := A)).symm x))}
  map {a b} f x hx := by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [uliftYonedaEquiv_symm_map]
    have h := (IsPullback.of_hasPullback (pullback.snd _ _)
      (uliftYoneda.{max v (u + 1)}.map f.unop)).paste_horiz (IsPullback.of_hasPullback
        (presheafUniverseTotalπ.{u} A) ((uliftYonedaEquiv.{max v (u + 1)} (C := A)).symm x))
    exact (snd_iff_of_isPullback P h (IsPullback.of_hasPullback _ _)).1
      (MorphismProperty.pullback_snd (P := P) _ _ hx)

theorem mem_presheafUniverseSub_iff (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1))))
    [P.IsStableUnderBaseChange] {a : Aᵒᵖ} (x : (presheafUniverse.{u} A).obj a) :
    x ∈ (presheafUniverseSub.{u} A P).obj a ↔ P (pullback.snd (presheafUniverseTotalπ.{u} A)
      ((uliftYonedaEquiv.{max v (u + 1)} (C := A)).symm x)) :=
  Iff.rfl

theorem mem_presheafUniverseSub_iff_of_isPullback
    (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))) [P.IsStableUnderBaseChange]
    {E F : Aᵒᵖ ⥤ Type (max v w (u + 1))} {p : E ⟶ F} {χ : F ⟶ presheafUniverse.{u} A}
    {q : E ⟶ presheafUniverseTotal.{u} A} (h : IsPullback q p (presheafUniverseTotalπ.{u} A) χ)
    {a : A} (σ : uliftYoneda.{max v (u + 1)}.obj a ⟶ F) :
    χ.app (op a) (uliftYonedaEquiv σ) ∈ (presheafUniverseSub.{u} A P).obj (op a) ↔
      P (pullback.snd p σ) := by
  rw [mem_presheafUniverseSub_iff, ← uliftYonedaEquiv_comp, Equiv.symm_apply_apply]
  exact snd_iff_of_isPullback P (IsPullback.of_hasPullback _ _)
    ((IsPullback.of_hasPullback p σ).paste_horiz h)

noncomputable def presheafUniverseSubTotal (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1))))
    [P.IsStableUnderBaseChange] : Aᵒᵖ ⥤ Type (max v w (u + 1)) :=
  pullback (presheafUniverseTotalπ.{u} A) (presheafUniverseSub.{u} A P).ι

noncomputable def presheafUniverseSubTotalπ
    (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))) [P.IsStableUnderBaseChange] :
    presheafUniverseSubTotal.{u} A P ⟶ (presheafUniverseSub.{u} A P).toFunctor :=
  pullback.snd _ _

theorem isPullback_presheafUniverseSubTotalπ
    (P : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))) [P.IsStableUnderBaseChange] :
    IsPullback (P := presheafUniverseSubTotal.{u} A P) (pullback.fst _ _)
      (presheafUniverseSubTotalπ.{u} A P)
      (presheafUniverseTotalπ.{u} A) (presheafUniverseSub.{u} A P).ι :=
  IsPullback.of_hasPullback _ _

theorem rlp_iff_forall_pullback {T : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))}
    (hT : ∀ ⦃K L⦄ (j : K ⟶ L), T j → ∃ a : A, Nonempty (L ≅ uliftYoneda.{max v (u + 1)}.obj a))
    {E F : Aᵒᵖ ⥤ Type (max v w (u + 1))} (p : E ⟶ F) :
    T.rlp p ↔ ∀ (a : A) (σ : uliftYoneda.{max v (u + 1)}.obj a ⟶ F), T.rlp (pullback.snd p σ) := by
  refine ⟨fun hp a σ ↦ MorphismProperty.pullback_snd (P := T.rlp) p σ hp, fun h K L j hj ↦ ?_⟩
  obtain ⟨a, ⟨e⟩⟩ := hT j hj
  let he : Arrow.mk j ≅ Arrow.mk (j ≫ e.hom) := Arrow.isoMk (Iso.refl _) e
  have : HasLiftingProperty (j ≫ e.hom) p := by
    refine (hasLiftingProperty_iff_forall_pullback _ p).2 fun σ ↦ ?_
    have := h a σ j hj
    exact HasLiftingProperty.of_arrow_iso_left he _
  exact HasLiftingProperty.of_arrow_iso_left he.symm p

theorem rlp_presheafUniverseSubTotalπ {T : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))}
    (hT : ∀ ⦃K L⦄ (j : K ⟶ L), T j → ∃ a : A, Nonempty (L ≅ uliftYoneda.{max v (u + 1)}.obj a)) :
    T.rlp (presheafUniverseSubTotalπ.{u} A T.rlp) :=
  (rlp_iff_forall_pullback.{u} A hT _).2 fun _ σ ↦
    (mem_presheafUniverseSub_iff_of_isPullback.{u} A T.rlp
      (isPullback_presheafUniverseSubTotalπ.{u} A T.rlp) σ).1 (uliftYonedaEquiv σ).2

theorem rlp_iff_exists_isPullback {T : MorphismProperty (Aᵒᵖ ⥤ Type (max v w (u + 1)))}
    (hT : ∀ ⦃K L⦄ (j : K ⟶ L), T j → ∃ a : A, Nonempty (L ≅ uliftYoneda.{max v (u + 1)}.obj a))
    {E F : Aᵒᵖ ⥤ Type (max v w (u + 1))} (p : E ⟶ F)
    (hp : ∀ (a : Aᵒᵖ) (x : F.obj a), Small.{u} {e : E.obj a // p.app a e = x}) :
    T.rlp p ↔ ∃ (χ : F ⟶ (presheafUniverseSub.{u} A T.rlp).toFunctor)
      (q : E ⟶ presheafUniverseSubTotal.{u} A T.rlp),
      IsPullback q p (presheafUniverseSubTotalπ.{u} A T.rlp) χ := by
  refine ⟨fun hpT ↦ ?_, fun ⟨χ, q, h⟩ ↦
    MorphismProperty.of_isPullback h (rlp_presheafUniverseSubTotalπ.{u} A hT)⟩
  obtain ⟨χ, q, h⟩ := exists_isPullback_presheafUniverseTotalπ.{u} A p hp
  have hχ : Subfunctor.range χ ≤ presheafUniverseSub.{u} A T.rlp := by
    rintro ⟨a⟩ _ ⟨y, rfl⟩
    rw [← uliftYonedaEquiv.apply_symm_apply y]
    exact (mem_presheafUniverseSub_iff_of_isPullback.{u} A T.rlp h _).2
      ((rlp_iff_forall_pullback.{u} A hT p).1 hpT a _)
  have hS := isPullback_presheafUniverseSubTotalπ.{u} A T.rlp
  refine ⟨Subfunctor.lift χ hχ, hS.lift q (p ≫ Subfunctor.lift χ hχ)
    (by rw [Category.assoc, Subfunctor.lift_ι, h.w]), IsPullback.of_right ?_ (hS.lift_snd _ _ _) hS⟩
  rwa [hS.lift_fst, Subfunctor.lift_ι]

namespace CategoryOfElements

variable {C : Type v} [Category.{w} C] {F : Cᵒᵖ ⥤ Type (max t s)}

private def totalMapRight {G G' : F.Elements ⥤ Type s} (β : G ⟶ G') : total G ⟶ total G' where
  app _ := ↾fun p ↦ ⟨p.1, β.app _ p.2⟩
  naturality {c d} f := ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦
    congrArg (Sigma.mk (F.map f x))
      (NatTrans.naturality_apply β (homMk (F.elementsMk c x) (F.elementsMk d (F.map f x)) f rfl) e)

def totalIso {G G' : F.Elements ⥤ Type s} (β : G ≅ G') : total G ≅ total G' where
  hom := totalMapRight β.hom
  inv := totalMapRight β.inv
  hom_inv_id := NatTrans.ext (funext fun c ↦ ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦
    congrArg (Sigma.mk x) (β.hom_inv_id_app_apply (F.elementsMk c x) e))
  inv_hom_id := NatTrans.ext (funext fun c ↦ ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦
    congrArg (Sigma.mk x) (β.inv_hom_id_app_apply (F.elementsMk c x) e))

@[reassoc (attr := simp)]
theorem totalIso_hom_comp_totalπ {G G' : F.Elements ⥤ Type s} (β : G ≅ G') :
    (totalIso β).hom ≫ totalπ G' = totalπ G :=
  rfl

private theorem total_map_mk (G : F.Elements ⥤ Type s) {c d : Cᵒᵖ} {x : F.obj c} {y : F.obj d}
    (φ : c ⟶ d) (hφ : F.map φ x = y) (e : G.obj (F.elementsMk c x)) :
    (total G).map φ ⟨x, e⟩ = ⟨y, G.map (homMk (F.elementsMk c x) (F.elementsMk d y) φ hφ) e⟩ := by
  subst hφ
  rfl

variable {F' E' : Cᵒᵖ ⥤ Type (max t s)} {G : F.Elements ⥤ Type s} {f' : E' ⟶ F'}
  {k : total G ⟶ E'} {i : F ⟶ F'}

private def toFibre (h : CommSq k (totalπ G) f' i) (y : F.Elements) (e : G.obj y) :
    {e' : E'.obj y.1 // f'.app y.1 e' = i.app y.1 y.2} :=
  ⟨k.app y.1 ⟨y.2, e⟩, congrArg (fun α ↦ α.app y.1 ⟨y.2, e⟩) h.w⟩

private theorem toFibre_bijective (h : IsPullback k (totalπ G) f' i) (y : F.Elements) :
    Function.Bijective (toFibre h.toCommSq y) := by
  obtain ⟨-, hinj, hsurj⟩ := (Limits.Types.isPullback_iff _ _ _ _).1 (h.app y.1)
  refine ⟨fun e₁ e₂ he ↦ ?_, fun r ↦ ?_⟩
  · have := hinj ⟨y.2, e₁⟩ ⟨y.2, e₂⟩ ⟨congrArg Subtype.val he, rfl⟩
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2
  · obtain ⟨⟨x, e⟩, hk, rfl : x = y.2⟩ := hsurj r.1 y.2 r.2
    exact ⟨e, Subtype.ext hk⟩

noncomputable def isoFibresOfIsPullback [∀ c x, Small.{s} {e : E'.obj c // f'.app c e = x}]
    (h : IsPullback k (totalπ G) f' i) : G ≅ map i ⋙ fibres f' :=
  NatIso.ofComponents
    (fun y ↦ ((Equiv.ofBijective _ (toFibre_bijective h y)).trans (equivShrink _)).toIso)
    (by
      rintro ⟨c, x⟩ ⟨d, y⟩ ⟨φ, hφ⟩
      refine ConcreteCategory.hom_ext _ _ fun e ↦ congrArg (equivShrink _) (Subtype.ext ?_)
      have H : k.app d ⟨y, G.map ⟨φ, hφ⟩ e⟩ = E'.map φ ((equivShrink _).symm
          (equivShrink _ (toFibre h.toCommSq (F.elementsMk c x) e))).1 := by
        rw [Equiv.symm_apply_apply]
        exact (congrArg (k.app d) (total_map_mk G φ hφ e)).symm.trans
          (NatTrans.naturality_apply k φ ⟨x, e⟩)
      exact H)

end CategoryOfElements

private theorem exists_comp_eq_and_iso {C D : Type*} [Category C] [Category D] (j : C ⥤ D)
    (hj : Function.Injective j.obj) {G : C ⥤ Type s} {G' : D ⥤ Type s} (α : G ≅ j ⋙ G') :
    ∃ H : D ⥤ Type s, j ⋙ H = G ∧ Nonempty (H ≅ G') := by
  classical
  let obj : D → Type s := fun d ↦ if h : ∃ c, j.obj c = d then G.obj h.choose else G'.obj d
  let e : ∀ d, obj d ≅ G'.obj d := fun d ↦ if h : ∃ c, j.obj c = d then
    eqToIso (dif_pos h) ≪≫ α.app h.choose ≪≫ eqToIso (congrArg G'.obj h.choose_spec)
    else eqToIso (dif_neg h)
  let H : D ⥤ Type s :=
    { obj
      map {d d'} f := (e d).hom ≫ G'.map f ≫ (e d').inv
      map_id d := by simp
      map_comp f g := by simp }
  have hobj : ∀ c, obj (j.obj c) = G.obj c := fun c ↦ (dif_pos ⟨c, rfl⟩).trans
    (congrArg G.obj (hj (⟨c, rfl⟩ : ∃ c', j.obj c' = j.obj c).choose_spec))
  have he : ∀ c, e (j.obj c) = eqToIso (hobj c) ≪≫ α.app c := fun c ↦ by
    have key : ∀ c₁ (hc : c₁ = c) (h₁ : obj (j.obj c) = G.obj c₁)
        (h₂ : G'.obj (j.obj c₁) = G'.obj (j.obj c)),
        eqToIso h₁ ≪≫ α.app c₁ ≪≫ eqToIso h₂ = eqToIso (hobj c) ≪≫ α.app c := by
      rintro _ rfl _ _
      ext
      simp
    simp only [e, dif_pos (⟨c, rfl⟩ : ∃ c', j.obj c' = j.obj c)]
    exact key _ (hj (⟨c, rfl⟩ : ∃ c', j.obj c' = j.obj c).choose_spec) _ _
  refine ⟨H, Functor.ext hobj fun c c' f ↦ ?_, ⟨NatIso.ofComponents e fun f ↦ by simp [H]⟩⟩
  simp only [Functor.comp_map, H, he, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [← Functor.comp_map j G', ← α.hom.naturality_assoc, Iso.hom_inv_id_app_assoc]

open CategoryOfElements in
theorem exists_extension_classifying {X X' B B' : Aᵒᵖ ⥤ Type (max v w (u + 1))}
    {f : X ⟶ B} {f' : X' ⟶ B'} {g : X ⟶ X'} {i : B ⟶ B'} [Mono i] (sq : IsPullback g f f' i)
    (hf' : ∀ (a : Aᵒᵖ) (x : B'.obj a), Small.{u} {e : X'.obj a // f'.app a e = x})
    (χ : B ⟶ presheafUniverse.{u} A) (q : X ⟶ presheafUniverseTotal.{u} A)
    (hχ : IsPullback q f (presheafUniverseTotalπ.{u} A) χ) :
    ∃ (χ' : B' ⟶ presheafUniverse.{u} A) (q' : X' ⟶ presheafUniverseTotal.{u} A),
      IsPullback q' f' (presheafUniverseTotalπ.{u} A) χ' ∧ i ≫ χ' = χ := by
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : total.{u, max v w (u + 1)} (map χ ⋙ presheafUniverseFamily A) ≅ X,
      e₀.hom ≫ f = totalπ.{u, max v w (u + 1)} _ :=
    ⟨_, IsPullback.isoIsPullback_hom_snd _ _ (isPullback_totalMap.{u, max v w (u + 1)} χ _) hχ⟩
  have hsq : IsPullback (e₀.hom ≫ g) (totalπ.{u, max v w (u + 1)}
      (map χ ⋙ presheafUniverseFamily A)) f' i := by
    simpa using (IsPullback.of_horiz_isIso (g := 𝟙 B)
      ⟨by rw [Category.comp_id, he₀]⟩).paste_horiz sq
  have hi : Function.Injective (map i).obj := by
    rintro ⟨c, x⟩ ⟨c', x'⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    obtain rfl := (mono_iff_injective (i.app c)).1 inferInstance (eq_of_heq h)
    rfl
  obtain ⟨H, hH, ⟨β⟩⟩ := exists_comp_eq_and_iso (map i) hi (isoFibresOfIsPullback hsq)
  let χ' := presheafUniverseEquiv A B' H
  have hχ' : map χ' ⋙ presheafUniverseFamily A = H :=
    (presheafUniverseEquiv A B').symm_apply_apply H
  obtain ⟨e, he⟩ : ∃ e : total.{u, max v w (u + 1)} (map χ' ⋙ presheafUniverseFamily A) ≅ X',
      e.hom ≫ f' = totalπ.{u, max v w (u + 1)} _ := by
    rw [hχ']
    exact ⟨totalIso β ≪≫ totalFibresIso f', by simp⟩
  refine ⟨χ', e.inv ≫ totalMap.{u, max v w (u + 1)} χ' _,
    (isPullback_totalMap.{u, max v w (u + 1)} χ' (presheafUniverseFamily A)).of_iso e
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (e.hom_inv_id_assoc _).symm)
      ((Category.comp_id _).trans he.symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm), ?_⟩
  rw [← presheafUniverseEquiv_naturality, hH]
  exact (presheafUniverseEquiv A B).apply_symm_apply χ

end CategoryTheory
