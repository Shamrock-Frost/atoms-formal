import Atoms.ForMathlib.CategoryTheory.Limits.Types.Pushouts
import Atoms.Homotopical.Cellular.MonoSaturated
import Atoms.Homotopical.EilenbergZilber.Skeleton

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical.EZCategory

universe w v u

section General

variable {A : Type u} [Category.{v} A]

def IsDominant {X : Aᵒᵖ ⥤ Type w} {a : A} (x : X.obj (op a)) : Prop :=
  ∀ e : a ≅ a, X.map e.hom.op x = x → e = Iso.refl a

theorem isDominant_of_hasTrivialAutomorphisms {X : Aᵒᵖ ⥤ Type w} [HasTrivialAutomorphisms A]
    {a : A} (x : X.obj (op a)) : IsDominant x :=
  fun _ _ ↦ Subsingleton.elim _ _

def IsNormal (X : Aᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃a : A⦄ (x : X.obj (op a)), IsNondegenerate X x → IsDominant x

variable (A) in
def normalMonomorphisms : MorphismProperty (Aᵒᵖ ⥤ Type w) :=
  fun _ Y i ↦ Mono i ∧ ∀ ⦃a : A⦄ (y : Y.obj (op a)), IsNondegenerate Y y →
    y ∉ Set.range (i.app (op a)) → IsDominant y

theorem IsNondegenerate.app_of_injective {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) {a : A}
    (hφ : Function.Injective (φ.app (op a))) {x : X.obj (op a)} (hx : IsNondegenerate X x) :
    IsNondegenerate Y (φ.app (op a) x) := by
  rintro b p hp ⟨y, hy⟩
  have hfix : X.map (p ≫ section_ p).op x = x := hφ (by
    rw [NatTrans.naturality_apply, ← hy, ← Functor.map_comp_apply, ← op_comp, Category.assoc,
      IsSplitEpi.id, Category.comp_id])
  refine hx p hp ⟨X.map (section_ p).op x, ?_⟩
  rw [← Functor.map_comp_apply, ← op_comp, hfix]

theorem IsNondegenerate.of_app {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) {a : A} {x : X.obj (op a)}
    (h : IsNondegenerate Y (φ.app (op a) x)) : IsNondegenerate X x := by
  rintro b p hp ⟨y, rfl⟩
  exact h p hp ⟨φ.app _ y, (NatTrans.naturality_apply φ p.op y).symm⟩

theorem IsDominant.of_app {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) {a : A} {x : X.obj (op a)}
    (h : IsDominant (φ.app (op a) x)) : IsDominant x := fun e he ↦
  h e (by rw [← NatTrans.naturality_apply, he])

theorem IsDominant.app_of_injective {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) {a : A}
    (hφ : Function.Injective (φ.app (op a))) {x : X.obj (op a)} (h : IsDominant x) :
    IsDominant (φ.app (op a) x) := fun e he ↦
  h e (hφ (by rw [NatTrans.naturality_apply, he]))

theorem IsNormal.of_mono {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) [Mono φ] (hY : IsNormal Y) :
    IsNormal X := fun _ _ hx ↦
  IsDominant.of_app φ (hY _ (hx.app_of_injective φ (injective_of_mono (φ.app _))))

theorem isNormal_of_hasTrivialAutomorphisms [HasTrivialAutomorphisms A] (X : Aᵒᵖ ⥤ Type w) :
    IsNormal X := fun _ x _ ↦
  isDominant_of_hasTrivialAutomorphisms x

theorem isNormal_uliftYoneda [EZCategory A] (a : A) : IsNormal (uliftYoneda.{w}.obj a) := by
  intro b f hf e he
  obtain ⟨c, p, i, hp, hi, hpi⟩ := exists_factorization f.down
  have : IsIso p := hf p hp ⟨⟨i⟩, ULift.ext _ _ hpi⟩
  have hm : Mono f.down := hpi ▸ mono_comp p i
  exact Iso.ext ((cancel_mono f.down).1 (by simpa using congrArg ULift.down he))

theorem normalMonomorphisms_le_monomorphisms :
    (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type w)) ≤ MorphismProperty.monomorphisms _ :=
  fun _ _ _ hi ↦ hi.1

theorem normalMonomorphisms_of_isNormal {X Y : Aᵒᵖ ⥤ Type w} (i : X ⟶ Y) [Mono i]
    (hY : IsNormal Y) : normalMonomorphisms A i :=
  ⟨inferInstance, fun _ y hy _ ↦ hY y hy⟩

theorem IsNormal.of_normalMonomorphisms {X Y : Aᵒᵖ ⥤ Type w} {i : X ⟶ Y}
    (hi : normalMonomorphisms A i) (hX : IsNormal X) : IsNormal Y := by
  intro a y hy
  have := hi.1
  by_cases hr : y ∈ Set.range (i.app (op a))
  · obtain ⟨x, rfl⟩ := hr
    exact IsDominant.app_of_injective i (injective_of_mono (i.app _)) (hX x (hy.of_app i))
  · exact hi.2 y hy hr

theorem isNormal_iff_normalMonomorphisms {E X : Aᵒᵖ ⥤ Type w} (hE : IsInitial E) (f : E ⟶ X) :
    IsNormal X ↔ normalMonomorphisms A f := by
  have hempty : ∀ (a : Aᵒᵖ) (x : E.obj a), False := fun a x ↦
    (((hE.to (⊥ : Subfunctor X).toFunctor).app a x).2 : _)
  have : Mono f := (NatTrans.mono_iff_mono_app f).2 fun a ↦
    (mono_iff_injective _).2 fun x _ _ ↦ (hempty a x).elim
  refine ⟨fun h ↦ normalMonomorphisms_of_isNormal f h, fun h a y hy ↦ h.2 y hy ?_⟩
  rintro ⟨x, -⟩
  exact hempty _ x

theorem normalMonomorphisms_ι_iff {Y : Aᵒᵖ ⥤ Type w} (R : Subfunctor Y) :
    normalMonomorphisms A R.ι ↔ ∀ ⦃a : A⦄ (y : Y.obj (op a)), IsNondegenerate Y y →
      y ∉ R.obj (op a) → IsDominant y := by
  have hr : ∀ a : A, Set.range (R.ι.app (op a)) = R.obj (op a) := fun a ↦
    Subtype.range_coe_subtype
  refine ⟨fun h a y hy hR ↦ h.2 y hy (hr a ▸ hR), fun h ↦ ⟨inferInstance, fun a y hy hR ↦ ?_⟩⟩
  exact h y hy (hr a ▸ hR)

theorem normalMonomorphisms_eq_monomorphisms [HasTrivialAutomorphisms A] :
    (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type w)) =
      MorphismProperty.monomorphisms _ :=
  le_antisymm normalMonomorphisms_le_monomorphisms fun _ _ _ (hi : Mono _) ↦
    ⟨hi, fun _ y _ _ ↦ isDominant_of_hasTrivialAutomorphisms y⟩

instance isStableUnderCobaseChange_normalMonomorphisms :
    (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type w)).IsStableUnderCobaseChange where
  of_isPushout {X Y X' Y'} {i u i' v} sq hi := by
    have := hi.1
    have : Mono i' := (MorphismProperty.monomorphisms _).of_isPushout sq this
    refine ⟨this, fun a s' hs' hs'X ↦ ?_⟩
    have sq' := sq.map ((evaluation _ _).obj (op a))
    obtain ⟨x', hx'⟩ | ⟨s, hs₁, hs⟩ := Types.eq_or_eq_of_isPushout' sq' s'
    · exact absurd ⟨x', hx'⟩ hs'X
    replace hs₁ : v.app (op a) s = s' := hs₁
    replace hs : s ∉ Set.range (i.app (op a)) := hs
    subst hs₁
    have hsd : IsDominant s := hi.2 s (hs'.of_app v) hs
    intro e he
    refine hsd e ((Types.eq_of_isPushout_of_notMem_range sq' (y := Y.map e.hom.op s) ?_).2 s
      ?_).symm
    · rintro ⟨x, hx⟩
      refine hs ⟨X.map e.inv.op x, ?_⟩
      replace hx : i.app (op a) x = Y.map e.hom.op s := hx
      rw [NatTrans.naturality_apply, hx, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id,
        op_id, Functor.map_id_apply]
    · simpa [NatTrans.naturality_apply] using he.symm

instance isStableUnderRetracts_normalMonomorphisms :
    (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type w)).IsStableUnderRetracts where
  of_retract {X Y X' Y'} {f g} h hg := by
    have := hg.1
    have : Mono f := (MorphismProperty.monomorphisms _).of_retract h this
    refine ⟨this, fun a y hy hyX ↦ ?_⟩
    have hret : ∀ z, h.r.right.app (op a) (h.i.right.app (op a) z) = z := fun z ↦ by
      rw [← NatTrans.comp_app_apply, h.retract_right]
      rfl
    have hinj : Function.Injective (h.i.right.app (op a)) := fun y₁ y₂ e ↦ by
      rw [← hret y₁, e, hret]
    refine IsDominant.of_app h.i.right (hg.2 _ (hy.app_of_injective _ hinj) ?_)
    rintro ⟨x', hx'⟩
    refine hyX ⟨h.r.left.app _ x', ?_⟩
    have hw := ConcreteCategory.congr_hom (NatTrans.congr_app h.r_w (op a)) x'
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hw
    rw [hw, hx', hret]

end General

section Small

variable {A : Type v} [SmallCategory A]

private theorem injective_ι_app_app_of_isColimit {J : Type (max w v)} [LinearOrder J]
    (F : J ⥤ Aᵒᵖ ⥤ Type (max w v)) (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h)))
    {c : Cocone F} (hc : IsColimit c) (j : J) (a : Aᵒᵖ) :
    Function.Injective ((c.ι.app j).app a) := by
  intro x y hxy
  have hc' := isColimitOfPreserves ((evaluation Aᵒᵖ (Type (max w v))).obj a) hc
  obtain ⟨k, f, g, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ (evaluation Aᵒᵖ _).obj a) hc'
      (xi := x) (xj := y)).1 hxy
  obtain rfl : g = f := Subsingleton.elim _ _
  have := hF j k (leOfHom g)
  exact injective_of_mono ((F.map (homOfLE (leOfHom g))).app a) hfg

private theorem normalMonomorphisms_of_transfiniteCompositionOfShape {J : Type (max w v)}
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : Aᵒᵖ ⥤ Type (max w v)} {f : X ⟶ Y}
    (h : (normalMonomorphisms A).TransfiniteCompositionOfShape J f) :
    normalMonomorphisms A f := by
  have hmono : ∀ j, Mono (h.incl.app j) := fun j ↦
    (MorphismProperty.monomorphisms _).transfiniteCompositionsOfShape_le (Set.Ici j) _
      ⟨(h.ici j).ofLE normalMonomorphisms_le_monomorphisms⟩
  have : Mono f := by
    rw [← h.fac]
    exact mono_comp _ _
  refine ⟨this, fun a y hy hyX ↦ ?_⟩
  have hnat : ∀ (i j : J) (hij : i ≤ j) (x : (h.F.obj i).obj (op a)),
      (h.incl.app j).app (op a) ((h.F.map (homOfLE hij)).app (op a) x) =
        (h.incl.app i).app (op a) x := fun i j hij x ↦ by
    rw [← NatTrans.comp_app_apply, h.incl.naturality]
    simp
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op a)) h.isColimit) y
  replace hx : (h.incl.app j).app (op a) x = y := hx
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    have hfac : ∀ z, (h.isoBot.inv ≫ h.incl.app ⊥).app (op a) z = f.app (op a) z := fun z ↦ by
      rw [h.fac]
    refine absurd ⟨h.isoBot.hom.app _ x, ?_⟩ hyX
    rw [← hfac, NatTrans.comp_app_apply, Iso.hom_inv_id_app_apply, hx]
  | succ k hk ih =>
    by_cases hxk : x ∈ Set.range ((h.F.map (homOfLE (Order.le_succ k))).app (op a))
    · obtain ⟨x', rfl⟩ := hxk
      exact ih x' ((hnat k _ (Order.le_succ k) x').symm.trans hx)
    · subst hx
      exact IsDominant.app_of_injective _ (injective_of_mono _)
        ((h.map_mem k hk).2 x (hy.of_app _) hxk)
  | isSuccLimit j hj ih =>
    obtain ⟨⟨k, hk⟩, x', rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op a))
        (h.F.isColimitOfIsWellOrderContinuous j hj)) x
    exact ih k hk x' ((hnat k j hk.le x').symm.trans hx)

instance isSaturated_normalMonomorphisms :
    IsSaturated.{max w v} (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) where
  isStableUnderCobaseChange := inferInstance
  isStableUnderRetracts := inferInstance
  isStableUnderTransfiniteComposition :=
    ⟨fun _ _ _ _ _ ↦ ⟨fun _ _ _ ⟨h⟩ ↦ normalMonomorphisms_of_transfiniteCompositionOfShape h⟩⟩

theorem isMonoSaturatedClass_isNormal :
    IsMonoSaturatedClass fun X : Aᵒᵖ ⥤ Type (max w v) ↦ IsNormal X where
  of_isPushout {X₀ X₁ X₂ X₃ f₁ f₂ g₁ g₂} sq hf₁ _ h₁ h₂ := by
    have := hf₁
    exact IsNormal.of_normalMonomorphisms ((normalMonomorphisms A).of_isPushout sq.flip
      (normalMonomorphisms_of_isNormal f₁ h₁)) h₂
  of_isColimit J _ _ F hF c hc hP := by
    intro a y hy
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op a)) hc) y
    have hinj := injective_ι_app_app_of_isColimit F hF hc j (op a)
    exact IsDominant.app_of_injective _ hinj (hP j x (hy.of_app _))

def autCongruence (a : A) : RepresentableCongruence a where
  setoid _ :=
    { r f g := ∃ e : a ≅ a, f ≫ e.hom = g
      iseqv :=
        { refl f := ⟨Iso.refl a, Category.comp_id f⟩
          symm := by
            rintro f g ⟨e, rfl⟩
            exact ⟨e.symm, by simp⟩
          trans := by
            rintro f g k ⟨e, rfl⟩ ⟨e', rfl⟩
            exact ⟨e ≪≫ e', by simp⟩ } }
  rel_comp g := by
    rintro f f' ⟨e, rfl⟩
    exact ⟨e, Category.assoc _ _ _⟩

theorem hasTrivialAutomorphisms_of_forall_isNormal
    (h : ∀ X : Aᵒᵖ ⥤ Type (max w v), IsNormal X) : HasTrivialAutomorphisms A where
  subsingleton_aut a := by
    let Q := (autCongruence a).quotient.{w}
    let x : Q.obj (op a) := Quotient.mk _ ⟨𝟙 a⟩
    have hx : IsNondegenerate Q x := by
      rintro b p hp ⟨y, hy⟩
      induction y using Quotient.inductionOn with | h u => ?_
      obtain ⟨e, he⟩ : ∃ e : a ≅ a, (p ≫ u.down) ≫ e.hom = 𝟙 a := Quotient.exact hy
      have : IsSplitMono p := IsSplitMono.mk' ⟨u.down ≫ e.hom, by simpa using he⟩
      exact isIso_of_mono_of_isSplitEpi p
    have hfix : ∀ e : a ≅ a, Q.map e.hom.op x = x := fun e ↦
      Quotient.sound ⟨e.symm, by simp⟩
    refine ⟨fun e₁ e₂ ↦ ?_⟩
    rw [h Q x hx e₁ (hfix e₁), h Q x hx e₂ (hfix e₂)]

end Small

end Atoms.Homotopical.EZCategory
