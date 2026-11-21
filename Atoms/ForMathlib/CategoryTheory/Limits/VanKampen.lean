import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.VanKampen

namespace CategoryTheory.Limits

universe w

theorem nonempty_isColimit_of_isPullback_types {J : Type*} [Category J] {F F' : J ⥤ Type w}
    {c : Cocone F} (hc : IsColimit c) (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (h : ∀ j, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) : Nonempty (IsColimit c') := by
  have hc' := (Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩
  have hw : ∀ j (z : F'.obj j), c.ι.app j (α.app j z) = f (c'.ι.app j z) := fun j z ↦
    (ConcreteCategory.congr_hom (h j).w z).symm
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  refine ⟨⟨?_, ?_⟩⟩
  · intro a a' ha
    induction a using Quot.ind with | mk a => ?_
    induction a' using Quot.ind with | mk a' => ?_
    obtain ⟨j, z⟩ := a
    obtain ⟨k, z'⟩ := a'
    change c'.ι.app j z = c'.ι.app k z' at ha
    set x := c'.ι.app j z with hx
    have hval : ∀ q₁ q₂ : (Σ j, F.obj j), Relation.EqvGen F.ColimitTypeRel q₁ q₂ →
        c.ι.app q₁.1 q₁.2 = c.ι.app q₂.1 q₂.2 := fun q₁ q₂ hq ↦
      congrArg (F.descColimitType (F.coconeTypesEquiv.symm c))
        ((F.ιColimitType_eq_iff q₁.2 q₂.2).2 hq)
    have key : ∀ q₁ q₂ : (Σ j, F.obj j), Relation.EqvGen F.ColimitTypeRel q₁ q₂ →
        c.ι.app q₁.1 q₁.2 = f x →
          ∀ (z₁ : F'.obj q₁.1) (z₂ : F'.obj q₂.1), α.app _ z₁ = q₁.2 → c'.ι.app _ z₁ = x →
            α.app _ z₂ = q₂.2 → c'.ι.app _ z₂ = x →
              F'.ιColimitType q₁.1 z₁ = F'.ιColimitType q₂.1 z₂ := by
      intro q₁ q₂ hq
      induction hq with
      | rel q₁ q₂ hr =>
        obtain ⟨g, hg⟩ := hr
        intro _ z₁ z₂ hz₁ hx₁ hz₂ hx₂
        have : F'.map g z₁ = z₂ := by
          refine Types.ext_of_isPullback (h q₂.1) ?_ ?_
          · rw [hx₂, ← hx₁]
            exact ConcreteCategory.congr_hom (c'.w g) z₁
          · rw [hz₂, hg, ← hz₁]
            exact ConcreteCategory.congr_hom (α.naturality g) z₁
        rw [← this, Functor.ιColimitType_map]
      | refl q =>
        intro _ z₁ z₂ hz₁ hx₁ hz₂ hx₂
        rw [Types.ext_of_isPullback (h q.1) (hx₁.trans hx₂.symm) (hz₁.trans hz₂.symm)]
      | symm q₁ q₂ hq ih =>
        intro h₂ z₂ z₁ hz₂ hx₂ hz₁ hx₁
        exact (ih ((hval _ _ hq).trans h₂) z₁ z₂ hz₁ hx₁ hz₂ hx₂).symm
      | trans q₁ q₂ q₃ hq₁₂ _ ih₁ ih₂ =>
        intro h₁ z₁ z₃ hz₁ hx₁ hz₃ hx₃
        have h₂ := (hval _ _ hq₁₂).symm.trans h₁
        obtain ⟨z₂, hx₂, hz₂⟩ := Types.exists_of_isPullback (h q₂.1) x q₂.2 h₂.symm
        exact (ih₁ h₁ z₁ z₂ hz₁ hx₁ hz₂ hx₂).trans (ih₂ h₂ z₂ z₃ hz₂ hx₂ hz₃ hx₃)
    have hrel : Relation.EqvGen F.ColimitTypeRel ⟨j, α.app j z⟩ ⟨k, α.app k z'⟩ := by
      rw [← Functor.ιColimitType_eq_iff]
      apply hc'.bijective.1
      change c.ι.app j (α.app j z) = c.ι.app k (α.app k z')
      rw [hw, hw, ← ha]
    exact key _ _ hrel (hw j z) z z' rfl rfl rfl ha.symm
  · intro x
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc (f x)
    obtain ⟨z, hz, -⟩ := Types.exists_of_isPullback (h j) x y hy.symm
    exact ⟨F'.ιColimitType j z, hz⟩

theorem nonempty_isColimit_of_isPullback {C : Type*} [Category C] {J : Type*}
    [Category J] [HasColimitsOfShape J (Type w)] {F F' : J ⥤ C ⥤ Type w} {c : Cocone F}
    (hc : IsColimit c)
    (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (h : ∀ j, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) : Nonempty (IsColimit c') :=
  ⟨evaluationJointlyReflectsColimits c' fun x ↦
    (nonempty_isColimit_of_isPullback_types
      (isColimitOfPreserves ((evaluation C (Type w)).obj x) hc)
      (((evaluation C (Type w)).obj x).mapCocone c')
      (Functor.whiskerRight α ((evaluation C (Type w)).obj x))
      (((evaluation C (Type w)).obj x).map f)
      (fun j ↦ (h j).map ((evaluation C (Type w)).obj x))).some⟩

theorem Types.isUniversalColimit {J : Type*} [Category J] {F : J ⥤ Type w} {c : Cocone F}
    (hc : IsColimit c) : IsUniversalColimit c :=
  fun _ c' α f _ _ h ↦ nonempty_isColimit_of_isPullback_types hc c' α f h

theorem FunctorToTypes.isUniversalColimit {C : Type*} [Category C] {J : Type*} [Category J]
    [HasColimitsOfShape J (Type w)] {F : J ⥤ C ⥤ Type w} {c : Cocone F} (hc : IsColimit c) :
    IsUniversalColimit c :=
  fun _ c' α f _ _ h ↦ nonempty_isColimit_of_isPullback hc c' α f h

end CategoryTheory.Limits

namespace CategoryTheory

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : Type v'} [Category.{u'} J]

theorem isUniversalColimit_of_preservesColimitsOfShape_pullback [HasPullbacks C]
    [HasColimitsOfShape J C]
    (H : ∀ {X Y : C} (f : X ⟶ Y), PreservesColimitsOfShape J (Over.pullback f))
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  intro F' c' α f h _ hpb
  let G : J ⥤ Over c.pt :=
    { obj j := Over.mk (c.ι.app j)
      map u := Over.homMk (F.map u) (c.w u) }
  let d : Cocone G :=
    { pt := Over.mk (𝟙 c.pt)
      ι := { app j := Over.homMk (c.ι.app j) } }
  have hd : IsColimit d :=
    isColimitOfReflects (Over.forget c.pt) (IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _)))
  have := H f
  let e := isColimitOfPreserves (Over.pullback f ⋙ Over.forget c'.pt) hd
  have hpb' : ∀ j, IsPullback (α.app j) (c'.ι.app j) (G.obj j).hom f := fun j => (hpb j).flip
  let β : F' ≅ G ⋙ Over.pullback f ⋙ Over.forget c'.pt :=
    NatIso.ofComponents (fun j => (hpb' j).isoPullback) fun {j k} u => by
      apply pullback.hom_ext
      · dsimp only [Functor.comp_obj, Over.forget_obj, Over.pullback_obj_left]
        simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
          pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc]
        exact α.naturality u
      · dsimp only [Functor.comp_obj, Over.forget_obj, Over.pullback_obj_left]
        simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
          pullback.lift_snd, IsPullback.isoPullback_hom_snd]
        exact c'.w u
  have hsq : IsPullback f (𝟙 c'.pt) d.pt.hom f :=
    (IsPullback.of_vert_isIso ⟨by simp⟩ : IsPullback f (𝟙 c'.pt) (𝟙 c.pt) f)
  refine ⟨IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv β _).symm e)
    (Cocone.ext hsq.isoPullback.symm fun j => ?_)⟩
  refine (Iso.comp_inv_eq _).2 ?_
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app]
  apply pullback.hom_ext
  · calc (β.hom.app j ≫ (Over.pullback f ⋙ Over.forget c'.pt).map (d.ι.app j)) ≫
          pullback.fst d.pt.hom f
        = (hpb' j).isoPullback.hom ≫ pullback.fst (G.obj j).hom f ≫ c.ι.app j :=
          (Category.assoc _ _ _).trans (congrArg ((hpb' j).isoPullback.hom ≫ ·)
            (pullback.lift_fst _ _ _))
      _ = c'.ι.app j ≫ f :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ c.ι.app j) (hpb' j).isoPullback_hom_fst).trans (congr_app h j))
      _ = (c'.ι.app j ≫ hsq.isoPullback.hom) ≫ pullback.fst d.pt.hom f :=
          (congrArg (c'.ι.app j ≫ ·) hsq.isoPullback_hom_fst).symm.trans
            (Category.assoc _ _ _).symm
  · calc (β.hom.app j ≫ (Over.pullback f ⋙ Over.forget c'.pt).map (d.ι.app j)) ≫
          pullback.snd d.pt.hom f
        = (hpb' j).isoPullback.hom ≫ pullback.snd (G.obj j).hom f :=
          (Category.assoc _ _ _).trans (congrArg ((hpb' j).isoPullback.hom ≫ ·)
            (pullback.lift_snd _ _ _))
      _ = c'.ι.app j := IsPullback.isoPullback_hom_snd _
      _ = (c'.ι.app j ≫ hsq.isoPullback.hom) ≫ pullback.snd d.pt.hom f :=
          ((Category.comp_id _).symm.trans (congrArg (c'.ι.app j ≫ ·)
            hsq.isoPullback_hom_snd).symm).trans (Category.assoc _ _ _).symm

theorem preservesColimitsOfShape_pullback_of_isUniversalColimit [HasPullbacks C]
    [HasColimitsOfShape J C]
    (hU : ∀ {F : J ⥤ C} {c : Cocone F}, IsColimit c → IsUniversalColimit c)
    {X Y : C} (f : X ⟶ Y) : PreservesColimitsOfShape J (Over.pullback f) := by
  refine ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩
  have hc₀ := isColimitOfPreserves (Over.forget Y) hc
  let c₁ := (Over.forget X).mapCocone ((Over.pullback f).mapCocone c)
  have sq : ∀ {A B : C} (x : A ⟶ B) (h : B ⟶ Y) (k : A ⟶ Y) (hk : x ≫ h = k),
      IsPullback (pullback.lift (pullback.fst k f ≫ x) (pullback.snd k f)
        (by rw [Category.assoc, hk, pullback.condition])) (pullback.fst k f)
        (pullback.fst h f) x := by
    intro A B x h k hk
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback h f).flip
    subst hk
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (x ≫ h) f).flip
  obtain ⟨h⟩ := hU hc₀ c₁ ⟨fun j => pullback.fst (K.obj j).hom f,
      fun _ _ _ => pullback.lift_fst _ _ _⟩ (pullback.fst c.pt.hom f)
    (NatTrans.ext (funext fun _ => (pullback.lift_fst _ _ _).symm))
    (fun j k u => sq (K.map u).left (K.obj k).hom (K.obj j).hom (Over.w (K.map u)))
    (fun j => sq (c.ι.app j).left c.pt.hom (K.obj j).hom (Over.w (c.ι.app j)))
  exact ⟨isColimitOfReflects (Over.forget X) h⟩

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem IsPushout.hom_ext_of_isUniversalColimit {H : IsPushout f g h i}
    (hU : IsUniversalColimit (PushoutCocone.mk h i H.w))
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} [HasPullback αX f] {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z} {T : C} {f₁ f₂ : Z' ⟶ T}
    (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i)
    (h'_w : h' ≫ f₁ = h' ≫ f₂) (i'_w : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ := by
  let l := hi.lift (pullback.fst αX f ≫ h') (pullback.snd αX f ≫ g)
    (by simp only [Category.assoc, hh.toCommSq.w, pullback.condition_assoc, ← H.w])
  have hf : IsPullback (pullback.fst αX f) (pullback.snd αX f) αX f :=
    IsPullback.of_hasPullback αX f
  have hg : IsPullback l (pullback.snd αX f) αY g := by
    refine IsPullback.of_right' ?_ hi
    rw [← H.w]
    exact IsPullback.paste_horiz hf hh
  have w : CommSq (pullback.fst αX f) l h' i' := ⟨by simp only [IsPullback.lift_fst, l]⟩
  obtain ⟨hc⟩ := hU w.cocone
    ⟨by rintro (_ | _ | _); exacts [pullback.snd αX f, αX, αY], by
      rintro _ _ (_ | _ | _)
      · simp
      exacts [hf.w, hg.w]⟩ αZ
    (by
      ext (_ | _ | _)
      · exact (hf.w_assoc h).symm.trans ((congrArg (pullback.fst αX f ≫ ·) hh.w).symm.trans
          (Category.assoc _ _ _).symm)
      exacts [hh.w.symm, hi.w.symm])
    (by
      rintro _ _ (_ | _ | _)
      · simpa using IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
      exacts [hf, hg])
    (by
      rintro (_ | _ | _)
      · exact hf.paste_horiz hh
      exacts [hh, hi])
  exact (IsPushout.of_isColimit hc).hom_ext h'_w i'_w

end CategoryTheory
