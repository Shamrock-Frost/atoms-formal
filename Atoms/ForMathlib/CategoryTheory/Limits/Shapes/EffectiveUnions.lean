import Atoms.ForMathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.MorphismProperty.Limits

universe v u

namespace CategoryTheory

open Limits

class HasEffectiveUnions (C : Type u) [Category.{v} C] : Prop where
  mono_pushoutDesc {P Y Z W : C} {f : P ⟶ Y} {g : P ⟶ Z} {a : Y ⟶ W} {b : Z ⟶ W}
    [HasPushout f g] (h : IsPullback f g a b) [Mono a] [Mono b] : Mono (pushout.desc a b h.w)

variable {C : Type u} [Category.{v} C]

private theorem eq_comp_of_comp_eq_comp [HasPullbacks C] {P Y Z W Q : C} {f : P ⟶ Y}
    {g : P ⟶ Z} {h : Y ⟶ Q} {i : Z ⟶ Q} {a : Y ⟶ W} {b : Z ⟶ W} {d : Q ⟶ W}
    (H : IsPushout f g h i) (hU : IsUniversalColimit (PushoutCocone.mk h i H.w))
    (hpb : IsPullback f g a b) [Mono a] (hda : h ≫ d = a) (hdb : i ≫ d = b) {S : C}
    (k : S ⟶ Y) (w : S ⟶ Q) (hw : w ≫ d = k ≫ a) : w = k ≫ h := by
  refine H.hom_ext_of_isUniversalColimit hU (IsPullback.of_hasPullback w h)
    (IsPullback.of_hasPullback w i) ?_ ?_
  · rw [pullback.condition, ← Category.assoc]
    congr 1
    refine (cancel_mono a).1 ?_
    calc pullback.snd w h ≫ a
        = pullback.snd w h ≫ h ≫ d := by rw [hda]
      _ = pullback.fst w h ≫ w ≫ d := by
          rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = (pullback.fst w h ≫ k) ≫ a := by rw [hw, Category.assoc]
  · obtain ⟨δ, hδf, hδg⟩ := hpb.exists_lift (pullback.fst w i ≫ k) (pullback.snd w i) (by
      rw [Category.assoc, ← hw, ← Category.assoc, pullback.condition, Category.assoc, hdb])
    rw [pullback.condition, ← hδg, Category.assoc, ← H.w, ← Category.assoc, hδf,
      Category.assoc]

theorem hasEffectiveUnions_of_isUniversalColimit [HasPullbacks C]
    (hU : ∀ {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
      (H : IsPushout f g h i), IsUniversalColimit (PushoutCocone.mk h i H.w)) :
    HasEffectiveUnions C where
  mono_pushoutDesc {P Y Z W f g a b} _ hpb _ _ := by
    let H := IsPushout.of_hasPushout f g
    constructor
    intro T u v huv
    refine H.hom_ext_of_isUniversalColimit (hU H) (IsPullback.of_hasPullback u _)
      (IsPullback.of_hasPullback u _) ?_ ?_
    · rw [pullback.condition, eq_comp_of_comp_eq_comp H (hU H) hpb (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _) _ (pullback.fst u (pushout.inl f g) ≫ v) (by
          rw [Category.assoc, ← huv, ← Category.assoc, pullback.condition, Category.assoc,
            pushout.inl_desc])]
    · rw [pullback.condition, eq_comp_of_comp_eq_comp H.flip (hU H.flip) hpb.flip
        (pushout.inr_desc _ _ _) (pushout.inl_desc _ _ _) _
        (pullback.fst u (pushout.inr f g) ≫ v) (by
          rw [Category.assoc, ← huv, ← Category.assoc, pullback.condition, Category.assoc,
            pushout.inr_desc])]

theorem mono_of_isPushout_of_isPullback [HasPushouts C] [HasEffectiveUnions C]
    [(MorphismProperty.monomorphisms C).IsStableUnderCobaseChange]
    {X₀ X₁ X₂ X Y₀ Y₁ Y₂ Y : C} {f : X₀ ⟶ X₁} {g : X₀ ⟶ X₂} {a : X₁ ⟶ X} {b : X₂ ⟶ X}
    (hX : IsPushout f g a b) {f' : Y₀ ⟶ Y₁} {g' : Y₀ ⟶ Y₂} {a' : Y₁ ⟶ Y} {b' : Y₂ ⟶ Y}
    (hY : IsPushout f' g' a' b') {u₀ : X₀ ⟶ Y₀} {u₁ : X₁ ⟶ Y₁} {u₂ : X₂ ⟶ Y₂}
    (hpb : IsPullback f u₀ u₁ f') [hf' : Mono f'] [hu₁ : Mono u₁] [hu₂ : Mono u₂]
    (hg : g ≫ u₂ = u₀ ≫ g')
    {u : X ⟶ Y} (ha : a ≫ u = u₁ ≫ a') (hb : b ≫ u = u₂ ≫ b') : Mono u := by
  have hZ := IsPushout.of_hasPushout f u₀
  have hm : Mono (pushout.desc u₁ f' hpb.w) := HasEffectiveUnions.mono_pushoutDesc hpb
  have hW := IsPushout.of_hasPushout (pushout.inr f u₀) g'
  have hbig : IsPushout f (g ≫ u₂) (pushout.inl f u₀ ≫ pushout.inl (pushout.inr f u₀) g')
      (pushout.inr (pushout.inr f u₀) g') := by
    rw [hg]
    exact hZ.paste_vert hW
  have hv := IsPushout.of_top' hbig hX
  have : Mono (hX.desc (pushout.inl f u₀ ≫ pushout.inl (pushout.inr f u₀) g')
      (u₂ ≫ pushout.inr (pushout.inr f u₀) g') (hbig.w.trans (Category.assoc _ _ _))) :=
    (MorphismProperty.monomorphisms C).of_isPushout hv hu₂
  have hY' : IsPushout (pushout.inr f u₀ ≫ pushout.desc u₁ f' hpb.w) g' a' b' := by
    rwa [pushout.inr_desc]
  have hn := IsPushout.of_left' hY' hW
  have : Mono (hW.desc (pushout.desc u₁ f' hpb.w ≫ a') b'
      ((Category.assoc _ _ _).symm.trans hY'.w)) :=
    (MorphismProperty.monomorphisms C).of_isPushout hn.flip hm
  convert mono_comp (hX.desc (pushout.inl f u₀ ≫ pushout.inl (pushout.inr f u₀) g')
      (u₂ ≫ pushout.inr (pushout.inr f u₀) g') (hbig.w.trans (Category.assoc _ _ _)))
    (hW.desc (pushout.desc u₁ f' hpb.w ≫ a') b' ((Category.assoc _ _ _).symm.trans hY'.w)) using 1
  refine hX.hom_ext ?_ ?_
  · rw [ha, hX.inl_desc_assoc, Category.assoc, hW.inl_desc, pushout.inl_desc_assoc]
  · rw [hb, hX.inr_desc_assoc, Category.assoc, hW.inr_desc]

end CategoryTheory
