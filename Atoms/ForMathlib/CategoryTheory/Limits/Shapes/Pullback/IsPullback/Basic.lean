import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category C]

theorem of_prod_snd_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct X A]
    [HasBinaryProduct X B] :
    IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd := by
  have w : (prod.snd : X ⨯ A ⟶ A) ≫ f = prod.map (𝟙 X) f ≫ prod.snd := by simp
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s ↦ prod.lift (s.snd ≫ prod.fst) s.fst)
    (fun s ↦ prod.lift_snd _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · apply prod.hom_ext
    · rw [Category.assoc, prod.map_fst, ← Category.assoc, prod.lift_fst]
      simp
    · rw [Category.assoc, prod.map_snd, ← Category.assoc, prod.lift_snd]
      exact s.condition
  · apply prod.hom_ext
    · rw [prod.lift_fst, ← h₂, Category.assoc, prod.map_fst]
      simp
    · rw [prod.lift_snd, h₁]

open MonoidalCategory in
theorem of_snd_whiskerLeft [CartesianMonoidalCategory C] (X : C) {A B : C}
    (f : A ⟶ B) : IsPullback (CartesianMonoidalCategory.snd X A) (X ◁ f) f
      (CartesianMonoidalCategory.snd X B) := by
  have w : CartesianMonoidalCategory.snd X A ≫ f =
      (X ◁ f) ≫ CartesianMonoidalCategory.snd X B :=
    (CartesianMonoidalCategory.whiskerLeft_snd X f).symm
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s ↦ CartesianMonoidalCategory.lift (s.snd ≫ CartesianMonoidalCategory.fst X B) s.fst)
    (fun s ↦ CartesianMonoidalCategory.lift_snd _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [s.condition]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.lift_fst, ← h₂, Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_fst]
    · rw [CartesianMonoidalCategory.lift_snd, h₁]

end CategoryTheory.IsPullback

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

private theorem app_comp_app_eq_id (K : C ⥤ C) (η : 𝟭 C ⟶ K) (σ : K ⟶ 𝟭 C)
    (hησ : η ≫ σ = 𝟙 (𝟭 C)) (X : C) : η.app X ≫ σ.app X = 𝟙 X := by
  simpa using congrArg (fun τ => NatTrans.app τ X) hησ

private theorem app_retraction_comp_eq (K : C ⥤ C) (η : 𝟭 C ⟶ K) (σ : K ⟶ 𝟭 C)
    (hησ : η ≫ σ = 𝟙 (𝟭 C)) {X Y Z : C} (m : X ⟶ Y) {a : Z ⟶ K.obj X} {b : Z ⟶ Y}
    (h : a ≫ K.map m = b ≫ η.app Y) : (a ≫ σ.app X) ≫ m = b := by
  have hσ : σ.app X ≫ m = K.map m ≫ σ.app Y := (σ.naturality m).symm
  rw [Category.assoc, hσ, ← Category.assoc, h, Category.assoc,
    app_comp_app_eq_id K η σ hησ Y, Category.comp_id]

private theorem app_retraction_comp_app_eq (K : C ⥤ C) (η : 𝟭 C ⟶ K) (σ : K ⟶ 𝟭 C)
    (hησ : η ≫ σ = 𝟙 (𝟭 C)) {X Y Z : C} (m : X ⟶ Y) [Mono (K.map m)] {a : Z ⟶ K.obj X}
    {b : Z ⟶ Y} (h : a ≫ K.map m = b ≫ η.app Y) : (a ≫ σ.app X) ≫ η.app X = a := by
  rw [← cancel_mono (K.map m), Category.assoc]
  have hη : η.app X ≫ K.map m = m ≫ η.app Y := (η.naturality m).symm
  rw [hη, ← Category.assoc, app_retraction_comp_eq K η σ hησ m h, h]

theorem isPullback_app_of_retraction (K : C ⥤ C) (η : 𝟭 C ⟶ K) (σ : K ⟶ 𝟭 C)
    (hησ : η ≫ σ = 𝟙 (𝟭 C)) {X Y : C} (m : X ⟶ Y) [Mono (K.map m)] :
    IsPullback (η.app X) m (K.map m) (η.app Y) := by
  have w : CommSq (η.app X) m (K.map m) (η.app Y) := ⟨(η.naturality m).symm⟩
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk w.w (fun s => s.fst ≫ σ.app X)
    (fun s => app_retraction_comp_app_eq K η σ hησ m s.condition)
    (fun s => app_retraction_comp_eq K η σ hησ m s.condition) ?_)
  intro s d hd _
  rw [← hd, Category.assoc, app_comp_app_eq_id K η σ hησ X]
  exact (Category.comp_id d).symm

theorem IsPullback.of_retractions {A B C' D : C} {i : A ⟶ B} {j : A ⟶ C'} {k : C' ⟶ D}
    {l : B ⟶ D} (w : i ≫ l = j ≫ k) {r : C' ⟶ A} {q : D ⟶ C'} {p : D ⟶ B} (hr : j ≫ r = 𝟙 A)
    (hq : k ≫ q = 𝟙 C') (hp : l ≫ p = 𝟙 B) (hpk : k ≫ p = r ≫ i) : IsPullback i j l k := by
  have : Mono k := (SplitMono.mk q hq).mono
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w (fun s => s.snd ≫ r)
    (fun s => ?_) (fun s => ?_) (fun s m _ h => by rw [← h, Category.assoc, hr, Category.comp_id]))
  · rw [Category.assoc, ← hpk, ← Category.assoc, ← s.condition, Category.assoc, hp,
      Category.comp_id]
  · rw [← cancel_mono k, Category.assoc, Category.assoc, ← w, ← Category.assoc r, ← hpk,
      Category.assoc, ← Category.assoc s.snd, ← s.condition, Category.assoc, ← Category.assoc l,
      hp, Category.id_comp]

section MapIso

variable {C D : Type*} [Category C] [Category D]

theorem Functor.isIso_map_of_isPushout (G : C ⥤ D) {X₁ X₂ X₃ X₄ Z : C} {t : X₁ ⟶ X₂}
    {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (s : IsPushout t l r b)
    [PreservesColimit (span t l) G] (ht : IsIso (G.map t)) (φ : X₄ ⟶ Z)
    (h : IsIso (G.map (b ≫ φ))) : IsIso (G.map φ) :=
  have := (s.map G).isIso_inr_of_isIso
  (isIso_comp_left_iff (G.map b) _).1 (G.map_comp b φ ▸ h)

theorem Functor.isIso_map_of_isPushout' (G : C ⥤ D) {X₁ X₂ X₃ X₄ Z : C} {t : X₁ ⟶ X₂}
    {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (s : IsPushout t l r b)
    [PreservesColimit (span t l) G] (hl : IsIso (G.map l)) (φ : X₄ ⟶ Z)
    (h : IsIso (G.map (r ≫ φ))) : IsIso (G.map φ) :=
  have := preservesPushout_symmetry G t l
  G.isIso_map_of_isPushout s.flip hl φ h

end MapIso

end CategoryTheory
