import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C]

theorem isPullback_pullback_map {E' E F' F X' X S' S O : C}
    {eE : E' ⟶ E} {fE' : E' ⟶ F'} {fE : E ⟶ F} {eF : F' ⟶ F} (hE : IsPullback eE fE' fE eF)
    {yX : X' ⟶ X} {gX' : X' ⟶ S'} {gX : X ⟶ S} {yS : S' ⟶ S} (hX : IsPullback yX gX' gX yS)
    {πE' : E' ⟶ X'} {πE : E ⟶ X} {πF' : F' ⟶ S'} {πF : F ⟶ S}
    (h₁ : eE ≫ πE = πE' ≫ yX) (h₂ : fE' ≫ πF' = πE' ≫ gX') (h₃ : fE ≫ πF = πE ≫ gX)
    (h₄ : eF ≫ πF = πF' ≫ yS) {x : O ⟶ X'} {x₁ : O ⟶ X} {x₂ : O ⟶ S'} {x₃ : O ⟶ S}
    (hx₁ : x ≫ yX = x₁) (hx₂ : x ≫ gX' = x₂) (hx₃ : x₁ ≫ gX = x₃) :
    IsPullback (pullback.map πE' x πE x₁ eE (𝟙 O) yX h₁.symm (by rw [Category.id_comp, hx₁]))
      (pullback.map πE' x πF' x₂ fE' (𝟙 O) gX' h₂.symm (by rw [Category.id_comp, hx₂]))
      (pullback.map πE x₁ πF x₃ fE (𝟙 O) gX h₃.symm (by rw [Category.id_comp, hx₃]))
      (pullback.map πF' x₂ πF x₃ eF (𝟙 O) yS h₄.symm
        (by rw [Category.id_comp, ← hx₃, ← hx₁, ← hx₂, Category.assoc, Category.assoc, hX.w])) := by
  have hs (s : PullbackCone
      (pullback.map πE x₁ πF x₃ fE (𝟙 O) gX h₃.symm (by rw [Category.id_comp, hx₃]))
      (pullback.map πF' x₂ πF x₃ eF (𝟙 O) yS h₄.symm (by
        rw [Category.id_comp, ← hx₃, ← hx₁, ← hx₂, Category.assoc, Category.assoc, hX.w]))) :
      (s.fst ≫ pullback.fst _ _) ≫ fE = (s.snd ≫ pullback.fst _ _) ≫ eF ∧
        s.fst ≫ pullback.snd _ _ = s.snd ≫ pullback.snd _ _ := by
    refine ⟨?_, ?_⟩
    · have h := congrArg (· ≫ pullback.fst _ _) s.condition
      simp only [Category.assoc, pullback.lift_fst] at h
      simpa only [Category.assoc] using h
    · have h := congrArg (· ≫ pullback.snd _ _) s.condition
      simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using h
  refine ⟨⟨pullback.hom_ext ?_ ?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ pullback.lift
    (hE.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) (hs s).1)
    (s.fst ≫ pullback.snd _ _) (hX.hom_ext ?_ ?_)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_)⟩⟩
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hE.w]
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  · simp only [Category.assoc, ← h₁, IsPullback.lift_fst_assoc, hx₁, pullback.condition]
  · simp only [Category.assoc, ← h₂, IsPullback.lift_snd_assoc, hx₂, pullback.condition]
    simp only [← Category.assoc, (hs s).2]
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, (hs s).2]
  · refine pullback.hom_ext (hE.hom_ext ?_ ?_) ?_
    · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_fst, ← hm₁]
    · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_snd, ← hm₂]
    · simp only [pullback.lift_snd, ← hm₁, Category.assoc, Category.comp_id]

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

noncomputable def arrowIsoPushoutDescSymm {A B D Z : C} (f : A ⟶ B)
    (g : A ⟶ D) (a : B ⟶ Z) (b : D ⟶ Z) (w : f ≫ a = g ≫ b)
    [HasPushout f g] [HasPushout g f] :
    Arrow.mk (pushout.desc b a w.symm) ≅ Arrow.mk (pushout.desc a b w) :=
  Arrow.isoMk (pushoutSymmetry g f) (Iso.refl _) (pushout.hom_ext
    (by simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id,
      inl_comp_pushoutSymmetry_hom_assoc, pushout.inl_desc, pushout.inr_desc])
    (by simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id,
      inr_comp_pushoutSymmetry_hom_assoc, pushout.inl_desc, pushout.inr_desc]))

end CategoryTheory.Limits
