import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.EffectiveUnions
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

universe v u

namespace CategoryTheory.Adhesive

open Limits

variable {C : Type u} [Category.{v} C] [Adhesive C]

instance hasEffectiveUnions : HasEffectiveUnions C where
  mono_pushoutDesc {P Y Z W} {f g a b} _ h _ _ := by
    have e : pushout.desc a b h.w =
        pushout.map f g (pullback.fst a b) (pullback.snd a b) (𝟙 _) (𝟙 _) h.isoPullback.hom
          (by simp) (by simp) ≫ pushout.desc a b pullback.condition := by
      refine pushout.hom_ext ?_ ?_
      · rw [pushout.inl_desc, pushout.inl_desc_assoc, Category.id_comp, pushout.inl_desc]
      · rw [pushout.inr_desc, pushout.inr_desc_assoc, Category.id_comp, pushout.inr_desc]
    rw [e]
    infer_instance

end CategoryTheory.Adhesive

namespace CategoryTheory.Functor.PushoutObjObj

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃] [Adhesive C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}

theorem mono_map_app_of_mono_ι (sq : F.PushoutObjObj f₁ f₂) [Mono sq.ι]
    [Mono ((F.map f₁).app X₂)] : Mono ((F.map f₁).app Y₂) := by
  have : Mono sq.inr := Adhesive.mono_of_isPushout_of_mono_left sq.isPushout
  exact sq.inr_ι ▸ mono_comp sq.inr sq.ι

theorem mono_obj_map_of_mono_ι (sq : F.PushoutObjObj f₁ f₂) [Mono sq.ι]
    [Mono ((F.obj X₁).map f₂)] : Mono ((F.obj Y₁).map f₂) :=
  have : Mono sq.flip.ι := inferInstanceAs (Mono sq.ι)
  have : Mono ((F.flip.map f₂).app X₁) := inferInstanceAs (Mono ((F.obj X₁).map f₂))
  mono_map_app_of_mono_ι sq.flip

end CategoryTheory.Functor.PushoutObjObj
