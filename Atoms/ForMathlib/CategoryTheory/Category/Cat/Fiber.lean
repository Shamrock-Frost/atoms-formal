import Atoms.ForMathlib.CategoryTheory.Category.Cat.Limit
import Atoms.ForMathlib.CategoryTheory.FiberedCategory.Fiber

namespace CategoryTheory.Cat

open Limits _root_.CategoryTheory.Functor

universe u

section Pullback

variable {A' A B' B : Cat.{u, u}} {w : A' ⟶ A} {u' : A' ⟶ B'} {u : A ⟶ B} {v : B' ⟶ B}

theorem isEquivalence_mapOfSquare_of_isPullback (h : IsPullback w u' u v) (b' : B') :
    (Fiber.mapOfSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
      (congrArg Cat.Hom.toFunctor h.w) b').IsEquivalence where
  faithful := ⟨fun {a₁ a₂} φ₁ φ₂ e => Fiber.hom_ext (Cat.hom_ext_of_isPullback h
    (by simpa using congrArg Fiber.fiberInclusion.map e)
    (by rw [Fiber.map_fiberInclusion_map, Fiber.map_fiberInclusion_map]))⟩
  full := ⟨fun {a₁ a₂} ψ => by
    obtain ⟨γ, hγ₁, hγ₂⟩ := Cat.exists_hom_of_isPullback h (Fiber.fiberInclusion.map ψ)
      (eqToHom ((Fiber.obj_fiberInclusion_obj a₁).trans (Fiber.obj_fiberInclusion_obj a₂).symm))
      (by
        simp only [eqToHom_map, eqToHom_trans]
        exact Fiber.map_fiberInclusion_map ψ)
    have : u'.toFunctor.IsHomLift (𝟙 b') γ :=
      IsHomLift.of_fac _ _ _ (Fiber.obj_fiberInclusion_obj a₁) (Fiber.obj_fiberInclusion_obj a₂)
        (by simp [hγ₂])
    exact ⟨Fiber.homMk u'.toFunctor b' γ, Fiber.hom_ext hγ₁⟩⟩
  essSurj := ⟨fun x => by
    obtain ⟨a', ha₁, ha₂⟩ := Cat.exists_obj_of_isPullback h (Fiber.fiberInclusion.obj x) b'
      (Fiber.obj_fiberInclusion_obj x)
    exact ⟨Fiber.mk ha₂, ⟨eqToIso (Fiber.fiberInclusion_obj_inj ha₁)⟩⟩⟩

end Pullback

theorem isPullback_fiberInclusion_fromPUnit {A B : Cat.{u, u}} (u : A ⟶ B) (b : B) :
    IsPullback (Fiber.fiberInclusion : Fiber u.toFunctor b ⥤ A).toCatHom
      ((Functor.const (Fiber u.toFunctor b)).obj
        (⟨⟨⟩⟩ : Discrete PUnit.{u + 1})).toCatHom u
      (Functor.fromPUnit.{u} b).toCatHom := by
  refine Cat.isPullback_of_elementwise (Cat.Hom.ext Fiber.fiberInclusion_comp_eq_const)
    (fun e _ => Fiber.fiberInclusion_obj_inj e) (fun x _ e => ⟨Fiber.mk e, rfl, rfl⟩)
    (fun e _ => Fiber.hom_ext e) (fun {p₁ p₂} α _ e => ?_)
  have : u.toFunctor.IsHomLift (𝟙 b) α :=
    IsHomLift.of_fac' _ _ _ (Fiber.obj_fiberInclusion_obj p₁) (Fiber.obj_fiberInclusion_obj p₂) e
  exact ⟨Fiber.homMk u.toFunctor b α, rfl, rfl⟩

theorem isPullback_fiberInclusion_mapOfSquare_comp {A B C : Cat.{u, u}} (p : A ⟶ B) (q : B ⟶ C)
    (c : C) :
    IsPullback (Fiber.fiberInclusion : Fiber (p ≫ q).toFunctor c ⥤ A).toCatHom
      (Fiber.mapOfSquare p.toFunctor (p ≫ q).toFunctor q.toFunctor (𝟭 C) rfl c).toCatHom p
      (Fiber.fiberInclusion : Fiber q.toFunctor c ⥤ B).toCatHom := by
  refine Cat.isPullback_of_elementwise rfl (fun e _ => Fiber.fiberInclusion_obj_inj e)
    (fun x y e => ⟨Fiber.mk (p := (p ≫ q).toFunctor) (a := x)
      ((congrArg q.toFunctor.obj e).trans (Fiber.obj_fiberInclusion_obj y)), rfl,
      Fiber.fiberInclusion_obj_inj e⟩) (fun e _ => Fiber.hom_ext e) (fun {x₁ x₂} α β e => ?_)
  have e' : p.toFunctor.map α = 𝟙 _ ≫ Fiber.fiberInclusion.map β ≫ 𝟙 _ := e
  rw [Category.id_comp, Category.comp_id] at e'
  have : (p ≫ q).toFunctor.IsHomLift (𝟙 c) α :=
    IsHomLift.of_fac' _ _ _ (Fiber.obj_fiberInclusion_obj x₁) (Fiber.obj_fiberInclusion_obj x₂)
      ((congrArg q.toFunctor.map e').trans ((Fiber.map_fiberInclusion_map β).trans
        (by rw [Category.id_comp, eqToHom_trans]; rfl)))
  exact ⟨Fiber.homMk (p ≫ q).toFunctor c α, rfl, Fiber.hom_ext e'⟩

section Under

instance isIso_underPostForget (T : Cat.{u, u}) {X : T} (f : Under X) :
    IsIso (Under.post (X := f) (Under.forget X)).toCatHom :=
  ⟨(Under.iteratedSliceBackward f).toCatHom,
    Cat.Hom.ext (Under.post_forget_comp_iteratedSliceBackward f),
    Cat.Hom.ext (Under.iteratedSliceBackward_comp_post_forget f)⟩

theorem isPullback_underPost_underPost {A B : Cat.{u, u}} (u : A ⟶ B) {a : A} (z : Under a) :
    IsPullback (Under.post (X := z) (Under.forget a)).toCatHom
      (Under.post (X := z) (Under.post u.toFunctor)).toCatHom
      (Under.post (X := z.right) u.toFunctor).toCatHom
      (Under.post (X := (Under.post u.toFunctor).obj z)
        (Under.forget (u.toFunctor.obj a))).toCatHom :=
  @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (isIso_underPostForget A z)
    (isIso_underPostForget B ((Under.post u.toFunctor).obj z)) ⟨rfl⟩

private theorem under_hom_comp_eqToHom {T : Type u} [Category.{u} T] {X : T} {y y' : Under X}
    (H : y = y') : y.hom ≫ eqToHom (congrArg Under.right H) = y'.hom := by
  subst H
  simp

theorem isPullback_underPost_of_isPullback {A' A B' B : Cat.{u, u}} {w : A' ⟶ A}
    {u' : A' ⟶ B'} {u : A ⟶ B} {v : B' ⟶ B} (h : IsPullback w u' u v) (a' : A') :
    IsPullback (Under.post (X := a') w.toFunctor).toCatHom
      (Under.post (X := a') u'.toFunctor).toCatHom
      (Under.post (X := w.toFunctor.obj a') u.toFunctor).toCatHom
      (Under.post (X := u'.toFunctor.obj a') v.toFunctor ⋙
        Under.map (eqToHom (Cat.obj_eq_of_isPullback h a'))).toCatHom := by
  have e := Cat.obj_eq_of_isPullback h
  have sq : ∀ {x y : A'} (f : x ⟶ y), u.toFunctor.map (w.toFunctor.map f) =
      eqToHom (e x) ≫ v.toFunctor.map (u'.toFunctor.map f) ≫ eqToHom (e y).symm := fun f => by
    have := Functor.congr_hom (congrArg Cat.Hom.toFunctor h.w) f
    simpa using this
  have comm : Under.post (X := a') w.toFunctor ⋙ Under.post u.toFunctor =
      Under.post u'.toFunctor ⋙ Under.post v.toFunctor ⋙ Under.map (eqToHom (e a')) := by
    refine Functor.ext (fun k => StructuredArrow.obj_ext _ _ (e k.right) ?_) (fun k k' φ => ?_)
    · exact (by rw [sq]; simp : u.toFunctor.map (w.toFunctor.map k.hom) ≫ eqToHom (e k.right) =
        eqToHom (e a') ≫ v.toFunctor.map (u'.toFunctor.map k.hom))
    · ext
      simp only [Under.comp_right, Under.eqToHom_right]
      exact sq φ.right
  refine Cat.isPullback_of_elementwise (Cat.Hom.ext comm)
    (fun {p₁ p₂} h₁ h₂ => ?_) (fun x y E => ?_) (fun H₁ H₂ => Under.UnderMorphism.ext
      (Cat.hom_ext_of_isPullback h (congrArg Under.Hom.right H₁) (congrArg Under.Hom.right H₂)))
    (fun {p₁ p₂ : Under a'}
      (α : (Under.post w.toFunctor).obj p₁ ⟶ (Under.post w.toFunctor).obj p₂)
      (β : (Under.post u'.toFunctor).obj p₁ ⟶ (Under.post u'.toFunctor).obj p₂)
      (E : (Under.post u.toFunctor).map α = eqToHom (Functor.congr_obj comm p₁) ≫
        (Under.post v.toFunctor ⋙ Under.map (eqToHom (e a'))).map β ≫
          eqToHom (Functor.congr_obj comm p₂).symm) => ?_)
  · have hr := Cat.obj_ext_of_isPullback h (congrArg Under.right h₁) (congrArg Under.right h₂)
    refine StructuredArrow.obj_ext _ _ hr (Cat.hom_ext_of_isPullback h ?_ ?_)
    · rw [Functor.map_comp, Functor.id_map, eqToHom_map]
      exact under_hom_comp_eqToHom h₁
    · rw [Functor.map_comp, Functor.id_map, eqToHom_map]
      exact under_hom_comp_eqToHom h₂
  · have Er : u.toFunctor.obj x.right = v.toFunctor.obj y.right := congrArg Under.right E
    have Eh : u.toFunctor.map x.hom ≫ eqToHom Er = eqToHom (e a') ≫ v.toFunctor.map y.hom :=
      under_hom_comp_eqToHom E
    have Eh' : u.toFunctor.map x.hom =
        eqToHom (e a') ≫ v.toFunctor.map y.hom ≫ eqToHom Er.symm := by
      rw [← Category.assoc, ← Eh]
      simp
    obtain ⟨a'', h₁, h₂⟩ := Cat.exists_obj_of_isPullback h x.right y.right Er
    obtain ⟨γ, hγ₁, hγ₂⟩ := Cat.exists_hom_of_isPullback h (p₁ := a') (p₂ := a'')
      (x.hom ≫ eqToHom h₁.symm) (y.hom ≫ eqToHom h₂.symm) (by simp [Eh', eqToHom_map])
    refine ⟨Under.mk γ, StructuredArrow.obj_ext _ _ h₁ ?_, StructuredArrow.obj_ext _ _ h₂ ?_⟩
    · exact (by rw [hγ₁]; simp : w.toFunctor.map γ ≫ eqToHom h₁ = x.hom)
    · exact (by rw [hγ₂]; simp : u'.toFunctor.map γ ≫ eqToHom h₂ = y.hom)
  · have Er : u.toFunctor.map α.right = eqToHom (e p₁.right) ≫ v.toFunctor.map β.right ≫
        eqToHom (e p₂.right).symm := by
      have := congrArg Under.Hom.right E
      simp only [Under.comp_right, Under.eqToHom_right] at this
      exact this
    obtain ⟨γ₀, hγ₁, hγ₂⟩ := Cat.exists_hom_of_isPullback h (p₁ := p₁.right) (p₂ := p₂.right)
      α.right β.right Er
    have hw : p₁.hom ≫ γ₀ = p₂.hom := Cat.hom_ext_of_isPullback h
      (by rw [Functor.map_comp, hγ₁]; exact Under.w α)
      (by rw [Functor.map_comp, hγ₂]; exact Under.w β)
    exact ⟨Under.homMk γ₀ hw, Under.UnderMorphism.ext hγ₁, Under.UnderMorphism.ext hγ₂⟩

end Under

end CategoryTheory.Cat
