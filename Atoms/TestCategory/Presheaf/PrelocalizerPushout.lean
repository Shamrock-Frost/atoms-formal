import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Atoms.TestCategory.Presheaf.Aspherical
import Atoms.TestCategory.Presheaf.ElementsColimit
import Atoms.TestCategory.BasicLocalizer.GrothendieckConstruction

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

section Fibre

variable {A} {F₀ F₁ F₂ F' : Aᵒᵖ ⥤ Type u} {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'}
  {ε₂ : F₂ ⟶ F'}

variable (w : φ₁ ≫ ε₁ = φ₂ ≫ ε₂) (a : A) (s : F'.obj (op a))

abbrev pushoutFiberFunctor : AsSmall.{u} WalkingSpan ⥤ Type u :=
  colimitFiberFunctor A (smallSpan φ₁ φ₂) ((PushoutCocone.mk ε₁ ε₂ w).whisker AsSmall.down) a s

abbrev PushoutFiber : Type u := (pushoutFiberFunctor w a s).Elements

variable {w a s}

theorem pushoutFiber_hom_subsingleton (p q : PushoutFiber w a s) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => CategoryOfElements.ext _ _ _ (ULift.ext _ _ (Subsingleton.elim _ _))⟩

def pushoutFiberHomOfEq {j : AsSmall.{u} WalkingSpan} {x y : (pushoutFiberFunctor w a s).obj j}
    (e : x.1 = y.1) :
    (pushoutFiberFunctor w a s).elementsMk j x ⟶ (pushoutFiberFunctor w a s).elementsMk j y :=
  eqToHom (congrArg (Sigma.mk j) (Subtype.ext e))

def pushoutFiberHomFst {x : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.zero⟩}
    {y : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.left⟩} (e : φ₁.app (op a) x.1 = y.1) :
    (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.zero⟩ x ⟶
      (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.left⟩ y :=
  ⟨⟨WalkingSpan.Hom.fst⟩, Subtype.ext e⟩

def pushoutFiberHomSnd {x : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.zero⟩}
    {y : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.right⟩} (e : φ₂.app (op a) x.1 = y.1) :
    (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.zero⟩ x ⟶
      (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.right⟩ y :=
  ⟨⟨WalkingSpan.Hom.snd⟩, Subtype.ext e⟩

theorem pushoutFiber_fst_eq {x : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.zero⟩}
    {y : (pushoutFiberFunctor w a s).obj ⟨WalkingSpan.left⟩}
    (f : (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.zero⟩ x ⟶
      (pushoutFiberFunctor w a s).elementsMk ⟨WalkingSpan.left⟩ y) :
    φ₁.app (op a) x.1 = y.1 := by
  obtain ⟨⟨g⟩, hg⟩ := f
  cases g
  exact congrArg Subtype.val hg

theorem pushoutFiber_id_eq {j : WalkingSpan} {x y : (pushoutFiberFunctor w a s).obj ⟨j⟩}
    (f : (pushoutFiberFunctor w a s).elementsMk ⟨j⟩ x ⟶
      (pushoutFiberFunctor w a s).elementsMk ⟨j⟩ y) : x.1 = y.1 := by
  obtain ⟨g, hg⟩ := f
  obtain rfl : g = 𝟙 _ := ULift.ext _ _ (Subsingleton.elim _ _)
  rw [CategoryTheory.Functor.map_id] at hg
  exact congrArg Subtype.val hg

variable (a s)

noncomputable def pushoutFiberLower (h : IsPushout φ₁ φ₂ ε₁ ε₂) [Mono φ₁]
    {p₀ : F₂.obj (op a)} (hp : ε₂.app (op a) p₀ = s) :
    PushoutFiber h.w a s ⥤ PushoutFiber h.w a s where
  obj p := match p with
    | ⟨⟨WalkingSpan.left⟩, x⟩ =>
      ⟨⟨WalkingSpan.zero⟩, ⟨(FunctorToTypes.exists_app_eq_of_isPushout a s h hp x.1 x.2).choose,
        (congrArg (ε₁.app (op a))
          (FunctorToTypes.exists_app_eq_of_isPushout a s h hp x.1 x.2).choose_spec.1).trans x.2⟩⟩
    | p => p
  map {p q} f := by
    rcases p with ⟨⟨_ | _ | _⟩, x⟩ <;> rcases q with ⟨⟨_ | _ | _⟩, y⟩ <;>
      rcases f with ⟨⟨g⟩, hg⟩ <;> cases g
    · exact ⟨⟨WidePushoutShape.Hom.id _⟩, hg⟩
    · refine pushoutFiberHomOfEq ?_
      refine injective_of_mono (φ₁.app (op a)) ?_
      exact (pushoutFiber_fst_eq ⟨⟨WalkingSpan.Hom.fst⟩, hg⟩).trans
        (FunctorToTypes.exists_app_eq_of_isPushout a s h hp y.1 y.2).choose_spec.1.symm
    · exact ⟨⟨WalkingSpan.Hom.snd⟩, hg⟩
    · refine pushoutFiberHomOfEq ?_
      have e : x.1 = y.1 := pushoutFiber_id_eq (w := h.w) (a := a) (s := s)
        (j := WalkingSpan.left) (x := x) (y := y) ⟨⟨WidePushoutShape.Hom.id _⟩, hg⟩
      obtain ⟨y, hy⟩ := y
      obtain rfl : x.1 = y := e
      rfl
    · exact ⟨⟨WidePushoutShape.Hom.id _⟩, hg⟩
  map_id _ := (pushoutFiber_hom_subsingleton _ _).elim _ _
  map_comp _ _ := (pushoutFiber_hom_subsingleton _ _).elim _ _

namespace BasicLocalizer

theorem aspherical_pushoutFiber_of_mem_range (h : IsPushout φ₁ φ₂ ε₁ ε₂) [Mono φ₁]
    {p₀ : F₂.obj (op a)} (hp : ε₂.app (op a) p₀ = s) :
    𝒲.Aspherical (Cat.of (PushoutFiber h.w a s)) := by
  have inj₂ : Function.Injective (ε₂.app (op a)) :=
    Types.pushoutCocone_inr_injective_of_isColimit (h.app (op a)).isColimit
      (injective_of_mono (φ₁.app (op a)))
  have hw : ∀ x : F₀.obj (op a),
      ε₁.app (op a) (φ₁.app (op a) x) = ε₂.app (op a) (φ₂.app (op a) x) := fun x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app h.w _) x
  refine 𝒲.aspherical_of_thin (C := Cat.of (PushoutFiber h.w a s))
    pushoutFiber_hom_subsingleton (pushoutFiberLower a s h hp)
    (⟨⟨WalkingSpan.right⟩, ⟨p₀, hp⟩⟩ : PushoutFiber h.w a s) (fun p => ?_) (fun p => ?_)
  · rcases p with ⟨⟨_ | _ | _⟩, x⟩
    · exact 𝟙 _
    · refine pushoutFiberHomFst ?_
      exact (FunctorToTypes.exists_app_eq_of_isPushout a s h hp x.1 x.2).choose_spec.1
    · exact 𝟙 _
  · rcases p with ⟨⟨_ | _ | _⟩, x⟩
    · refine pushoutFiberHomSnd ?_
      refine inj₂ ?_
      exact (hw x.1).symm.trans (x.2.trans hp.symm)
    · refine pushoutFiberHomSnd ?_
      exact (FunctorToTypes.exists_app_eq_of_isPushout a s h hp x.1 x.2).choose_spec.2
    · refine pushoutFiberHomOfEq ?_
      exact inj₂ (x.2.trans hp.symm)

theorem aspherical_pushoutFiber_of_notMem_range (h : IsPushout φ₁ φ₂ ε₁ ε₂)
    (hs : ∀ p₀ : F₂.obj (op a), ε₂.app (op a) p₀ ≠ s) :
    𝒲.Aspherical (Cat.of (PushoutFiber h.w a s)) := by
  have hX := h.app (op a)
  have hw : ∀ x : F₀.obj (op a),
      ε₁.app (op a) (φ₁.app (op a) x) = ε₂.app (op a) (φ₂.app (op a) x) := fun x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app h.w _) x
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, ε₁.app (op a) x₁ = s := by
    rcases Types.eq_or_eq_of_isPushout hX s with hx | ⟨p₀, hp⟩
    · exact hx
    · exact (hs p₀ hp).elim
  refine 𝒲.aspherical_of_thin (C := Cat.of (PushoutFiber h.w a s))
    pushoutFiber_hom_subsingleton (𝟭 _)
    (⟨⟨WalkingSpan.left⟩, ⟨x₁, hx₁⟩⟩ : PushoutFiber h.w a s) (fun p => 𝟙 p) (fun p => ?_)
  rcases p with ⟨⟨_ | _ | _⟩, x⟩
  · exact (hs _ ((hw x.1).symm.trans x.2)).elim
  · refine pushoutFiberHomOfEq ?_
    refine ((Types.eq_of_isPushout_of_notMem_range hX.flip ?_).2 _
      (x.2.trans hx₁.symm).symm).symm
    rintro ⟨x₀, hx₀⟩
    exact hs _ ((hw x₀).symm.trans ((congrArg (ε₁.app (op a)) hx₀).trans x.2))
  · exact (hs x.1 x.2).elim

end BasicLocalizer

end Fibre

namespace BasicLocalizer

theorem aspherical_colimitFiberFunctor_smallSpan {F₀ F₁ F₂ F' : Aᵒᵖ ⥤ Type u}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    (h : IsPushout φ₁ φ₂ ε₁ ε₂) [Mono φ₁] (a : A) (s : F'.obj (op a)) :
    𝒲.Aspherical (Cat.of (colimitFiberFunctor A (smallSpan φ₁ φ₂)
      ((PushoutCocone.mk ε₁ ε₂ h.w).whisker AsSmall.down) a s).Elements) := by
  by_cases hs : ∃ p₀ : F₂.obj (op a), ε₂.app (op a) p₀ = s
  · obtain ⟨p₀, hp⟩ := hs
    exact 𝒲.aspherical_pushoutFiber_of_mem_range a s h hp
  · exact 𝒲.aspherical_pushoutFiber_of_notMem_range a s h fun p₀ hp => hs ⟨p₀, hp⟩

theorem W_elementsColimitComparison_smallSpan {F₀ F₁ F₂ F' : Aᵒᵖ ⥤ Type u}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    (h : IsPushout φ₁ φ₂ ε₁ ε₂) [Mono φ₁] :
    𝒲.W (elementsColimitComparison A (smallSpan φ₁ φ₂)
      ((PushoutCocone.mk ε₁ ε₂ h.w).whisker AsSmall.down)) :=
  𝒲.W_elementsColimitComparison A _ _ fun a s =>
    𝒲.aspherical_colimitFiberFunctor_smallSpan A h a s

theorem wPsh_of_isPushout {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : Aᵒᵖ ⥤ Type u}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono ψ₁]
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : 𝒲.wPsh A χ₀) (hχ₁ : 𝒲.wPsh A χ₁) (hχ₂ : 𝒲.wPsh A χ₂) : 𝒲.wPsh A χ' := by
  let χ : smallSpan φ₁ φ₂ ⟶ smallSpan ψ₁ ψ₂ :=
    Functor.whiskerLeft AsSmall.down (spanHomMk χ₀ χ₁ χ₂ h₁ h₂)
  have hnat := elementsColimitComparison_naturality A χ
    ((PushoutCocone.mk ε₁ ε₂ hF.w).whisker AsSmall.down)
    ((PushoutCocone.mk η₁ η₂ hG.w).whisker AsSmall.down) χ' (by
      rintro ⟨_ | _ | _⟩
      · change (φ₁ ≫ ε₁) ≫ χ' = χ₀ ≫ ψ₁ ≫ η₁
        rw [Category.assoc, h₁', ← Category.assoc, h₁, Category.assoc]
      · exact h₁'
      · exact h₂')
  have hmap : 𝒲.W (Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).toCatHom :=
    𝒲.W_grothendieckMap _ (by
      rintro ⟨_ | _ | _⟩
      · exact hχ₀
      · exact hχ₁
      · exact hχ₂)
  have hcomp := 𝒲.W.comp_mem _ _ hmap (𝒲.W_elementsColimitComparison_smallSpan A hG)
  rw [hnat] at hcomp
  exact 𝒲.W.of_precomp _ _ (𝒲.W_elementsColimitComparison_smallSpan A hF) hcomp

end BasicLocalizer

variable {A} in
theorem BasicLocalizer.pshAspherical_of_isPushout (hA : 𝒲.Aspherical (Cat.of A))
    {X₀ X₁ X₂ X : Aᵒᵖ ⥤ Type u} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X} {g₂ : X₂ ⟶ X}
    (h : IsPushout f₁ f₂ g₁ g₂) [Mono f₁] (h₀ : 𝒲.PshAspherical A X₀)
    (h₁ : 𝒲.PshAspherical A X₁) (h₂ : 𝒲.PshAspherical A X₂) : 𝒲.PshAspherical A X := by
  rw [𝒲.pshAspherical_iff_wPsh_terminal_from _ hA] at h₀ h₁ h₂ ⊢
  exact 𝒲.wPsh_of_isPushout A h (IsPushout.id_horiz (𝟙 _)) _ _ _ _
    (terminal.hom_ext _ _) (terminal.hom_ext _ _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)
    h₀ h₁ h₂

end Atoms.TestCategory
