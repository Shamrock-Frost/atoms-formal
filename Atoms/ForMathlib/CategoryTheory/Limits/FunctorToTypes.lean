import Atoms.ForMathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Filtered

namespace CategoryTheory

open Limits Opposite

universe w u

namespace FunctorToTypes

variable {A : Type u} [SmallCategory A]

section Colimit

variable {I : Type u} [SmallCategory I]

theorem colimit_ι_app_map_apply (F : I ⥤ Aᵒᵖ ⥤ Type u) (a : A) {i j : I} (k : i ⟶ j)
    (x : (F.obj i).obj (op a)) :
    (colimit.ι F j).app (op a) ((F.map k).app (op a) x) = (colimit.ι F i).app (op a) x :=
  congrArg (fun φ : F.obj i ⟶ colimit F => φ.app (op a) x) (colimit.w F k)

end Colimit

section Chain

variable {J : Type w} [LinearOrder J]

theorem injective_colimit_ι_app_app (F : J ⥤ Aᵒᵖ ⥤ Type w)
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) {c : Cocone F} (hc : IsColimit c)
    (a : A) (j : J) : Function.Injective ((c.ι.app j).app (op a)) := by
  intro x y hxy
  have hc' := isColimitOfPreserves ((evaluation Aᵒᵖ (Type w)).obj (op a)) hc
  obtain ⟨k, f, g, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ (evaluation Aᵒᵖ (Type w)).obj (op a)) hc'
      (xi := x) (xj := y)).1 hxy
  have hg : g = f := Subsingleton.elim _ _
  subst hg
  have hm : Mono ((F.map g).app (op a)) := by
    have h := hF j k (leOfHom g)
    rw [show homOfLE (leOfHom g) = g from Subsingleton.elim _ _] at h
    exact inferInstance
  exact (mono_iff_injective ((F.map g).app (op a))).1 hm hfg

end Chain

section Pushout

variable {F₀ F₁ F₂ F' : Aᵒᵖ ⥤ Type u} {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'}
  {ε₂ : F₂ ⟶ F'} (a : A) (s : F'.obj (op a))

theorem exists_app_eq_of_isPushout (h : IsPushout φ₁ φ₂ ε₁ ε₂) [Mono φ₁]
    {p₀ : F₂.obj (op a)} (hp : ε₂.app (op a) p₀ = s) (x : F₁.obj (op a))
    (hx : ε₁.app (op a) x = s) : ∃ x₀, φ₁.app (op a) x₀ = x ∧ φ₂.app (op a) x₀ = p₀ :=
  (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit (h.app (op a)).isColimit
    (injective_of_mono (φ₁.app (op a))) x p₀).1 (hx.trans hp.symm)

end Pushout

section Coproduct

theorem mono_coprodDesc_of_disjoint {C : Type*} [Category* C] {T T' L : Cᵒᵖ ⥤ Type w}
    (a : T ⟶ L) (b : T' ⟶ L) [Mono a] [Mono b]
    (h : ∀ U, Disjoint (Set.range (a.app U)) (Set.range (b.app U))) :
    Mono (coprod.desc a b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  have hc := (isColimitMapCoconeBinaryCofanEquiv ((evaluation _ _).obj U) _ _)
    (isColimitOfPreserves ((evaluation _ _).obj U) (coprodIsCoprod T T'))
  obtain ⟨-, -, hcompl⟩ := (Types.binaryCofan_isColimit_iff _).mp ⟨hc⟩
  have ha := (mono_iff_injective _).1 (NatTrans.mono_iff_mono_app a |>.1 inferInstance U)
  have hb := (mono_iff_injective _).1 (NatTrans.mono_iff_mono_app b |>.1 inferInstance U)
  have hl (x : T.obj U) :
      (coprod.desc a b).app U ((coprod.inl : T ⟶ T ⨿ T').app U x) = a.app U x := by
    rw [← NatTrans.comp_app_apply, coprod.inl_desc]
  have hr (x : T'.obj U) :
      (coprod.desc a b).app U ((coprod.inr : T' ⟶ T ⨿ T').app U x) = b.app U x := by
    rw [← NatTrans.comp_app_apply, coprod.inr_desc]
  intro z₁ z₂ hz
  rcases Set.eq_univ_iff_forall.mp hcompl.sup_eq_top z₁ with ⟨x₁, rfl⟩ | ⟨x₁, rfl⟩ <;>
    rcases Set.eq_univ_iff_forall.mp hcompl.sup_eq_top z₂ with ⟨x₂, rfl⟩ | ⟨x₂, rfl⟩
  · exact congrArg _ (ha ((hl x₁).symm.trans (hz.trans (hl x₂))))
  · exact absurd ((hl x₁).symm.trans (hz.trans (hr x₂))) (Set.disjoint_range_iff.1 (h U) x₁ x₂)
  · exact absurd ((hl x₂).symm.trans (hz.symm.trans (hr x₁))) (Set.disjoint_range_iff.1 (h U) x₂ x₁)
  · exact congrArg _ (hb ((hr x₁).symm.trans (hz.trans (hr x₂))))

end Coproduct

end FunctorToTypes

section Initial

universe w₁ v₁ u₁

instance FunctorToTypes.isEmpty_initial_obj {B : Type u₁} [Category.{v₁} B] (a : B) :
    IsEmpty ((⊥_ (B ⥤ Type w₁)).obj a) :=
  (Types.initial_iff_empty _).mp ⟨initialIsInitial.isInitialObj ((evaluation _ _).obj a) _⟩

end Initial

theorem FunctorToTypes.subsingleton_terminal_obj (A : Type u) [SmallCategory A] (c : Aᵒᵖ) :
    Subsingleton ((⊤_ (Aᵒᵖ ⥤ Type u)).obj c) :=
  ⟨fun x y => yonedaEquiv.symm.injective
    (terminal.hom_ext ((yonedaEquiv (X := unop c)).symm x) (yonedaEquiv.symm y))⟩

noncomputable def elementsTerminalProj (A : Type u) [SmallCategory A] :
    ((⊤_ (Aᵒᵖ ⥤ Type u)).Elements)ᵒᵖ ⥤ A where
  obj X := unop X.unop.1
  map f := f.unop.val.unop
  map_id _ := rfl
  map_comp _ _ := rfl

instance isEquivalence_elementsTerminalProj (A : Type u) [SmallCategory A] :
    (elementsTerminalProj A).IsEquivalence where
  faithful := ⟨fun h => Quiver.Hom.unop_inj
    (CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj h))⟩
  full := ⟨fun {X Y} g => ⟨(CategoryOfElements.homMk Y.unop X.unop g.op
    ((FunctorToTypes.subsingleton_terminal_obj A _).elim _ _)).op, rfl⟩⟩
  essSurj := ⟨fun a => ⟨op ⟨op a, yonedaEquiv (terminal.from (yoneda.obj a))⟩, ⟨Iso.refl _⟩⟩⟩

noncomputable def elementsTerminalEquivalence (A : Type u) [SmallCategory A] :
    ((⊤_ (Aᵒᵖ ⥤ Type u)).Elements)ᵒᵖ ≌ A :=
  (elementsTerminalProj A).asEquivalence

namespace FunctorToTypes

variable {C : Type u} [SmallCategory C]

@[simps]
noncomputable def toConstTerminal {I : Type u} [SmallCategory I] (F : I ⥤ Cᵒᵖ ⥤ Type u) :
    F ⟶ (Functor.const I).obj (⊤_ (Cᵒᵖ ⥤ Type u)) where
  app _ := terminal.from _
  naturality _ _ _ := terminal.hom_ext _ _

end FunctorToTypes

end CategoryTheory
