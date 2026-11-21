import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.TestCategory.Presheaf.ElementsColimit
import Atoms.TestCategory.BasicLocalizer.GrothendieckConstruction

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
variable {J : Type u} [LinearOrder J] [WellFoundedLT J]

theorem hasInitial_colimitFiberFunctor_elements (F : J ⥤ Aᵒᵖ ⥤ Type u)
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) {c : Cocone F} (hc : IsColimit c)
    (a : A) (s : c.pt.obj (op a)) : HasInitial (colimitFiberFunctor A F c a s).Elements := by
  have hc' := isColimitOfPreserves ((evaluation Aᵒᵖ (Type u)).obj (op a)) hc
  let S : Set J := {i | Nonempty ((colimitFiberFunctor A F c a s).obj i)}
  have hne : S.Nonempty := by
    obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hc' s
    exact ⟨i, ⟨⟨x, hx⟩⟩⟩
  let i₀ : J := wellFounded_lt.min S hne
  let x₀ : (colimitFiberFunctor A F c a s).obj i₀ :=
    Classical.choice (wellFounded_lt.min_mem S hne)
  let p₀ : (colimitFiberFunctor A F c a s).Elements := ⟨i₀, x₀⟩
  have hle : ∀ p : (colimitFiberFunctor A F c a s).Elements, i₀ ≤ p.1 := fun p =>
    not_lt.1 (wellFounded_lt.not_lt_min S (x := p.1) ⟨p.2⟩)
  let hom : ∀ p : (colimitFiberFunctor A F c a s).Elements, p₀ ⟶ p := fun p =>
    ⟨homOfLE (hle p), Subtype.ext (FunctorToTypes.injective_colimit_ι_app_app F hF hc a p.1
      (((congrArg (fun φ : F.obj i₀ ⟶ c.pt => φ.app (op a) x₀.1)
        (c.w (homOfLE (hle p)))).trans x₀.2).trans p.2.2.symm))⟩
  exact IsInitial.hasInitial (IsInitial.ofUniqueHom hom fun p m =>
    CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _))

namespace BasicLocalizer

theorem W_elementsColimitComparison_of_mono (F : J ⥤ Aᵒᵖ ⥤ Type u)
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) {c : Cocone F} (hc : IsColimit c) :
    𝒲.W (elementsColimitComparison A F c) :=
  𝒲.W_elementsColimitComparison A F c fun a s =>
    have : HasInitial (Cat.of (colimitFiberFunctor A F c a s).Elements) :=
      hasInitial_colimitFiberFunctor_elements A F hF hc a s
    𝒲.aspherical_of_hasInitial _

theorem wPsh_of_isColimit {X Y : J ⥤ Aᵒᵖ ⥤ Type u}
    (hX : ∀ (i j : J) (h : i ≤ j), Mono (X.map (homOfLE h)))
    (hY : ∀ (i j : J) (h : i ≤ j), Mono (Y.map (homOfLE h)))
    (φ : X ⟶ Y) (hφ : ∀ j, 𝒲.wPsh A (φ.app j)) {cX : Cocone X} {cY : Cocone Y}
    (hcX : IsColimit cX) (hcY : IsColimit cY) (f : cX.pt ⟶ cY.pt)
    (hf : ∀ j, cX.ι.app j ≫ f = φ.app j ≫ cY.ι.app j) : 𝒲.wPsh A f := by
  have hG : 𝒲.W (Grothendieck.map (Functor.whiskerRight φ (elementsFunctor A))).toCatHom :=
    𝒲.W_grothendieckMap _ fun j => hφ j
  have hKY := 𝒲.W_elementsColimitComparison_of_mono A Y hY hcY
  have hKX := 𝒲.W_elementsColimitComparison_of_mono A X hX hcX
  have e := elementsColimitComparison_naturality A φ cX cY f hf
  exact 𝒲.W.of_precomp _ _ hKX (e ▸ 𝒲.W.comp_mem _ _ hG hKY)

end BasicLocalizer

end Atoms.TestCategory
