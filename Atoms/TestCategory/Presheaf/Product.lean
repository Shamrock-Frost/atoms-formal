import Atoms.TestCategory.Presheaf.Transport

open CategoryTheory Limits Opposite

universe u

namespace Atoms.TestCategory

namespace BasicLocalizer

theorem wPsh_prod_of_forall_sectL {A B : Type u} [SmallCategory A] [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) {X Y : (A × B)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y)
    (h : ∀ b : B, 𝒲.wPsh A (Functor.whiskerLeft (Prod.sectL A b).op φ)) :
    𝒲.wPsh (A × B) φ := by
  let α := Functor.whiskerRight (prodCurryMap φ) Functor.elementsFunctor
  have hα : ∀ b : Bᵒᵖ, 𝒲.W (α.app b) := by
    intro b
    apply (𝒲.W_opFunctor_map_iff (α.app b)).mp
    exact h b.unop
  have hg : 𝒲.W (Grothendieck.map α).toCatHom := 𝒲.W_grothendieckMap α hα
  have he := 𝒲.W_iff_of_isEquivalence_of_iso
    (prodElementsFunctor X).toCatHom (prodElementsFunctor Y).toCatHom
    (show (prodElementsFunctor X).IsEquivalence from inferInstance)
    (show (prodElementsFunctor Y).IsEquivalence from inferInstance)
    (Grothendieck.map α).toCatHom (NatTrans.mapElements φ).toCatHom
    (prodElementsFunctorNaturality φ)
  have hm : 𝒲.W (NatTrans.mapElements φ).toCatHom := he.mp hg
  exact (𝒲.W_opFunctor_map_iff (NatTrans.mapElements φ).toCatHom).mpr hm

theorem wPsh_prod_of_forall_sectR {A B : Type u} [SmallCategory A] [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) {X Y : (A × B)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y)
    (h : ∀ a : A, 𝒲.wPsh B (Functor.whiskerLeft (Prod.sectR a B).op φ)) :
    𝒲.wPsh (A × B) φ := by
  rw [𝒲.wPsh_eq_inverseImage_presheafEquivalence (CategoryTheory.Prod.braiding A B)]
  apply 𝒲.wPsh_prod_of_forall_sectL _
  intro a
  exact h a

theorem wPsh_of_wPsh_whiskerLeft_fst {A B : Type u} [SmallCategory A] [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) (b₀ : B) {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (h : 𝒲.wPsh (A × B)
      (Functor.whiskerLeft (CategoryTheory.Prod.fst A B).op f)) : 𝒲.wPsh A f := by
  let p := (CategoryTheory.Prod.fst A B).op
  let s := (Prod.sectL A b₀).op
  let iX : (elementsFunctor A).obj X ⟶ (elementsFunctor (A × B)).obj (p ⋙ X) :=
    Cat.opFunctor.map (Functor.Elements.precomp s (p ⋙ X)).toCatHom
  let iY : (elementsFunctor A).obj Y ⟶ (elementsFunctor (A × B)).obj (p ⋙ Y) :=
    Cat.opFunctor.map (Functor.Elements.precomp s (p ⋙ Y)).toCatHom
  let rX : (elementsFunctor (A × B)).obj (p ⋙ X) ⟶ (elementsFunctor A).obj X :=
    Cat.opFunctor.map (Functor.Elements.precomp p X).toCatHom
  let rY : (elementsFunctor (A × B)).obj (p ⋙ Y) ⟶ (elementsFunctor A).obj Y :=
    Cat.opFunctor.map (Functor.Elements.precomp p Y).toCatHom
  have hrX : iX ≫ rX = 𝟙 _ :=
    Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  have hrY : iY ≫ rY = 𝟙 _ :=
    Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  have hs : iX ≫ (elementsFunctor (A × B)).map (Functor.whiskerLeft p f) =
      (elementsFunctor A).map f ≫ iY :=
    Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  have ht : (elementsFunctor (A × B)).map (Functor.whiskerLeft p f) ≫ rY =
      rX ≫ (elementsFunctor A).map f :=
    Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  let R : RetractArrow ((elementsFunctor A).map f)
      ((elementsFunctor (A × B)).map (Functor.whiskerLeft p f)) :=
    { i := Arrow.homMk iX iY hs
      r := Arrow.homMk rX rY ht
      retract := Arrow.hom_ext _ _ hrX hrY }
  exact 𝒲.W.of_retract R h

end BasicLocalizer

end Atoms.TestCategory
