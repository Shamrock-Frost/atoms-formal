import Atoms.ForMathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

namespace CategoryTheory.Cat

open Limits

universe u

def sliceFstSnd (A B : Cat.{u, u}) (a : A) :
    Cat.of (CostructuredArrow (CategoryTheory.Prod.fst ↥A ↥B) a) ⟶ B :=
  (CostructuredArrow.proj _ a ⋙ CategoryTheory.Prod.snd ↥A ↥B).toCatHom

def commaSquareFunctor {A' A B' B : Cat.{u, u}}
    (w : A' ⟶ A) (u' : A' ⟶ B') (u : A ⟶ B) (v : B' ⟶ B)
    (h : w ≫ u = u' ≫ v) (b : B') :
    CostructuredArrow u'.toFunctor b ⥤ CostructuredArrow u.toFunctor (v.toFunctor.obj b) :=
  CostructuredArrow.map₂ (eqToHom (congrArg Cat.Hom.toFunctor h)) (𝟙 _)

theorem commaSquareFunctor_comp_map {A' A B' B : Cat.{u, u}} (w : A' ⟶ A) (u' : A' ⟶ B')
    (u : A ⟶ B) (v : B' ⟶ B) (hw : w ≫ u = u' ≫ v) {b c : B'} (f : b ⟶ c) :
    CostructuredArrow.map (S := u'.toFunctor) f ⋙ commaSquareFunctor w u' u v hw c =
      commaSquareFunctor w u' u v hw b ⋙ CostructuredArrow.map (v.toFunctor.map f) := by
  refine CategoryTheory.Functor.ext (fun X => CostructuredArrow.obj_ext _ _ rfl ?_)
    (fun X Y φ => ?_)
  · simp only [commaSquareFunctor, Functor.comp_obj, CostructuredArrow.map₂_obj_hom,
      CostructuredArrow.map_obj_hom, Functor.map_comp, Category.assoc, Category.comp_id]
    exact (congrArg (· ≫ _) (u.toFunctor.map_id _)).trans (Category.id_comp _)
  · apply CostructuredArrow.hom_ext
    simp only [commaSquareFunctor, Functor.comp_map, CostructuredArrow.map₂_map_left,
      CostructuredArrow.map_map_left, CostructuredArrow.comp_left]
    erw [CostructuredArrow.eqToHom_left, CostructuredArrow.eqToHom_left]
    simp

section NatTrans

variable {A' A B' B : Cat.{u, u}}

def commaSquareNatTrans (w : A' ⟶ A) (u' : A' ⟶ B') (u : A ⟶ B) (v : B' ⟶ B)
    (hw : w ≫ u = u' ≫ v) :
    CostructuredArrow.functor u'.toFunctor ⟶
      v.toFunctor ⋙ CostructuredArrow.functor u.toFunctor where
  app b := (commaSquareFunctor w u' u v hw b).toCatHom
  naturality _ _ f := Cat.Hom.ext (commaSquareFunctor_comp_map w u' u v hw f)

end NatTrans

section CommaComparison

variable {A' A B' B : Cat.{u, u}}

def idSectionAdjunction (u : A ⟶ B) :
    Comma.idSection u.toFunctor ⊣ Comma.fst u.toFunctor (𝟭 B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun a X =>
        { toFun := fun m => m.left
          invFun := fun f => ⟨f, u.toFunctor.map f ≫ X.hom, by simp [Comma.idSection]⟩
          left_inv := fun m => by
            have := m.w
            simp only [Comma.idSection, Functor.id_map, Functor.id_obj] at this
            ext
            · rfl
            · simpa [Comma.idSection] using this
          right_inv := fun f => rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Comma.hom_ext
        · rfl
        · change u.toFunctor.map (f ≫ g) ≫ _ = u.toFunctor.map f ≫ u.toFunctor.map g ≫ _
          simp }

def commaSquareSliceEquivalence (w : A' ⟶ A) (u' : A' ⟶ B') (u : A ⟶ B)
    (v : B' ⟶ B) (hw : w ≫ u = u' ≫ v) (b : B')
    (x : CostructuredArrow u.toFunctor (v.toFunctor.obj b)) :
    CostructuredArrow (Comma.ofSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
          (congrArg Cat.Hom.toFunctor hw))
        (⟨x.left, b, x.hom⟩ : Comma u.toFunctor v.toFunctor) ≌
      CostructuredArrow (commaSquareFunctor w u' u v hw b) x :=
  CategoryTheory.Equivalence.mk
    { obj := fun y => CostructuredArrow.mk (Y := CostructuredArrow.mk (Y := y.left) y.hom.right)
        (CostructuredArrow.homMk y.hom.left (by
          have := y.hom.w
          simp only [Comma.ofSquare] at this
          simp only [commaSquareFunctor, CostructuredArrow.map₂_obj_hom,
            CategoryTheory.eqToHom_app,
            Category.comp_id]
          exact this))
      map := fun {y₁ y₂} g => CostructuredArrow.homMk
        (CostructuredArrow.homMk g.left (congrArg CommaMorphism.right (CostructuredArrow.w g)))
        (by
          ext
          exact (congrArg CommaMorphism.left (CostructuredArrow.w g) :)) }
    { obj := fun z => CostructuredArrow.mk (Y := z.left.left)
        (⟨z.hom.left, z.left.hom, by
          have := CostructuredArrow.w z.hom
          simp only [commaSquareFunctor, CostructuredArrow.map₂_obj_hom,
            CategoryTheory.eqToHom_app,
            Category.comp_id] at this
          simp only [Comma.ofSquare]
          exact this⟩ :
          (Comma.ofSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
            (congrArg Cat.Hom.toFunctor hw)).obj z.left.left ⟶ ⟨x.left, b, x.hom⟩)
      map := fun {z₁ z₂} g => CostructuredArrow.homMk g.left.left (by
        apply Comma.hom_ext
        · exact (congrArg CommaMorphism.left (CostructuredArrow.w g) :)
        · exact CostructuredArrow.w g.left) }
  (NatIso.ofComponents (fun y => Iso.refl _)
    (fun g => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  (NatIso.ofComponents (fun z => Iso.refl _)
    (fun g => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm))

end CommaComparison

end CategoryTheory.Cat
