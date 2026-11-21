import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Hom

namespace CategoryTheory.Cat

open Opposite

universe u

abbrev twistedArrow (A : Cat.{u, u}) : Cat.{u, u} := Cat.of (Functor.hom ↥A).Elements

def twistedArrowTarget (A : Cat.{u, u}) : twistedArrow A ⟶ A :=
  (CategoryOfElements.π (Functor.hom ↥A) ⋙ CategoryTheory.Prod.snd _ _).toCatHom

def twistedArrowSource (A : Cat.{u, u}) : twistedArrow A ⟶ Cat.opFunctor.obj A :=
  (CategoryOfElements.π (Functor.hom ↥A) ⋙ CategoryTheory.Prod.fst _ _).toCatHom

section TwistedArrow

variable {A : Cat.{u, u}}

theorem twistedArrow_hom_comm {X Y : twistedArrow A} (φ : X ⟶ Y) :
    φ.1.1.unop ≫ X.2 ≫ φ.1.2 = Y.2 :=
  φ.2

def twistedArrowHomMk {X Y : twistedArrow A} (g : unop Y.1.1 ⟶ unop X.1.1) (h : X.1.2 ⟶ Y.1.2)
    (w : g ≫ X.2 ≫ h = Y.2) : X ⟶ Y :=
  ⟨(g.op, h), w⟩

theorem twistedArrow_hom_ext {X Y : twistedArrow A} {φ ψ : X ⟶ Y}
    (h₁ : φ.1.1.unop = ψ.1.1.unop) (h₂ : φ.1.2 = ψ.1.2) : φ = ψ :=
  Subtype.ext (Prod.ext (Quiver.Hom.unop_inj h₁) h₂)

@[simp]
theorem twistedArrowTarget_map {X Y : twistedArrow A} (φ : X ⟶ Y) :
    (twistedArrowTarget A).toFunctor.map φ = φ.1.2 :=
  rfl

end TwistedArrow

section Target

variable (A : Cat.{u, u}) (b : A)

def twistedArrowTargetSliceCompose :
    CostructuredArrow (twistedArrowTarget A).toFunctor b ⥤ (Over b)ᵒᵖ where
  obj X := op (Over.mk (X.left.2 ≫ X.hom))
  map {X Y} φ := Quiver.Hom.op (Over.homMk φ.left.1.1.unop (by
    have w := CostructuredArrow.w φ
    have c := twistedArrow_hom_comm φ.left
    simp only [twistedArrowTarget_map] at w
    dsimp
    rw [← w]
    refine Eq.trans ?_ (congrArg (· ≫ Y.hom) c)
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm.trans (Category.assoc _ _ _).symm))
  map_id _ := rfl
  map_comp _ _ := rfl

def twistedArrowTargetFibreInclusion :
    (Over b)ᵒᵖ ⥤ CostructuredArrow (twistedArrowTarget A).toFunctor b where
  obj m := CostructuredArrow.mk
    (Y := (show twistedArrow A from ⟨(op (unop m).left, b), (unop m).hom⟩)) (𝟙 b)
  map {m m'} φ := CostructuredArrow.homMk
    (twistedArrowHomMk φ.unop.left (𝟙 b) (by
      change φ.unop.left ≫ m.unop.hom ≫ 𝟙 b = m'.unop.hom
      rw [Category.comp_id]
      exact Over.w φ.unop))
    (show 𝟙 b ≫ 𝟙 b = 𝟙 b from Category.comp_id _)
  map_id _ := rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _
    (twistedArrow_hom_ext rfl (Category.comp_id (𝟙 b)).symm)

def twistedArrowTargetSliceComposeAdjunction :
    twistedArrowTargetSliceCompose A b ⊣ twistedArrowTargetFibreInclusion A b :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X m =>
        { toFun := fun ψ => CostructuredArrow.homMk
            (twistedArrowHomMk ψ.unop.left X.hom (Over.w ψ.unop))
            (show X.hom ≫ 𝟙 b = X.hom from Category.comp_id _)
          invFun := fun φ => Quiver.Hom.op (Over.homMk φ.left.1.1.unop (by
            have w : φ.left.1.2 ≫ 𝟙 b = X.hom := CostructuredArrow.w φ
            have c : φ.left.1.1.unop ≫ X.left.2 ≫ φ.left.1.2 = m.unop.hom :=
              twistedArrow_hom_comm φ.left
            have hk : X.hom = φ.left.1.2 := w.symm.trans (Category.comp_id _)
            change φ.left.1.1.unop ≫ X.left.2 ≫ X.hom = m.unop.hom
            exact (congrArg (fun k : X.left.1.2 ⟶ b => φ.left.1.1.unop ≫ X.left.2 ≫ k) hk).trans
              c))
          left_inv := fun ψ => Quiver.Hom.unop_inj (Over.OverMorphism.ext rfl)
          right_inv := fun φ => CostructuredArrow.hom_ext _ _
            (twistedArrow_hom_ext rfl (by
              have w : φ.left.1.2 ≫ 𝟙 b = X.hom := CostructuredArrow.w φ
              change X.hom = φ.left.1.2
              exact w.symm.trans (Category.comp_id _))) }
      homEquiv_naturality_left_symm := fun f g =>
        Quiver.Hom.unop_inj (Over.OverMorphism.ext rfl)
      homEquiv_naturality_right := fun {X _ _} f g => CostructuredArrow.hom_ext _ _
        (twistedArrow_hom_ext rfl (Category.comp_id X.hom).symm) }

end Target

def twistedArrowOpIso (A : Cat.{u, u}) : twistedArrow A ≅ twistedArrow (Cat.opFunctor.obj A) where
  hom := Functor.toCatHom
    { obj X := ⟨(op (op X.1.2), X.1.1), X.2.op⟩
      map φ := twistedArrowHomMk φ.1.2.op φ.1.1
        (Quiver.Hom.unop_inj ((Category.assoc _ _ _).trans (twistedArrow_hom_comm φ)))
      map_id _ := twistedArrow_hom_ext rfl rfl
      map_comp _ _ := twistedArrow_hom_ext rfl rfl }
  inv := Functor.toCatHom
    { obj X := ⟨(X.1.2, X.1.1.unop.unop), X.2.unop⟩
      map φ := twistedArrowHomMk φ.1.2.unop φ.1.1.unop.unop
        ((Category.assoc _ _ _).symm.trans (congrArg Quiver.Hom.unop (twistedArrow_hom_comm φ)))
      map_id _ := twistedArrow_hom_ext rfl rfl
      map_comp _ _ := twistedArrow_hom_ext rfl rfl }
  hom_inv_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  inv_hom_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)

theorem twistedArrowOpIso_hom_comp_twistedArrowTarget (A : Cat.{u, u}) :
    (twistedArrowOpIso A).hom ≫ twistedArrowTarget (Cat.opFunctor.obj A) =
      twistedArrowSource A :=
  rfl

def twistedArrowMap {A B : Cat.{u, u}} (F : A ⟶ B) : twistedArrow A ⟶ twistedArrow B :=
  Functor.toCatHom
    { obj X := ⟨(op (F.toFunctor.obj (unop X.1.1)), F.toFunctor.obj X.1.2), F.toFunctor.map X.2⟩
      map {X _} φ := twistedArrowHomMk (F.toFunctor.map φ.1.1.unop) (F.toFunctor.map φ.1.2)
        (((F.toFunctor.map_comp φ.1.1.unop (X.2 ≫ φ.1.2)).trans
          (congrArg (F.toFunctor.map φ.1.1.unop ≫ ·) (F.toFunctor.map_comp X.2 φ.1.2))).symm.trans
          (congrArg F.toFunctor.map (twistedArrow_hom_comm φ)))
      map_id _ := twistedArrow_hom_ext (F.toFunctor.map_id _) (F.toFunctor.map_id _)
      map_comp _ _ := twistedArrow_hom_ext (F.toFunctor.map_comp _ _) (F.toFunctor.map_comp _ _) }

theorem twistedArrowMap_comp_twistedArrowTarget {A B : Cat.{u, u}} (F : A ⟶ B) :
    twistedArrowMap F ≫ twistedArrowTarget B = twistedArrowTarget A ≫ F :=
  rfl

theorem twistedArrowMap_comp_twistedArrowSource {A B : Cat.{u, u}} (F : A ⟶ B) :
    twistedArrowMap F ≫ twistedArrowSource B = twistedArrowSource A ≫ Cat.opFunctor.map F :=
  rfl

end CategoryTheory.Cat
