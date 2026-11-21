import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

namespace CategoryTheory

open Limits MonoidalCategory Opposite

universe u

section OverRestrict

variable (A : Type u) [SmallCategory A]

def elementsOverRestrictToProd (a : A) (F : Aᵒᵖ ⥤ Type u) :
    ((Over.forget a).op ⋙ F).Elements ⥤ (FunctorToTypes.prod (yoneda.obj a) F).Elements where
  obj X := ⟨op X.1.unop.left, (X.1.unop.hom, X.2)⟩
  map {X Y} φ := ⟨φ.1.unop.left.op, _root_.Prod.ext (Over.w φ.1.unop) φ.2⟩

def elementsProdToOverRestrict (a : A) (F : Aᵒᵖ ⥤ Type u) :
    (FunctorToTypes.prod (yoneda.obj a) F).Elements ⥤ ((Over.forget a).op ⋙ F).Elements where
  obj Y := ⟨op (Over.mk Y.2.1), Y.2.2⟩
  map {Y Z} ψ :=
    ⟨(Over.homMk ψ.1.unop (congrArg _root_.Prod.fst ψ.2)).op, by exact congrArg _root_.Prod.snd ψ.2⟩

def elementsOverRestrictEquivalence (a : A) (F : Aᵒᵖ ⥤ Type u) :
    (((Over.forget a).op ⋙ F).Elements)ᵒᵖ ≌
      ((FunctorToTypes.prod (yoneda.obj a) F).Elements)ᵒᵖ :=
  Equivalence.op
    { functor := elementsOverRestrictToProd A a F
      inverse := elementsProdToOverRestrict A a F
      unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
        CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj (Over.OverMorphism.ext
          ((Category.id_comp _).trans (Category.comp_id _).symm))))
      counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
        CategoryOfElements.ext _ _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))
      functor_unitIso_comp _ := CategoryOfElements.ext _ _ _ (Category.comp_id _) }

end OverRestrict

section Slice

variable {A : Type u} [SmallCategory A] (Y X : Aᵒᵖ ⥤ Type u) (c : (X.Elements)ᵒᵖ)

abbrev elementsSnd : ((Y ⊗ X).Elements)ᵒᵖ ⥤ (X.Elements)ᵒᵖ :=
  (CategoryOfElements.map (CartesianMonoidalCategory.snd Y X)).op

def costructuredArrowElementsSndToElements :
    CostructuredArrow (elementsSnd Y X) c ⥤
      ((FunctorToTypes.prod (yoneda.obj (unop c.unop.1)) Y).Elements)ᵒᵖ where
  obj α := op ⟨α.left.unop.1, (α.hom.unop.1.unop, α.left.unop.2.1)⟩
  map φ := Quiver.Hom.op ⟨φ.left.unop.1, _root_.Prod.ext
    (congrArg (fun k => k.unop.1.unop) (CostructuredArrow.w φ))
    (congrArg _root_.Prod.fst φ.left.unop.2)⟩
  map_id _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

def elementsToCostructuredArrowElementsSnd :
    ((FunctorToTypes.prod (yoneda.obj (unop c.unop.1)) Y).Elements)ᵒᵖ ⥤
      CostructuredArrow (elementsSnd Y X) c where
  obj e := CostructuredArrow.mk (S := elementsSnd Y X) (T := c)
    (Y := op ((Y ⊗ X).elementsMk e.unop.1 (e.unop.2.2, X.map e.unop.2.1.op c.unop.2)))
    (Quiver.Hom.op (CategoryOfElements.homMk _ _ e.unop.2.1.op rfl))
  map {e e'} ψ := CostructuredArrow.homMk
    (Quiver.Hom.op ⟨ψ.unop.1, _root_.Prod.ext (congrArg _root_.Prod.snd ψ.unop.2) (by
      have hg : ψ.unop.1.unop ≫ e'.unop.2.1 = e.unop.2.1 := congrArg _root_.Prod.fst ψ.unop.2
      change X.map ψ.unop.1 (X.map e'.unop.2.1.op c.unop.2) = X.map e.unop.2.1.op c.unop.2
      rw [← hg, op_comp, Functor.map_comp_apply]
      rfl)⟩)
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (by
      have hg : ψ.unop.1.unop ≫ e'.unop.2.1 = e.unop.2.1 := congrArg _root_.Prod.fst ψ.unop.2
      change e'.unop.2.1.op ≫ ψ.unop.1 = e.unop.2.1.op
      rw [← hg, op_comp]
      rfl)))
  map_id _ := CostructuredArrow.hom_ext _ _
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))
  map_comp _ _ := CostructuredArrow.hom_ext _ _
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))

def costructuredArrowElementsSndEquivalence :
    CostructuredArrow (elementsSnd Y X) c ≌
      ((FunctorToTypes.prod (yoneda.obj (unop c.unop.1)) Y).Elements)ᵒᵖ where
  functor := costructuredArrowElementsSndToElements Y X c
  inverse := elementsToCostructuredArrowElementsSnd Y X c
  unitIso := NatIso.ofComponents
    (fun α => CostructuredArrow.isoMk
      (Iso.op (CategoryOfElements.isoMk
        ((Y ⊗ X).elementsMk α.left.unop.1 (α.left.unop.2.1, X.map α.hom.unop.1 c.unop.2))
        α.left.unop (Iso.refl α.left.unop.1) (by
          have h : ((α.left.unop.2.1, X.map α.hom.unop.1 c.unop.2) :
              (Y ⊗ X).obj α.left.unop.1) = α.left.unop.2 := _root_.Prod.ext rfl α.hom.unop.2
          exact (ConcreteCategory.congr_hom ((Y ⊗ X).map_id _) _).trans h)))
      (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.comp_id _))))
    (fun _ => CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm))))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm)))
  functor_unitIso_comp _ :=
    Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.id_comp _))

end Slice

end CategoryTheory
