import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Widesubcategory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

variable (F : C ⥤ D) {P : MorphismProperty C} {Q : MorphismProperty D}
  [P.IsMultiplicative] [Q.IsMultiplicative]

@[simps]
def mapWideSubcategory (h : P ≤ Q.inverseImage F) : WideSubcategory P ⥤ WideSubcategory Q where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom, h _ f.property⟩
  map_id X := WideSubcategory.hom_ext _ (F.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ (F.map_comp f.hom g.hom)

theorem mapWideSubcategory_comp_wideSubcategoryInclusion (h : P ≤ Q.inverseImage F) :
    F.mapWideSubcategory h ⋙ wideSubcategoryInclusion Q = wideSubcategoryInclusion P ⋙ F :=
  rfl

end Functor

section ConcreteCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} D]
  {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
  [ConcreteCategory.{w} D FD] (F : C → D) (P : MorphismProperty D) [P.IsMultiplicative]

instance InducedWideCategory.instFunLike (X Y : InducedWideCategory D F P) :
    FunLike (InducedWideCategory.Hom (F := F) (P := P) X Y) (ToType (F X)) (ToType (F Y)) where
  coe f := f.hom
  coe_injective _ _ h := InducedWideCategory.Hom.ext (ConcreteCategory.coe_ext h)

instance InducedWideCategory.concreteCategory :
    ConcreteCategory (InducedWideCategory D F P)
      (InducedWideCategory.Hom (F := F) (P := P)) where
  hom f := f
  ofHom f := f
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := ConcreteCategory.id_apply _
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _

variable {FC : C → C → Type*} {CC : C → Type w} [Category.{v₁} C]
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
  (Q : MorphismProperty C) [Q.IsMultiplicative]

instance WideSubcategory.instFunLike (X Y : WideSubcategory Q) :
    FunLike (InducedWideCategory.Hom (F := WideSubcategory.obj) (P := Q) X Y)
      (ToType X.obj) (ToType Y.obj) :=
  InducedWideCategory.instFunLike WideSubcategory.obj Q X Y

instance WideSubcategory.concreteCategory :
    ConcreteCategory (WideSubcategory Q)
      (InducedWideCategory.Hom (F := WideSubcategory.obj) (P := Q)) :=
  InducedWideCategory.concreteCategory WideSubcategory.obj Q

end ConcreteCategory

end CategoryTheory
