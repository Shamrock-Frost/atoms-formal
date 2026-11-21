import Atoms.ForMathlib.CategoryTheory.Elements
import Atoms.ForMathlib.CategoryTheory.EqToHom
import Atoms.TestCategory.BasicLocalizer.Basic

open CategoryTheory Opposite

namespace Atoms.TestCategory

universe u

def nerveFunctor (A : Type u) [SmallCategory A] : Cat.{u, u} ⥤ (Aᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft Aᵒᵖ (Cat.{u, u})ᵒᵖ (Type u)).obj (Over.mapFunctor A).op

variable {A : Type u} [SmallCategory A]

def nerveUnitApp (X : Aᵒᵖ ⥤ Type u) : X ⟶ (nerveFunctor A).obj ((elementsFunctor A).obj X) where
  app a := TypeCat.ofHom fun x => (Functor.elementSliceFunctor X x).toCatHom
  naturality a b g := by
    ext x
    exact Cat.Hom.ext (Functor.elementSliceFunctor_eq_map_comp X g x)

def nerveUnit (A : Type u) [SmallCategory A] :
    𝟭 (Aᵒᵖ ⥤ Type u) ⟶ elementsFunctor A ⋙ nerveFunctor A where
  app X := nerveUnitApp X
  naturality X Y α := by
    ext a x
    exact Cat.Hom.ext (Functor.elementSliceFunctor_naturality α x)

abbrev nerveElementFunctor (C : Cat.{u, u}) {a : Aᵒᵖ} (F : ((nerveFunctor A).obj C).obj a) :
    Over a.unop ⥤ C :=
  Cat.Hom.toFunctor (F : Cat.of (Over a.unop) ⟶ C)

def nerveFunctorObjIso (C : Cat.{u, u}) :
    (nerveFunctor A).obj C ≅ (Over.mapFunctor A).nerve C :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := Cat.Hom.toFunctor
      invFun := Cat.Hom.ofFunctor
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ => rfl)

@[simp]
theorem nerveFunctorObjIso_hom_app_apply (C : Cat.{u, u}) {a : Aᵒᵖ}
    (F : ((nerveFunctor A).obj C).obj a) :
    (nerveFunctorObjIso C).hom.app a F = nerveElementFunctor C F :=
  rfl

def nerveCounitFunctor (C : Cat.{u, u}) : (((nerveFunctor A).obj C).Elements)ᵒᵖ ⥤ C :=
  (NatTrans.mapElements (nerveFunctorObjIso C).hom).op ⋙
    (Over.mapFunctor A).nerveEvalTerminal (fun a => Over.mkIdIsTerminal a) C

theorem nerveElementFunctor_obj_eq (C : Cat.{u, u})
    {p q : (((nerveFunctor A).obj C).Elements)ᵒᵖ} (m : p ⟶ q) :
    (nerveElementFunctor C p.unop.2).obj (Over.mk (𝟙 p.unop.1.unop)) =
      (nerveElementFunctor C q.unop.2).obj (Over.mk (𝟙 p.unop.1.unop ≫ m.unop.1.unop)) :=
  (congrArg (fun F => (nerveElementFunctor C F).obj (Over.mk (𝟙 p.unop.1.unop))) m.unop.2).symm

theorem nerveCounitFunctor_map (C : Cat.{u, u}) {p q : (((nerveFunctor A).obj C).Elements)ᵒᵖ}
    (m : p ⟶ q) :
    (nerveCounitFunctor C).map m = eqToHom (nerveElementFunctor_obj_eq C m) ≫
      (nerveElementFunctor C q.unop.2).map
        (Over.homMk (𝟙 p.unop.1.unop ≫ m.unop.1.unop) (by simp) :
          Over.mk (𝟙 p.unop.1.unop ≫ m.unop.1.unop) ⟶ Over.mk (𝟙 q.unop.1.unop)) :=
  rfl

theorem nerveCounitFunctor_naturality {C D : Cat.{u, u}} (G : C ⟶ D) :
    (NatTrans.mapElements ((nerveFunctor A).map G)).op ⋙ nerveCounitFunctor D =
      nerveCounitFunctor C ⋙ G.toFunctor :=
  Functor.ext (fun _ => rfl)
    (fun _ _ _ => G.toFunctor.eqToHom_comp_map_eq_map_eqToHom_comp _ _ _ _ _)

def nerveCounit (A : Type u) [SmallCategory A] :
    nerveFunctor A ⋙ elementsFunctor A ⟶ 𝟭 Cat.{u, u} where
  app C := (nerveCounitFunctor C).toCatHom
  naturality _ _ G := Cat.Hom.ext (nerveCounitFunctor_naturality G)

theorem mapElements_nerveUnitApp_op_comp_nerveCounitFunctor (X : Aᵒᵖ ⥤ Type u) :
    (NatTrans.mapElements (nerveUnitApp X)).op ⋙
        nerveCounitFunctor ((elementsFunctor A).obj X) = 𝟭 _ :=
  Functor.ext_of_comp_faithful (CategoryOfElements.π X).op
    (fun p => congrArg op (Sigma.ext rfl (heq_of_eq
      (show X.map (𝟙 p.unop.1.unop).op p.unop.2 = p.unop.2 by simp))))
    (Functor.ext (fun _ => rfl) (fun p q m => by
      change (CategoryOfElements.π X).op.map ((nerveCounitFunctor _).map
        ((NatTrans.mapElements (nerveUnitApp X)).op.map m)) = _
      rw [nerveCounitFunctor_map]
      exact ((CategoryOfElements.π X).op.map_eqToHom_comp_eq _ _ _ _).trans (congrArg
        (fun l : op (op p.unop.1.unop) ⟶ op (op q.unop.1.unop) => eqToHom rfl ≫ l ≫ eqToHom rfl)
        (congrArg (fun l : p.unop.1.unop ⟶ q.unop.1.unop => l.op.op)
          (Category.id_comp m.unop.val.unop)))))

private theorem eqToHom_comp_map_map_from {C : Type*} [Category C] {a : A} (F : Over a ⥤ C)
    {f f' : Over a} (k : f ⟶ f')
    (e : F.obj ((Over.map f.hom).obj (Over.mk (𝟙 f.left))) =
      F.obj ((Over.map f'.hom).obj ((Over.map k.left).obj (Over.mk (𝟙 f.left)))))
    (h₁ : F.obj ((Over.map f.hom).obj (Over.mk (𝟙 f.left))) = F.obj f)
    (h₂ : F.obj ((Over.map f'.hom).obj (Over.mk (𝟙 f'.left))) = F.obj f') :
    eqToHom e ≫ F.map ((Over.map f'.hom).map
        ((Over.mkIdIsTerminal f'.left).from ((Over.map k.left).obj (Over.mk (𝟙 f.left))))) =
      eqToHom h₁ ≫ F.map k ≫ eqToHom h₂.symm := by
  rw [show eqToHom e = F.map (eqToHom (by simp [Over.map_obj_mk])) from (eqToHom_map F _).symm,
    show eqToHom h₁ = F.map (eqToHom (Over.map_hom_obj_mk_id f)) from (eqToHom_map F _).symm,
    show eqToHom h₂.symm = F.map (eqToHom (Over.map_hom_obj_mk_id f').symm) from
      (eqToHom_map F _).symm]
  simp only [← Functor.map_comp]
  congr 1
  ext
  simp

theorem elementSliceFunctor_comp_nerveCounitFunctor (C : Cat.{u, u}) {a : Aᵒᵖ}
    (F : ((nerveFunctor A).obj C).obj a) :
    Functor.elementSliceFunctor ((nerveFunctor A).obj C) F ⋙ nerveCounitFunctor C =
      nerveElementFunctor C F :=
  Functor.ext (fun f => congrArg (nerveElementFunctor C F).obj (Over.map_hom_obj_mk_id f))
    (fun _ f' k => eqToHom_comp_map_map_from (nerveElementFunctor C F) k _ _
      (congrArg (nerveElementFunctor C F).obj (Over.map_hom_obj_mk_id f')))

def nerveAdjunction (A : Type u) [SmallCategory A] : elementsFunctor A ⊣ nerveFunctor A where
  unit := nerveUnit A
  counit := nerveCounit A
  left_triangle_components X :=
    Cat.Hom.ext (mapElements_nerveUnitApp_op_comp_nerveCounitFunctor X)
  right_triangle_components C := by
    ext a F
    exact Cat.Hom.ext (elementSliceFunctor_comp_nerveCounitFunctor C F)

theorem nerveAdjunction_counit_app_obj (A : Type u) [SmallCategory A] (C : Cat.{u, u})
    (p : (elementsFunctor A).obj ((nerveFunctor A).obj C)) :
    ((nerveAdjunction A).counit.app C).toFunctor.obj p =
      (Cat.Hom.toFunctor (p.unop.2 : Cat.of (Over p.unop.1.unop) ⟶ C)).obj
        (Over.mk (𝟙 p.unop.1.unop)) :=
  rfl

theorem nerveAdjunction_unit_app_app_obj (A : Type u) [SmallCategory A] (X : Aᵒᵖ ⥤ Type u)
    (a : Aᵒᵖ) (x : X.obj a) (f : Over a.unop) :
    (Cat.Hom.toFunctor (((nerveAdjunction A).unit.app X).app a x :
        Cat.of (Over a.unop) ⟶ Cat.of (X.Elements)ᵒᵖ)).obj f =
      Opposite.op ⟨Opposite.op f.left, X.map f.hom.op x⟩ :=
  rfl

end Atoms.TestCategory
