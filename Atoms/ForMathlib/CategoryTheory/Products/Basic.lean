import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Types.Basic

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Prod

open Opposite

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

theorem map_op_mkHom_apply (X : (A × B)ᵒᵖ ⥤ Type w) {a a' : A} {b b' : B} (f : a' ⟶ a)
    (g : b' ⟶ b) (x : X.obj (op (a, b))) :
    X.map (op (Prod.mkHom f g)) x =
      X.map (op (Prod.mkHom f (𝟙 b'))) (X.map (op (Prod.mkHom (𝟙 a) g)) x) := by
  rw [← Functor.map_comp_apply]
  refine congrArg (fun m => X.map m x) ?_
  apply Quiver.Hom.unop_inj
  apply CategoryTheory.Prod.hom_ext <;> simp

end CategoryTheory.Prod

namespace CategoryTheory

universe u

def prodCurry {A B : Type u} [SmallCategory A] [SmallCategory B]
    (X : (A × B)ᵒᵖ ⥤ Type u) : Bᵒᵖ ⥤ (Aᵒᵖ ⥤ Type u) :=
  Functor.curry.obj ((CategoryTheory.Prod.swap Bᵒᵖ Aᵒᵖ ⋙
    (prodOpEquiv (C := A) (D := B)).inverse) ⋙ X)

def prodCurryMap {A B : Type u} [SmallCategory A] [SmallCategory B]
    {X Y : (A × B)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y) : prodCurry X ⟶ prodCurry Y :=
  Functor.curry.map (Functor.whiskerLeft
    (CategoryTheory.Prod.swap Bᵒᵖ Aᵒᵖ ⋙
      (prodOpEquiv (C := A) (D := B)).inverse) φ)

section Fibre

open Limits Opposite

variable {A : Type u} [SmallCategory A] (J : Type u) [SmallCategory J] (j : J)

def fibreRestriction : ((A × J)ᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft _ _ (Type u)).obj (Prod.sectL A j).op

def fibreExtension : (Aᵒᵖ ⥤ Type u) ⥤ ((A × J)ᵒᵖ ⥤ Type u) where
  obj X :=
    { obj x := X.obj (op x.unop.1) × (x.unop.2 ⟶ j)
      map g := ↾fun z ↦ (X.map g.unop.1.op z.1, g.unop.2 ≫ z.2)
      map_id x := by
        refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
        simp
      map_comp g h := by
        refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
        simp }
  map f :=
    { app x := ↾fun z ↦ (f.app (op x.unop.1) z.1, z.2)
      naturality x y g := by
        refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
        simp [NatTrans.naturality_apply] }

instance preservesColimitsOfSize_fibreRestriction :
    PreservesColimitsOfSize.{u, u} (fibreRestriction (A := A) J j) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    ((Functor.whiskeringLeft _ _ (Type u)).obj (Prod.sectL A j).op))

instance preservesLimitsOfSize_fibreRestriction :
    PreservesLimitsOfSize.{u, u} (fibreRestriction (A := A) J j) :=
  inferInstanceAs (PreservesLimitsOfSize.{u, u}
    ((Functor.whiskeringLeft _ _ (Type u)).obj (Prod.sectL A j).op))

instance preservesMonomorphisms_fibreRestriction :
    (fibreRestriction (A := A) J j).PreservesMonomorphisms where
  preserves f hf := by
    rw [NatTrans.mono_iff_mono_app] at hf ⊢
    exact fun _ ↦ hf _

theorem hom_ext_fibreRestriction {X Y : (A × J)ᵒᵖ ⥤ Type u} {f g : X ⟶ Y}
    (h : ∀ j, (fibreRestriction J j).map f = (fibreRestriction J j).map g) : f = g :=
  NatTrans.ext (funext fun x ↦ NatTrans.congr_app (h x.unop.2) (op x.unop.1))

private def fibreTranspose {X : Aᵒᵖ ⥤ Type u} {Y : (A × J)ᵒᵖ ⥤ Type u}
    (ψ : (fibreExtension J j).obj X ⟶ Y) : X ⟶ (fibreRestriction J j).obj Y where
  app a := ↾fun x ↦ ψ.app (op (a.unop, j)) ((x, 𝟙 j) : X.obj a × (j ⟶ j))
  naturality a b g := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    refine (congrArg (ψ.app (op (b.unop, j))) ?_).trans
      (NatTrans.naturality_apply ψ ((Prod.sectL A j).op.map g) ((x, 𝟙 j) : X.obj a × (j ⟶ j)))
    exact Prod.ext rfl (Category.comp_id _).symm

private def fibreTransposeInv {X : Aᵒᵖ ⥤ Type u} {Y : (A × J)ᵒᵖ ⥤ Type u}
    (φ : X ⟶ (fibreRestriction J j).obj Y) : (fibreExtension J j).obj X ⟶ Y where
  app x := ↾fun z ↦
    Y.map (op ((𝟙 x.unop.1, z.2) : x.unop ⟶ (x.unop.1, j))) (φ.app (op x.unop.1) z.1)
  naturality x y g := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    refine ((congrArg (Y.map _) (NatTrans.naturality_apply φ g.unop.1.op z.1)).trans
      (Functor.map_comp_apply Y _ _ _).symm).trans
      (Eq.trans ?_ (Functor.map_comp_apply Y _ _ _))
    refine congrArg (fun h ↦ Y.map h (φ.app (op x.unop.1) z.1)) (Quiver.Hom.unop_inj ?_)
    exact Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
      (Category.comp_id (g.unop.2 ≫ z.2))

def fibreExtensionAdjunction : fibreExtension (A := A) J j ⊣ fibreRestriction J j :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun := fibreTranspose J j
          invFun := fibreTransposeInv J j
          left_inv ψ := by
            refine NatTrans.ext (funext fun x ↦ ConcreteCategory.hom_ext _ _ fun z ↦ ?_)
            refine (NatTrans.naturality_apply ψ
              (op ((𝟙 x.unop.1, z.2) : x.unop ⟶ (x.unop.1, j))) _).symm.trans
                (congrArg (ψ.app x) (Prod.ext ?_ (Category.comp_id z.2)))
            exact Functor.map_id_apply X _ z.1
          right_inv φ := by
            refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
            exact Functor.map_id_apply Y (op (a.unop, j)) (φ.app a x) }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

instance preservesMonomorphisms_fibreExtension :
    (fibreExtension (A := A) J j).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app] at hf ⊢
    intro x
    have hx := hf (op x.unop.1)
    rw [mono_iff_injective] at hx ⊢
    intro z z' h
    have h₁ := congrArg _root_.Prod.fst h
    have h₂ := congrArg _root_.Prod.snd h
    exact Prod.ext (hx h₁) h₂

def fibreCofan (k : J) (X : Aᵒᵖ ⥤ Type u) : Cofan (fun _ : k ⟶ j ↦ X) :=
  Cofan.mk ((fibreRestriction J k).obj ((fibreExtension J j).obj X)) fun s ↦
    { app a := ↾fun x ↦ ((x, s) : X.obj a × (k ⟶ j))
      naturality a b g := by
        refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
        exact Prod.ext rfl (Category.id_comp s).symm }

def isColimitFibreCofan (k : J) (X : Aᵒᵖ ⥤ Type u) : IsColimit (fibreCofan J j k X) :=
  Cofan.IsColimit.mk _
    (fun t ↦
      { app a := ↾fun (z : X.obj a × (k ⟶ j)) ↦ (t.inj z.2).app a z.1
        naturality a b g := by
          refine ConcreteCategory.hom_ext _ _ fun (z : X.obj a × (k ⟶ j)) ↦ ?_
          refine Eq.trans ?_ (NatTrans.naturality_apply (t.inj z.2) g z.1)
          exact congrArg (fun s ↦ (t.inj s).app b (X.map g z.1)) (Category.id_comp z.2) })
    (fun _ _ ↦ rfl)
    (fun t m hm ↦ by
      refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _
        fun (z : X.obj a × (k ⟶ j)) ↦ ?_)
      exact congrArg (fun φ ↦ φ z.1) (NatTrans.congr_app (hm z.2) a))

end Fibre

end CategoryTheory
