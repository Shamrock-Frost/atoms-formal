import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

universe w v u

namespace CategoryTheory

open Limits

variable {A : Type u} [Category.{v} A]

theorem natTrans_app_app_map_app {C : Type*} [Category C] {F G : C ⥤ Aᵒᵖ ⥤ Type w} (η : F ⟶ G)
    {X Y : C} (u : X ⟶ Y) (a : Aᵒᵖ) (x : (F.obj X).obj a) :
    (η.app Y).app a ((F.map u).app a x) = (G.map u).app a ((η.app X).app a x) :=
  ConcreteCategory.congr_hom (NatTrans.naturality_app η a u) x

end CategoryTheory
