import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

namespace CategoryTheory.Cat

open Limits

universe u

private def arrowOfNatTrans {X C : Cat.{u, u}} {F G : X ⟶ C} (τ : F.toFunctor ⟶ G.toFunctor) :
    ↥X ⥤ Arrow ↥C where
  obj x := Arrow.mk (τ.app x)
  map f := Arrow.homMk (F.toFunctor.map f) (G.toFunctor.map f) (τ.naturality f)
  map_id x := Arrow.hom_ext _ _ (F.toFunctor.map_id x) (G.toFunctor.map_id x)
  map_comp f g := Arrow.hom_ext _ _ (F.toFunctor.map_comp f g) (G.toFunctor.map_comp f g)

theorem exists_natTrans_of_isPushout {A A' B B' C : Cat.{u, u}} {α : A ⟶ A'}
    {i : A ⟶ B} {i' : A' ⟶ B'} {β : B ⟶ B'} (h : IsPushout α i i' β) {F G : B' ⟶ C}
    (τ₁ : (i' ≫ F).toFunctor ⟶ (i' ≫ G).toFunctor) (τ₂ : (β ≫ F).toFunctor ⟶ (β ≫ G).toFunctor)
    (hτ : ∀ a : ↥A,
      Arrow.mk (τ₁.app (α.toFunctor.obj a)) = Arrow.mk (τ₂.app (i.toFunctor.obj a))) :
    ∃ τ : F.toFunctor ⟶ G.toFunctor,
      ∀ a' : ↥A', Arrow.mk (τ.app (i'.toFunctor.obj a')) = Arrow.mk (τ₁.app a') := by
  have hw' : α.toFunctor ⋙ arrowOfNatTrans τ₁ = i.toFunctor ⋙ arrowOfNatTrans τ₂ :=
    CategoryTheory.Functor.ext (fun a => @id ((α.toFunctor ⋙ arrowOfNatTrans τ₁).obj a =
      (i.toFunctor ⋙ arrowOfNatTrans τ₂).obj a) (hτ a)) fun a b f => Arrow.hom_ext _ _
      (by
        rw [Arrow.comp_left, Arrow.comp_left, Arrow.eqToHom_left, Arrow.eqToHom_left]
        exact Functor.congr_hom (congrArg Cat.Hom.toFunctor (h.w =≫ F)) f)
      (by
        rw [Arrow.comp_right, Arrow.comp_right, Arrow.eqToHom_right, Arrow.eqToHom_right]
        exact Functor.congr_hom (congrArg Cat.Hom.toFunctor (h.w =≫ G)) f)
  have hw : α ≫ (arrowOfNatTrans τ₁).toCatHom = i ≫ (arrowOfNatTrans τ₂).toCatHom :=
    Cat.Hom.ext hw'
  let E : ↥B' ⥤ Arrow ↥C :=
    (h.desc (arrowOfNatTrans τ₁).toCatHom (arrowOfNatTrans τ₂).toCatHom hw).toFunctor
  have hL : E ⋙ Arrow.leftFunc = F.toFunctor := congrArg Cat.Hom.toFunctor
    (h.hom_ext ((h.inl_desc_assoc _ _ _ _).trans rfl) ((h.inr_desc_assoc _ _ _ _).trans rfl) :
      h.desc _ _ hw ≫ Arrow.leftFunc.toCatHom = F)
  have hR : E ⋙ Arrow.rightFunc = G.toFunctor := congrArg Cat.Hom.toFunctor
    (h.hom_ext ((h.inl_desc_assoc _ _ _ _).trans rfl) ((h.inr_desc_assoc _ _ _ _).trans rfl) :
      h.desc _ _ hw ≫ Arrow.rightFunc.toCatHom = G)
  refine ⟨eqToHom hL.symm ≫ Functor.whiskerLeft E Arrow.leftToRight ≫ eqToHom hR,
    fun a' => ?_⟩
  have hE : E.obj (i'.toFunctor.obj a') = Arrow.mk (τ₁.app a') :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (h.inl_desc _ _ hw)) a'
  simp only [NatTrans.comp_app, CategoryTheory.eqToHom_app, Functor.whiskerLeft_app,
    Arrow.leftToRight_app]
  simp only [Arrow.arrow_mk_eqToHom_comp]
  exact (Arrow.arrow_mk_comp_eqToHom _ _).trans ((Arrow.mk_eq _).trans hE)

end CategoryTheory.Cat
